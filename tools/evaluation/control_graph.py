"""Root/exit-preserving edit distance for normalized Clang C control graphs.

Metric: nirvana-control-topology-v1 (not SAILR CFGED or semantic equivalence).
Labels are entry, exit, return, flow and branch. Edges are directed and retain
multiplicity; branch polarity and expression text are erased. Unreachable
blocks are removed, except the distinguished exit. Single-successor flow
blocks are contracted, including data operations and goto trampolines. A
self-loop remains. Consequently this metric observes control topology, not
arithmetic, effect contents or duplication inside a basic block.

Node insertion/deletion/relabel costs 1; edge insertion/deletion costs 1.
Entry and exit must correspond. Search considers maximum-cardinality partial
bijections: adding a remaining pair costs at most one relabel instead of two
node edits, and cannot increase edge cost over deleting/inserting its incident
edges. A finite search returns an exact result or a witnessed upper bound,
with a lower bound from unmatched labels and edge partitions. No third-party packages.
"""
from collections import Counter
import re
import time

METRIC = 'nirvana-control-topology-v1'
MAX_BLOCKS = 2048
MAX_DISTANCE_NODES = 64


class Unsupported(ValueError):
    """The selected function or dump is outside this reader's contract."""


def validate(graph):
    nodes = graph['nodes']
    edges = graph['edges']
    if not nodes or len(nodes) > MAX_BLOCKS:
        raise Unsupported('graph size limit')
    if any(type(n) is not int for n in nodes):
        raise Unsupported('node IDs must be integers')
    if any(kind not in {'entry', 'exit', 'return', 'flow', 'branch'} for kind in nodes.values()):
        raise Unsupported('unknown node label')
    if any(sum(kind == expected for kind in nodes.values()) != 1 for expected in ['entry', 'exit']):
        raise Unsupported('require exactly one entry and exit')
    if any(a not in nodes or b not in nodes for a, b in edges):
        raise Unsupported('edge outside graph')


def graph_from_json(value):
    """Restore integer node IDs from a saved normalized graph artifact."""
    if any(str(n) != str(int(n)) for n in value['nodes']):
        raise Unsupported('noncanonical JSON node ID')
    result = {'nodes': {int(n): k for n, k in value['nodes'].items()},
              'edges': [tuple(edge) for edge in value['edges']]}
    validate(result)
    return result


def parse_dump(text, function):
    """Read one named C function from Clang 18 debug.DumpCFG output.

    Explicit NULL and (Unreachable) successor slots are recorded as pruned.
    Malformed successor counts, duplicate blocks, missing endpoints, unknown
    block annotations and missing non-exit successor lists are rejected.
    """
    if len(text.encode()) > 4 * 1024 * 1024:
        raise Unsupported('dump size limit')
    headers = [i for i, line in enumerate(text.splitlines())
               if line and not line[0].isspace() and re.search(r'\b' + re.escape(function) + r'\s*\(', line)]
    if len(headers) != 1:
        raise Unsupported('require one named function in CFG dump')
    nodes, successors, returns = {}, {}, set()
    current = None
    pruned = gotos = 0
    for line in text.splitlines()[headers[0] + 1:]:
        if line and not line[0].isspace():
            break
        block = re.fullmatch(r' \[B(\d+)(?: \((ENTRY|EXIT|NORETURN)\))?\]', line)
        if block:
            current = int(block[1])
            if current in nodes or len(nodes) >= MAX_BLOCKS:
                raise Unsupported('duplicate block or block limit')
            nodes[current] = {'ENTRY': 'entry', 'EXIT': 'exit'}.get(block[2], 'flow')
        elif line.startswith(' [B'):
            raise Unsupported('unknown block header')
        elif 'Succs (' in line:
            match = re.fullmatch(r'\s+Succs \((\d+)\):(.*)', line)
            if current is None or not match or current in successors:
                raise Unsupported('malformed successor list')
            tokens = match[2].split()
            if len(tokens) != int(match[1]):
                raise Unsupported('successor count mismatch')
            successors[current] = []
            for token in tokens:
                target = re.fullmatch(r'B(\d+)(\(Unreachable\))?', token)
                if token == 'NULL' or target and target[2]:
                    pruned += 1
                elif target:
                    successors[current].append(int(target[1]))
                else:
                    raise Unsupported('unknown successor token: ' + token)
        elif re.match(r'\s+\d+: return(?:\s|;)', line):
            returns.add(current)
        elif re.match(r'\s+T: goto\b', line):
            gotos += 1
    for node, kind in nodes.items():
        if kind != 'exit' and node not in successors:
            raise Unsupported('missing successor list')
        if kind == 'flow':
            nodes[node] = 'return' if node in returns else 'branch' if len(successors.get(node, [])) > 1 else 'flow'
    graph = {'nodes': nodes, 'edges': [(a, b) for a, rows in successors.items() for b in rows]}
    validate(graph)
    return graph, {'raw_blocks': len(nodes), 'pruned_successor_slots': pruned, 'gotos': gotos}


def normalize(graph):
    validate(graph)
    nodes = dict(graph['nodes'])
    edges = list(graph['edges'])
    entry = next(n for n, kind in nodes.items() if kind == 'entry')
    reachable, pending = set(), [entry]
    outgoing = {}
    for a, b in edges:
        outgoing.setdefault(a, []).append(b)
    while pending:
        node = pending.pop()
        if node not in reachable:
            reachable.add(node)
            pending.extend(outgoing.get(node, []))
    unreachable = {n for n in nodes if n not in reachable and nodes[n] != 'exit'}
    nodes = {n: k for n, k in nodes.items() if n not in unreachable}
    edges = [(a, b) for a, b in edges if a in nodes and b in nodes]
    contracted = 0
    while True:
        outgoing = {}
        for a, b in edges:
            outgoing.setdefault(a, []).append(b)
        node = next((n for n in sorted(nodes) if nodes[n] == 'flow'
                     and len(outgoing.get(n, [])) == 1 and outgoing[n][0] != n), None)
        if node is None:
            break
        target = outgoing[node][0]
        edges = [(a, target if b == node else b) for a, b in edges if a != node]
        del nodes[node]
        contracted += 1
    result = {'nodes': nodes, 'edges': sorted(edges)}
    validate(result)
    return result, {'unreachable_blocks': len(unreachable), 'contracted_flow_blocks': contracted}


def mapping_cost(left, right, mapping):
    """Replay a witness independently of the search's incremental cost."""
    validate(left)
    validate(right)
    if not set(mapping) <= set(left['nodes']) or not set(mapping.values()) <= set(right['nodes']):
        raise ValueError('mapping outside graph')
    if len(set(mapping.values())) != len(mapping):
        raise ValueError('mapping must be injective')
    for kind in ['entry', 'exit']:
        a = next(n for n, k in left['nodes'].items() if k == kind)
        b = next(n for n, k in right['nodes'].items() if k == kind)
        if mapping.get(a) != b:
            raise ValueError('mapping must preserve entry and exit')
    nodes = len(left['nodes']) + len(right['nodes']) - 2 * len(mapping)
    nodes += sum(left['nodes'][a] != right['nodes'][b] for a, b in mapping.items())
    projected = Counter((mapping[a], mapping[b]) for a, b in left['edges'] if a in mapping and b in mapping)
    omitted = sum(a not in mapping or b not in mapping for a, b in left['edges'])
    target = Counter(map(tuple, right['edges']))
    edges = omitted + sum(abs(projected[e] - target[e]) for e in projected.keys() | target.keys())
    return nodes + edges


def completion_bound(left, right, mapping, *, fixed_edges=None, fixed_labels=None):
    """Admissible cost for any maximum-cardinality completion of this injection.

    The smaller graph is on the left. Fixed/fixed edges are exact. For each
    fixed pair, incoming/outgoing edges to the remaining sets form disjoint
    partitions; internal remaining edges form one more. Every partition needs
    at least its edge-count difference in edits. Remaining labels contribute
    unavoidable mismatches, even when the larger side has inserted nodes.
    """
    ln, rn = left['nodes'], right['nodes']
    used = set(mapping.values())
    a, b = set(ln) - mapping.keys(), set(rn) - used
    labels_a, labels_b = Counter(ln[n] for n in a), Counter(rn[n] for n in b)
    labels = sum(max(0, count - labels_b[kind]) for kind, count in labels_a.items())
    if fixed_labels is None:
        fixed_labels = sum(ln[x] != rn[y] for x, y in mapping.items())
    if fixed_edges is None:
        le, re_ = Counter(left['edges']), Counter(right['edges'])
        fixed_edges = sum(abs(le[x, z] - re_[y, w])
                          for x, y in mapping.items() for z, w in mapping.items())
    def partitions(edges, fixed):
        outgoing, incoming = Counter(), Counter()
        internal = 0
        for x, y in edges:
            if x in fixed:
                if y not in fixed:
                    outgoing[x] += 1
            elif y in fixed:
                incoming[y] += 1
            else:
                internal += 1
        return outgoing, incoming, internal
    ao, ai, ae = partitions(left['edges'], mapping)
    bo, bi, be = partitions(right['edges'], used)
    boundary = sum(abs(ao[x] - bo[y]) + abs(ai[x] - bi[y]) for x, y in mapping.items())
    return len(rn) - len(ln) + fixed_labels + labels + fixed_edges + boundary + abs(ae - be)


def distance(left, right, *, max_states=100000, seconds=1.0):
    validate(left)
    validate(right)
    if max_states < 1 or not 0 < seconds < float('inf'):
        raise ValueError('require positive finite search budgets')
    if max(len(left['nodes']), len(right['nodes'])) > MAX_DISTANCE_NODES:
        raise Unsupported('distance node limit')
    start = time.monotonic()
    original_left, original_right = left, right
    swapped = len(left['nodes']) > len(right['nodes'])
    if swapped:
        left, right = right, left
    ln, rn = left['nodes'], right['nodes']
    le, re_ = Counter(map(tuple, left['edges'])), Counter(map(tuple, right['edges']))
    mapping = {next(n for n, k in ln.items() if k == kind): next(n for n, k in rn.items() if k == kind)
               for kind in ['entry', 'exit']}
    remaining = set(rn) - set(mapping.values())
    degree_l = Counter(n for edge in left['edges'] for n in edge)
    degree_r = Counter(n for edge in right['edges'] for n in edge)
    order = sorted(set(ln) - set(mapping), key=lambda n: (-degree_l[n], ln[n], n))
    greedy = dict(mapping)
    available = set(remaining)
    for a in order:
        b = min(available, key=lambda b: (ln[a] != rn[b], abs(degree_l[a] - degree_r[b]), b))
        greedy[a] = b
        available.remove(b)
    best, witness = mapping_cost(left, right, greedy), greedy
    node_delta = len(rn) - len(ln)
    edge_delta = abs(len(left['edges']) - len(right['edges']))
    lower = completion_bound(left, right, mapping)
    states, limit = 0, None

    def edge_increment(a, b):
        return abs(le[a, a] - re_[b, b]) + sum(
            abs(le[a, x] - re_[b, y]) + abs(le[x, a] - re_[y, b]) for x, y in mapping.items())

    def visit(index, labels, edge_cost):
        nonlocal best, witness, states, limit
        if best == lower:
            return
        if states >= max_states:
            limit = 'state_limit'
            return
        if time.monotonic() - start >= seconds:
            limit = 'time_limit'
            return
        states += 1
        if node_delta + labels + max(edge_delta, edge_cost) >= best:
            return
        if completion_bound(left, right, mapping, fixed_edges=edge_cost, fixed_labels=labels) >= best:
            return
        if index == len(order):
            cost = mapping_cost(left, right, mapping)
            if cost < best:
                best, witness = cost, dict(mapping)
            return
        a = order[index]
        choices = sorted(remaining, key=lambda b: (ln[a] != rn[b], edge_increment(a, b), b))
        for b in choices:
            extra = edge_increment(a, b)
            mapping[a] = b
            remaining.remove(b)
            visit(index + 1, labels + (ln[a] != rn[b]), edge_cost + extra)
            remaining.add(b)
            del mapping[a]
            if limit or best == lower:
                break

    labels = sum(ln[a] != rn[b] for a, b in mapping.items())
    initial_edges = sum(abs(le[a, x] - re_[b, y]) for a, b in mapping.items() for x, y in mapping.items())
    visit(0, labels, initial_edges)
    if swapped:
        witness = {b: a for a, b in witness.items()}
    assert mapping_cost(original_left, original_right, witness) == best
    exact = limit is None or best == lower
    return {'metric': METRIC, 'status': 'exact' if exact else 'upper_bound',
            'lower_bound': best if exact else lower, 'upper_bound': best,
            'reason': 'partition_lower_bound' if best == lower else 'search_complete' if exact else limit,
            'mapping': sorted(witness.items()), 'search_states': states,
            'wall_seconds': time.monotonic() - start}
