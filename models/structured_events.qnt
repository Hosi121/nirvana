// Independent lexical AST cursor versus source PC. fixtures.qnt is exported
// from actual Rust Program/Node values by examples/structure_model.rs.
module structured_events {
  import fixtures.* from "./fixtures"

  type Frame = { looped: bool, first: int, next: int }
  type Key = { pc: int, phase: int, cursor: int, stack: List[Frame] }
  var s: {
    which: int, pc: int, phase: int, cursor: int, stack: List[Frame],
    remaining: int, status: int, bad: bool, trace: List[int],
    instruction: int, seen: Set[Key], reason: str, outcome: int
  }

  val c = cases.nth(s.which)
  val n = c.arena.nth(s.cursor)
  val source = c.code.nth(s.pc)
  val key = { pc: s.pc, phase: s.phase, cursor: s.cursor, stack: s.stack }

  action initialize(ids: Set[int]): bool = {
    nondet which = ids.oneOf()
    nondet budget = 0.to(6).oneOf()
    s' = { which: which, pc: 0, phase: 0, cursor: cases.nth(which).root,
      stack: [], remaining: budget, status: 0, bad: false, trace: [],
      instruction: -1, seen: Set(), reason: "", outcome: -1 }
  }
  action init = initialize(selected)

  action reject(reason: str): bool = s' = { ...s, bad: true, status: 4, reason: reason }
  action route(cursor: int, stack: List[Frame]): bool =
    if (s.seen.contains(key)) reject("silent-cycle")
    else s' = { ...s, cursor: cursor, stack: stack, seen: s.seen.union(Set(key)) }

  action unwind =
    if (s.stack.length() == 0) reject("fell-out-of-function")
    else {
      val top = s.stack.nth(s.stack.length() - 1)
      if (top.looped) route(top.first, s.stack)
      else route(top.next, s.stack.slice(0, s.stack.length() - 1))
    }

  action transfer = {
    val loops = 0.to(s.stack.length() - 1).filter(i => s.stack.nth(i).looped)
    if (loops.size() <= n.level) reject("invalid-transfer")
    else {
      // Counting enclosing loops avoids treating an If continuation as a loop.
      val target = loops.filter(i => loops.filter(j => j > i).size() == n.level)
        .fold(0, (sum, i) => sum + i)
      val frame = s.stack.nth(target)
      if (n.kind == 5) route(frame.next, s.stack.slice(0, target))
      else route(frame.first, s.stack.slice(0, target + 1))
    }
  }

  action guestStep =
    if (n.kind != 1 or n.pc != s.pc) reject("step-pc")
    else if (s.remaining == 0)
      s' = { ...s, status: 3, instruction: s.pc }
    else if (n.token != source.body) reject("ordered-body")
    else s' = { ...s, remaining: s.remaining - 1, instruction: s.pc,
      phase: 1, cursor: n.next, trace: s.trace.append(s.pc), seen: Set() }

  action evaluate =
    if ((n.kind != 2 and n.kind != 3) or n.token != source.expression)
      reject("condition-evaluation")
    else {
      // Outcomes are shared only after the expression tokens match. Only the
      // designated Load condition can fault in this first exported family.
      nondet outcome = (if (source.faulty) Set(0, 1, 2) else Set(0, 1)).oneOf()
      if (outcome == 2) s' = { ...s, status: 2, outcome: outcome }
      else {
        val nextPc = if (outcome == 1) source.yes else source.no
        val cursor = if (n.kind == 2) n.next
          else if (outcome == 1) n.first else n.other
        val stack = if (n.kind == 2) s.stack
          else s.stack.append({ looped: false, first: 0, next: n.next })
        s' = { ...s, pc: nextPc, phase: 0, cursor: cursor, stack: stack, outcome: outcome }
      }
    }

  action control =
    if (source.kind == 0) s' = { ...s, pc: source.yes, phase: 0 }
    else if (source.kind == 1) evaluate
    else if (n.kind != 7 or n.token != source.expression) reject("return-expression")
    else s' = { ...s, status: 1 }

  action step =
    if (s.status != 0) s' = s
    else if (c.early and s.remaining == 0 and s.phase == 1) reject("budget-before-control")
    else if (s.cursor == 0) unwind
    else if (n.kind == 4) route(n.first,
      s.stack.append({ looped: true, first: n.first, next: n.next }))
    else if (n.kind == 5 or n.kind == 6) transfer
    else if (s.phase == 0) guestStep
    else control

  invariant consistent = not(s.bad)
  invariant finiteBounds = s.remaining >= 0 and s.remaining <= 6
    and s.trace.length() <= 6 and s.stack.length() <= 8
  observation returned = s.status == 1
  observation faulted = s.status == 2
  observation suspended = s.status == 3
}
