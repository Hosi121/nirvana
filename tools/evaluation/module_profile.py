"""Replay linked-leaf observer records; compare identical ELF/input contracts.

Full RAM is compared inside each generated C observer. Saved output contains
all registers, status/PC/budgets/fault and a RAM digest. Replay checks those
rows and the retained expected RAM bytes, without executing stored binaries.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path

MODES=[f'{mode}{opt}-64' for mode in ['core','readable','locals'] for opt in ['-O0','-O2']]
PROFILE='linked-leaf-state4-full-state-v1'


def require(test,message):
    if not test: raise ValueError(message)


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def words(path,width):
    lines=path.read_text().splitlines();result=[]
    for line in lines:
        tokens=line.split()
        require(len(tokens)==width and all(t.isascii() and t.isdecimal() and int(t)<2**64 for t in tokens),'module word row: '+path.name)
        result.append(list(map(int,tokens)))
    return result


def replay(directory):
    directory=Path(directory);report=json.loads((directory/'report.json').read_text())
    require(report['schema']=='nirvana-module-evaluation-v1' and report['profile']==PROFILE,'module profile schema')
    require(report['status'] in ['passed','unsupported','evaluator_error','budget_exhausted'],'module outcome')
    require(report.get('limits')==dict(root_instructions=256,cases=4096,expected_ram_bytes=134217728),'module observer limits')
    for key in ['requested_vectors','native_requested','stack_size','load_bias']:
        require(type(report[key]) is int and report[key]>=0,'module profile integer: '+key)
    inputs=words(directory/'inputs.txt',4);count=len(inputs)
    require(1<=count<=256 and report['requested_vectors']==count and report['native_requested'] in [0,count],'module input denominator')
    hashes={name:sha(directory/name) for name in ['report.json','input.elf','inputs.txt']}
    native=words(directory/'native-observed.tsv',5) if report['native_requested'] and (directory/'native-observed.tsv').exists() else None
    if native is not None:
        require(len(native)==count,'native module denominator');hashes['native-observed.tsv']=sha(directory/'native-observed.tsv')
    result={'status':report['status'],'report':report,'sha256':hashes,'native_rows':0,'generated_rows':0}
    if report['status']!='passed':
        require(isinstance(report.get('reason'),str) and bool(report['reason']),'module failure reason');return result
    for key in ['cases','native_compared','native_inconclusive','generated_compared','checked_ram_bytes','memory_base','memory_size','state_pointer','entry','resumption_cases']:
        require(type(report[key]) is int and report[key]>=0,'module observation integer: '+key)
    cases=words(directory/'cases.tsv',6);expected=words(directory/'expected.tsv',94)
    require(count<=len(cases)==len(expected)==report['cases']<=4096,'module case denominator')
    require(report['resumption_cases']==len(cases)-count and report['generated_compared']==len(cases)*6,'module resumption/generated denominator')
    require(report['checked_ram_bytes']==report['generated_compared']*report['memory_size'],'module RAM denominator')
    require((directory/'initial-registers.bin').stat().st_size==640,'module initial registers')
    offset=report['state_pointer']-report['memory_base'];size=report['memory_size']
    require(0<=offset<=size-32 and size*len(cases)<=128*1024*1024,'module state object or replay byte budget')
    for i,(case,row) in enumerate(zip(cases,expected)):
        require(row[0]==row[13] and row[7]+row[8]==case[5],'module register/budget observation')
        if i<count: require(case==[*inputs[i],report['entry'],1024],'module native entry profile')
        path=directory/f'memory-{i:04}.bin';memory=path.read_bytes()
        require(len(memory)==size,'module memory byte denominator')
        require(row[1:5]==[int.from_bytes(memory[offset+n*8:offset+n*8+8],'little') for n in range(4)],'module state memory words')
        digest=14695981039346656037
        for byte in memory: digest=((digest^byte)*1099511628211)%(2**64)
        require(digest==row[93],'module expected RAM digest');hashes[path.name]=sha(path)
    compared=0
    if report['native_requested']:
        require(native is not None,'missing native observations')
        for row,observed in zip(expected[:count],native):
            if row[5]==0:
                require(row[:5]==observed,'module native observations differ');compared+=1
    require(compared==report['native_compared'] and (count-compared if native is not None else 0)==report['native_inconclusive'],'module native comparison denominator')
    for mode in MODES:
        path=directory/(mode+'.observed.tsv');observed=words(path,94)
        require(observed==expected,'module generated observations differ: '+mode);hashes[path.name]=sha(path)
    for name in ['cases.tsv','expected.tsv','initial-registers.bin','selected.c']:
        hashes[name]=sha(directory/name)
    result.update(native_rows=compared,generated_rows=len(cases)*6,
                  full_ram='byte comparisons in the successful generated observer; replay of expected bytes and digest')
    return result


def compare(before,after):
    roots=[Path(before),Path(after)]
    indices=[{p.name:p for p in root.iterdir() if p.is_dir() and (p/'report.json').exists()} for root in roots]
    require(bool(indices[0]) and indices[0].keys()==indices[1].keys(),'module requested profile denominator')
    rows=[]
    for name in sorted(indices[0]):
        a,b=[replay(index[name]) for index in indices]
        for key in ['input.elf','inputs.txt']:
            require(a['sha256'][key]==b['sha256'][key],name+': changed module input')
        for key in ['profile','requested_vectors','native_requested','stack_size','load_bias','limits']:
            require(a['report'][key]==b['report'][key],name+': changed module contract')
        if all('native-observed.tsv' in r['sha256'] for r in [a,b]):
            require(a['sha256']['native-observed.tsv']==b['sha256']['native-observed.tsv'],name+': changed native observations')
        rows.append({'id':name,'before':a,'after':b,'regression':a['status']=='passed' and b['status']!='passed'})
    return {'schema':'nirvana-module-comparison-v1','requested':len(rows),
            'before':dict(Counter(r['before']['status'] for r in rows)),
            'after':dict(Counter(r['after']['status'] for r in rows)),
            'regressions':sum(r['regression'] for r in rows),
            'candidate_errors':sum(r['after']['status']=='evaluator_error' for r in rows),'rows':rows}
