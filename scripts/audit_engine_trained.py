#!/usr/bin/env python3
"""Authenticate the local conditional theorem evidence. No proof checker is launched."""
import hashlib
import json
from pathlib import Path
import re
import sys
ROOT=Path(__file__).resolve().parent.parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    p=ROOT/'pilot/engine'
    expected={
      'LoadComplete':'trained3-loadcomplete-7',
      'Trained.Emb':'trained3-pilot-emb-5',
      'Trained.WQ':'trained3-wq', 'Trained.WK':'trained3-wk',
      'Trained.WV':'trained3-wv', 'Trained.WO':'trained3-wo',
      'Trained.Win':'trained3-win', 'Trained.Wout':'trained3-wout-structural',
      'Trained.U':'trained3-u-2', 'Trained.Vectors':'trained3-vectors-2',
      'Trained.Weights':'trained3-weights', 'Trained':'trained3-final'}
    rows=[]
    for suffix,label in expected.items():
        receipt=json.loads((p/(label+'.json')).read_text())
        module='LcnExec.Engine.'+suffix
        assert receipt['exit']==0 and receipt['module']==module
        log=p/(label+'.log')
        assert 'error:' not in log.read_text()
        assert 'warning:' not in log.read_text()
        rows.append({'module':module,'receipt':label+'.json','receipt_sha256':sha(p/(label+'.json')),'log_sha256':sha(log),'wall_seconds':receipt['wall_seconds'],'peak_rss_kib':receipt['peak_rss_kib']})
    theorem_names=['trained_load_ok','trained_view','accepted_weights_nonempty','trained_engine_adds_of']
    log=(p/'trained3-final.log').read_text()
    axioms={}
    for n in theorem_names:
        found=re.findall(r"'LcnExec.Engine\."+n+r"' depends on axioms: \[([^\]]*)\]",log)
        assert len(found)==1
        a=[v.strip() for v in found[0].split(',')]
        assert a==['propext','Classical.choice','Quot.sound']
        axioms[n]=a
    replay=json.loads((p/'trained3-final-replay.json').read_text())
    assert replay['exit']==0 and replay['module']=='LcnExec.Engine.Trained'
    assert replay['command'][-3:]==['env','leanchecker','LcnExec.Engine.Trained']
    seen=set();todo=['LcnExec.Engine.Trained'];closure={}
    while todo:
        m=todo.pop()
        if m in seen:continue
        seen.add(m)
        src=ROOT/'lean'/(m.replace('.','/')+'.lean')
        obj=ROOT/'lean/.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
        assert src.is_file() and obj.is_file(),m
        text=src.read_text()
        assert re.search(r'\b(sorry|admit|native_decide)\b',text) is None,m
        closure[m]={'source_sha256':sha(src),'olean_sha256':sha(obj)}
        todo += [n for n in re.findall(r'^import ([\w.]+)$',text,re.M) if n.startswith(('LcnExec.','TransformerInt.'))]
    all_receipts=[]
    for f in sorted(p.glob('trained3-*.json')):
        if f.name == 'trained3-LOCAL-VERIFIED.json': continue
        r=json.loads(f.read_text())
        if 'exit' in r:
            all_receipts.append({'path':f.name,'exit':r['exit'],'module':r['module'],'wall_seconds':r['wall_seconds']})
    out={'scope':'local conditional trained theorem only','base_commit':'c1faf49a5f49652eada47d2c9cafd6f950b86f94','local_build':'passed','regular_module_replay':'passed','fresh_final_closure_replay':'not run','nanoda_final':'not run','unconditional_final':'staged, not compiled','axioms':axioms,'builds':rows,'replay':replay,'closure':closure,'local_project_closure_modules':len(closure),'required_new_modules':len(rows),'all_attempt_receipts':all_receipts,'attempts_with_receipts':len(all_receipts),'successful_attempt_receipts':sum(r['exit']==0 for r in all_receipts),'failed_attempt_receipts':sum(r['exit']!=0 for r in all_receipts),'interrupted_without_receipt':['trained3-wout.log','trained3-gate-u.log'],'generator_sha256':sha(ROOT/'scripts/gen_engine_trained.py'),'staged_final_source_sha256':sha(ROOT/'lean/LcnExec/Engine/TrainedFinal.lean')}
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
