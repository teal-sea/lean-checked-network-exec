#!/usr/bin/env python3
"""Audit exact package 2 sources, ordinary builds, replays, axioms and fault control.
This does not launch Lean. Reproduce kernel checks with check_engine_module.py.
"""
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parent.parent
OUT=ROOT/'pilot/engine'
ALLOW={'propext','Classical.choice','Quot.sound'}
MODULES=[
 ('Stages','stages-02','stages2-replay'),
 ('Load','load2-15','load2-replay'),
 ('Projection','project2-final-build','project2-final-replay'),
 ('Exponential','exp2-final-exp-build','exp2-final-exp-replay'),
 ('Softmax','exp2-final-soft-build','exp2-final-soft-replay'),
 ('Downstream','downstream2-fresh','downstream2-replay'),
 ('Mixing','mixing2-fresh','mixing2-replay'),
 ('Attention','down2-attention-final2-build','down2-attention-final2-replay'),
 ('Argmax','argmax2-02','argmax2-replay'),
 ('Correct','correct2-03','correct2-replay')]
STAGES={
 'LoadStage':'load_sound','ProjectStage':'project_eq','EmbedStage':'embed_eq',
 'ScoreStage':'scores_eq','ExpStage':'exp_eq','SoftmaxStage':'softmax_eq',
 'HeadOutputStage':'head_output_eq','AttentionStage':'attention_eq',
 'ResidualStage':'residual_eq','HiddenStage':'mlp_hidden_eq',
 'MlpOutputStage':'mlp_output_eq','FinalStage':'final_eq',
 'UnembedStage':'unembed_eq','ArgmaxStage':'argmax_eq',
 'ForwardStage':'forward_eq','EngineCorrect':'engine_correct'}

sha=lambda b:hashlib.sha256(b).hexdigest()
file_sha=lambda p:sha(p.read_bytes())

def original(p):
    backup=p.with_name(p.name+'.raw.gz')
    return gzip.decompress(backup.read_bytes()) if backup.exists() else p.read_bytes()

for record in json.loads((OUT/'package2-normalization.json').read_text()):
    p=ROOT/record['path']
    assert sha(original(p))==record['raw_sha256']
    assert file_sha(p)==record['normalized_sha256']

# The contract, input program, model and accepted package 1 sources must be unchanged.
unchanged=['rust/engine/src/lib.rs','lean/LcnExec/Translated/Engine.lean',
 'lean/LcnExec/Engine/Contract.lean','lean/LcnExec/Engine/Dot.lean',
 'lean/LcnExec/Engine/View.lean','pilot/transformer-int/TransformerInt/Model.lean']
for name in unchanged:
    base=subprocess.check_output(['git','show','49777e3:'+name],cwd=ROOT)
    assert base==(ROOT/name).read_bytes(),name
frozen=subprocess.check_output(['git','show','d02b3df:lean/LcnExec/Engine/Stages.lean'],cwd=ROOT)
assert frozen==(ROOT/'lean/LcnExec/Engine/Stages.lean').read_bytes()

sources=list((ROOT/'lean/LcnExec/Engine').glob('*.lean'))
for p in sources:
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|extern|implemented_by)\b',p.read_text()),p
for p in (ROOT/'lean').rglob('*.lean'):
    if '.lake' not in p.parts:
        assert not re.search(r'\b(sorry|admit)\b',p.read_text()),p

full='\n'.join(p.read_text() for p in sources)
for stage,name in STAGES.items():
    assert re.search(r'^theorem '+name+r' : '+stage+r' :=',full,re.M),(name,stage)

records=[]
all_names=[]
for short,build_label,replay_label in MODULES:
    module='LcnExec.Engine.'+short
    src=ROOT/f'lean/LcnExec/Engine/{short}.lean'
    obj=ROOT/f'lean/.lake/build/lib/lean/LcnExec/Engine/{short}.olean'
    text=src.read_text()
    names=re.findall(r'^theorem (\w+)',text,re.M)
    printed=re.findall(r'^#print axioms (\w+)$',text,re.M)
    assert len(names)==len(set(names))==len(printed)==len(set(printed))
    assert set(names)==set(printed)
    all_names.extend(names)
    log=original(OUT/(build_label+'.log')).decode()
    assert not re.search(r'(?m)^(?:error|warning)(?:\([^)]*\))?:',log)
    audits=re.findall(r"'LcnExec\.Engine\.(\w+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    selected=[(n,[a.strip() for a in axs.split(',') if a.strip()]) for n,axs in audits if n in names]
    assert [n for n,_ in selected]==printed,(short,selected,printed)
    assert all(set(axs)<=ALLOW for _,axs in selected)
    receipts=[]
    for label,tail in [(build_label,['lake','build',module]),(replay_label,['lake','env','leanchecker',module])]:
        p=OUT/(label+'.json')
        receipt=json.loads(p.read_text())
        cmd=receipt['command']
        assert receipt['exit']==0 and receipt['module']==module
        assert cmd[:2]==['flock','/home/thomas/.hermes/cache/scratch/lean-single-check.lock']
        assert all(x in cmd for x in ['MemoryMax=6G','CPUQuota=200%','LEAN_NUM_THREADS=2'])
        assert cmd[-len(tail):]==tail and receipt['available_gib_before']>=12
        raw=original(p.with_suffix('.log')).decode()
        assert not re.search(r'(?m)^(?:error|warning)(?:\([^)]*\))?:',raw)
        receipts.append(receipt)
    assert obj.is_file()
    records.append({'module':module,'source_sha256':file_sha(src),'object_sha256':file_sha(obj),
      'theorems':names,'axioms':dict(selected),'build_label':build_label,'build':receipts[0],
      'replay_label':replay_label,'replay':receipts[1]})
assert len(all_names)==len(set(all_names))

# Bind all prior worker source/object claims, not their narrative summaries.
worker=json.loads((OUT/'down2-ACCEPTED.json').read_text())
for m in worker['modules']:
    assert file_sha(ROOT/m['source'])==m['source_sha256']
    assert file_sha(ROOT/m['object'])==m['object_sha256']
for name,key in [('load2-ACCEPTED.json','file_sha256'),('exp2-ACCEPTED.json','file_sha256'),('project2-ACCEPTED.json','sha256')]:
    for rel,digest in json.loads((OUT/name).read_text())[key].items():
        p=Path(rel) if rel.startswith('/') else ROOT/rel
        assert sha(original(p))==digest,(name,rel)

fault=OUT/'fault2/attempt-02'
fr=json.loads((fault/'RESULT.json').read_text())
assert fr['status']=='passed'
for name,digest in fr['source_hashes'].items():
    assert sha(original(fault/name))==digest,name
base=(ROOT/'rust/engine/src/lib.rs').read_bytes()
assert (fault/'positive-lib.rs').read_bytes()==base
assert (fault/'changed-lib.rs').read_bytes()==base.replace(b'acc += x[i] * y[i];',b'acc += x[0] * y[i];')
assert gzip.decompress((fault/'positive-Engine.lean.gz').read_bytes())==(ROOT/'lean/LcnExec/Translated/Engine.lean').read_bytes()
assert gzip.decompress((fault/'changed-Engine.lean.gz').read_bytes())!=gzip.decompress((fault/'positive-Engine.lean.gz').read_bytes())
exits={r['label']:r['exit'] for r in fr['records']}
assert exits=={'positive-translate':0,'positive-translation-build':0,'positive-dot-proof':0,
              'changed-translate':0,'changed-translation-build':0,'changed-dot-proof':1}
assert '⊢ ↑(↑x)[↑i] = ↑(↑x)[0]' in original(fault/'changed-dot-proof.log').decode()
assert 'sorryAx' not in original(fault/'positive-dot-proof.log').decode()

# Count recorded development processes separately from expected negative controls.
changed=subprocess.check_output(['git','diff','49777e3','--name-only','--','pilot/engine'],cwd=ROOT,text=True).splitlines()
processes=[]
for name in changed:
    if not name.endswith('.json') or '/fault2/' in name:
        continue
    p=ROOT/name
    try: j=json.loads(p.read_text())
    except (ValueError,OSError): continue
    if isinstance(j,dict) and isinstance(j.get('command'),list) and 'module' in j and 'exit' in j:
        processes.append({'path':name,'exit':j['exit'],'replay':'leanchecker' in j['command']})

compiler=Path.home()/'.elan/toolchains/leanprover--lean4---v4.35.0/bin'
receipt={'status':'passed','contract':'LcnExec.Engine.EngineCorrect, unchanged from 49777e3',
 'freeze_commit':'d02b3df34bb42c219baf6e51a05ce5e25d112b8f','stages':STAGES,
 'new_module_count':len(records),'new_theorem_count':len(all_names),'modules':records,
 'compiler_sha256':{n:file_sha(compiler/n) for n in ['lean','leanchecker','lake']},
 'unchanged_source_sha256':{n:file_sha(ROOT/n) for n in unchanged},
 'fault_control':'pilot/engine/fault2/attempt-02/RESULT.json','fault_exits':exits,
 'development_processes':processes,'recorded_process_count':len(processes),
 'recorded_nonzero_count':sum(p['exit']!=0 for p in processes),
 'recorded_zero_count':sum(p['exit']==0 for p in processes),
 'unreceipted_timeout_logs':['load2-07.log','project2-embed-a1.log','exp2-01.log','down2-residual-a1-fix2.log'],
 'limits':['No gate 4 generated modules built or replayed','No trained-instance faithful-decoding or load theorem',
           'No fresh replay of whole dependency closure or third kernel','Translator and rustc are not certified',
           'Successful leanchecker is silent; authentic exit status is the replay verdict',
           'Wall times include shared-lock waits and Lake setup; RSS is child maximum, not aggregate RSS']}
(OUT/'package2-ACCEPTED.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['status','new_module_count','new_theorem_count','recorded_process_count','recorded_zero_count','recorded_nonzero_count']}))
