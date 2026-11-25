#!/usr/bin/env python3
"""Retranslate a copied Rust crate, then reject a planted dot indexing fault.
Never edits the live Rust, translation, or positive compiled objects.
"""
import gzip
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
BASE_OUT = ROOT / 'pilot/engine/fault2'
BASE_OUT.mkdir(exist_ok=True)
OUT = BASE_OUT / f'attempt-{len(list(BASE_OUT.glob("attempt-*"))) + 1:02d}'
OUT.mkdir()
SCRATCH = Path(tempfile.mkdtemp(prefix='engine-fault2-', dir=os.environ['TMPDIR']))
ENV = dict(os.environ)
ENV['PATH'] = str(Path.home()/'.elan/bin') + ':' + ENV['PATH']
ENV['XDG_RUNTIME_DIR'] = f'/run/user/{os.getuid()}'
ENV['CI'] = '1'
ENV['CARGO_BUILD_JOBS'] = '4'
LOCK = '/home/thomas/.hermes/cache/scratch/lean-single-check.lock'
records = []

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def run(label, cmd, cwd, env=ENV, lean=False):
    mem = subprocess.check_output(['free','-g'], text=True)
    available = int(next(x for x in mem.splitlines() if x.startswith('Mem:')).split()[-1])
    assert available >= 12, mem
    (OUT/(label+'-host.txt')).write_text(mem)
    if lean:
        cmd = ['flock',LOCK,'systemd-run','--user','--scope','-p','MemoryMax=6G',
               '-p','CPUQuota=200%','env','LEAN_NUM_THREADS=2',*cmd]
    start=time.monotonic()
    with (OUT/(label+'.log')).open('w') as log:
        p=subprocess.run(cmd,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT)
    r={'label':label,'command':cmd,'cwd':str(cwd),'exit':p.returncode,
       'wall_seconds':time.monotonic()-start,
       'peak_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
       'rss_method':'cumulative maximum RUSAGE_CHILDREN, not isolated per-step RSS',
       'available_gib_before':available,'log_sha256':sha(OUT/(label+'.log'))}
    records.append(r)
    (OUT/(label+'.json')).write_text(json.dumps(r,indent=2)+'\n')
    return p.returncode

# Minimal scratch copy; all third-party objects remain in the existing dependency cache.
for d in ['scripts','rust','lean']:
    (SCRATCH/d).mkdir()
for f in ['translate.sh','common.sh']:
    shutil.copy2(ROOT/'scripts'/f,SCRATCH/'scripts'/f)
shutil.copytree(ROOT/'rust/engine',SCRATCH/'rust/engine',ignore=shutil.ignore_patterns('target'))
(SCRATCH/'rust/transformer').symlink_to(ROOT/'rust/transformer',target_is_directory=True)
(SCRATCH/'toolchain').symlink_to(ROOT/'toolchain',target_is_directory=True)
base=(ROOT/'rust/engine/src/lib.rs').read_bytes()
source=SCRATCH/'rust/engine/src/lib.rs'
leanpath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT/'lean',env=ENV,text=True).strip()
leanbin=subprocess.check_output(['lake','env','which','lean'],cwd=ROOT/'lean',env=ENV,text=True).strip()

for label, changed in [('positive',False),('changed',True)]:
    if changed:
        text=base.decode()
        assert text.count('acc += x[i] * y[i];') == 1
        source.write_text(text.replace('acc += x[i] * y[i];','acc += x[0] * y[i];'))
    else:
        source.write_bytes(base)
    shutil.copy2(source,OUT/(label+'-lib.rs'))
    tenv=dict(ENV,ROOT=str(SCRATCH),WORK=str(SCRATCH/'work'),EVIDENCE=str(SCRATCH/'evidence'))
    assert run(label+'-translate',['nice','-n','10','bash',str(SCRATCH/'scripts/translate.sh'),'engine'],SCRATCH,tenv)==0
    translated=SCRATCH/'lean/LcnExec/Translated/Engine.lean'
    with (OUT/(label+'-Engine.lean.gz')).open('wb') as f:
        f.write(gzip.compress(translated.read_bytes(),mtime=0))
    for name in ['charon.log','aeneas.log','summary.txt']:
        shutil.copy2(SCRATCH/'evidence/translate/engine'/name,OUT/(label+'-'+name))
    lib=SCRATCH/label/'lib'
    (lib/'LcnExec/Translated').mkdir(parents=True)
    cenv=dict(ENV,LEAN_PATH=str(lib)+':'+leanpath)
    assert run(label+'-translation-build',[leanbin,'--root='+str(SCRATCH/'lean'),str(translated),'-o',str(lib/'LcnExec/Translated/Engine.olean')],ROOT/'lean',cenv,lean=True)==0
    code=run(label+'-dot-proof',[leanbin,str(ROOT/'lean/LcnExec/Engine/Dot.lean')],ROOT/'lean',cenv,lean=True)
    if changed:
        assert code != 0
        log=(OUT/(label+'-dot-proof.log')).read_text()
        assert 'error: unsolved goals' in log and '⊢ ↑(↑x)[↑i] = ↑(↑x)[0]' in log, log
        assert 'unknownIdentifier' not in log and 'failed to read' not in log
    else:
        assert code == 0
        assert 'sorryAx' not in (OUT/(label+'-dot-proof.log')).read_text()

assert (ROOT/'rust/engine/src/lib.rs').read_bytes()==base
receipt={'status':'passed','fault':'Rust dot: x[i] changed to x[0]',
         'scope':'Unmodified dot proof passes on freshly translated original Rust and fails on freshly translated mutated Rust',
         'scratch':str(SCRATCH),'records':records,
         'source_hashes':{p.name:sha(p) for p in OUT.iterdir() if p.is_file()},
         'positive_source_unchanged':True,
         'limits':'Fault control checks the dot stage, not a trained instance or gate 4. Per-step RSS is a cumulative child maximum.'}
(OUT/'RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':receipt['status'],'exits':{r['label']:r['exit'] for r in records},'evidence':str(OUT)}))
