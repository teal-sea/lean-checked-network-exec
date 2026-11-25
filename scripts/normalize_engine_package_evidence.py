#!/usr/bin/env python3
"""Normalize only package 2 display evidence; preserve original bytes and hashes."""
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
ROOT = Path(__file__).resolve().parent.parent
paths = subprocess.check_output(['git','diff','--cached','--name-only','49777e3'],cwd=ROOT,text=True).splitlines()
records=[]
for name in paths:
    p=ROOT/name
    if p.suffix not in {'.log','.part'} or not name.startswith('pilot/engine/'):
        continue
    raw=p.read_bytes()
    normalized=('\n'.join(x.rstrip() for x in raw.decode().splitlines()).rstrip()+'\n').encode()
    if raw==normalized:
        continue
    backup=p.with_name(p.name+'.raw.gz')
    assert not backup.exists(),backup
    backup.write_bytes(gzip.compress(raw,mtime=0))
    p.write_bytes(normalized)
    records.append({'path':name,'raw_archive':str(backup.relative_to(ROOT)),
                    'raw_sha256':hashlib.sha256(raw).hexdigest(),
                    'normalized_sha256':hashlib.sha256(normalized).hexdigest()})
out=ROOT/'pilot/engine/package2-normalization.json'
assert not out.exists(),out
out.write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'normalized_files':len(records),'original_bytes_retained':True}))
