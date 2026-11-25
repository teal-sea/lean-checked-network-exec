from datetime import datetime, timezone
from pathlib import Path
import argparse, base64, hashlib, json, re, shlex, subprocess as sp, tarfile

ap = argparse.ArgumentParser()
ap.add_argument('inner', type=Path)
ap.add_argument('outer', type=Path)
ap.add_argument('out', type=Path)
a = ap.parse_args()
h = Path.home()
s = h / '.hermes/cache/scratch/lcn-sol-20261123'
b = h / 'bin/boat-run'
i = h / 'worktrees/lcn-exec-general-lm-20261120'
lease = json.loads((s / 'ENGINE-BOX-WINDOW.json').read_text())
clamp = json.loads((i / 'evidence/e4-e6-integration/proof-checkpoint-sol-rescale-clamp/RECEIPT.json').read_text())
box, cutoff = lease['box'], lease['archive_after']
sha = lambda data: hashlib.sha256(data).hexdigest()
b64 = lambda data: shlex.quote(base64.b64encode(data).decode())
call = lambda *args, timeout=14: json.loads(sp.check_output([b, *args], timeout=timeout))
x = call('info', box, '--json')['sandbox']
assert box == 'bx_9m9mrg3q' and x['state'] in ('idle', 'running') and x['type'] == 'large' and x['archiveAfter'] == cutoff
assert (datetime.fromisoformat(cutoff) - datetime.now(timezone.utc)).total_seconds() > 155
inner, outer = a.inner.read_bytes(), a.outer.read_bytes()
for data in (inner, outer):
    assert len(data) < 40000 and not re.search(rb'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', data)
assert re.findall(rb'(?m)^theorem (\w+)', inner)[-1:] == [b'unembed_inner_spec']
assert re.findall(rb'(?m)^theorem (\w+)', outer)[-2:] == [b'unembed_loop0_spec', b'unembed_spec']
check = (b'import LcnExec.GeneralEngine.Unembed\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace LcnExec.GeneralEngine\n'
         + '''example (W : general_engine.Weights) (hW : LoadBounds W)
    (fin : Array I64 128#usize) (hfin : Bounded Envelope.final_stream fin) :
    general_engine.unembed W fin ⦃ out =>
      ints out = GeneralModel.unembed (toGeneralModel W) (ints fin) ∧
      Bounded Envelope.logit out ⦄ := unembed_spec W hW fin hfin
#print axioms unembed_inner_spec
#print axioms unembed_loop0_spec
#print axioms unembed_spec
end LcnExec.GeneralEngine
'''.encode())
cmd = f'''set -eu
cd "$HOME/e4/repo/lean"
tc="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin"
test "$(tr -d '\\r\\n' < lean-toolchain)" = leanprover/lean4:v4.35.0
awk '$1=="MemAvailable:" {{ok=($2 >= 10485760)}} END {{exit !ok}}' /proc/meminfo
test "$(sha256sum LcnExec/GeneralEngine/RescaleClamp.lean | cut -d ' ' -f 1)" = {clamp['source_sha256']}
test -f .lake/build/lib/lean/LcnExec/GeneralEngine/MlpOutputInner.olean
d=$(mktemp -d "$HOME/e4/qa-sol-unembed-XXXXXXXX")
mkdir -p "$d/LcnExec"
cp -as "$PWD/.lake/build/lib/lean/LcnExec/." "$d/LcnExec/"
m="$d/LcnExec/GeneralEngine"
for n in Unembed UnembedInner; do test ! -e "$m/$n.olean"; test ! -e "$m/$n.lean"; done
printf %s {b64(inner)} | base64 -d > "$m/UnembedInner.lean"
printf %s {b64(outer)} | base64 -d > "$m/Unembed.lean"
printf %s {b64(check)} | base64 -d > "$d/TypedAudit.lean"
test "$(sha256sum "$m/UnembedInner.lean" | cut -d ' ' -f 1)" = {sha(inner)}
test "$(sha256sum "$m/Unembed.lean" | cut -d ' ' -f 1)" = {sha(outer)}
"$tc/lean" --version > "$d/toolchain.txt"
exec 9>"$HOME/e4/locks/build.lock"
flock -w 9 9
export LEAN_NUM_THREADS=2 PATH="$tc:$PATH"
ir=0
orr=125
ar=125
touch "$d/Outer.log" "$d/Audit.log"
timeout 31s "$tc/lake" env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; "$2/lean" --root="$1" -o "$1/LcnExec/GeneralEngine/UnembedInner.olean" "$1/LcnExec/GeneralEngine/UnembedInner.lean"' bash "$d" "$tc" > "$d/Inner.log" 2>&1 || ir=$?
if test "$ir" = 0; then
 orr=0
 timeout 31s "$tc/lake" env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; "$2/lean" --root="$1" -o "$1/LcnExec/GeneralEngine/Unembed.olean" "$1/LcnExec/GeneralEngine/Unembed.lean"' bash "$d" "$tc" > "$d/Outer.log" 2>&1 || orr=$?
fi
if test "$orr" = 0; then
 ar=0
 timeout 16s "$tc/lake" env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; "$2/lean" "$1/TypedAudit.lean"' bash "$d" "$tc" > "$d/Audit.log" 2>&1 || ar=$?
fi
printf '%s %s %s\\n' "$ir" "$orr" "$ar" > "$d/exit.txt"
cp "$m/UnembedInner.lean" "$d/UnembedInner.lean.txt"
cp "$m/Unembed.lean" "$d/Unembed.lean.txt"
mv "$d/TypedAudit.lean" "$d/TypedAudit.lean.txt"
tar -C "$d" -czf "$d.tar.gz" -- Inner.log Outer.log Audit.log exit.txt toolchain.txt TypedAudit.lean.txt UnembedInner.lean.txt Unembed.lean.txt
printf '%s\\n' "$d"; sha256sum "$d.tar.gz"
'''
a.out.mkdir(parents=True, exist_ok=False)
q = call('exec', '--timeout', '105', box, '--', 'bash', '-lc', cmd, timeout=113)
(a.out / 'boat-command.json').write_text(json.dumps(q, indent=2) + '\n')
assert q['success'] and not q['stdoutTruncated'] and q['exitCode'] == 0, q.get('stderr')
rd, row = q['stdout'].strip().splitlines()
ah, apath = row.split()
assert re.fullmatch(r'/home/user/e4/qa-sol-unembed-[A-Za-z0-9]{8}', rd) and apath == rd + '.tar.gz'
archive = a.out / 'unembed-replay.tar.gz'
sp.run([b, 'scp', f'{box}:{apath}', archive], capture_output=True, check=True, timeout=19)
assert sha(archive.read_bytes()) == ah
expected = {'Inner.log', 'Outer.log', 'Audit.log', 'exit.txt', 'toolchain.txt', 'TypedAudit.lean.txt', 'UnembedInner.lean.txt', 'Unembed.lean.txt'}
with tarfile.open(archive) as z:
    members = z.getmembers()
    assert len(members) == len(expected) and {m.name for m in members} == expected and all(m.isfile() for m in members)
    files = {m.name: z.extractfile(m).read() for m in members}
assert (files['UnembedInner.lean.txt'], files['Unembed.lean.txt'], files['TypedAudit.lean.txt']) == (inner, outer, check)
for name, content in files.items():
    (a.out / name).write_bytes(content)
exits = dict(zip(('Inner', 'Outer', 'Audit'), map(int, files['exit.txt'].split()), strict=True))
e = {n: re.findall(r'(?m)^.*?:(\d+):(\d+): error(?:\([^)]*\))?: (.*)$', files[n+'.log'].decode()) for n in exits}
w = {n: len(re.findall(rb'(?m)^.*?:\d+:\d+: warning:', files[n+'.log'])) for n in exits}
r = {'box': box, 'cutoff': cutoff, 'exits': exits, 'errors': e, 'warnings': w, 'inner_sha256': sha(inner), 'outer_sha256': sha(outer), 'command_id': q['commandId'], 'finished_at': q['finishedAt'], 'files_sha256': {f.name: sha(f.read_bytes()) for f in sorted(a.out.iterdir())}}
(a.out / 'RECEIPT.json').write_text(json.dumps(r, indent=2) + '\n')
print('exits', exits, 'errors', e, 'warnings', w, flush=True)
which = next((n for n in exits if exits[n] not in (0, 125)), 'Audit')
print(files[which + '.log'].decode()[:5000])
