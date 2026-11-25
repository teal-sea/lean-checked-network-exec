#!/usr/bin/env bash
set -euo pipefail
run=$1
cutoff=$2
cd "$HOME/e4/repo/lean"
tc="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0"
mod=LcnExec.GeneralEngine.Correct
thm=LcnExec.GeneralEngine.general_engine_correct
export PATH="$tc/bin:/usr/bin:/bin" LEAN_NUM_THREADS=2 TMPDIR="$run/tmp"
mkdir -m 700 "$TMPDIR"
export LEAN_PATH="$("$tc/bin/lake" env printenv LEAN_PATH)"
unset PYTHONPATH
exec 9>"$HOME/e4/locks/build.lock"
flock -w 12 9
printf '%s\n' "$LEAN_PATH" > "$run/lean-path.txt"
printf '%s\n' "$mod" "$thm" > "$run/scope.txt"
sha256sum --strict -c "$run/binaries.sha256" > "$run/binaries.log"
sha256sum --strict -c "$run/sources.sha256" > "$run/sources.before.log"
sha256sum --strict -c "$run/final-object.sha256" > "$run/final-object.before.log"
test "$(tr -d '\r\n' < lean-toolchain)" = leanprover/lean4:v4.35.0
"$tc/bin/lean" --version > "$run/lean-version.txt"
for r in /proc/loadavg /proc/meminfo; do cp "$r" "$run/${r##*/}.before"; done
df -Pk "$run" > "$run/disk.before"
awk 'NR==2 {ok=($4>=41943040 && $5+0<90)} END {exit !ok}' "$run/disk.before"
awk '$1=="MemAvailable:" {ok=($2>=10485760)} END {exit !ok}' "$run/meminfo.before"
objects() {
  /usr/bin/python3 -I - "$PWD" "$tc" "$1" <<'PY'
from pathlib import Path
import hashlib, os, sys
repo, tc, out = map(Path, sys.argv[1:4]); roots = [Path(p).resolve() for p in os.environ['LEAN_PATH'].split(':') if p]; expected = set((repo/'.lake/packages'/p/'.lake/build/lib/lean').resolve() for p in ('Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib')); expected.update(p.resolve() for p in (repo/'.lake/build/lib/lean',repo.parent/'toolchain/aeneas/backends/lean/.lake/build/lib/lean',tc/'lib/lean')); assert set(roots)==expected and len(roots)==len(expected), roots
with out.open('x') as f:
    for root in roots:
        if root == (repo/'.lake/packages/Cli/.lake/build/lib/lean').resolve() and not root.exists():
            print('absent',0,root,sep='\t',file=f)
            continue
        assert root.is_dir(), root
        paths=sorted(p for p in root.rglob('*.olean*') if p.is_file()); assert paths, root
        for p in paths:
            assert p.resolve().is_relative_to(root), (p,p.resolve(),root)
            with p.open('rb') as stream: digest=hashlib.file_digest(stream,'sha256').hexdigest()
            print(digest,p.stat().st_size,p,sep='\t',file=f)
PY
}
step() {
  local key=$1 ceiling=$2 budget now ec=0
  shift 2
  now=$(date +%s)
  budget=$((cutoff - now - 180))
  if ((budget<30)); then printf '%s\n' 125 > "$run/$key.exit"; return 125; fi
  if ((budget>ceiling)); then budget=$ceiling; fi
  printf 'start %s at %s with %ss\n' "$key" "$(date -u +%FT%TZ)" "$budget"
  printf '%s\n' "$@" > "$run/$key.argv"
  /usr/bin/time -v -o "$run/$key.time" timeout --signal=TERM --kill-after=8s "$budget" "$@" > "$run/$key.stdout" 2> "$run/$key.stderr" || ec=$?
  printf '%s\n' "$ec" > "$run/$key.exit"
  printf 'end %s exit %s\n' "$key" "$ec"
  return "$ec"
}
trap 'ec=$?; printf "%s\n" "$ec" > "$run/suite.exit"' EXIT
printf '%s\n' ready > "$run/READY"
objects "$run/objects.before.tsv"
step ordinary 120 "$tc/bin/leanchecker" "$mod"
fresh=0
step fresh 1750 "$tc/bin/leanchecker" --fresh "$mod" || fresh=$?
exp=0
step export 960 "$tc/bin/leanexport" "$mod" -- "$thm" || exp=$?
if ((exp==0)) && test -s "$run/export.stdout"; then
  stat -c '%s' "$run/export.stdout" > "$run/export.bytes"
  sha256sum "$run/export.stdout" > "$run/export.sha256"
  /usr/bin/python3 -I - "$run" <<'PY'
from pathlib import Path
import json,sys
r=Path(sys.argv[1])
p={'export_file_path':str(r/'export.stdout'),'use_stdin':False,'permitted_axioms':['propext','Classical.choice','Quot.sound'],'unpermitted_axiom_hard_error':True,'nat_extension':True,'string_extension':True,'pp_declars':[],'pp_to_stdout':False,'print_success_message':True}
(r/'nanoda.json').write_text(json.dumps(p,indent=2)+'\n')
PY
  na=0
  step nanoda 925 "$tc/bin/nanoda_bin" "$run/nanoda.json" || na=$?
else
  na=125
  printf '%s\n' "$na" > "$run/nanoda.exit"
fi
objects "$run/objects.after.tsv"
cmp "$run/objects.before.tsv" "$run/objects.after.tsv"
sha256sum --strict -c "$run/sources.sha256" > "$run/sources.after.log"
sha256sum --strict -c "$run/final-object.sha256" > "$run/final-object.after.log"
sha256sum --strict -c "$run/binaries.sha256" > "$run/binaries.after.log"
[[ "$fresh $exp $na" == '0 0 0' ]]
