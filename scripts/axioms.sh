#!/usr/bin/env bash
# `#print axioms` on every theorem named in gates/theorems.txt, compared with gates/allowlist.
# Any axiom outside the allowlist fails the gate and is printed by name. An axiom brought in by
# a translation (for example for a function Aeneas cannot model) is a failure, never an
# allowlist addition. Output: evidence/axioms/.
source "$(dirname "$0")/common.sh"
need lake
need python3

out="$EVIDENCE/axioms"
probe="$WORK/axioms/PrintAxioms.lean"
rm -rf "$out" "$(dirname "$probe")"
mkdir -p "$out" "$(dirname "$probe")"
[ -n "$(theorems)" ] || die "no theorems listed in ${THEOREMS#"$ROOT"/}"
{
  theorems | awk '{print "import " $1}' | sort -u
  theorems | awk '{print "#print axioms " $2}'
} > "$probe"
cp "$probe" "$out/PrintAxioms.lean"

(cd "$LEAN_DIR" && lake env lean "$probe") > "$out/print-axioms.out" 2>&1 \
  || die "lean failed on the axiom probe (evidence/axioms/print-axioms.out)"

set +e
python3 - "$out/print-axioms.out" "$THEOREMS" "$ALLOWLIST" > "$out/result.txt" <<'PY'
import re
import sys

log = open(sys.argv[1]).read()
def entries(path):
    return [l.split() for l in open(path) if l.strip() and not l.lstrip().startswith("#")]
names = [e[1] for e in entries(sys.argv[2])]
allowed = {e[0] for e in entries(sys.argv[3])}
found = {}
# `#print axioms` wraps long lists over several lines, so the whole output is parsed.
for m in re.finditer(r"'(\S+)' depends on axioms: \[([^\]]*)\]", log, re.S):
    found[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
for m in re.finditer(r"'(\S+)' does not depend on any axioms", log):
    found[m.group(1)] = []
failed = False
for name in names:
    if name not in found:
        print(f"{name}: no axioms line in the output")
        failed = True
        continue
    extra = sorted(set(found[name]) - allowed)
    note = f"  NOT ALLOWED: {', '.join(extra)}" if extra else ""
    print(f"{name}: [{', '.join(found[name])}]{note}")
    failed |= bool(extra)
print("axioms: FAIL" if failed else f"axioms: ok ({len(names)} theorems, allowlist {sorted(allowed)})")
sys.exit(1 if failed else 0)
PY
status=$?
set -e
cat "$out/result.txt"
[ "$status" -eq 0 ] || die "axioms outside gates/allowlist, or a missing axioms line (evidence/axioms/result.txt)"
