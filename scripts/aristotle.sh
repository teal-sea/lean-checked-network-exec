#!/usr/bin/env bash
# Send one crate to Aristotle and keep a record of what went up and what came back.
#
#   scripts/aristotle.sh stage   <target>             copy the upload to .work/aristotle/<target>/ and list it
#   scripts/aristotle.sh submit  <target> [--no-questions]
#                                                      stage, record the balance, submit, record the project id
#   scripts/aristotle.sh status  <target>             task state, property counts, open questions
#   scripts/aristotle.sh answer  <target> <qid>=<answer> [...]
#   scripts/aristotle.sh continue <target> <prompt-file>   another run in the same project (spends credits)
#   scripts/aristotle.sh fetch   <target>             save summary, properties, events and the result archive
#   scripts/aristotle.sh balance                      print the credit balance
#
# <target> is a crate under rust/ (adder, mlp, transformer) or c/ (c-adder is c/adder).
# The upload is the crate's Cargo.toml, Cargo.lock, src/ and SPEC.md, and nothing else.
# Every run spends credits. Evidence goes to evidence/aristotle/<target>/.
#
# The key comes from ARISTOTLE_API_KEY or from `aristotle login`. In a claude.ai cloud session the
# network proxy injects the saved key, so ARISTOTLE_API_KEY only has to be non-empty there.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARISTOTLE="${ARISTOTLE_BIN:-aristotle}"
PYTHON="${ARISTOTLE_PYTHON:-python3}"
PROMPT_DEFAULT="Perform the formal verification of this crate as specified in SPEC.md."

die() { echo "aristotle.sh: $*" >&2; exit 1; }
now() { date -u +%Y-%m-%dT%H:%M:%SZ; }

src_dir() {
  case "$1" in
    c-*) echo "$ROOT/c/${1#c-}" ;;
    *)   echo "$ROOT/rust/$1" ;;
  esac
}

balance_json() {
  "$PYTHON" - <<'EOF'
import asyncio, json, sys
try:
    from aristotlelib import api_request
except ImportError:
    sys.exit("aristotlelib is not importable by this python; set ARISTOTLE_PYTHON")
async def main():
    async with api_request.AristotleRequestClient() as c:
        r = await c.get("/billing/balance")
        d = r.json()
        per = d.get("credit_display_config", {}).get("small_credits_per_credit", 1)
        out = {k: d.get(k) for k in ("credits", "free_credits", "paid_credits", "observed_at", "next_expiry_at")}
        out["small_credits_per_credit"] = per
        out["credits_display"] = d.get("credits", 0) / per
        print(json.dumps(out))
asyncio.run(main())
EOF
}

stage() {
  local target="$1" src stage
  src="$(src_dir "$target")"
  stage="$ROOT/.work/aristotle/$target"
  [ -f "$src/SPEC.md" ] || die "$src/SPEC.md is missing"
  rm -rf "$stage"; mkdir -p "$stage"
  local f
  for f in Cargo.toml Cargo.lock SPEC.md Makefile; do
    [ -f "$src/$f" ] && cp "$src/$f" "$stage/$f"
  done
  [ -d "$src/src" ] && cp -R "$src/src" "$stage/src"
  # C targets keep their sources beside SPEC.md
  find "$src" -maxdepth 1 -type f \( -name '*.c' -o -name '*.h' \) -exec cp {} "$stage/" \;
  (cd "$stage" && find . -type f | LC_ALL=C sort | while read -r p; do
     printf '%s  %s\n' "$(sha256sum "$p" | cut -d' ' -f1)" "${p#./}"; done)
}

cmd="${1:-}"; shift || true
case "$cmd" in
  balance)
    balance_json
    ;;
  stage)
    [ $# -ge 1 ] || die "usage: stage <target>"
    stage "$1"
    ;;
  submit)
    [ $# -ge 1 ] || die "usage: submit <target> [--no-questions]"
    target="$1"; shift
    ev="$ROOT/evidence/aristotle/$target"; mkdir -p "$ev"
    [ ! -f "$ev/project_id" ] || die "$ev/project_id exists: this target was already submitted (use continue)"
    stage "$target" > "$ev/upload.sha256"
    prompt="${ARISTOTLE_PROMPT:-$PROMPT_DEFAULT}"
    printf '%s\n' "$prompt" > "$ev/prompt.txt"
    "$ARISTOTLE" --version > "$ev/cli-version.txt" 2>&1
    balance_json > "$ev/balance-before.json"
    echo "submitted_at $(now)" > "$ev/submit.txt"
    echo "repo_commit $(git -C "$ROOT" rev-parse HEAD) dirty=$(git -C "$ROOT" status --porcelain | wc -l)" >> "$ev/submit.txt"
    # Returns as soon as the project exists; the run goes on at Harmonic.
    "$ARISTOTLE" submit "$prompt" --project-dir "$ROOT/.work/aristotle/$target" \
        --name "lcn-exec-$target" --json "$@" > "$ev/submit.json" 2> "$ev/submit.err" \
      || { cat "$ev/submit.err" >&2; die "submit failed; see $ev/submit.err"; }
    "$PYTHON" - "$ev/submit.json" > "$ev/project_id.tmp" <<'PYEOF'
import json, sys
def find(o):
    if isinstance(o, dict):
        if isinstance(o.get("project_id"), str):
            return o["project_id"]
        o = list(o.values())
    if isinstance(o, list):
        for v in o:
            r = find(v)
            if r:
                return r
    return None
pid = find(json.load(open(sys.argv[1])))
if not pid:
    sys.exit("no project_id in the submit output")
print(pid)
PYEOF
    mv "$ev/project_id.tmp" "$ev/project_id"
    echo "project $(cat "$ev/project_id")"
    echo "https://aristotle.harmonic.fun/projects/$(cat "$ev/project_id")?view=props"
    ;;
  status)
    [ $# -ge 1 ] || die "usage: status <target>"
    ev="$ROOT/evidence/aristotle/$1"; pid="$(cat "$ev/project_id")"
    "$ARISTOTLE" show "$pid" --json --limit 5 > "$ev/status.json" 2> "$ev/status.err" || { cat "$ev/status.err" >&2; exit 1; }
    "$ARISTOTLE" questions "$pid" --json > "$ev/questions.json" 2>> "$ev/status.err" || true
    "$PYTHON" - "$ev/status.json" "$ev/questions.json" <<'EOF'
import json, sys, collections
d = json.load(open(sys.argv[1]))
t = d.get("task", d)
print("task", t.get("agent_task_id"), "status", t.get("status"), "updated", t.get("last_updated_at"))
props = d.get("properties") or d.get("declarations") or []
c = collections.Counter((p.get("status") or p.get("verdict") or "?") for p in props)
print("properties", dict(c))
for e in (d.get("events") or [])[:5]:
    print("  event", e.get("created_at"), e.get("event_type"), (e.get("content") or e.get("explanation") or "")[:160].replace("\n", " "))
try:
    q = json.load(open(sys.argv[2])).get("questions", [])
except Exception:
    q = []
open_q = [x for x in q if x.get("pending")]
print("questions", len(q), "open", len(open_q))
for x in open_q:
    print("  OPEN", x.get("question_id"), (x.get("content") or "")[:600])
    for s in x.get("suggestions") or []:
        print("     suggestion:", s)
EOF
    ;;
  answer)
    [ $# -ge 2 ] || die "usage: answer <target> <question-id>=<answer> [...]"
    ev="$ROOT/evidence/aristotle/$1"; pid="$(cat "$ev/project_id")"; shift
    args=(); for a in "$@"; do args+=(--answer "$a"); done
    { echo "answered_at $(now)"; printf '%s\n' "$@"; echo; } >> "$ev/answers.txt"
    "$ARISTOTLE" questions "$pid" "${args[@]}" --json
    ;;
  continue)
    [ $# -ge 2 ] || die "usage: continue <target> <prompt-file>"
    ev="$ROOT/evidence/aristotle/$1"; pid="$(cat "$ev/project_id")"
    n="$(ls "$ev" | grep -c '^continue-.*\.txt$' || true)"; n=$((n + 1))
    cp "$2" "$ev/continue-$n.txt"
    balance_json > "$ev/balance-before-continue-$n.json"
    "$ARISTOTLE" continue "$pid" --prompt-file "$2" --json > "$ev/continue-$n.json"
    echo "continued $pid (run $n) at $(now)" | tee -a "$ev/submit.txt"
    ;;
  fetch)
    [ $# -ge 1 ] || die "usage: fetch <target>"
    ev="$ROOT/evidence/aristotle/$1"; pid="$(cat "$ev/project_id")"
    "$ARISTOTLE" show "$pid" --json --limit 200 > "$ev/task.json"
    "$ARISTOTLE" tasks "$pid" --json > "$ev/tasks.json"
    "$ARISTOTLE" properties "$pid" --json > "$ev/properties.json"
    "$ARISTOTLE" properties "$pid" --kind definition --json > "$ev/definitions.json" || true
    "$ARISTOTLE" questions "$pid" --json > "$ev/questions.json" || true
    balance_json > "$ev/balance-after.json"
    mkdir -p "$ROOT/.work/aristotle-results/$1"
    "$ARISTOTLE" download "$pid" --destination "$ROOT/.work/aristotle-results/$1/" --json > "$ev/download.json" || true
    "$PYTHON" - "$ev" <<'EOF'
import json, sys, collections, pathlib
ev = pathlib.Path(sys.argv[1])
d = json.load(open(ev / "task.json")); t = d.get("task", d)
(ev / "summary.md").write_text((t.get("output_summary") or "(no summary yet)") + "\n")
props = json.load(open(ev / "properties.json")).get("declarations", [])
c = collections.Counter((p.get("status") or "?") for p in props)
b0 = json.load(open(ev / "balance-before.json")); b1 = json.load(open(ev / "balance-after.json"))
lines = [f"task {t.get('agent_task_id')} status {t.get('status')}",
         f"created {t.get('created_at')} updated {t.get('last_updated_at')}",
         f"properties {dict(c)}",
         f"credits before {b0['credits_display']} after {b1['credits_display']} (other runs between the two readings are included)"]
(ev / "result.txt").write_text("\n".join(lines) + "\n")
print("\n".join(lines))
EOF
    ;;
  *)
    sed -n '2,18p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    exit 2
    ;;
esac
