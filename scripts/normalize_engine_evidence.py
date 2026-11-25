#!/usr/bin/env python3
"""Keep raw evidence compressed, remove terminal CR/trailing whitespace from readable copies."""
import gzip
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
paths = list((root / "pilot/engine").rglob("*.log"))
paths += list((root / "evidence/translate/engine").glob("*.log"))
paths += [root / "pilot/engine/failures/nested-return/lib.rs"]
changed = []
for path in paths:
    raw = path.read_bytes()
    normalized = ("\n".join(line.rstrip() for line in raw.decode().splitlines()).rstrip() + "\n").encode()
    if normalized == raw:
        continue
    backup = path.with_name(path.name + ".raw.gz")
    if backup.exists():
        raise SystemExit(f"Refusing to overwrite raw evidence: {backup}")
    with backup.open("wb") as out:
        with gzip.GzipFile(filename="", mode="wb", fileobj=out, mtime=0) as archive:
            archive.write(raw)
    path.write_bytes(normalized)
    changed.append(str(path.relative_to(root)))
(root / "pilot/engine/evidence-normalization.json").write_text(json.dumps(changed, indent=2) + "\n")
print(json.dumps(changed))
