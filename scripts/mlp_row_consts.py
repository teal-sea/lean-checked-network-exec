#!/usr/bin/env python3
"""Rewrite the tables of rust/mlp/src/weights.rs with one `const` per row. Used by scripts/mlp_pilot.sh.

rust/mlp/src/weights.rs writes each table as one array literal of 113 rows of 128 entries:

    pub static E1: [[i8; HID]; P] = [
        [92, 104, ...],
        ...
    ];

Aeneas translates that to one Lean definition with 14,464 scalar literals, which Lean does not
elaborate within the limits of the generated file (evidence/mlp/pilot/). This script writes the
same tables, entry for entry, as

    const E1_ROW_0: [i8; HID] = [92, 104, ...];
    ...
    pub static E1: [[i8; HID]; P] = [
        E1_ROW_0,
        ...
    ];

so that Aeneas emits one Lean definition per row. Nothing else in the file changes, and
src/lib.rs is not touched.

Usage: mlp_row_consts.py IN.rs OUT.rs
"""

import re
import sys

TABLE = re.compile(r"pub static (\w+): \[\[i8; HID\]; P\] = \[\n(.*?)\n\];", re.S)
ROWS, COLUMNS = 113, 128


def rewrite(source: str) -> str:
    out, position, tables = [], 0, 0
    for match in TABLE.finditer(source):
        name = match.group(1)
        rows = [line.strip().rstrip(",") for line in match.group(2).split("\n") if line.strip()]
        if len(rows) != ROWS:
            raise SystemExit(f"{name}: {len(rows)} rows, expected {ROWS}")
        for row in rows:
            if not (row.startswith("[") and row.endswith("]")) or len(row[1:-1].split(",")) != COLUMNS:
                raise SystemExit(f"{name}: a row is not a list of {COLUMNS} entries")
        consts = "".join(f"const {name}_ROW_{i}: [i8; HID] = {row};\n" for i, row in enumerate(rows))
        table = f"pub static {name}: [[i8; HID]; P] = [\n" + "".join(
            f"    {name}_ROW_{i},\n" for i in range(ROWS)
        ) + "];"
        out += [source[position : match.start()], consts, table]
        position = match.end()
        tables += 1
    if tables != 3:
        raise SystemExit(f"found {tables} tables, expected 3 (E1, E2, W2)")
    out.append(source[position:])
    return "".join(out)


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: mlp_row_consts.py IN.rs OUT.rs", file=sys.stderr)
        return 2
    with open(sys.argv[1]) as f:
        source = f.read()
    with open(sys.argv[2], "w") as f:
        f.write(rewrite(source))
    return 0


if __name__ == "__main__":
    sys.exit(main())
