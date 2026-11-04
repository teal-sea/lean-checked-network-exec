//! Runs `smoke::sum` on each input line for scripts/diff.sh.
//! Input: one slice per line, whitespace-separated u32 values (an empty line is the empty slice).
//! Output: `ok <sum>`, `fail overflow` when the sum panics on overflow, `fail panic: <message>`
//! on any other panic. The Lean evaluator (lean/LcnExec/Smoke/Main.lean) prints the same format.
#![forbid(unsafe_code)]

use std::io::{self, BufRead, Write};

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut out = io::BufWriter::new(io::stdout().lock());
    for line in io::stdin().lock().lines() {
        let line = line.expect("read stdin");
        let xs: Vec<u32> = line
            .split_whitespace()
            .map(|t| t.parse().expect("each value is a u32"))
            .collect();
        match std::panic::catch_unwind(|| smoke::sum(&xs)) {
            Ok(total) => writeln!(out, "ok {total}"),
            Err(payload) => {
                let message = payload
                    .downcast_ref::<&str>()
                    .map(|s| s.to_string())
                    .or_else(|| payload.downcast_ref::<String>().cloned())
                    .unwrap_or_default();
                if message.contains("overflow") {
                    writeln!(out, "fail overflow")
                } else {
                    writeln!(out, "fail panic: {message}")
                }
            }
        }
        .expect("write stdout");
    }
}
