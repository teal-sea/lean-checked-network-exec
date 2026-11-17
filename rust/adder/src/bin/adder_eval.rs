//! Runs `adder::add_bits` and `adder::add_u64` on each input line for scripts/diff.sh.
//!
//! Input, one case per line:
//!   `bits <a> <b> <sum>`  three strings of `0`/`1` (`-` is the empty string): the bits of the two
//!                         numbers, least significant first and of equal length, and the initial
//!                         contents of the `sum` buffer (any length)
//!   `u64 <a> <b>`         two decimal u64 values
//! Output, one line per input line:
//!   `some <carry> <sum>` or `none <sum>` for `bits`, with `sum` as the call left it;
//!   `ok <sum> <carry>` for `u64`;
//!   `fail overflow` when the call panics on overflow, `fail panic: <message>` on any other panic.
//! The Lean evaluators (lean/LcnExec/Adder/Main.lean and NetMain.lean) print the same format.
#![forbid(unsafe_code)]

use std::io::{self, BufRead, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

enum Case {
    Bits(Vec<(bool, bool)>, Vec<bool>),
    U64(u64, u64),
}

fn parse_bits(token: &str) -> Option<Vec<bool>> {
    if token == "-" {
        return Some(Vec::new());
    }
    token
        .chars()
        .map(|c| match c {
            '0' => Some(false),
            '1' => Some(true),
            _ => None,
        })
        .collect()
}

fn parse_line(line: &str) -> Option<Case> {
    let tokens: Vec<&str> = line.split_whitespace().collect();
    match tokens.as_slice() {
        ["bits", a, b, sum] => {
            let (a, b, sum) = (parse_bits(a)?, parse_bits(b)?, parse_bits(sum)?);
            if a.len() != b.len() {
                return None;
            }
            Some(Case::Bits(a.into_iter().zip(b).collect(), sum))
        }
        ["u64", a, b] => Some(Case::U64(a.parse().ok()?, b.parse().ok()?)),
        _ => None,
    }
}

fn show_bit(b: bool) -> char {
    if b { '1' } else { '0' }
}

fn show_bits(bits: &[bool]) -> String {
    if bits.is_empty() {
        return "-".to_string();
    }
    bits.iter().map(|&b| show_bit(b)).collect()
}

fn eval(case: Case) -> String {
    match case {
        Case::Bits(xs, mut sum) => match adder::add_bits(&xs, &mut sum) {
            Some(carry) => format!("some {} {}", show_bit(carry), show_bits(&sum)),
            None => format!("none {}", show_bits(&sum)),
        },
        Case::U64(a, b) => {
            let (sum, carry) = adder::add_u64(a, b);
            format!("ok {} {}", sum, show_bit(carry))
        }
    }
}

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut out = io::BufWriter::new(io::stdout().lock());
    for line in io::stdin().lock().lines() {
        let line = line.expect("read stdin");
        let Some(case) = parse_line(&line) else {
            out.flush().expect("write stdout");
            eprintln!("bad input line: {line}");
            std::process::exit(1);
        };
        match catch_unwind(AssertUnwindSafe(|| eval(case))) {
            Ok(text) => writeln!(out, "{text}"),
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
