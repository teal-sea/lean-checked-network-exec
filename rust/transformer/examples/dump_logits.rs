//! Prints every logit of every pair, for scripts/check_transformer_int.py.
//! One line per pair, `a b l0 l1 ... l112`, in the order a then b.
#![forbid(unsafe_code)]

use std::io::{self, BufWriter, Write};

use transformer::{P, logits};

fn main() {
    let mut out = BufWriter::new(io::stdout().lock());
    for a in 0..P {
        for b in 0..P {
            let l = logits(a, b).expect("a and b are below 113");
            write!(out, "{a} {b}").expect("write stdout");
            for v in l {
                write!(out, " {v}").expect("write stdout");
            }
            writeln!(out).expect("write stdout");
        }
    }
    out.flush().expect("flush stdout");
}
