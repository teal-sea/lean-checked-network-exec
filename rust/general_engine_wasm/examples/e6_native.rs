//! Native gate E6 verification run (host build of the exact `general_engine` the
//! WebAssembly page uses).
//!
//! Reads the two GLMW v1 fixtures, checks `load_check`, runs all 12,769 mod-113
//! pairs through `general_engine::predict_next`, hashes the 113 logits of every
//! pair with the same FNV-1a 64 scheme as `rust/transformer/tests/all_pairs.rs`
//! and compares against the frozen reference, then runs greedy byte-level
//! generation for a fixed prompt list. Everything is written as JSON to
//! evidence/e6-wasm/native-general.json, which scripts/e6_wasm_receipt.js compares
//! against the same computations done inside actual WebAssembly.
use std::fs;
use std::path::PathBuf;

use general_engine::{MAX_SEQ, forward_logits, generate_greedy, load_check, predict_next};
use general_engine_wasm::GLMW_FILE_LEN;
use general_engine_wasm::{ZERO_WEIGHTS, parse_glmw_into};

fn repo_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn load_fixture(name: &str) -> [u8; GLMW_FILE_LEN] {
    let path = repo_dir().join("weights").join(name);
    let bytes = fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    assert_eq!(
        bytes.len(),
        GLMW_FILE_LEN,
        "{}: wrong length",
        path.display()
    );
    let mut buf = [0u8; GLMW_FILE_LEN];
    buf.copy_from_slice(&bytes);
    buf
}

fn fnv1a64_i64(value: i64, hash: u64) -> u64 {
    let mut h = hash;
    for byte in value.to_le_bytes() {
        h = (h ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

fn main() {
    let started = std::time::Instant::now();
    let mut out = String::new();
    out.push_str("{\n");

    // mod-113: load, all 12,769 pairs, the frozen logit hash and margin.
    let mod113 = load_fixture("mod113_v1.bin");
    let mut mod113_weights = ZERO_WEIGHTS;
    assert!(
        parse_glmw_into(&mod113, &mut mod113_weights),
        "mod113_v1.bin parses"
    );
    let mod113_ok = load_check(&mod113_weights);
    assert!(mod113_ok, "mod113_v1.bin fails load_check");
    let sweep_started = std::time::Instant::now();
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    let mut min_margin = i64::MAX;
    let mut min_pair = (0usize, 0usize);
    let mut pairs = 0usize;
    let mut wrong = 0usize;
    for a in 0..113usize {
        for b in 0..113usize {
            let mut tokens = [0usize; MAX_SEQ];
            tokens[0] = a;
            tokens[1] = b;
            tokens[2] = 113; // the `=` token
            let logits = forward_logits(&mod113_weights, &tokens, 3)
                .unwrap_or_else(|| panic!("forward_logits rejected ({a},{b})"));
            let got = predict_next(&mod113_weights, &tokens, 3).expect("predict_next");
            if got != (a + b) % 113 {
                wrong += 1;
            }
            let want = (a + b) % 113;
            let mut runner_up = i64::MIN;
            for c in 0..113 {
                if c != want && logits[c] > runner_up {
                    runner_up = logits[c];
                }
            }
            let margin = logits[want] - runner_up;
            assert!(margin > 0, "margin {margin} at ({a}, {b})");
            if margin < min_margin {
                min_margin = margin;
                min_pair = (a, b);
            }
            for c in 0..113 {
                hash = fnv1a64_i64(logits[c], hash);
            }
            pairs += 1;
        }
    }
    assert_eq!(pairs, 12_769);
    assert_eq!(wrong, 0, "{wrong} of 12,769 mod-113 pairs wrong");
    let sweep_ms = sweep_started.elapsed().as_millis();
    let reference =
        fs::read_to_string(repo_dir().join("rust/transformer/tests/fixtures/python_reference.txt"))
            .expect("read python_reference.txt");
    let ref_hash = reference
        .lines()
        .find_map(|l| l.strip_prefix("logits_fnv1a64 "))
        .expect("logits_fnv1a64 line")
        .trim()
        .to_string();
    let ref_margin = reference
        .lines()
        .find_map(|l| l.strip_prefix("min_margin "))
        .expect("min_margin line")
        .trim()
        .to_string();
    let ref_pair = reference
        .lines()
        .find_map(|l| l.strip_prefix("min_margin_pair "))
        .expect("min_margin_pair line")
        .trim()
        .to_string();
    let hash_hex = format!("{hash:016x}");
    assert_eq!(
        hash_hex, ref_hash,
        "logit hash differs from the frozen reference"
    );
    assert_eq!(min_margin.to_string(), ref_margin);
    assert_eq!(format!("{} {}", min_pair.0, min_pair.1), ref_pair);

    out.push_str("  \"mod113\": {\n");
    out.push_str("    \"load_check\": true,\n");
    out.push_str("    \"pairs\": 12769,\n");
    out.push_str("    \"exact\": 12769,\n");
    out.push_str(&format!("    \"sweep_wall_ms\": {sweep_ms},\n"));
    out.push_str("    \"logits_fnv1a64\": \"");
    out.push_str(&hash_hex);
    out.push_str("\",\n");
    out.push_str(&format!("    \"min_margin\": {min_margin},\n"));
    out.push_str(&format!(
        "    \"min_margin_pair\": [{}, {}]\n",
        min_pair.0, min_pair.1
    ));
    out.push_str("  },\n");

    // byte-LM: load, greedy generation for a fixed prompt list, final logits of
    // the first prompt for a bit-for-bit Wasm/native comparison.
    let bytelm = load_fixture("tiny_bytelm_v1.bin");
    let mut bytelm_weights = ZERO_WEIGHTS;
    assert!(
        parse_glmw_into(&bytelm, &mut bytelm_weights),
        "tiny_bytelm_v1.bin parses"
    );
    let bytelm_ok = load_check(&bytelm_weights);
    assert!(bytelm_ok, "tiny_bytelm_v1.bin fails load_check");
    let mut corrupt = bytelm;
    corrupt[16] = 99;
    let mut rejected_weights = ZERO_WEIGHTS;
    let corrupt_parsed = parse_glmw_into(&corrupt, &mut rejected_weights);
    let corrupt_accepted = load_check(&rejected_weights);
    assert!(corrupt_parsed && !corrupt_accepted, "corrupt tok[0][0] control");
    out.push_str(&format!(
        "  \"corrupt\": {{\"offset\": 16, \"byte\": 99, \"parsed\": {corrupt_parsed}, \"load_check\": {corrupt_accepted}}},\n"
    ));

    let prompts: [&[u8]; 5] = [
        b"A stitch in time",
        b"Hello, world! It",
        b"The quick brown ",
        b"count with me: 1 2 ",
        b"mod 113 is a pri",
    ];
    let mut first_run_tokens: Option<Vec<usize>> = None;
    out.push_str("  \"bytelm\": {\n");
    out.push_str("    \"load_check\": true,\n");
    out.push_str("    \"prompts\": [\n");
    let mut first = true;
    for prompt in prompts {
        let mut tokens = [0usize; MAX_SEQ];
        let prompt_len = prompt.len().min(MAX_SEQ);
        for i in 0..prompt_len {
            tokens[i] = prompt[i] as usize;
        }
        let final_len = generate_greedy(&bytelm_weights, &mut tokens, prompt_len, 32 - prompt_len)
            .expect("generate_greedy");
        let generated: Vec<usize> = tokens[prompt_len..final_len].to_vec();
        if first_run_tokens.is_none() {
            first_run_tokens = Some(generated.clone());
        }
        if !first {
            out.push_str(",\n");
        }
        first = false;
        out.push_str("      {\n");
        out.push_str(&format!(
            "        \"prompt_utf8\": {:?},\n",
            String::from_utf8_lossy(prompt)
        ));
        out.push_str(&format!("        \"prompt_bytes\": {prompt:?},\n"));
        out.push_str(&format!("        \"prompt_len\": {prompt_len},\n"));
        out.push_str(&format!("        \"final_len\": {final_len},\n"));
        out.push_str("        \"tokens\": [");
        for (i, t) in generated.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            out.push_str(&t.to_string());
        }
        out.push_str("]\n      }");
    }
    out.push_str("\n    ],\n");

    // Determinism: a second run of the first prompt must give the same tokens.
    let prompt = prompts[0];
    let mut tokens = [0usize; MAX_SEQ];
    for i in 0..prompt.len() {
        tokens[i] = prompt[i] as usize;
    }
    let final_len2 = generate_greedy(
        &bytelm_weights,
        &mut tokens,
        prompt.len(),
        32 - prompt.len(),
    )
    .expect("greedy 2");
    let second_run: Vec<usize> = tokens[prompt.len()..final_len2].to_vec();
    let deterministic = first_run_tokens.as_deref() == Some(second_run.as_slice());
    assert!(deterministic, "greedy generation is not deterministic");
    out.push_str("    \"deterministic_repeat\": true,\n");

    // Raw logits of the first prompt, for the Wasm bit-for-bit comparison.
    let mut tokens = [0usize; MAX_SEQ];
    for i in 0..prompt.len() {
        tokens[i] = prompt[i] as usize;
    }
    let logits = forward_logits(&bytelm_weights, &tokens, prompt.len()).expect("logits");
    out.push_str("    \"prompt0_logits\": [");
    for (i, v) in logits.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(&format!("\"{v}\""));
    }
    out.push_str("]\n");
    out.push_str("  },\n");
    out.push_str(&format!("  \"wall_ms\": {}\n", started.elapsed().as_millis()));
    out.push_str("}\n");

    let evidence = repo_dir().join("evidence/e6-wasm/native-general.json");
    fs::create_dir_all(evidence.parent().unwrap()).unwrap();
    fs::write(&evidence, out).unwrap();
    println!("wrote {}", evidence.display());
    println!("mod113: 12,769/12,769 exact, logit hash {hash_hex} (matches frozen reference)");
    println!("bytelm: load_check pass, greedy deterministic on repeat");
}
