//! Differential conformance testing for nickelean.
//!
//! Generates random JSON values, serializes them with serde_json (which Nickel uses),
//! then outputs both the value and serialized form. A companion Lean program can
//! deserialize and compare against the Lean model's toJson/fromJson.
//!
//! Usage:
//!   cargo run -- generate [--count N] [--seed S]   # emit random test cases as JSON
//!   cargo run -- roundtrip                          # verify serde_json roundtrip
//!   cargo run -- escaping                           # test string escaping specifically

use nickel_lang_core::error::NullReporter;
use nickel_lang_core::eval::cache::CacheImpl;
use nickel_lang_core::program::Program;
use nickel_lang_core::serialize::{self, ExportFormat};
use rand::prelude::IndexedRandom;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde_json::{Map, Number, Value};
use std::env;
use std::io::Cursor;

fn random_value(rng: &mut impl Rng, depth: u32) -> Value {
    if depth == 0 {
        return random_leaf(rng);
    }
    match rng.random_range(0..6) {
        0 => Value::Null,
        1 => Value::Bool(rng.random()),
        2 => random_number(rng),
        3 => Value::String(random_string(rng)),
        4 => {
            let len = rng.random_range(0..5);
            Value::Array((0..len).map(|_| random_value(rng, depth - 1)).collect())
        }
        _ => {
            let len = rng.random_range(0..5);
            let mut map = Map::new();
            for _ in 0..len {
                map.insert(random_key(rng), random_value(rng, depth - 1));
            }
            Value::Object(map)
        }
    }
}

fn random_leaf(rng: &mut impl Rng) -> Value {
    match rng.random_range(0..4) {
        0 => Value::Null,
        1 => Value::Bool(rng.random()),
        2 => random_number(rng),
        _ => Value::String(random_string(rng)),
    }
}

fn random_number(rng: &mut impl Rng) -> Value {
    match rng.random_range(0..3) {
        0 => Value::Number(Number::from(rng.random_range(-1000i64..1000))),
        1 => {
            let n: f64 = rng.random_range(-1e10..1e10);
            Number::from_f64(n).map_or(Value::Null, Value::Number)
        }
        _ => Value::Number(Number::from(0)),
    }
}

fn random_string(rng: &mut impl Rng) -> String {
    let len = rng.random_range(0..20);
    (0..len).map(|_| random_char(rng)).collect()
}

fn random_char(rng: &mut impl Rng) -> char {
    match rng.random_range(0..10) {
        0..7 => rng.random_range(0x20u32..0x7F) as u8 as char,
        7 => rng.random_range(0u32..0x20) as u8 as char,
        8 => *['"', '\\', '\n', '\r', '\t']
            .choose(rng)
            .unwrap(),
        _ => char::from_u32(rng.random_range(0x80u32..0x800)).unwrap_or('?'),
    }
}

fn random_key(rng: &mut impl Rng) -> String {
    let len = rng.random_range(1..10);
    (0..len)
        .map(|_| rng.random_range(b'a'..=b'z') as char)
        .collect()
}

/// Escape-specific test cases: strings that exercise edge cases
fn escaping_test_cases() -> Vec<(&'static str, String)> {
    vec![
        ("empty", String::new()),
        ("simple", "hello world".into()),
        ("quotes", r#"say "hi""#.into()),
        ("backslash", r"path\to\file".into()),
        ("newline", "line1\nline2".into()),
        ("tab", "col1\tcol2".into()),
        ("carriage_return", "a\rb".into()),
        ("null_char", "\0".into()),
        ("bell", "\x07".into()),
        ("backspace", "\x08".into()),
        ("formfeed", "\x0C".into()),
        ("all_control", (0u8..0x20).map(|b| b as char).collect()),
        ("mixed", "hello \"world\"\n\ttab\\slash\0end".into()),
        ("unicode_bmp", "café résumé naïve".into()),
        ("unicode_cjk", "\u{4F60}\u{597D}\u{4E16}\u{754C}".into()),
        (
            "already_escaped_looking",
            r"\\n is not a newline".into(),
        ),
    ]
}

fn cmd_generate(count: usize, seed: u64) {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut cases = Vec::new();
    for _ in 0..count {
        let value = random_value(&mut rng, 3);
        let serialized = serde_json::to_string(&value).unwrap();
        let parsed: Value = serde_json::from_str(&serialized).unwrap();
        assert_eq!(value, parsed, "serde_json self-roundtrip failed");
        cases.push(serde_json::json!({
            "value": value,
            "serialized": serialized,
        }));
    }
    println!("{}", serde_json::to_string_pretty(&cases).unwrap());
}

fn cmd_roundtrip() {
    let mut rng = StdRng::seed_from_u64(42);
    let mut pass = 0;
    let mut fail = 0;
    for i in 0..1000 {
        let value = random_value(&mut rng, 3);
        let serialized = serde_json::to_string(&value).unwrap();
        match serde_json::from_str::<Value>(&serialized) {
            Ok(parsed) if parsed == value => pass += 1,
            Ok(parsed) => {
                eprintln!("FAIL case {i}: roundtrip mismatch");
                eprintln!("  original:   {value}");
                eprintln!("  serialized: {serialized}");
                eprintln!("  parsed:     {parsed}");
                fail += 1;
            }
            Err(e) => {
                eprintln!("FAIL case {i}: parse error: {e}");
                eprintln!("  serialized: {serialized}");
                fail += 1;
            }
        }
    }
    println!("serde_json roundtrip: {pass} passed, {fail} failed");
}

fn cmd_escaping() {
    let cases = escaping_test_cases();
    let mut pass = 0;
    let mut fail = 0;
    for (name, input) in &cases {
        let value = Value::String(input.clone());
        let serialized = serde_json::to_string(&value).unwrap();
        match serde_json::from_str::<Value>(&serialized) {
            Ok(parsed) if parsed == value => {
                pass += 1;
                println!("  PASS {name}: {serialized}");
            }
            Ok(parsed) => {
                fail += 1;
                eprintln!("  FAIL {name}: roundtrip mismatch");
                eprintln!("    input:      {input:?}");
                eprintln!("    serialized: {serialized}");
                eprintln!("    parsed:     {parsed}");
            }
            Err(e) => {
                fail += 1;
                eprintln!("  FAIL {name}: parse error: {e}");
            }
        }
    }

    // Output test vectors for Lean comparison
    println!("\n--- Test vectors (for Lean comparison) ---");
    for (name, input) in &cases {
        let value = Value::String(input.clone());
        let serialized = serde_json::to_string(&value).unwrap();
        let escaped_content = &serialized[1..serialized.len() - 1];
        println!("{name}\t{input:?}\t{escaped_content}");
    }

    println!("\nEscaping tests: {pass} passed, {fail} failed");
}

/// Evaluate a Nickel expression and return the JSON string output.
fn eval_nickel(source: &str) -> Result<String, String> {
    let mut program = Program::<CacheImpl>::new_from_source(
        Cursor::new(source),
        "<test>",
        std::io::sink(),
        NullReporter {},
    )
    .map_err(|e| format!("program creation failed: {e:?}"))?;

    let value = program
        .eval_full_for_export()
        .map_err(|e| format!("eval failed: {e:?}"))?;

    serialize::validate(ExportFormat::Json, &value)
        .map_err(|e| format!("validation failed: {e:?}"))?;

    serialize::to_string(ExportFormat::Json, &value)
        .map_err(|e| format!("serialization failed: {e:?}"))?
        .pipe(Ok)
}

trait Pipe: Sized {
    fn pipe<F, R>(self, f: F) -> R
    where
        F: FnOnce(Self) -> R,
    {
        f(self)
    }
}
impl<T> Pipe for T {}

/// Test cases: (name, nickel expression, expected serde_json Value)
fn nickel_test_cases() -> Vec<(&'static str, &'static str, Value)> {
    vec![
        // Primitives
        ("null", "null", Value::Null),
        ("true", "true", Value::Bool(true)),
        ("false", "false", Value::Bool(false)),
        ("integer", "42", Value::Number(Number::from(42))),
        ("negative", "-7", Value::Number(Number::from(-7))),
        ("zero", "0", Value::Number(Number::from(0))),
        (
            "float",
            "3.14",
            Value::Number(Number::from_f64(3.14).unwrap()),
        ),
        ("empty_string", r#""""#, Value::String(String::new())),
        (
            "simple_string",
            r#""hello world""#,
            Value::String("hello world".into()),
        ),
        // Strings with special characters
        (
            "string_quotes",
            r#""say \"hi\"""#,
            Value::String("say \"hi\"".into()),
        ),
        (
            "string_newline",
            r#""line1%{"\n"}line2""#,
            Value::String("line1\nline2".into()),
        ),
        (
            "string_tab",
            r#""col1%{"\t"}col2""#,
            Value::String("col1\tcol2".into()),
        ),
        // Computed values
        (
            "arithmetic",
            "2 + 3",
            Value::Number(Number::from(5)),
        ),
        (
            "string_concat",
            r#""hello" ++ " " ++ "world""#,
            Value::String("hello world".into()),
        ),
        // Arrays
        ("empty_array", "[]", Value::Array(vec![])),
        (
            "simple_array",
            "[1, 2, 3]",
            Value::Array(vec![
                Value::Number(Number::from(1)),
                Value::Number(Number::from(2)),
                Value::Number(Number::from(3)),
            ]),
        ),
        (
            "mixed_array",
            r#"[1, "two", true, null]"#,
            Value::Array(vec![
                Value::Number(Number::from(1)),
                Value::String("two".into()),
                Value::Bool(true),
                Value::Null,
            ]),
        ),
        // Records
        (
            "simple_record",
            r#"{ name = "alice", age = 30 }"#,
            serde_json::json!({"age": 30, "name": "alice"}),
        ),
        (
            "nested_record",
            r#"{ outer = { inner = 42 } }"#,
            serde_json::json!({"outer": {"inner": 42}}),
        ),
        // Complex: let bindings, functions applied
        (
            "let_binding",
            r#"let x = 10 in { value = x * 2 }"#,
            serde_json::json!({"value": 20}),
        ),
        (
            "array_map",
            r#"std.array.map (fun x => x + 1) [1, 2, 3]"#,
            Value::Array(vec![
                Value::Number(Number::from(2)),
                Value::Number(Number::from(3)),
                Value::Number(Number::from(4)),
            ]),
        ),
        // Realistic config (use different name to avoid recursive field shadowing)
        (
            "config",
            r#"
            let server_port = 8080 in
            {
              server = {
                host = "0.0.0.0",
                port = server_port,
                debug = false,
              },
              database = {
                url = "postgres://localhost/mydb",
                pool_size = 5,
              },
            }
            "#,
            serde_json::json!({
                "server": {
                    "host": "0.0.0.0",
                    "port": 8080,
                    "debug": false
                },
                "database": {
                    "url": "postgres://localhost/mydb",
                    "pool_size": 5
                }
            }),
        ),
    ]
}

fn cmd_nickel() {
    let cases = nickel_test_cases();
    let mut pass = 0;
    let mut fail = 0;

    for (name, source, expected) in &cases {
        match eval_nickel(source) {
            Ok(json_str) => {
                match serde_json::from_str::<Value>(&json_str) {
                    Ok(actual) => {
                        if &actual == expected {
                            pass += 1;
                            println!("  PASS {name}");
                        } else {
                            fail += 1;
                            eprintln!("  FAIL {name}: value mismatch");
                            eprintln!("    expected: {expected}");
                            eprintln!("    actual:   {actual}");
                        }
                    }
                    Err(e) => {
                        fail += 1;
                        eprintln!("  FAIL {name}: JSON parse error: {e}");
                        eprintln!("    json_str: {json_str}");
                    }
                }
            }
            Err(e) => {
                fail += 1;
                eprintln!("  FAIL {name}: {e}");
            }
        }
    }

    println!("\nNickel conformance: {pass} passed, {fail} failed out of {} tests", cases.len());
    if fail > 0 {
        std::process::exit(1);
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let cmd = args.get(1).map(|s| s.as_str()).unwrap_or("roundtrip");

    match cmd {
        "float_vectors" => cmd_float_vectors(),
        "generate" => {
            let count = args
                .get(2)
                .and_then(|s| s.parse().ok())
                .unwrap_or(100);
            let seed = args
                .get(3)
                .and_then(|s| s.parse().ok())
                .unwrap_or(42);
            cmd_generate(count, seed);
        }
        "roundtrip" => cmd_roundtrip(),
        "escaping" => cmd_escaping(),
        "nickel" => cmd_nickel(),
        _ => {
            eprintln!("Usage: nickelean-conformance <generate|roundtrip|escaping|nickel>");
            std::process::exit(1);
        }
    }
}

fn cmd_float_vectors() {
    use serde_json::Value;
    let values: Vec<f64> = vec![0.1, 0.5, 1.5, 3.14159, -2.718, 1e10, 1e-10,
                                 5e-324, 1.7976931348623157e308, -0.0, 0.0,
                                 1.0/3.0, 2.0_f64.sqrt()];
    for v in &values {
        let json_val = Value::from(*v);
        let s = serde_json::to_string(&json_val).unwrap();
        println!("  f64={v:>25} → json={s}");
    }
}
