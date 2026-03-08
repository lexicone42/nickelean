# Nickelean

Formally verified JSON roundtrip for [Nickel](https://nickel-lang.org/) values in Lean 4.

**Main theorem**: For all `NickelValue`s `v`:

```lean
theorem json_roundtrip (v : NickelValue) : fromJson (toJson v) = some v
```

Serializing a Nickel value to its JSON AST representation and deserializing it back yields the original value — proved for all inputs, including nested arrays, records, and strings with arbitrary escape sequences.

## What this proves

Nickel is a configuration language that evaluates to JSON-serializable values. This library proves that an abstract model of Nickel's JSON serialization roundtrips correctly at the AST level:

1. **String escaping roundtrip** — `unescapeJsonString (escapeJsonString s) = some s` for all strings, including control characters (U+0000–U+001F), quotes, backslashes, and `\uXXXX` hex escapes.

2. **Structural roundtrip** — The mutual recursion over `NickelValue` (which contains `List NickelValue` and `List (String × NickelValue)`) is handled by three mutually-recursive theorems covering values, arrays, and record fields.

3. **IEEE 754 conformance boundary** — Documents where the exact-rational model diverges from Rust's `serde_json` + Ryu implementation (numbers outside f64 range or requiring >53-bit mantissa).

## What this does NOT prove

- **No connection to Nickel's Rust implementation** — The Lean `toJson`/`fromJson` functions are an independent model. They are not extracted from or verified against Nickel's `serde::Serialize`/`Deserialize` code. However, cross-validation tests (`CrossValidation.lean`) verify that the Lean model's JSON output matches `serde_json`'s output for 22 test vectors.
- **AST-level roundtrip** — The main roundtrip theorem is `NickelValue → JsonValue → NickelValue`. A JSON text printer (`PrintJson.lean`) is provided for cross-validation but the full `NickelValue → String → NickelValue` text roundtrip is not yet composed into a single theorem.
- **Numbers are exact rationals** — `JsonNumber` uses `Int / Nat`, not floating-point. The roundtrip holds for all rationals, but `JsonNumber` equality is non-canonical (`1/2 ≠ 2/4`) and no normalization is modeled.

## Project structure

```
Nickelean/
├── JsonValue.lean              # JSON AST (numbers as exact rationals)
├── Value.lean                  # NickelValue type (Nickel's JSON-serializable subset)
├── Escape.lean                 # String escaping and unescaping
├── ToJson.lean                 # NickelValue → JsonValue serialization
├── FromJson.lean               # JsonValue → Option NickelValue deserialization
├── Roundtrip.lean              # Main roundtrip theorem (mutual recursion)
├── Roundtrip/
│   └── EscapeRoundtrip.lean    # 5-layer escape roundtrip proof
├── PrintJson.lean              # JSON text printer (JsonValue → String)
├── CrossValidation.lean        # Cross-validation against serde_json output
├── Float64.lean                # IEEE 754 conformance predicates
├── RecordOrder.lean            # Field ordering and normalization
├── DecidableEq.lean            # DecidableEq for nested inductives
└── Tests.lean                  # Runtime conformance tests
conformance/
└── src/main.rs                 # Differential testing against serde_json
```

## Building

Requires [Lean 4](https://lean-lang.org/) v4.28.0 (see `lean-toolchain`).

```bash
lake build
```

All proofs are constructive — no `sorry`, no `axiom`, no `native_decide` except for hex digit base cases.

## Conformance testing

The Rust conformance suite generates random test vectors and verifies them against `serde_json`:

```bash
cd conformance
cargo run -- roundtrip    # 1000 random roundtrip tests
cargo run -- escaping     # 16 hand-crafted escape edge cases
```

## Design decisions

- **Numbers as rationals**: `JsonNumber` uses `Int / Nat` (with `den_pos` proof) rather than floating-point. This makes the roundtrip theorem unconditional — it holds for *all* rationals, not just f64-representable ones.

- **Mutual recursion**: Lean 4 cannot derive structural recursion through `List` wrappers in nested inductives. All functions (`toJson`, `fromJson`, `DecidableEq`) and all proofs use explicit mutual recursion with list helpers.

- **Full Unicode escaping**: Handles ASCII, BMP `\uXXXX` escapes, and surrogate pair decoding (`\uD800`–`\uDFFF` sequences for non-BMP characters). Non-BMP characters are passed through as raw UTF-8 by the escaper (valid per RFC 8259) but can be decoded from surrogate pairs when unescaping.

## Related work

- [ryu-lean4](https://github.com/lexicone42/ryu-lean4) — Formal verification of the Ryu float-to-string algorithm in Lean 4, proving the full `toF64(parse(format(ryu(x)))) = x` roundtrip for all finite IEEE 754 doubles.

## License

MIT
