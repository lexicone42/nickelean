# Nickelean

Formally verified JSON serialization for [Nickel](https://nickel-lang.org/) values in Lean 4, with proven conformance to [serde_json](https://github.com/serde-rs/json) and verified float formatting via [ryu-lean4](https://github.com/lexicone42/ryu-lean4).

## Main theorems

**Text-level roundtrip (integers)** — Serialize a Nickel value to a JSON string, parse it back, recover the original:

```lean
theorem full_text_roundtrip (v : NickelValue) (hdo : NickelAllDenOne v) :
    (parseJV ((printJsonValue (toJson v)).toList) (jsonSize (toJson v))).bind
      (fun ⟨jv, _⟩ => fromJson jv) = some v
```

**Float roundtrip through JSON parser** — For any finite F64, parsing its Ryu-formatted output with our JSON parser and rounding back gives the original F64:

```lean
theorem float_text_roundtrip_f64 (x : F64) (hfin : F64.isFinite x)
    (rest : List Char) (hrest : NonNumContHead rest)
    (hne : (Ryu.ryu x hfin).digits ≠ 0) :
    let d := Ryu.ryu x hfin
    let jn := decimalToJsonNumber d.sign d.digits d.exponent
    parseJsonNumber ((Decimal.format d).toList ++ rest) = some (jn, rest) ∧
    F64.roundToNearestEven jn.toMathRat = x
```

**AST-level roundtrip** — The foundational theorem, unconditional on all NickelValues:

```lean
theorem json_roundtrip (v : NickelValue) : fromJson (toJson v) = some v
```

**Float number roundtrip** — Non-integer numbers serialized via IEEE 754 + Ryu roundtrip through parsing:

```lean
theorem serialize_num_float_roundtrip (jn : JsonNumber)
    (hfin : F64.isFinite (F64.roundToNearestEven jn.toMathRat))
    (hni : ¬(jn.numerator % jn.denominator == 0)) :
    (Decimal.parse (formatSerdeNumberF64 (classifyNumberF64 jn hfin))).map Decimal.toF64
      = some (F64.roundToNearestEven jn.toMathRat)
```

Zero `sorry`s. Zero axioms. All proofs checked by Lean's kernel.

## What this proves

The library verifies the complete JSON serialization pipeline for Nickel values:

1. **String escaping roundtrip** — `unescapeJsonString (escapeJsonString s) = some s` for all strings. Escaping matches serde_json character-for-character (including `\b`, `\f`, `\uXXXX` for control chars).

2. **JSON text roundtrip** — A recursive descent JSON parser that provably inverts the JSON printer. Handles null, booleans, integers, quoted strings with escape sequences, arrays, and nested objects.

3. **serde_json serialization spec** — Formal specification of serde_json's compact JSON output format, with proven equivalence to our printer for integer-valued numbers.

4. **Float formatting via Ryu** — Integration with [ryu-lean4](https://github.com/lexicone42/ryu-lean4)'s verified IEEE 754 float-to-string algorithm. The composition theorem shows: `Rational → F64 (round-to-nearest-even) → Ryu (shortest decimal) → String → parse → F64` roundtrips correctly.

5. **Nickel's serialize_num dispatch** — Models Nickel's three-way number classification (negative integer / positive integer / float), matching `core/src/serialize/mod.rs`.

6. **Record field sorting** — `toJsonSorted` matches Nickel's alphabetical field ordering.

7. **71 cross-validation test vectors** — 33 serde_json output tests (primitives, strings, arrays, objects), 22 decimal/scientific notation parser tests (including zmij `e+` notation), and 16 serde_json float format tests (e.g. `0.1`, `1.7976931348623157e+308`). All verified at compile time.

## Project structure

```
Nickelean/
├── JsonValue.lean              # JSON AST (numbers as exact rationals)
├── Value.lean                  # NickelValue type (Nickel's JSON-serializable subset)
├── Escape.lean                 # String escaping/unescaping (matches serde_json)
├── ToJson.lean                 # NickelValue → JsonValue (with sorted variant)
├── FromJson.lean               # JsonValue → Option NickelValue
├── Roundtrip.lean              # AST roundtrip theorem (mutual recursion)
├── Roundtrip/
│   └── EscapeRoundtrip.lean    # 5-layer escape roundtrip proof
├── PrintJson.lean              # JSON text printer (JsonValue → String)
├── ParseJsonText.lean          # JSON text parser + text roundtrip proof (850 lines)
├── FullTextRoundtrip.lean      # Capstone: NickelValue → String → NickelValue
├── SerdeSpec.lean              # serde_json serialization spec + integer proof
├── SerdeFloat.lean             # ryu-lean4 integration + float composition theorem
├── CrossValidation.lean        # 33 serde + 38 decimal/float cross-validation tests
├── DecimalParseRoundtrip.lean  # parseJsonNumber roundtrips with Decimal.format
├── UnifiedRoundtrip.lean       # Unified number roundtrip + sorted roundtrip + parseJV lift
├── Float64.lean                # IEEE 754 conformance predicates
├── RecordOrder.lean            # Field ordering and normalization
├── DecidableEq.lean            # DecidableEq for nested inductives
└── Tests.lean                  # Runtime conformance tests
conformance/
└── src/main.rs                 # Differential testing against serde_json (Rust)
doc/
├── proof-narrative.md          # Detailed proof walkthrough
└── aeneas-path.md              # Reference: Rust→Lean extraction via Aeneas
```

## Building

Requires [Lean 4](https://lean-lang.org/) v4.29.0-rc6 (see `lean-toolchain`). Dependencies: [Mathlib](https://github.com/leanprover-community/mathlib4) v4.28.0 and [ryu-lean4](https://github.com/lexicone42/ryu-lean4).

```bash
lake build        # ~20 min first build (fetches Mathlib), incremental after
lake exe nickelean  # runs cross-validation and conformance tests
```

## How the proofs compose

```
NickelValue ──toJson──▸ JsonValue ──printJsonValue──▸ String
     │                                                   │
     │              AST roundtrip (proven)                │ JSON text roundtrip (proven)
     │                                                   │
NickelValue ◂──fromJson── JsonValue ◂──parseJV───────────┘

For float numbers:
  JsonNumber ──toMathRat──▸ ℚ ──roundToNearestEven──▸ F64 ──ryu──▸ Decimal ──format──▸ String
                                                       │                                  │
                                                       └──────── ryu-lean4 roundtrip ─────┘
```

The capstone `full_text_roundtrip` composes all stages in 4 lines.

## Conformance with Nickel's Rust implementation

The Lean model is independently written, not extracted from Nickel's Rust code. Conformance is established through:

- **Formal spec matching**: `SerdeSpec.lean` formalizes serde_json's serialization behavior and proves it matches our printer for integer-valued numbers
- **Float formatting**: `SerdeFloat.lean` connects to ryu-lean4's proven F64 roundtrip (same algorithm as serde_json v1.0.140)
- **String escaping**: Fixed to match serde_json character-for-character (`\b`, `\f` as named escapes, not `\u0008`/`\u000c`)
- **71 cross-validation tests**: 33 serde output + 22 decimal parser + 16 serde float format, all compile-time verified
- **Rust differential testing**: 1000+ random roundtrip tests via the conformance suite

**Unified number roundtrip** — A single theorem covering both integer and float numbers:

```lean
theorem number_serde_roundtrip_unified (jn : JsonNumber)
    (hfin : F64.isFinite (F64.roundToNearestEven jn.toMathRat))
    (rest : List Char) (hrest : NonNumContHead rest) :
    ∃ jn', parseJsonNumber ((formatSerdeNumberF64 (classifyNumberF64 jn hfin)).toList ++ rest)
      = some (jn', rest) ∧
    (jn.denominator = 1 → jn' = jn) ∧
    F64.roundToNearestEven jn'.toMathRat = F64.roundToNearestEven jn.toMathRat
```

### Known limitations

- **Float string format differs from serde_json** — Our `Decimal.format` always produces scientific notation (`1e-1`, `3.14159e0`). serde_json post-processes Ryu's output into "nicer" forms: `0.1` instead of `1e-1`, `10000000000.0` for integers-as-floats, `e+308` with explicit `+`. The DIGITS are identical (both come from Ryu), so the roundtrip is correct, but the character-level output format differs. Our parser handles both formats (`e`, `e+`, with/without decimal point).
- **Numbers are exact rationals** — `JsonNumber` uses `Int / Nat`, not floating-point. Non-canonical equality (`1/2 ≠ 2/4`) by design.
- **serde_json version** — Spec targets v1.0.140 (uses ryu for floats). Nickel could upgrade to v1.0.147+ (uses zmij). Our parser accepts both `e` and `e+` notation.

## Related work

- [ShortestDecimal](https://github.com/lexicone42/shortest-decimal) — Generic, formally verified roundtrip framework for IEEE 754 float-to-decimal algorithms (~7,848 lines). The algorithm-independent foundation.
- [ryu-lean4](https://github.com/lexicone42/ryu-lean4) — Verified Ryu float-to-string roundtrip for all finite IEEE 754 doubles (~3,231 lines). Instantiates ShortestDecimal.
- [Nickel](https://nickel-lang.org/) — The configuration language whose serialization we formalize
- [Ryu paper](https://dl.acm.org/doi/10.1145/3296979.3192369) — Ulf Adams, PLDI 2018

## License

MIT
