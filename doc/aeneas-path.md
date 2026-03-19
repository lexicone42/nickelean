# Aeneas Path: Rust-to-Lean Extraction for Nickel Conformance

Reference document for using [Aeneas](https://github.com/AeneasVerif/aeneas) to formally verify
that Nickel's Rust serialization code matches the nickelean Lean model.

## What Aeneas does

Aeneas translates safe Rust programs into pure functional code for theorem provers:

```
Rust source -> Charon (MIR extraction) -> LLBC (JSON IR) -> Aeneas -> Lean 4 / Coq / F* / HOL4
```

The Lean backend generates monadic code wrapping every operation in `Result` (any Rust operation that
could panic returns `Result T`). Mutable borrows become "backward functions" — returning
`(value, continuation)` pairs.

## Current Lean backend limitations (as of March 2026)

These features are **skipped** in Aeneas's Lean backend (verified by reading test skip annotations):

| Feature | Status | Impact on us |
|---------|--------|-------------|
| Closures | Skipped | Can't extract `sort_by_key` |
| Iterators | Skipped | Can't extract iterator-based code |
| Most loop patterns | Skipped | Only simple while-with-counter works |
| `Ord` trait / sorting | Skipped | Can't extract record key sorting |
| `dyn` / dynamic dispatch | Skipped | — |
| String char operations | Skipped | Can't extract string escaping |
| `Default`, `Deref`, `Drop` | Skipped | — |
| Derive macros (most) | Skipped | — |

Features that **work**: primitives, structs, enums, pattern matching, simple traits, generics,
associated types, const generics, basic arithmetic, array/slice indexing, `Vec` basics.

## Why direct extraction of Nickel's serialization fails

Nickel's `serialize_num` in `core/src/serialize/mod.rs`:

```rust
pub fn serialize_num<S: Serializer>(n: &Number, serializer: S) -> Result<S::Ok, S::Error> {
    if n.is_integer() {
        if *n < 0 {
            if let Ok(n) = i64::try_from(n) { return n.serialize(serializer); }
        } else if let Ok(n) = u64::try_from(n) { return n.serialize(serializer); }
    }
    f64::rounding_from(n, RoundingMode::Nearest).0.serialize(serializer)
}
```

Blockers:
1. **malachite::Rational** — huge external crate, Charon would make it opaque
2. **serde::Serializer trait** — complex associated types (`S::Ok`, `S::Error`), not Aeneas-friendly
3. **No f64 model** — Aeneas has no IEEE 754 float semantics in its Lean backend

## What WOULD work: standalone mirror functions

Write simplified Rust functions that mirror Nickel's logic without serde/malachite dependencies:

### Number classification (feasible today)

```rust
// standalone_nickel_num/src/lib.rs
pub enum NumClass {
    NegInt(i64),
    PosInt(u64),
    Float,
}

/// Mirrors Nickel's serialize_num branching logic.
/// Takes a rational as (numerator, denominator) with den > 0.
pub fn classify_number(num: i64, den: u64) -> NumClass {
    if den == 0 { return NumClass::Float; }
    if num % (den as i64) != 0 { return NumClass::Float; }
    let int_val = num / (den as i64);
    if int_val < 0 {
        NumClass::NegInt(int_val)
    } else {
        NumClass::PosInt(int_val as u64)
    }
}
```

This uses only primitives — well within Aeneas's Lean backend capabilities.

### Record key sorting (NOT feasible today)

`Vec::sort_by_key` requires closures and `Ord`, both Lean-skipped. Would need a custom
insertion sort using only while loops:

```rust
pub fn sort_keys(keys: &mut Vec<(String, u32)>) {
    let mut i = 1;
    while i < keys.len() {
        let mut j = i;
        while j > 0 && keys[j - 1].0 > keys[j].0 {
            keys.swap(j - 1, j);
            j -= 1;
        }
        i += 1;
    }
}
```

**Problem**: `String` comparison (`>`) likely requires `Ord` which is Lean-skipped.
Might work with byte-level comparison on `Vec<u8>` instead.

### String escaping (NOT feasible today)

String character iteration requires the skipped string-chars feature.

## Getting started with Aeneas

### Installation

```bash
# Requires OCaml 5.x via OPAM
opam install . --deps-only
make setup-charon && make
```

### Hello world workflow

1. Create a Rust crate:
   ```bash
   cargo init --lib hello_aeneas
   ```

2. Write a simple function in `src/lib.rs`:
   ```rust
   pub fn add_saturating(x: u32, y: u32) -> u32 {
       let sum = x.wrapping_add(y);
       if sum < x { u32::MAX } else { sum }
   }
   ```

3. Run Charon:
   ```bash
   charon --preset=aeneas  # produces hello_aeneas.llbc
   ```

4. Run Aeneas:
   ```bash
   aeneas -backend lean hello_aeneas.llbc
   ```

5. Get Lean files — auto-generated with `Result` monad wrapping

6. Write proofs using `progress` tactic:
   ```lean
   theorem add_saturating_comm (x y : Std.U32) :
       add_saturating x y = add_saturating y x := by
     unfold add_saturating
     progress as ⟨sum_xy⟩  -- step through wrapping_add
     progress as ⟨sum_yx⟩
     simp_all [Std.U32.wrapping_add_comm]
   ```

### Key proof tactics

- `progress` — step through one monadic operation in extracted code
- `scalar_tac` — arithmetic reasoning about bounded integers (U32, I64, etc.)
- `simp_all` — standard simplification

### Files to study in the Aeneas repo

- `tests/src/demo.rs` — tutorial Rust source
- `tests/lean/Demo/Demo.lean` — auto-generated Lean
- `tests/lean/Demo/Properties.lean` — hand-written proofs (79 lines, clear examples)
- `tests/src/hashmap.rs` — most complex proven example (custom HashMap)

## What extending Aeneas to cover our full needs would require

### Gap 1: Closures for sorting (~months of Aeneas development)

Closures are supported in F*/Coq backends but not Lean. Enabling them in Lean requires:
- Translating closure captures to Lean structures
- Handling the `Fn`/`FnMut`/`FnOnce` trait hierarchy in Lean's type system
- This is active Aeneas development work, not something we'd do ourselves

### Gap 2: String operations (~months)

The `string-chars.rs` test is Lean-skipped. Handling Rust's `char` iteration over strings requires
modeling UTF-8 encoding/decoding in Lean, which is substantial.

### Gap 3: External crate integration

Charon makes foreign crate items opaque by default. For malachite, you'd need to:
- Write Lean specifications for every malachite function used by Nickel
- Prove those specs match malachite's behavior (separately)
- Use `--extract-opaque-bodies` carefully and deal with translation errors

### Gap 4: Serde trait machinery

The `Serializer` trait has ~30 methods with associated types and builder patterns
(`SerializeMap`, `SerializeSeq`). Modeling this in Lean would be a research project.

### Realistic effort estimate

| Component | Effort | Feasibility |
|-----------|--------|-------------|
| Number classification extraction | 1-2 weeks | Feasible now |
| Custom insertion sort extraction | 2-4 weeks | Possibly feasible |
| String escaping extraction | Months | Requires Aeneas improvements |
| Full serde trait modeling | Research project | Not feasible near-term |
| **Total for full conformance** | **6-12 months** | Requires upstream Aeneas work |

**Comparison**: Path 4 (formal spec in pure Lean) is ~830 lines and 4-8 weeks, with no
dependency on upstream Aeneas development.

## When Aeneas becomes the right tool

Aeneas would be the right approach if:
1. Nickel refactored `serialize_num` into a standalone, serde-free function
2. Aeneas's Lean backend adds closure support (actively developed)
3. You want to verify a self-contained Rust crate (not one with heavy trait dependencies)

The crypto domain (HACL*, SymCrypt, libcrux) is where Aeneas shines — array manipulation,
bitwise ops, simple control flow. Rich trait hierarchies and external crate dependencies
are uncharted territory.

## References

- [Aeneas GitHub](https://github.com/AeneasVerif/aeneas) — 641 stars, very active
- [Charon GitHub](https://github.com/AeneasVerif/charon) — Rust MIR frontend
- [Aeneas documentation](https://aeneasverif.github.io/)
- [ICFP 2022 paper](https://dl.acm.org/doi/10.1145/3547647) — "Aeneas: Rust verification by functional translation"
- [Lean backend case study](https://lean-lang.org/use-cases/aeneas/)
- [Microsoft SymCrypt verification](https://www.emergentmind.com/topics/charon-aeneas-pipeline) — largest production user
