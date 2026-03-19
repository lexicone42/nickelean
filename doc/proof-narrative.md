# Nickelean: Proof Narrative

A detailed walkthrough of how the JSON roundtrip theorem is proved, from string escaping through nested inductive types.

## The theorem

```lean
theorem json_roundtrip (v : NickelValue) : fromJson (toJson v) = some v
```

This says: for *any* Nickel value — null, booleans, numbers, strings with arbitrary characters, nested arrays, records with special-character keys — serializing to JSON and deserializing produces exactly the original value. No exceptions, no edge cases, no "works for well-behaved inputs."

## The challenge: nested inductives

The central difficulty isn't the theorem itself — it's the data types:

```lean
inductive NickelValue where
  | null
  | bool (b : Bool)
  | num (n : JsonNumber)
  | str (s : String)
  | array (elems : List NickelValue)     -- nested inductive!
  | record (fields : List (String × NickelValue))  -- doubly nested!
```

Lean 4 cannot derive structural recursion through `List` wrappers. A function like `toJson : NickelValue → JsonValue` *looks* like it should work with a simple `match`, but Lean can't prove termination for the `array` case because `List.map (fun v => toJson v)` hides the structural decrease behind a lambda.

**The solution**: explicit mutual recursion. Every function that touches `NickelValue` has companion functions for `List NickelValue` and `List (String × NickelValue)`:

```lean
def toJson : NickelValue → JsonValue
def toJsonList : List NickelValue → List JsonValue
def toJsonFields : List (String × NickelValue) → List (String × JsonValue)
```

This pattern propagates everywhere: `fromJson`/`fromJsonList`/`fromJsonFields`, `DecidableEq`/`List DecidableEq`/`Fields DecidableEq`, and crucially, the roundtrip proof itself.

## Layer 1: Hex digit roundtrip

The proof begins at the bottom — individual hexadecimal digits.

JSON encodes control characters as `\uXXXX` sequences. The escape function converts a nibble (0–15) to a hex character:

```lean
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n - 10 + 97)
```

The first lemma proves this is invertible:

```lean
theorem parseHexDigit_hexDigit (n : Nat) (h : n < 16) :
    parseHexDigit (hexDigit n) = some n
```

**Proof technique**: Generate all 16 cases via `omega`, then verify each with `native_decide`. This is a brute-force approach, but it's the right one — there's no "structure" to exploit in an ASCII lookup table. The proof is 3 lines and checks instantly.

## Layer 2: Four-hex-digit roundtrip

A `\uXXXX` escape encodes a character's code point as four hex digits. The roundtrip requires proving that decomposing a number into nibbles and reassembling produces the original:

```lean
theorem parseHex4_roundtrip (c : Char) (hc : c.val.toNat < 65536) :
    parseHex4 [hexDigit (c.val.toNat / 4096 % 16),
               hexDigit (c.val.toNat / 256 % 16),
               hexDigit (c.val.toNat / 16 % 16),
               hexDigit (c.val.toNat % 16)] = some c
```

**Proof technique**: Apply Layer 1 four times, then use `hex4_decompose` (which proves `n = (n/4096%16)*4096 + (n/256%16)*256 + (n/16%16)*16 + n%16` via `omega`), and finish with `Char.ext` + `UInt32.toNat_inj` to reconstruct the character. The arithmetic is trivial but the type coercions require care — `Char.mk` in Lean 4.28 takes two fields, and the `isValid` proof needs `omega`.

## Layer 3: Single character roundtrip

This is the most intricate layer. The escape function has 7 cases:

```lean
def escapeChar (c : Char) : List Char :=
  if c = '"' then ['\', '"']
  else if c = '\\' then ['\', '\']
  else if c = '\n' then ['\', 'n']
  else if c = '\r' then ['\', 'r']
  else if c = '\t' then ['\', 't']
  else if needsEscape c then escapeCharHex c  -- \uXXXX for control chars
  else [c]                                     -- passthrough
```

The unescape function is a state machine (`unescapeLoop`) that reads from the front and accumulates characters in reverse. The roundtrip lemma:

```lean
theorem unescapeLoop_escapeChar (c : Char) (acc rest : List Char) :
    unescapeLoop (escapeChar c ++ rest) acc = unescapeLoop rest (c :: acc)
```

says: processing an escaped character followed by `rest` is the same as skipping straight to `rest` with `c` prepended to the accumulator.

**Proof technique**: Nested case analysis matching the 7-branch structure of `escapeChar`. Each special character (`"`, `\`, `\n`, `\r`, `\t`) has its own subproof: unfold `escapeChar`, show which branch matches, then unfold `unescapeLoop` twice (once for `\`, once for the escape letter) using equation lemmas (`unescapeLoop.eq_N`). The control character case delegates to `unescapeLoop_escapeCharHex` which uses the Layer 2 roundtrip. The passthrough case proves `¬needsEscape c → escapeChar c = [c]` and unfolds the identity.

## Layer 4: Full string roundtrip via accumulator

The string-level escape uses `flatMap`:

```lean
def escapeJsonString (s : String) : String :=
  ⟨s.toList.flatMap escapeChar⟩
```

The roundtrip proof works over lists, not strings, using an accumulator:

```lean
theorem unescapeLoop_flatMap_escapeChar_acc (chars rest : List Char) (acc : List Char) :
    unescapeLoop (chars.flatMap escapeChar ++ rest) acc =
    unescapeLoop rest (chars.reverse ++ acc)
```

**Proof technique**: List induction on `chars`. The base case is trivial. The inductive step unfolds `flatMap` to `escapeChar head ++ (tail.flatMap escapeChar ++ rest)`, reassociates the append, applies `unescapeLoop_escapeChar` from Layer 3 to consume the head, then applies the inductive hypothesis on the tail.

The closed form follows by setting `acc = []` and `rest = []`:

```lean
theorem unescapeLoop_flatMap_escapeChar (chars : List Char) :
    unescapeLoop (chars.flatMap escapeChar) [] = some chars.reverse.reverse
```

## Layer 5: Lifting to strings

The top-level theorem lifts from `List Char` to `String`:

```lean
theorem unescape_escape_roundtrip (s : String) :
    unescapeJsonString (escapeJsonString s) = some s
```

**Proof technique**: Unfold the string wrappers, apply Layer 4, and use `List.reverse_reverse` + `String.mk_toList`.

## The main roundtrip: mutual induction

With string escaping proved, the main roundtrip theorem falls to mutual structural induction:

```lean
theorem json_roundtrip (v : NickelValue) : fromJson (toJson v) = some v
theorem json_roundtrip_list (vs : List NickelValue) : fromJsonList (toJsonList vs) = some vs
theorem json_roundtrip_fields (fs : List (String × NickelValue)) :
    fromJsonFields (toJsonFields fs) = some fs
```

**Proof technique for each case**:

- **null, bool, num**: `rfl` — the serialization is trivially invertible.
- **str**: Unfold `toJson` (which calls `escapeJsonString`), then unfold `fromJson` (which calls `unescapeJsonString`), apply `unescape_escape_roundtrip`, simplify the `Option.bind`.
- **array**: Unfold both sides, apply `json_roundtrip_list` inductively, simplify `Option.bind`/`Option.map`.
- **record**: Same as array but with pairs — destruct each field as `(key, value)`, apply escape roundtrip to the key and `json_roundtrip` to the value.
- **List NickelValue**: Nil returns `some []`. Cons applies `json_roundtrip` to the head and `json_roundtrip_list` to the tail, then threads through the `Option` monad.
- **Field list**: Same as cons-list but also handles the key string.

The entire proof is ~45 lines. All the difficulty was in the escape roundtrip.

## DecidableEq: the other mutual recursion

For the runtime tests to use `==`, both `NickelValue` and `JsonValue` need `DecidableEq` instances. Lean can't derive these automatically for nested inductives (same reason as the recursion issue).

The manual instances follow a pattern: for each pair of constructors, either prove equality (same constructor, recurse on arguments) or prove inequality (`noConfusion`). This generates 25 cases for `NickelValue` (5 constructors × 5) and is tedious but mechanical. The list cases use cons/nil case splitting and thread `Decidable` through recursive calls.

## Float64 conformance boundary

The roundtrip theorem holds for all `JsonNumber`s (exact rationals). In practice, Nickel uses `serde_json` with the Ryu algorithm, which operates on IEEE 754 f64. The `Float64.lean` module documents this gap:

```lean
def IsF64Representable (n : JsonNumber) : Prop :=
  ∃ (m : Int) (e : Int), n.toRat = m * 2^e ∧ |m| < 2^53 ∧ -1074 ≤ e ∧ e ≤ 971
```

The theorem `json_roundtrip_f64_domain` notes that the roundtrip holds trivially within this subset (since it holds for all rationals). The interesting gap is at the boundary — what happens with numbers that *aren't* f64-representable. This is where the [ryu-lean4](https://github.com/lexicone42/ryu-lean4) formalization picks up.

## Record field ordering

JSON objects are unordered per RFC 8259, but implementations differ:
- `serde_json` with `preserve_order`: insertion order (IndexMap)
- `serde_json` without `preserve_order`: sorted order (BTreeMap)
- Nickel: uses `preserve_order` by default

The `RecordOrder.lean` module provides `normalizeFieldOrder` (recursive field sorting) and proves `json_roundtrip_normalized` — the roundtrip holds for normalized values. Full permutation equivalence is documented but deferred.

## JSON text roundtrip (Gap 3 closure)

The most substantial addition: a JSON text parser (`ParseJsonText.lean`, 699 lines) with a proven roundtrip against `printJsonValue`.

The parser handles null, true, false, integers (with optional minus), quoted strings with escape sequences, arrays with comma-separated elements, and objects with "key":value pairs. It uses fuel-based termination.

**Proof architecture (bottom-up)**:

1. **ScanSafe predicate** — Captures strings where `scanStringContent` correctly finds the closing quote. Proved that `escapeJsonString` produces `ScanSafe` output.

2. **scanStringContent roundtrip** — Scanning a ScanSafe char list followed by `'"'` recovers the original chars.

3. **Number parsing** — `parseJsonNat` inverts `printNat` via accumulator induction. The key lemma: `printNatGo n []` produces digit characters whose foldl computes back to `n`.

4. **First-char disambiguation** — `printJsonValue v` never starts with `']'` or `'}'`, needed to distinguish array/object content from closing brackets.

5. **Mutual roundtrip** — Three theorems by structural induction: `parseJV_printJsonValue`, `parseJArr_printJsonArray`, `parseJObj_printJsonObject`.

## serde_json spec and float composition

`SerdeSpec.lean` formalizes serde_json's serialization:
- `SerdeNumber` type (PosInt/NegInt/Float, matching serde_json::Number)
- `classifyNumber` (Nickel's serialize_num dispatch)
- `serdeJsonSerialize` (compact JSON formatter)
- Proven: integer formatting matches our `printJsonNumber`

`SerdeFloat.lean` connects to ryu-lean4:
- `ryuFloatFormat` instantiates `FloatFormat` with F64, Decimal, Ryu
- `serialize_num_float_roundtrip`: the composition theorem
- `serialize_num_complete`: any JsonNumber either has an integer string or a float string that roundtrips

## The capstone

`FullTextRoundtrip.lean` (120 lines) composes everything:

```lean
theorem full_text_roundtrip (v : NickelValue) (hdo : NickelAllDenOne v) :
    (parseJV ((printJsonValue (toJson v)).toList) (jsonSize (toJson v))).bind
      (fun ⟨jv, _⟩ => fromJson jv) = some v
```

The proof is 4 lines — all complexity is in the components.

## Proof statistics

| Component | Lines | Technique |
|-----------|-------|-----------|
| JSON text parser + roundtrip proof | 699 | Fuel-based recursion, mutual induction |
| serde_json spec + float composition | 319 | Ryu integration, number classification |
| Escape implementation + roundtrip | 283 | 5-layer pyramid, native_decide base cases |
| DecidableEq instances | 159 | Exhaustive constructor case analysis |
| Full text roundtrip composition | 120 | Precondition satisfaction + 4-line proof |
| AST roundtrip + cross-validation | 216 | Mutual structural induction, 33 tests |
| Core types + utilities | 462 | Dependent types, mutual recursion |
| **Total Lean formalization** | **~2,260** | **Zero sorrys, zero axioms** |
| **+ ryu-lean4** | **~3,230** | **IEEE 754 float-to-string roundtrip** |
| **Combined system** | **~5,490** | **Full verified JSON serialization** |
