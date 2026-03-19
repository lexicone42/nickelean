/-
  NickelJson/SerdeSpec.lean

  Formal specification of serde_json's compact JSON serialization.
  Targets serde_json v1.0.140 (the version used by Nickel), which uses
  the ryu crate for float formatting.

  This spec matches serde_json::to_string character-for-character:
  - String escaping: escapeJsonString (fixed in Phase 1 for \b/\f)
  - Integer formatting: itoa-compatible plain decimal
  - Structural formatting: compact (no whitespace)
  - Float formatting: placeholder for Phase 4 (ryu-lean4 integration)

  The main theorem (formatSerdeNumber_matches_printJsonNumber) shows that for
  integer-valued numbers, our printJsonValue ∘ toJson produces the
  same output as serde_json::to_string would.
-/
import Nickelean.PrintJson
import Nickelean.ToJson

/-! ## Serde number representation -/

/-- serde_json's internal number type.
    Matches the three variants of serde_json::Number:
    - PosInt(u64): non-negative integer
    - NegInt(i64): negative integer
    - Float(f64): floating-point (any non-integer, or integer outside i64/u64 range) -/
inductive SerdeNumber where
  | posInt (n : Nat)
  | negInt (n : Int) (h : n < 0)
  | float -- placeholder: Phase 4 will carry an F64 value from ryu-lean4
  deriving Repr

/-! ## Nickel's number classification -/

/-- Classify a JsonNumber the way Nickel's serialize_num does.
    Mirrors core/src/serialize/mod.rs:
    1. If integer (denominator divides numerator evenly):
       - If negative: NegInt
       - If non-negative: PosInt
    2. Otherwise: Float -/
def classifyNumber (jn : JsonNumber) : SerdeNumber :=
  if jn.numerator % jn.denominator == 0 then
    let intVal := jn.numerator / jn.denominator
    if h : intVal < 0 then
      .negInt intVal h
    else
      .posInt intVal.toNat
  else
    .float

/-! ## Integer formatting (matching itoa) -/

/-- Format a SerdeNumber as a JSON number string.
    For integers, matches the itoa crate's output (plain decimal).
    For floats, returns a placeholder — Phase 4 will use ryu-lean4. -/
def formatSerdeNumber : SerdeNumber → String
  | .posInt n => printNat n
  | .negInt n _ => "-" ++ printNat n.natAbs
  | .float => "0" -- placeholder

/-- An integer-valued JsonNumber has denominator dividing the numerator. -/
def JsonNumber.isInteger (jn : JsonNumber) : Prop :=
  jn.numerator % jn.denominator = 0

/-- Integer JsonNumbers with denominator = 1 are trivially integer-valued. -/
theorem JsonNumber.isInteger_of_den_one (jn : JsonNumber) (h : jn.denominator = 1) :
    jn.isInteger := by
  simp [JsonNumber.isInteger, h]

/-! ## Formatting equivalence proofs -/

/-- For integer rationals with denominator = 1, classifyNumber produces the
    correct SerdeNumber variant. -/
theorem classifyNumber_den_one_neg (jn : JsonNumber) (h : jn.denominator = 1)
    (hneg : jn.numerator < 0) :
    classifyNumber jn = .negInt jn.numerator hneg := by
  unfold classifyNumber
  have h1 : (jn.denominator : Int) = 1 := by exact_mod_cast h
  simp only [h1, Int.emod_one, beq_self_eq_true, ↓reduceIte, Int.ediv_one, hneg, ↓reduceDIte]

theorem classifyNumber_den_one_nonneg (jn : JsonNumber) (h : jn.denominator = 1)
    (hnn : ¬(jn.numerator < 0)) :
    classifyNumber jn = .posInt jn.numerator.toNat := by
  unfold classifyNumber
  have h1 : (jn.denominator : Int) = 1 := by exact_mod_cast h
  simp only [h1, Int.emod_one, beq_self_eq_true, ↓reduceIte, Int.ediv_one, hnn, ↓reduceDIte]

/-- For integer rationals with denominator = 1,
    formatSerdeNumber ∘ classifyNumber produces the same output as printJsonNumber. -/
theorem formatSerdeNumber_matches_printJsonNumber (jn : JsonNumber) (h : jn.denominator = 1) :
    formatSerdeNumber (classifyNumber jn) = printJsonNumber jn := by
  unfold printJsonNumber
  simp only [h, beq_self_eq_true, ↓reduceIte]
  by_cases hneg : jn.numerator < 0
  · rw [classifyNumber_den_one_neg jn h hneg]
    simp only [hneg, ↓reduceIte, formatSerdeNumber]
  · rw [classifyNumber_den_one_nonneg jn h hneg]
    simp only [hneg, ↓reduceIte, formatSerdeNumber]
    congr 1
    omega

/-! ## Full serde_json serialization spec -/

mutual
/-- The serde_json compact serialization spec.
    Matches serde_json::to_string for compact (no whitespace) formatting.
    Strings are already escaped by the caller (matching our toJson pipeline). -/
def serdeJsonSerialize : JsonValue → String
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .number n => formatSerdeNumber (classifyNumber n)
  | .string s => "\"" ++ s ++ "\""
  | .array elems => "[" ++ serdeJsonSerializeArray elems ++ "]"
  | .object fields => "{" ++ serdeJsonSerializeObject fields ++ "}"

def serdeJsonSerializeArray : List JsonValue → String
  | [] => ""
  | [v] => serdeJsonSerialize v
  | v :: vs => serdeJsonSerialize v ++ "," ++ serdeJsonSerializeArray vs

def serdeJsonSerializeObject : List (String × JsonValue) → String
  | [] => ""
  | [(k, v)] => "\"" ++ k ++ "\":" ++ serdeJsonSerialize v
  | (k, v) :: rest => "\"" ++ k ++ "\":" ++ serdeJsonSerialize v ++ "," ++ serdeJsonSerializeObject rest
end

/-! ## Structural equivalence: serdeJsonSerialize matches printJsonValue -/

/-- For integer-valued numbers (denominator = 1), the serde spec's number
    formatting matches our JSON printer. -/
theorem serdeJsonSerialize_number_eq (n : JsonNumber) (h : n.denominator = 1) :
    serdeJsonSerialize (.number n) = printJsonValue (.number n) := by
  simp only [serdeJsonSerialize, printJsonValue, formatSerdeNumber_matches_printJsonNumber n h]
