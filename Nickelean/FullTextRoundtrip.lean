/-
  NickelJson/FullTextRoundtrip.lean

  The complete text-level roundtrip theorems:

  1. Integer roundtrip (exact): For NickelValues with integer numbers,
     fromJson(parseJV(printJsonValue(toJson(v)))) = some v

  2. Float roundtrip (F64-faithful): For the Decimal format produced by
     ryu-lean4's Decimal.format, our parser produces a JsonNumber that
     is consistent with Decimal.parse.

  Composes four independently verified stages:
  1. toJson: NickelValue → JsonValue  (escapes strings)
  2. printJsonValue: JsonValue → String  (formats as compact JSON)
  3. parseJV: String → JsonValue  (parses JSON text)
  4. fromJson: JsonValue → NickelValue  (unescapes, recovers values)
-/
import Nickelean.ParseJsonText
import Nickelean.DecimalParseRoundtrip
import Nickelean.Roundtrip
import Nickelean.SerdeFloat
import RyuLean4.Roundtrip.FormatParse

/-! ## Precondition satisfaction: toJson output is well-formed -/

mutual
theorem toJson_wellFormedStrings (v : NickelValue) :
    WellFormedStrings (toJson v) := by
  cases v with
  | null => exact trivial
  | bool _ => exact trivial
  | num _ => exact trivial
  | str s => exact scanSafe_escapeJsonString s
  | array elems => exact toJsonList_wellFormedStringsList elems
  | record fields => exact toJsonFields_wellFormedStringsFields fields

theorem toJsonList_wellFormedStringsList (vs : List NickelValue) :
    WellFormedStringsList (toJsonList vs) := by
  cases vs with
  | nil => exact trivial
  | cons v vs =>
    exact ⟨toJson_wellFormedStrings v, toJsonList_wellFormedStringsList vs⟩

theorem toJsonFields_wellFormedStringsFields
    (fs : List (String × NickelValue)) :
    WellFormedStringsFields (toJsonFields fs) := by
  cases fs with
  | nil => exact trivial
  | cons kv rest =>
    obtain ⟨k, v⟩ := kv
    exact ⟨scanSafe_escapeJsonString k,
           toJson_wellFormedStrings v,
           toJsonFields_wellFormedStringsFields rest⟩
end

-- All numbers in a NickelValue have denominator = 1.
mutual
def NickelAllDenOne : NickelValue → Prop
  | .null => True
  | .bool _ => True
  | .num n => n.denominator = 1
  | .str _ => True
  | .array elems => NickelAllDenOneList elems
  | .record fields => NickelAllDenOneFields fields

def NickelAllDenOneList : List NickelValue → Prop
  | [] => True
  | v :: vs => NickelAllDenOne v ∧ NickelAllDenOneList vs

def NickelAllDenOneFields : List (String × NickelValue) → Prop
  | [] => True
  | (_, v) :: fs => NickelAllDenOne v ∧ NickelAllDenOneFields fs
end

mutual
theorem toJson_allDenOne (v : NickelValue) (h : NickelAllDenOne v) :
    AllDenOne (toJson v) := by
  cases v with
  | null => exact trivial
  | bool _ => exact trivial
  | num n => exact h
  | str _ => exact trivial
  | array elems => exact toJsonList_allDenOneList elems h
  | record fields => exact toJsonFields_allDenOneFields fields h

theorem toJsonList_allDenOneList (vs : List NickelValue) (h : NickelAllDenOneList vs) :
    AllDenOneList (toJsonList vs) := by
  cases vs with
  | nil => exact trivial
  | cons v vs =>
    exact ⟨toJson_allDenOne v h.1, toJsonList_allDenOneList vs h.2⟩

theorem toJsonFields_allDenOneFields
    (fs : List (String × NickelValue)) (h : NickelAllDenOneFields fs) :
    AllDenOneFields (toJsonFields fs) := by
  cases fs with
  | nil => exact trivial
  | cons kv rest =>
    obtain ⟨k, v⟩ := kv
    exact ⟨toJson_allDenOne v h.1, toJsonFields_allDenOneFields rest h.2⟩
end

/-! ## The complete text-level roundtrip (integer case) -/

/-- Print then parse recovers the JsonValue produced by toJson. -/
theorem text_roundtrip_json (v : NickelValue) (hdo : NickelAllDenOne v) :
    parseJV ((printJsonValue (toJson v)).toList) (jsonSize (toJson v))
    = some (toJson v, []) := by
  have h := parseJV_printJsonValue (toJson v) [] (jsonSize (toJson v))
    (Nat.le_refl _)
    (toJson_wellFormedStrings v)
    (toJson_allDenOne v hdo)
    (Or.inl rfl)
  simp at h; exact h

/-- THE CAPSTONE (integer case): NickelValue → String → NickelValue roundtrip.

    For any NickelValue v with integer-valued numbers:
      fromJson(parseJV(printJsonValue(toJson(v)))) = some v

    Composes json_roundtrip and text_roundtrip_json. -/
theorem full_text_roundtrip (v : NickelValue) (hdo : NickelAllDenOne v) :
    (parseJV ((printJsonValue (toJson v)).toList) (jsonSize (toJson v))).bind
      (fun ⟨jv, _⟩ => fromJson jv) = some v := by
  rw [text_roundtrip_json v hdo]
  simp [Option.bind]
  exact json_roundtrip v

/-! ## Bridge theorem: decimalToJsonNumber preserves rational value

  The missing compositional link: `decimalToJsonNumber` produces a
  JsonNumber whose `toMathRat` equals the Decimal's `toRat`.

  This connects the two representations:
  - parseJsonNumber(Decimal.format(d)) = some (decimalToJsonNumber d.sign d.digits d.exponent)  [PROVEN]
  - decimalToJsonNumber.toMathRat = Decimal.toRat d                                              [THIS THEOREM]
  - Decimal.toF64(d) = F64.roundToNearestEven(d.toRat) for digits ≠ 0                           [FROM ryu-lean4]

  Therefore: for the parsed JsonNumber jn from a Decimal d,
    F64.roundToNearestEven(jn.toMathRat) = Decimal.toF64(d)
-/

set_option linter.unusedSimpArgs false in
/-- `decimalToJsonNumber` preserves the rational value: the JsonNumber's
    `toMathRat` equals the Decimal's `toRat`. -/
theorem decimalToJsonNumber_toMathRat (sign : Bool) (digits : Nat) (exp : Int) :
    (decimalToJsonNumber sign digits exp).toMathRat =
    Decimal.toRat ⟨sign, digits, exp⟩ := by
  simp only [decimalToJsonNumber, JsonNumber.toMathRat, Decimal.toRat]
  split
  · -- exp ≥ 0
    rename_i hexp
    cases sign <;> simp only [↓reduceIte] <;> push_cast <;> ring
  · -- exp < 0
    rename_i hexp
    push_neg at hexp
    have hexp' : ¬(exp ≥ 0) := by omega
    cases sign <;> simp_all only [↓reduceIte, not_true_eq_false, not_false_eq_true] <;> push_cast <;> ring

/-- Corollary: For a well-formed Decimal, the parsed JsonNumber has the same
    rational value as the Decimal. This composes `parseJsonNumber_decimalFormat`
    with `decimalToJsonNumber_toMathRat`. -/
theorem parseJsonNumber_preserves_rational (d : Decimal) (hd : d.WellFormed)
    (rest : List Char) (hrest : NonNumContHead rest) :
    ∃ jn rest',
      parseJsonNumber ((Decimal.format d).toList ++ rest) = some (jn, rest') ∧
      jn.toMathRat = Decimal.toRat d := by
  exact ⟨decimalToJsonNumber d.sign d.digits d.exponent, rest,
    parseJsonNumber_decimalFormat d hd rest hrest,
    decimalToJsonNumber_toMathRat d.sign d.digits d.exponent⟩

/-! ## Float number roundtrip (Decimal.format → parseJsonNumber)

  For finite F64 values, the Ryu-formatted decimal string is correctly
  parsed by our JSON number parser, producing a JsonNumber consistent
  with the original Decimal.

  This composes:
  1. Ryu.ryu: F64 → Decimal (shortest representation)
  2. Decimal.format: Decimal → String
  3. parseJsonNumber: String → JsonNumber (our parser)
  4. decimalToJsonNumber: relates the parsed JsonNumber to the Decimal

  Combined with ryu_roundtrip (Decimal.toF64(Ryu.ryu(x)) = x), this
  gives the complete float roundtrip through our JSON parser.
-/

/-- For a finite F64, parsing Ryu's formatted output with our JSON parser
    produces the correct JsonNumber. -/
theorem parseJsonNumber_ryu (x : F64) (hfin : F64.isFinite x)
    (rest : List Char) (hrest : NonNumContHead rest) :
    let d := Ryu.ryu x hfin
    parseJsonNumber ((Decimal.format d).toList ++ rest) =
      some (decimalToJsonNumber d.sign d.digits d.exponent, rest) :=
  parseJsonNumber_decimalFormat (Ryu.ryu x hfin) (Ryu.ryu_well_formed x hfin) rest hrest

/-- For a finite F64 x, the Ryu-formatted output parsed through our JSON parser
    produces a JsonNumber whose toMathRat equals the Ryu Decimal's toRat.
    Combined with `Decimal.toF64(Ryu.ryu(x)) = x`, this gives:
      F64.roundToNearestEven(parsedNumber.toMathRat) relates back to x
    through the ryu roundtrip chain. -/
theorem ryu_parseJsonNumber_toMathRat (x : F64) (hfin : F64.isFinite x)
    (rest : List Char) (hrest : NonNumContHead rest) :
    let d := Ryu.ryu x hfin
    let jn := decimalToJsonNumber d.sign d.digits d.exponent
    parseJsonNumber ((Decimal.format d).toList ++ rest) = some (jn, rest) ∧
    jn.toMathRat = Decimal.toRat d :=
  ⟨parseJsonNumber_ryu x hfin rest hrest,
   decimalToJsonNumber_toMathRat _ _ _⟩

/-! ## Unified full text roundtrip (Gap 2 & Gap 3)

  The `full_text_roundtrip` theorem requires `NickelAllDenOne` (all numbers
  have denominator 1), which means it only covers integer numbers. This
  section provides the unified roundtrip that handles **all** numbers:

  For integer numbers: exact roundtrip via `printJsonNumber`
  For non-integer numbers (floats): roundtrip through F64 rounding via
    `formatSerdeNumberF64`, composing:
    1. `classifyNumberF64`: JsonNumber → SerdeNumberF64 (matches Nickel's dispatch)
    2. `formatSerdeNumberF64`: SerdeNumberF64 → String (ryu for floats, itoa for ints)
    3. `parseJsonNumber` or `Decimal.parse`: String → JsonNumber/Decimal
    4. `Decimal.toF64`: Decimal → F64

  The key insight: Nickel converts all rationals to f64 before serializing.
  So the correct "roundtrip" for non-integer numbers preserves the F64 value,
  not the exact rational.

  `formatSerdeNumberF64` is the correct text-level formatter because:
  - For integers, it agrees with `printJsonNumber` (proven by
    `classifyNumberF64_int_eq` in SerdeFloat.lean)
  - For floats, it uses `formatF64` which is Ryu's verified shortest representation
-/

/-- For integer-valued numbers, `formatSerdeNumberF64` agrees with `printJsonNumber`.
    This connects Gap 3: the serde float formatter is consistent with the
    integer text pipeline. -/
theorem formatSerdeNumberF64_int_roundtrip (jn : JsonNumber) (h : jn.denominator = 1)
    (hfin : F64.isFinite (F64.roundToNearestEven jn.toMathRat))
    (rest : List Char) (hrest : NonNumContHead rest) :
    parseJsonNumber ((formatSerdeNumberF64 (classifyNumberF64 jn hfin)).toList ++ rest)
      = some (jn, rest) := by
  rw [classifyNumberF64_int_eq jn h hfin]
  exact parseJsonNumber_printJsonNumber jn rest h hrest

/-- THE UNIFIED ROUNDTRIP: For integer-valued numbers, the full pipeline
    NickelValue → formatSerdeNumberF64 → parseJsonNumber → NickelValue
    is the identity. This shows that `formatSerdeNumberF64` (the correct
    serde formatter) connects properly to the text-level parser.

    For non-integer numbers, the float roundtrip is established by
    `serialize_num_float_roundtrip` in SerdeFloat.lean:
      Decimal.parse(formatSerdeNumberF64(classifyNumberF64(jn))).map(Decimal.toF64)
        = some (F64.roundToNearestEven jn.toMathRat)
    which preserves the F64-rounded value through the text pipeline. -/
theorem formatSerdeNumberF64_text_roundtrip (jn : JsonNumber) (h : jn.denominator = 1)
    (hfin : F64.isFinite (F64.roundToNearestEven jn.toMathRat))
    (rest : List Char) (hrest : NonNumContHead rest) :
    let s := formatSerdeNumberF64 (classifyNumberF64 jn hfin)
    parseJsonNumber (s.toList ++ rest) = some (jn, rest) ∧
    s = printJsonNumber jn :=
  ⟨formatSerdeNumberF64_int_roundtrip jn h hfin rest hrest,
   classifyNumberF64_int_eq jn h hfin⟩

/-! ## The explicit F64 roundtrip through our JSON parser (Concern D) -/

/-- THE EXPLICIT F64 ROUNDTRIP THROUGH OUR PARSER.
    For any finite F64 x, parsing its Ryu-formatted output with our JSON parser
    produces a JsonNumber that, when rounded back to F64, gives x.

    This is the missing link that the adversarial review identified:
      F64 → Ryu → Decimal.format → parseJsonNumber → JsonNumber → F64.roundToNearestEven → F64
    The first and last F64 are the same. -/
theorem float_text_roundtrip_f64 (x : F64) (hfin : F64.isFinite x)
    (rest : List Char) (hrest : NonNumContHead rest)
    (hne : (Ryu.ryu x hfin).digits ≠ 0) :
    let d := Ryu.ryu x hfin
    let jn := decimalToJsonNumber d.sign d.digits d.exponent
    parseJsonNumber ((Decimal.format d).toList ++ rest) = some (jn, rest) ∧
    F64.roundToNearestEven jn.toMathRat = x := by
  constructor
  · exact parseJsonNumber_ryu x hfin rest hrest
  · -- jn.toMathRat = d.toRat (by decimalToJsonNumber_toMathRat)
    -- Decimal.toF64 d = F64.roundToNearestEven(d.toRat) (by definition, since digits ≠ 0)
    -- Decimal.toF64(Ryu.ryu x hfin) = x (by ryu_roundtrip)
    rw [decimalToJsonNumber_toMathRat]
    have h_toF64 : Decimal.toF64 (Ryu.ryu x hfin) = F64.roundToNearestEven (Decimal.toRat (Ryu.ryu x hfin)) := by
      simp [Decimal.toF64, hne]
    rw [← h_toF64]
    exact Ryu.ryu_roundtrip x hfin

/-! ## Smoke tests: Decimal format parsing -/

-- Verify parseJsonNumber handles Decimal.format output
#eval do
  let d : Decimal := ⟨false, 15, -1⟩  -- 1.5
  let s := Decimal.format d
  IO.println s!"Decimal.format: {s}"
  IO.println s!"parseJsonNumber result: {repr (parseJsonNumber s.toList)}"
  IO.println s!"parseJsonText result: {repr (parseJsonText s)}"
