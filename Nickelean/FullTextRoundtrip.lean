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

/-! ## Smoke tests: Decimal format parsing -/

-- Verify parseJsonNumber handles Decimal.format output
#eval do
  let d : Decimal := ⟨false, 15, -1⟩  -- 1.5
  let s := Decimal.format d
  IO.println s!"Decimal.format: {s}"
  IO.println s!"parseJsonNumber result: {repr (parseJsonNumber s.toList)}"
  IO.println s!"parseJsonText result: {repr (parseJsonText s)}"
