/-
  NickelJson/FullTextRoundtrip.lean

  The complete text-level roundtrip theorem:
    For all NickelValues v (with integer numbers),
      fromJson(parseJV(printJsonValue(toJson(v)))) = some v

  Composes four independently verified stages:
  1. toJson: NickelValue → JsonValue  (escapes strings)
  2. printJsonValue: JsonValue → String  (formats as compact JSON)
  3. parseJV: String → JsonValue  (parses JSON text)
  4. fromJson: JsonValue → NickelValue  (unescapes, recovers values)
-/
import Nickelean.ParseJsonText
import Nickelean.Roundtrip

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

/-! ## The complete text-level roundtrip -/

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

/-- THE CAPSTONE: NickelValue → String → NickelValue roundtrip.

    For any NickelValue v with integer-valued numbers:
      fromJson(parseJV(printJsonValue(toJson(v)))) = some v

    Composes json_roundtrip and text_roundtrip_json. -/
theorem full_text_roundtrip (v : NickelValue) (hdo : NickelAllDenOne v) :
    (parseJV ((printJsonValue (toJson v)).toList) (jsonSize (toJson v))).bind
      (fun ⟨jv, _⟩ => fromJson jv) = some v := by
  rw [text_roundtrip_json v hdo]
  simp [Option.bind]
  exact json_roundtrip v
