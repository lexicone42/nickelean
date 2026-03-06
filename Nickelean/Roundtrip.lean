/-
  NickelJson/Roundtrip.lean

  The main roundtrip theorem:
    ∀ v : NickelValue, fromJson (toJson v) = some v

  NickelValue is a nested inductive (contains List NickelValue), so
  standard `induction` doesn't work. We prove mutually recursive
  lemmas that parallel the mutual toJson/fromJson definitions.
-/
import Nickelean.ToJson
import Nickelean.FromJson
import Nickelean.Roundtrip.EscapeRoundtrip

/-! ### Mutual roundtrip proofs -/

mutual
/-- The fundamental roundtrip property for NickelValue. -/
theorem json_roundtrip (v : NickelValue) : fromJson (toJson v) = some v := by
  cases v with
  | null => rfl
  | bool b => rfl
  | num n => rfl
  | str s =>
    unfold toJson fromJson
    rw [unescape_escape_roundtrip s]
    simp [bind, Option.bind]
  | array elems =>
    unfold toJson fromJson
    rw [json_roundtrip_list elems]
    simp [bind, Option.bind]
  | record fields =>
    unfold toJson fromJson
    rw [json_roundtrip_fields fields]
    simp [bind, Option.bind]

/-- Roundtrip for lists of values. -/
theorem json_roundtrip_list (vs : List NickelValue)
    : fromJsonList (toJsonList vs) = some vs := by
  cases vs with
  | nil =>
    unfold toJsonList fromJsonList
    rfl
  | cons v rest =>
    unfold toJsonList fromJsonList
    rw [json_roundtrip v]
    simp [bind, Option.bind]
    rw [json_roundtrip_list rest]

/-- Roundtrip for lists of key-value fields. -/
theorem json_roundtrip_fields (fs : List (String × NickelValue))
    : fromJsonFields (toJsonFields fs) = some fs := by
  cases fs with
  | nil =>
    unfold toJsonFields fromJsonFields
    rfl
  | cons f rest =>
    obtain ⟨k, v⟩ := f
    unfold toJsonFields fromJsonFields
    rw [unescape_escape_roundtrip k]
    simp [bind, Option.bind]
    rw [json_roundtrip v]
    simp
    rw [json_roundtrip_fields rest]
end
