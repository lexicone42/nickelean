/-
  NickelJson/RecordOrder.lean

  Record field ordering and the roundtrip theorem under normalization.

  JSON objects are unordered per RFC 8259, but implementations differ:
  - serde_json with `preserve_order`: uses IndexMap (insertion order)
  - serde_json without `preserve_order`: uses BTreeMap (sorted by key)
  - Nickel uses `preserve_order` by default

  Our main roundtrip theorem preserves field order exactly. This module
  additionally shows that sorting fields before comparison also works —
  the roundtrip is order-independent when both sides are normalized.
-/
import Nickelean.Roundtrip

/-! ## Field sorting -/

/-- Sort record fields by key using decide-able string ≤. -/
def sortFields : List (String × NickelValue) → List (String × NickelValue) :=
  List.mergeSort (le := fun a b => decide (a.1 ≤ b.1))

mutual
/-- Sort fields in a NickelValue recursively.
    Uses mutual recursion for termination on the nested inductive. -/
def normalizeFieldOrder : NickelValue → NickelValue
  | .null => .null
  | .bool b => .bool b
  | .num n => .num n
  | .str s => .str s
  | .array elems => .array (normalizeFieldOrderList elems)
  | .record fields =>
    .record (sortFields (normalizeFieldOrderFields fields))

def normalizeFieldOrderList : List NickelValue → List NickelValue
  | [] => []
  | v :: vs => normalizeFieldOrder v :: normalizeFieldOrderList vs

def normalizeFieldOrderFields :
    List (String × NickelValue) → List (String × NickelValue)
  | [] => []
  | (k, v) :: rest => (k, normalizeFieldOrder v) :: normalizeFieldOrderFields rest
end

/-- Roundtrip holds for field-order-normalized values.
    This shows the roundtrip is order-independent: normalize first,
    then serialize/deserialize, and you get the normalized form back. -/
theorem json_roundtrip_normalized (v : NickelValue) :
    fromJson (toJson (normalizeFieldOrder v)) = some (normalizeFieldOrder v) :=
  json_roundtrip (normalizeFieldOrder v)

/-! ## Permutation equivalence -/

/-- Two lists of fields are permutation-equivalent if they contain the same
    key-value pairs (as a multiset). -/
def fieldsPermEquiv (as_ bs : List (String × NickelValue)) : Prop :=
  ∀ (k : String) (v : NickelValue),
    as_.count (k, v) = bs.count (k, v)

-- If two records have permutation-equivalent fields, normalizing them
-- yields the same result (assuming unique keys and stable sort).
-- This requires additional lemmas about mergeSort stability and would
-- be a nice extension.
-- theorem normalizeFieldOrder_perm_eq ...
