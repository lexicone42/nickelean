/-
  NickelJson/ToJson.lean

  Serialize a NickelValue to a JsonValue.
  Mirrors Nickel's `serde::Serialize` implementation.

  Uses mutual recursion with explicit list helpers so Lean can infer
  structural termination (List.map with a lambda hides the decrease).
-/
import Nickelean.Value
import Nickelean.Escape

mutual
/-- Serialize a Nickel value to its JSON AST representation. -/
def toJson : NickelValue → JsonValue
  | .null => .null
  | .bool b => .bool b
  | .num n => .number n
  | .str s => .string (escapeJsonString s)
  | .array elems => .array (toJsonList elems)
  | .record fields => .object (toJsonFields fields)

/-- Serialize a list of Nickel values. -/
def toJsonList : List NickelValue → List JsonValue
  | [] => []
  | v :: vs => toJson v :: toJsonList vs

/-- Serialize a list of key-value fields. -/
def toJsonFields : List (String × NickelValue) → List (String × JsonValue)
  | [] => []
  | (k, v) :: rest => (escapeJsonString k, toJson v) :: toJsonFields rest
end

/-! ## Nickel-compatible serialization with sorted fields

  Nickel sorts record fields alphabetically before JSON export
  (see core/src/serialize/mod.rs: `entries.sort_by_key`).
  `toJsonSorted` composes field sorting with `toJson` to match. -/

/-- Sort fields by key (alphabetical). -/
def sortJsonFields : List (String × JsonValue) → List (String × JsonValue) :=
  List.mergeSort (le := fun a b => decide (a.1 ≤ b.1))

mutual
/-- Serialize with sorted record fields, matching Nickel's serialization order. -/
def toJsonSorted : NickelValue → JsonValue
  | .null => .null
  | .bool b => .bool b
  | .num n => .number n
  | .str s => .string (escapeJsonString s)
  | .array elems => .array (toJsonSortedList elems)
  | .record fields => .object (sortJsonFields (toJsonSortedFields fields))

def toJsonSortedList : List NickelValue → List JsonValue
  | [] => []
  | v :: vs => toJsonSorted v :: toJsonSortedList vs

def toJsonSortedFields : List (String × NickelValue) → List (String × JsonValue)
  | [] => []
  | (k, v) :: rest => (escapeJsonString k, toJsonSorted v) :: toJsonSortedFields rest
end
