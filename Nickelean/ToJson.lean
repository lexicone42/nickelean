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
