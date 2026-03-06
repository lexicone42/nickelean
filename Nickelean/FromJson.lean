/-
  NickelJson/FromJson.lean

  Deserialize a JsonValue back to a NickelValue.
  Mirrors Nickel's `serde::Deserialize` implementation.

  Uses mutual recursion with explicit list helpers for termination.
-/
import Nickelean.Value
import Nickelean.Escape

mutual
/-- Deserialize a JSON AST back to a Nickel value. -/
def fromJson : JsonValue → Option NickelValue
  | .null => some .null
  | .bool b => some (.bool b)
  | .number n => some (.num n)
  | .string s => do
    let s' ← unescapeJsonString s
    return .str s'
  | .array elems => do
    let parsed ← fromJsonList elems
    return .array parsed
  | .object fields => do
    let parsed ← fromJsonFields fields
    return .record parsed

/-- Deserialize a list of JSON values. -/
def fromJsonList : List JsonValue → Option (List NickelValue)
  | [] => some []
  | v :: vs => do
    let v' ← fromJson v
    let vs' ← fromJsonList vs
    return v' :: vs'

/-- Deserialize a list of JSON object fields. -/
def fromJsonFields : List (String × JsonValue) → Option (List (String × NickelValue))
  | [] => some []
  | (k, v) :: rest => do
    let k' ← unescapeJsonString k
    let v' ← fromJson v
    let rest' ← fromJsonFields rest
    return (k', v') :: rest'
end
