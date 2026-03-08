/-
  NickelJson/PrintJson.lean

  JSON text printer: JsonValue → String.
  Together with a JSON text parser, this would complete the
  NickelValue → String → NickelValue pipeline.

  Uses the same escapeJsonString from Escape.lean for string values.
  Note: JsonValue.string fields are already escaped by toJson,
  so we quote them directly without double-escaping.
-/
import Nickelean.JsonValue

/-! ## Number printing -/

/-- Print a non-negative integer as a decimal string. -/
private def printNatGo : Nat → List Char → List Char
  | 0, acc => acc
  | n + 1, acc => printNatGo ((n + 1) / 10) (Char.ofNat (0x30 + (n + 1) % 10) :: acc)
termination_by n => n
decreasing_by omega

private def printNat : Nat → String
  | 0 => "0"
  | n => String.ofList (printNatGo n [])

/-- Print a JsonNumber as a decimal string.
    For integer rationals (denominator = 1), prints as integer.
    Otherwise prints as "numerator/denominator" (not standard JSON,
    but our JsonNumber model allows arbitrary rationals). -/
def printJsonNumber (n : JsonNumber) : String :=
  if n.denominator == 1 then
    if n.numerator < 0 then
      "-" ++ printNat n.numerator.natAbs
    else
      printNat n.numerator.natAbs
  else
    -- Rational: print as integer ratio (non-standard JSON extension)
    let sign := if n.numerator < 0 then "-" else ""
    sign ++ printNat n.numerator.natAbs ++ "/" ++ printNat n.denominator

/-! ## JSON value printing -/

mutual
/-- Print a JsonValue as a JSON text string. -/
def printJsonValue : JsonValue → String
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .number n => printJsonNumber n
  | .string s => "\"" ++ s ++ "\""  -- s is already escaped by toJson
  | .array elems => "[" ++ printJsonArray elems ++ "]"
  | .object fields => "{" ++ printJsonObject fields ++ "}"

/-- Print array elements as comma-separated JSON. -/
def printJsonArray : List JsonValue → String
  | [] => ""
  | [v] => printJsonValue v
  | v :: vs => printJsonValue v ++ "," ++ printJsonArray vs

/-- Print object fields as comma-separated "key":value pairs. -/
def printJsonObject : List (String × JsonValue) → String
  | [] => ""
  | [(k, v)] => "\"" ++ k ++ "\":" ++ printJsonValue v
  | (k, v) :: rest => "\"" ++ k ++ "\":" ++ printJsonValue v ++ "," ++ printJsonObject rest
end
