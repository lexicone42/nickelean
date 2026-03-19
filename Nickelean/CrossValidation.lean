/-
  NickelJson/CrossValidation.lean

  Cross-validation between the Lean model and serde_json.
  For each test case, the expected JSON string was produced by
  serde_json::to_string in Rust. We verify the Lean model's
  printJsonValue ∘ toJson produces identical output.

  This bridges the model-reality gap for specific test vectors,
  providing evidence (not proof) that the Lean model matches
  the actual Nickel serialization behavior.
-/
import Nickelean.ToJson
import Nickelean.PrintJson

/-! ## String escaping cross-validation

These expected values were produced by:
  serde_json::to_string(&serde_json::Value::String(input))

The Lean model should produce the same escaped JSON strings. -/

/-- Verify the Lean model produces the same JSON as serde_json for a value. -/
private def crossCheck (label : String) (v : NickelValue) (expectedJson : String) : IO Unit := do
  let leanJson := printJsonValue (toJson v)
  if leanJson == expectedJson then
    IO.println s!"  MATCH {label}"
  else
    IO.eprintln s!"  MISMATCH {label}"
    IO.eprintln s!"    lean:     {leanJson}"
    IO.eprintln s!"    expected: {expectedJson}"
    throw (IO.Error.userError s!"cross-validation failed: {label}")

/-- Helper: JsonNumber from integer. -/
private def jn (n : Int) : JsonNumber := ⟨n, 1, by omega⟩

#eval do
  IO.println "Cross-validation: Lean model vs serde_json"

  -- Primitives (serde_json output verified in Rust)
  crossCheck "null" .null "null"
  crossCheck "true" (.bool true) "true"
  crossCheck "false" (.bool false) "false"
  crossCheck "zero" (.num (jn 0)) "0"
  crossCheck "pos_int" (.num (jn 42)) "42"
  crossCheck "neg_int" (.num (jn (-7))) "-7"

  -- Strings: serde_json escaping matches RFC 8259
  crossCheck "empty_string" (.str "") "\"\""
  crossCheck "simple_string" (.str "hello") "\"hello\""
  crossCheck "string_quotes" (.str "say \"hi\"") "\"say \\\"hi\\\"\""
  crossCheck "string_backslash" (.str "a\\b") "\"a\\\\b\""
  crossCheck "string_newline" (.str "a\nb") "\"a\\nb\""
  crossCheck "string_tab" (.str "a\tb") "\"a\\tb\""
  crossCheck "string_cr" (.str "a\rb") "\"a\\rb\""
  -- Control characters: serde_json uses \uXXXX for 0x00-0x1F except \b\t\n\f\r
  crossCheck "string_null" (.str (String.ofList [Char.ofNat 0])) "\"\\u0000\""
  crossCheck "string_bell" (.str (String.ofList [Char.ofNat 7])) "\"\\u0007\""
  crossCheck "string_bs" (.str (String.ofList [Char.ofNat 8])) "\"\\b\""
  crossCheck "string_ff" (.str (String.ofList [Char.ofNat 12])) "\"\\f\""

  -- Arrays
  crossCheck "empty_array" (.array []) "[]"
  crossCheck "int_array" (.array [.num (jn 1), .num (jn 2), .num (jn 3)]) "[1,2,3]"
  crossCheck "mixed_array" (.array [.num (jn 1), .str "two", .bool true, .null]) "[1,\"two\",true,null]"

  -- Objects (serde_json with preserve_order matches insertion order)
  crossCheck "empty_object" (.record []) "{}"
  crossCheck "simple_object" (.record [("name", .str "alice"), ("age", .num (jn 30))]) "{\"name\":\"alice\",\"age\":30}"

  -- Nested
  crossCheck "nested" (.record [("a", .array [.num (jn 1)]), ("b", .record [("c", .null)])]) "{\"a\":[1],\"b\":{\"c\":null}}"

  -- Additional edge cases
  crossCheck "string_slash" (.str "a/b") "\"a/b\""   -- forward slash NOT escaped (serde_json behavior)
  crossCheck "deeply_nested" (.array [.array [.array [.num (jn 1)]]]) "[[[1]]]"
  crossCheck "empty_nested" (.record [("a", .array []), ("b", .record [])]) "{\"a\":[],\"b\":{}}"
  crossCheck "large_int" (.num (jn 999999999)) "999999999"
  crossCheck "neg_large" (.num (jn (-123456789))) "-123456789"
  crossCheck "single_elem_arr" (.array [.null]) "[null]"
  crossCheck "bool_array" (.array [.bool true, .bool false, .bool true]) "[true,false,true]"
  crossCheck "string_with_escapes" (.str "line1\nline2\ttab") "\"line1\\nline2\\ttab\""
  crossCheck "unicode_passthrough" (.str "café") "\"café\""
  crossCheck "empty_key" (.record [("", .num (jn 0))]) "{\"\":0}"

  IO.println s!"Cross-validation: all {22 + 11} tests matched!"
