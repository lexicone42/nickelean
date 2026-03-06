/-
  NickelJson/Tests.lean

  Conformance test suite — exercises toJson/fromJson on concrete values
  to catch spec bugs. Uses #eval for runtime checking and example theorems
  for compile-time verification.
-/
import Nickelean.Roundtrip

/-! ## Test helpers -/

/-- Convenience constructor for JsonNumber. -/
def mkNum (n : Int) (d : Nat) (h : d > 0 := by omega) : JsonNumber :=
  ⟨n, d, h⟩

/-! ## Null / Bool -/

#eval do
  let v := NickelValue.null
  assert! fromJson (toJson v) == some v
  IO.println "null: OK"

#eval do
  let v := NickelValue.bool true
  assert! fromJson (toJson v) == some v
  let v := NickelValue.bool false
  assert! fromJson (toJson v) == some v
  IO.println "bool: OK"

/-! ## Numbers -/

#eval do
  -- Zero
  let v := NickelValue.num (mkNum 0 1)
  assert! fromJson (toJson v) == some v
  -- Positive integer
  let v := NickelValue.num (mkNum 42 1)
  assert! fromJson (toJson v) == some v
  -- Negative integer
  let v := NickelValue.num (mkNum (-7) 1)
  assert! fromJson (toJson v) == some v
  -- Rational
  let v := NickelValue.num (mkNum 1 3)
  assert! fromJson (toJson v) == some v
  IO.println "num: OK"

/-! ## Strings -/

#eval do
  -- Empty string
  let v := NickelValue.str ""
  assert! fromJson (toJson v) == some v
  -- Simple ASCII
  let v := NickelValue.str "hello world"
  assert! fromJson (toJson v) == some v
  -- String with quotes
  let v := NickelValue.str "say \"hi\""
  assert! fromJson (toJson v) == some v
  -- String with backslashes
  let v := NickelValue.str "path\\to\\file"
  assert! fromJson (toJson v) == some v
  -- String with newlines
  let v := NickelValue.str "line1\nline2\rline3\ttab"
  assert! fromJson (toJson v) == some v
  -- String with control characters (NUL, BEL, BS)
  let v := NickelValue.str (String.ofList [Char.ofNat 0, Char.ofNat 7, Char.ofNat 8])
  assert! fromJson (toJson v) == some v
  IO.println "str: OK"

/-! ## Arrays -/

#eval do
  -- Empty array
  let v := NickelValue.array []
  assert! fromJson (toJson v) == some v
  -- Simple array
  let v := NickelValue.array [.null, .bool true, .str "x"]
  assert! fromJson (toJson v) == some v
  -- Nested array
  let v := NickelValue.array [.array [.null], .array [.bool false]]
  assert! fromJson (toJson v) == some v
  IO.println "array: OK"

/-! ## Records -/

#eval do
  -- Empty record
  let v := NickelValue.record []
  assert! fromJson (toJson v) == some v
  -- Simple record
  let v := NickelValue.record [("name", .str "test"), ("value", .num (mkNum 42 1))]
  assert! fromJson (toJson v) == some v
  -- Record with special chars in keys
  let v := NickelValue.record [("key with \"quotes\"", .null), ("key\\backslash", .bool true)]
  assert! fromJson (toJson v) == some v
  -- Nested record
  let v := NickelValue.record [
    ("outer", .record [("inner", .str "deep")]),
    ("list", .array [.num (mkNum 1 1), .num (mkNum 2 1)])
  ]
  assert! fromJson (toJson v) == some v
  IO.println "record: OK"

/-! ## Complex nested value (mimics a realistic Nickel build.ncl output) -/

#eval do
  let buildConfig := NickelValue.record [
    ("name", .str "my-package"),
    ("version", .str "1.0.0"),
    ("sandbox", .record [
      ("network", .bool false),
      ("filesystem", .array [.str "/tmp", .str "/home"])
    ]),
    ("dependencies", .array [
      .record [("name", .str "dep-a"), ("version", .str "2.1.0")],
      .record [("name", .str "dep-b"), ("version", .str "0.3.0")]
    ]),
    ("metadata", .record [
      ("description", .str "A test package with \"special\" chars\nand newlines"),
      ("license", .str "MIT"),
      ("authors", .array [.str "Alice", .str "Bob"])
    ])
  ]
  assert! fromJson (toJson buildConfig) == some buildConfig
  IO.println "complex nested: OK"

/-! ## All tests summary -/

#eval IO.println "All conformance tests passed."
