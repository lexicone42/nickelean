/-
  NickelJson/Escape.lean

  JSON string escaping and unescaping.

  Phase 1: ASCII-only implementation. We escape the characters that JSON
  requires to be escaped (RFC 8259 §7):
    - quotation mark (")
    - reverse solidus (\)
    - control characters U+0000 through U+001F

  Phase 2 (future): full Unicode with \uXXXX and surrogate pair handling.
-/

/-- Characters that must be escaped in JSON strings. -/
def needsEscape (c : Char) : Bool :=
  c == '"' || c == '\\' || c.val < 0x20

/-- Hex digit character from a nibble (0-15). -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n)
  else Char.ofNat (0x61 + n - 10)

/-- Encode a character as a \uXXXX escape sequence. -/
def escapeCharHex (c : Char) : List Char :=
  let n := c.val.toNat
  ['\\', 'u',
   hexDigit (n / 4096 % 16),
   hexDigit (n / 256 % 16),
   hexDigit (n / 16 % 16),
   hexDigit (n % 16)]

/-- Escape a single character for JSON. -/
def escapeChar (c : Char) : List Char :=
  if c == '"' then ['\\', '"']
  else if c == '\\' then ['\\', '\\']
  else if c == '\n' then ['\\', 'n']
  else if c == '\r' then ['\\', 'r']
  else if c == '\t' then ['\\', 't']
  else if c.val < 0x20 then escapeCharHex c
  else [c]

/-- Escape a string for JSON serialization. -/
def escapeJsonString (s : String) : String :=
  String.ofList (s.toList.flatMap escapeChar)

/-- Parse a hex digit character to its numeric value. -/
def parseHexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.val.toNat - 0x30)
  else if 'a' ≤ c && c ≤ 'f' then some (c.val.toNat - 0x61 + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.val.toNat - 0x41 + 10)
  else none

/-- Parse a \uXXXX escape to a character. -/
def parseHex4 (a b c d : Char) : Option Char := do
  let va ← parseHexDigit a
  let vb ← parseHexDigit b
  let vc ← parseHexDigit c
  let vd ← parseHexDigit d
  let n := va * 4096 + vb * 256 + vc * 16 + vd
  if h : Nat.isValidChar n then
    some ⟨⟨n, by omega⟩, h⟩
  else
    none

/-- Unescape a JSON string (process escape sequences). Returns the remaining
    characters and the accumulated result. -/
def unescapeLoop : List Char → List Char → Option (List Char)
  | [], acc => some acc.reverse
  | '\\' :: '"' :: rest, acc => unescapeLoop rest ('"' :: acc)
  | '\\' :: '\\' :: rest, acc => unescapeLoop rest ('\\' :: acc)
  | '\\' :: '/' :: rest, acc => unescapeLoop rest ('/' :: acc)
  | '\\' :: 'n' :: rest, acc => unescapeLoop rest ('\n' :: acc)
  | '\\' :: 'r' :: rest, acc => unescapeLoop rest ('\r' :: acc)
  | '\\' :: 't' :: rest, acc => unescapeLoop rest ('\t' :: acc)
  | '\\' :: 'b' :: rest, acc => unescapeLoop rest (Char.ofNat 8 :: acc)
  | '\\' :: 'f' :: rest, acc => unescapeLoop rest (Char.ofNat 12 :: acc)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest, acc => do
    let ch ← parseHex4 a b c d
    unescapeLoop rest (ch :: acc)
  | '\\' :: _, _ => none  -- invalid escape
  | c :: rest, acc => unescapeLoop rest (c :: acc)

/-- Unescape a JSON string. -/
def unescapeJsonString (s : String) : Option String :=
  (unescapeLoop s.toList []).map String.ofList
