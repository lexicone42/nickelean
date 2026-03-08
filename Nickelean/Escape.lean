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

/-- Parse four hex digits to a 16-bit value. -/
def parseHex4Nat (a b c d : Char) : Option Nat := do
  let va ← parseHexDigit a
  let vb ← parseHexDigit b
  let vc ← parseHexDigit c
  let vd ← parseHexDigit d
  return va * 4096 + vb * 256 + vc * 16 + vd

/-- Check if a 16-bit value is a high surrogate (U+D800–U+DBFF). -/
def isHighSurrogate (n : Nat) : Bool := 0xD800 ≤ n && n ≤ 0xDBFF

/-- Check if a 16-bit value is a low surrogate (U+DC00–U+DFFF). -/
def isLowSurrogate (n : Nat) : Bool := 0xDC00 ≤ n && n ≤ 0xDFFF

/-- Decode a surrogate pair to a Unicode code point. -/
def decodeSurrogatePair (hi lo : Nat) : Nat :=
  0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)

/-- Parse a \uXXXX escape to a character. -/
def parseHex4 (a b c d : Char) : Option Char := do
  let n ← parseHex4Nat a b c d
  if h : Nat.isValidChar n then
    some ⟨⟨n, by omega⟩, h⟩
  else
    none

/-- Unescape a JSON string (process escape sequences). Returns the remaining
    characters and the accumulated result.
    Handles surrogate pairs: \uD800-\uDBFF followed by \uDC00-\uDFFF. -/
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
    let n ← parseHex4Nat a b c d
    if isHighSurrogate n then
      -- Expect \uXXXX low surrogate
      match rest with
      | '\\' :: 'u' :: a2 :: b2 :: c2 :: d2 :: rest2 => do
        let n2 ← parseHex4Nat a2 b2 c2 d2
        if isLowSurrogate n2 then
          let cp := decodeSurrogatePair n n2
          if h : Nat.isValidChar cp then
            unescapeLoop rest2 (⟨⟨cp, by omega⟩, h⟩ :: acc)
          else
            none
        else
          none  -- high surrogate not followed by low surrogate
      | _ => none  -- high surrogate at end of string or not followed by \u
    else if isLowSurrogate n then
      none  -- lone low surrogate is invalid
    else if h : Nat.isValidChar n then
      unescapeLoop rest (⟨⟨n, by omega⟩, h⟩ :: acc)
    else
      none
  | '\\' :: _, _ => none  -- invalid escape
  | c :: rest, acc => unescapeLoop rest (c :: acc)

/-- Unescape a JSON string. -/
def unescapeJsonString (s : String) : Option String :=
  (unescapeLoop s.toList []).map String.ofList
