/-
  NickelJson/ParseJsonText.lean

  JSON text parser: String → Option JsonValue.
  Inverts printJsonValue to complete the string-level roundtrip.

  The parser operates on List Char and uses fuel for termination.
  All recursive calls decrease fuel by at least 1.

  The number parser handles two formats:
  1. Plain integers: [-]<digits>  (from printJsonNumber with den=1)
  2. Decimal/scientific: [-]<digit>[.<digits>]e<int>  (from Decimal.format)

  These are distinguished by the presence of 'e' after initial digits.
-/
import Nickelean.PrintJson
import Nickelean.Escape
import Nickelean.Roundtrip.EscapeRoundtrip
import RyuLean4.Decimal.Decimal
import RyuLean4.Decimal.Format
import RyuLean4.Decimal.Parse
import RyuLean4.Roundtrip.FormatParse

/-! ## Number parsing -/

/-- Parse one or more decimal digits, accumulating the value. -/
def parseJsonNatAux : List Char → Nat → Bool → Option (Nat × List Char)
  | [], acc, true => some (acc, [])
  | [], _, false => none
  | c :: rest, acc, consumed =>
    if '0' ≤ c ∧ c ≤ '9' then
      parseJsonNatAux rest (acc * 10 + (c.toNat - '0'.toNat)) true
    else if consumed then
      some (acc, c :: rest)
    else
      none

/-- Parse a natural number (one or more digits). -/
def parseJsonNat (chars : List Char) : Option (Nat × List Char) :=
  parseJsonNatAux chars 0 false

/-- Parse an integer (possibly with leading minus sign).
    Delegates to Decimal.parseInt for reuse of existing roundtrip proofs. -/
def parseJsonInt (chars : List Char) : Option (Int × List Char) :=
  Decimal.parseInt chars

/-- Convert a Decimal (sign, digits, exponent) to a JsonNumber.
    The Decimal represents (-1)^sign × digits × 10^exponent.
    - If exponent ≥ 0: JsonNumber(±(digits × 10^exp), 1)
    - If exponent < 0: JsonNumber(±digits, 10^(-exp)) -/
def decimalToJsonNumber (sign : Bool) (digits : Nat) (exponent : Int) : JsonNumber :=
  let signedDigits : Int := if sign then -(digits : Int) else (digits : Int)
  if h : exponent ≥ 0 then
    ⟨signedDigits * (10 ^ exponent.toNat : Nat), 1, by omega⟩
  else
    ⟨signedDigits, 10 ^ (-exponent).toNat, by positivity⟩

/-- Skip an optional '+' after 'e' in scientific notation.
    zmij (serde_json ≥ 1.0.147) uses 'e+' for positive exponents;
    ryu (serde_json < 1.0.147) uses 'e'. Both are valid JSON. -/
def skipOptionalPlus : List Char → List Char
  | '+' :: rest => rest
  | rest => rest

def parseJsonNumberTail (sign : Bool) (n : Nat) (rest : List Char) : Option (JsonNumber × List Char) :=
  match rest with
  | 'e' :: expRest =>
    match Decimal.parseInt (skipOptionalPlus expRest) with
    | some (exp, rest') => some (decimalToJsonNumber sign n exp, rest')
    | none => none
  | '.' :: fracRest =>
    match Decimal.parseNat fracRest with
    | some (frac, 'e' :: expRest) =>
      let numFrac := fracRest.length - expRest.length - 1  -- chars between '.' and 'e'
      match Decimal.parseInt (skipOptionalPlus expRest) with
      | some (exp, rest') =>
        let fullDigits := n * 10 ^ numFrac + frac
        let fullExp := exp - (numFrac : Int)
        some (decimalToJsonNumber sign fullDigits fullExp, rest')
      | none => none
    | some (frac, rest') =>
      -- No exponent: e.g., "3.14" or "0.1" (serde_json format)
      let numFrac := fracRest.length - rest'.length
      let fullDigits := n * 10 ^ numFrac + frac
      some (decimalToJsonNumber sign fullDigits (-(numFrac : Int)), rest')
    | none => none
  | _ =>
    let signedN : Int := if sign then -(n : Int) else (n : Int)
    some (⟨signedN, 1, by omega⟩, rest)

/-- Parse a JSON number, handling both integer and scientific notation formats.
    - Plain integers: [-]<digits>
    - Scientific: [-]<digit>[.<digits>]e<int>
    Uses Decimal.parseNat (equivalent to parseJsonNat) for digit parsing. -/
def parseJsonNumber : List Char → Option (JsonNumber × List Char)
  | '-' :: rest =>
    match Decimal.parseNat rest with
    | some (n, rest') => parseJsonNumberTail true n rest'
    | none => none
  | chars =>
    match Decimal.parseNat chars with
    | some (n, rest) => parseJsonNumberTail false n rest
    | none => none

/-! ## String parsing -/

/-- Scan string content between quotes, handling escape sequences. -/
def scanStringContent : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | '"' :: rest, acc => some (acc.reverse, rest)
  | '\\' :: c :: rest, acc => scanStringContent rest (c :: '\\' :: acc)
  | c :: rest, acc => scanStringContent rest (c :: acc)

/-! ## JSON value parser (mutual recursion, fuel-based) -/

mutual
/-- Parse a JSON value. All recursive calls decrease fuel. -/
def parseJV : List Char → Nat → Option (JsonValue × List Char)
  | _, 0 => none
  | 'n' :: 'u' :: 'l' :: 'l' :: rest, _ => some (.null, rest)
  | 't' :: 'r' :: 'u' :: 'e' :: rest, _ => some (.bool true, rest)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest, _ => some (.bool false, rest)
  | '"' :: rest, _ =>
    match scanStringContent rest [] with
    | some (content, rest') => some (.string (String.ofList content), rest')
    | none => none
  | '[' :: ']' :: rest, _ => some (.array [], rest)
  | '[' :: rest, _ + 1 =>
    match parseJArr rest ‹_› with
    | some (elems, rest') => some (.array elems, rest')
    | none => none
  | '{' :: '}' :: rest, _ => some (.object [], rest)
  | '{' :: rest, _ + 1 =>
    match parseJObj rest ‹_› with
    | some (fields, rest') => some (.object fields, rest')
    | none => none
  | chars, _ =>
    match parseJsonNumber chars with
    | some (n, rest) => some (.number n, rest)
    | none => none

/-- Parse non-empty array elements. -/
def parseJArr : List Char → Nat → Option (List JsonValue × List Char)
  | _, 0 => none
  | chars, fuel + 1 =>
    match parseJV chars fuel with
    | some (v, ',' :: rest) =>
      match parseJArr rest fuel with
      | some (vs, rest') => some (v :: vs, rest')
      | none => none
    | some (v, ']' :: rest) => some ([v], rest)
    | _ => none

/-- Parse non-empty object fields. -/
def parseJObj : List Char → Nat → Option (List (String × JsonValue) × List Char)
  | _, 0 => none
  | '"' :: rest, fuel + 1 =>
    match scanStringContent rest [] with
    | some (key, ':' :: rest') =>
      match parseJV rest' fuel with
      | some (val, ',' :: rest'') =>
        match parseJObj rest'' fuel with
        | some (fields, rest''') => some ((String.ofList key, val) :: fields, rest''')
        | none => none
      | some (val, '}' :: rest'') => some ([(String.ofList key, val)], rest'')
      | _ => none
    | _ => none
  | _, _ => none
end

/-- Parse a complete JSON text string. -/
def parseJsonText (s : String) (fuel : Nat := s.length + 1) : Option JsonValue :=
  match parseJV s.toList fuel with
  | some (v, []) => some v
  | _ => none

/-! ## Smoke tests -/

#eval parseJsonText "null"
#eval parseJsonText "true"
#eval parseJsonText "false"
#eval parseJsonText "42"
#eval parseJsonText "-7"
#eval parseJsonText "\"hello\""
#eval parseJsonText "[1,2,3]"
#eval parseJsonText "{\"a\":1}"
#eval parseJsonText "[]"
#eval parseJsonText "{}"
#eval parseJsonText "[1,\"two\",true,null]"
#eval parseJsonText "{\"a\":[1],\"b\":{\"c\":null}}"

-- Scientific notation smoke tests
#eval parseJsonText "1e0"       -- 1
#eval parseJsonText "1e2"       -- 100
#eval parseJsonText "-5e1"      -- -50
#eval parseJsonText "1.5e1"     -- 15
#eval parseJsonText "1.5e-1"    -- 15/100 = 3/20... but we store as 15/10
#eval parseJsonNumber "1.5e-1".toList  -- should parse

/-! ## Roundtrip: parseJV ∘ printJsonValue = id

  We prove that parsing the printed JSON text recovers the original JsonValue.
  Preconditions:
  - Numbers have denominator = 1 (integer-valued)
  - Strings are well-formed (ScanSafe — no bare quotes/backslashes)
  - Rest doesn't start with a digit (NonDigitHead)
-/

/-! ### ScanSafe predicate -/

/-- A list of chars is "scan-safe": scanStringContent will correctly
    find a closing `"` placed after it. -/
inductive ScanSafe : List Char → Prop where
  | nil : ScanSafe []
  | escape (c : Char) (rest : List Char) : ScanSafe rest → ScanSafe ('\\' :: c :: rest)
  | plain (c : Char) (rest : List Char) :
      c ≠ '"' → c ≠ '\\' → ScanSafe rest → ScanSafe (c :: rest)

theorem ScanSafe.append (l1 l2 : List Char) (h1 : ScanSafe l1) (h2 : ScanSafe l2) :
    ScanSafe (l1 ++ l2) := by
  induction h1 with
  | nil => simpa
  | escape c rest _ ih => exact .escape c (rest ++ l2) ih
  | plain c rest hq hb _ ih => exact .plain c (rest ++ l2) hq hb ih

private theorem hexDigit_ne_dquote (n : Nat) (hn : n < 16) : hexDigit n ≠ '"' := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
         n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> native_decide

private theorem hexDigit_ne_backslash (n : Nat) (hn : n < 16) : hexDigit n ≠ '\\' := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
         n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> native_decide

theorem scanSafe_escapeChar (c : Char) : ScanSafe (escapeChar c) := by
  unfold escapeChar
  split; · exact .escape '"' [] .nil
  split; · exact .escape '\\' [] .nil
  split; · exact .escape 'n' [] .nil
  split; · exact .escape 'r' [] .nil
  split; · exact .escape 't' [] .nil
  split; · exact .escape 'b' [] .nil
  split; · exact .escape 'f' [] .nil
  split
  · unfold escapeCharHex; apply ScanSafe.escape 'u'
    exact .plain _ _ (hexDigit_ne_dquote _ (by omega)) (hexDigit_ne_backslash _ (by omega))
      (.plain _ _ (hexDigit_ne_dquote _ (by omega)) (hexDigit_ne_backslash _ (by omega))
        (.plain _ _ (hexDigit_ne_dquote _ (by omega)) (hexDigit_ne_backslash _ (by omega))
          (.plain _ _ (hexDigit_ne_dquote _ (by omega)) (hexDigit_ne_backslash _ (by omega)) .nil)))
  · rename_i h1 h2 _ _ _ _ _ _
    exact .plain _ _ (by intro heq; subst heq; simp at h1) (by intro heq; subst heq; simp at h2) .nil

theorem scanSafe_flatMap_escapeChar (cs : List Char) : ScanSafe (cs.flatMap escapeChar) := by
  induction cs with
  | nil => exact .nil
  | cons c rest ih => simp [List.flatMap_cons]; exact (scanSafe_escapeChar c).append _ _ ih

theorem scanSafe_escapeJsonString (s : String) : ScanSafe (escapeJsonString s).toList := by
  simp [escapeJsonString, String.toList_ofList]; exact scanSafe_flatMap_escapeChar s.toList

/-! ### scanStringContent roundtrip -/

theorem scanStringContent_scanSafe_acc (chars rest acc : List Char) (h : ScanSafe chars) :
    scanStringContent (chars ++ '"' :: rest) acc = some (acc.reverse ++ chars, rest) := by
  induction h generalizing acc with
  | nil => simp [scanStringContent.eq_2]
  | escape c rest' _ ih =>
    simp only [List.cons_append]
    rw [scanStringContent.eq_3, ih (c :: '\\' :: acc)]
    simp [List.reverse_cons, List.append_assoc]
  | plain c rest' hq hb _ ih =>
    simp only [List.cons_append]
    rw [scanStringContent.eq_4 acc c _ hq (by intro _ _ habs _; exact hb habs), ih (c :: acc)]
    simp [List.reverse_cons, List.append_assoc]

theorem scanStringContent_scanSafe (chars rest : List Char) (h : ScanSafe chars) :
    scanStringContent (chars ++ '"' :: rest) [] = some (chars, rest) := by
  rw [scanStringContent_scanSafe_acc chars rest [] h]; simp

/-! ### Number parsing roundtrip -/

theorem printNatGo_append (n : Nat) (acc : List Char) :
    printNatGo n acc = printNatGo n [] ++ acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    cases n with
    | zero => simp [printNatGo]
    | succ n =>
      rw [printNatGo, printNatGo,
          ih ((n+1)/10) (Nat.div_lt_self (by omega) (by omega))
            (Char.ofNat (0x30 + (n+1) % 10) :: acc),
          ih ((n+1)/10) (Nat.div_lt_self (by omega) (by omega))
            (Char.ofNat (0x30 + (n+1) % 10) :: [])]
      simp [List.append_assoc]

theorem printNatGo_ne_nil (n : Nat) (hn : n > 0) : printNatGo n [] ≠ [] := by
  cases n with
  | zero => omega
  | succ n => rw [printNatGo, printNatGo_append]; simp

private theorem ofNat_isDigit (d : Nat) (hd : d < 10) :
    '0' ≤ Char.ofNat (0x30 + d) ∧ Char.ofNat (0x30 + d) ≤ '9' := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨
         d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    exact ⟨by native_decide, by native_decide⟩

theorem printNatGo_allDigits (n : Nat) :
    ∀ c, c ∈ printNatGo n [] → '0' ≤ c ∧ c ≤ '9' := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => simp [printNatGo]
    | succ n =>
      rw [printNatGo, printNatGo_append]; intro c hc; simp at hc
      rcases hc with hc | rfl
      · exact ih ((n+1)/10) (Nat.div_lt_self (by omega) (by omega)) c hc
      · exact ofNat_isDigit ((n+1) % 10) (by omega)

private theorem ofNat_digit_val (d : Nat) (hd : d < 10) :
    (Char.ofNat (0x30 + d)).toNat - '0'.toNat = d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨
         d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;> native_decide

theorem printNatGo_foldl_zero (n : Nat) :
    (printNatGo n []).foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => simp [printNatGo]
    | succ n =>
      rw [printNatGo, printNatGo_append, List.foldl_append,
          show [Char.ofNat (0x30 + (n+1) % 10)].foldl (fun a c => a * 10 + (c.toNat - '0'.toNat))
            ((printNatGo ((n+1)/10) []).foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0) =
          (printNatGo ((n+1)/10) []).foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0 * 10 +
            ((Char.ofNat (0x30 + (n+1) % 10)).toNat - '0'.toNat)
          from by simp [List.foldl],
          ih ((n+1)/10) (Nat.div_lt_self (by omega) (by omega)),
          ofNat_digit_val ((n+1) % 10) (by omega)]
      omega

theorem parseJsonNatAux_allDigits (ds rest : List Char) (acc : Nat) (consumed : Bool)
    (hds : ∀ c, c ∈ ds → '0' ≤ c ∧ c ≤ '9')
    (hrest : rest = [] ∨ ∃ c t, rest = c :: t ∧ ¬('0' ≤ c ∧ c ≤ '9'))
    (hne : consumed = true ∨ ds ≠ []) :
    parseJsonNatAux (ds ++ rest) acc consumed =
      some (ds.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) acc, rest) := by
  induction ds generalizing acc consumed with
  | nil =>
    rcases hne with rfl | h
    · simp; rcases hrest with rfl | ⟨c, t, rfl, hc⟩
      · rw [parseJsonNatAux.eq_1]
      · rw [parseJsonNatAux.eq_3]; simp [hc]
    · exact absurd rfl h
  | cons d ds ih =>
    simp only [List.cons_append, List.foldl_cons]
    rw [parseJsonNatAux.eq_3]; simp [hds d (by simp)]
    exact ih _ true (fun c hc => hds c (List.mem_cons_of_mem d hc)) (Or.inl rfl)

/-- Rest starts with a non-digit character. -/
abbrev NonDigitHead (rest : List Char) : Prop :=
  rest = [] ∨ ∃ c t, rest = c :: t ∧ ¬('0' ≤ c ∧ c ≤ '9')

/-- Rest starts with a character that cannot continue a number.
    Excludes digits, 'e', 'E', '.', '-', '+'.
    This is needed for the extended parser which handles scientific notation. -/
abbrev NonNumContHead (rest : List Char) : Prop :=
  rest = [] ∨ ∃ c t, rest = c :: t ∧ ¬('0' ≤ c ∧ c ≤ '9') ∧ c ≠ 'e' ∧ c ≠ '.'

theorem NonNumContHead.toNonDigitHead {rest : List Char} (h : NonNumContHead rest) :
    NonDigitHead rest := by
  rcases h with rfl | ⟨c, t, rfl, hnd, _, _⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨c, t, rfl, hnd⟩

theorem parseJsonNat_printNat (n : Nat) (rest : List Char) (hrest : NonDigitHead rest) :
    parseJsonNat ((printNat n).toList ++ rest) = some (n, rest) := by
  simp [parseJsonNat]
  cases n with
  | zero =>
    simp [printNat]; rw [parseJsonNatAux.eq_3]; simp (config := { decide := true })
    rcases hrest with rfl | ⟨c, t, rfl, hc⟩
    · rw [parseJsonNatAux.eq_1]
    · rw [parseJsonNatAux.eq_3]; simp [hc]
  | succ n =>
    simp [printNat, String.toList_ofList]
    rw [parseJsonNatAux_allDigits (printNatGo (n+1) []) rest 0 false
        (printNatGo_allDigits (n+1)) hrest (Or.inr (printNatGo_ne_nil (n+1) (by omega)))]
    exact congrArg (fun x => some (x, rest)) (printNatGo_foldl_zero (n+1))

/-- Decimal.parseNat also roundtrips with printNat.
    Proof: Decimal.parseNatAux and parseJsonNatAux are equivalent (both accumulate
    digit values), so the result follows from parseJsonNat_printNat. -/
theorem decimalParseNat_printNat (n : Nat) (rest : List Char) (hrest : NonDigitHead rest) :
    Decimal.parseNat ((printNat n).toList ++ rest) = some (n, rest) := by
  suffices h : parseJsonNat ((printNat n).toList ++ rest) = Decimal.parseNat ((printNat n).toList ++ rest) by
    rw [← h]; exact parseJsonNat_printNat n rest hrest
  simp only [parseJsonNat, Decimal.parseNat]
  -- Need: parseJsonNatAux = Decimal.parseNatAux
  suffices ∀ (cs : List Char) (a : Nat) (b : Bool),
    parseJsonNatAux cs a b = Decimal.parseNatAux cs a b by
    exact this _ 0 false
  intro cs
  induction cs with
  | nil => intro a b; cases b <;> simp [parseJsonNatAux, Decimal.parseNatAux]
  | cons c rest ih =>
    intro a b
    simp only [parseJsonNatAux, Decimal.parseNatAux, Decimal.parseDigitChar]
    by_cases hd : '0' ≤ c ∧ c ≤ '9'
    · have hb : ('0' ≤ c && c ≤ '9') = true := by simp [hd.1, hd.2]
      simp only [hd]; exact ih _ _
    · have hb : ('0' ≤ c && c ≤ '9') = false := by
        cases h : ('0' ≤ c && c ≤ '9')
        · rfl
        · exfalso; simp [Bool.and_eq_true] at h; exact hd h
      simp only [hd, hb, ↓reduceIte]; cases b <;> rfl

theorem printNat_ne_nil (n : Nat) : (printNat n).toList ≠ [] := by
  cases n with
  | zero => simp [printNat]
  | succ n => simp [printNat, String.toList_ofList, printNatGo_ne_nil (n+1) (by omega)]

theorem printNat_first_digit (n : Nat) (c : Char) (cs : List Char)
    (h : (printNat n).toList = c :: cs) : '0' ≤ c ∧ c ≤ '9' := by
  cases n with
  | zero => simp [printNat] at h; obtain ⟨rfl, _⟩ := h; decide
  | succ n =>
    simp [printNat, String.toList_ofList] at h
    exact printNatGo_allDigits (n+1) c (by rw [h]; exact List.mem_cons_self)

/-- parseJsonNumberTail on a list not headed by 'e' or '.' returns plain integer -/
theorem parseJsonNumberTail_int (sign : Bool) (n : Nat) (rest : List Char)
    (hne : ∀ expRest, rest ≠ 'e' :: expRest) (hndot : ∀ fracRest, rest ≠ '.' :: fracRest) :
    parseJsonNumberTail sign n rest =
      some (⟨if sign then -(n : Int) else (n : Int), 1, by omega⟩, rest) := by
  unfold parseJsonNumberTail
  split
  · -- 'e' :: expRest case: impossible
    exact absurd rfl (hne _)
  · -- '.' :: fracRest case: impossible
    exact absurd rfl (hndot _)
  · -- catch-all: plain integer
    rfl

theorem parseJsonNumber_printJsonNumber (jn : JsonNumber) (rest : List Char)
    (hden : jn.denominator = 1) (hrest : NonNumContHead rest) :
    parseJsonNumber ((printJsonNumber jn).toList ++ rest) = some (jn, rest) := by
  simp only [printJsonNumber, hden, beq_self_eq_true, ↓reduceIte]
  have hrest_nd := hrest.toNonDigitHead
  -- rest doesn't start with 'e' or '.'
  have hne : ∀ expRest, rest ≠ 'e' :: expRest := by
    rcases hrest with rfl | ⟨c, t, rfl, _, hce, _⟩
    · intro _ h; exact List.cons_ne_nil _ _ h.symm
    · intro expRest h; exact hce (List.cons.inj h).1
  have hndot : ∀ fracRest, rest ≠ '.' :: fracRest := by
    rcases hrest with rfl | ⟨c, t, rfl, _, _, hcd⟩
    · intro _ h; exact List.cons_ne_nil _ _ h.symm
    · intro fracRest h; exact hcd (List.cons.inj h).1
  by_cases hneg : jn.numerator < 0
  · -- Negative: "-" ++ printNat |num|
    simp only [hneg, ↓reduceIte, String.toList_append, List.append_assoc]
    show parseJsonNumber ('-' :: ((printNat jn.numerator.natAbs).toList ++ rest)) = some (jn, rest)
    simp only [parseJsonNumber, decimalParseNat_printNat _ _ hrest_nd,
               parseJsonNumberTail_int _ _ _ hne hndot, ↓reduceIte]
    -- Goal: some (⟨-(natAbs .. : Int), 1, _⟩, rest) = some (jn, rest)
    have hna : -(jn.numerator.natAbs : Int) = jn.numerator := by
      rcases Int.natAbs_eq jn.numerator with h | h <;> omega
    cases jn with | mk num den hd =>
      simp at hden; subst hden; simp_all
  · -- Non-negative: printNat num
    simp only [hneg, ↓reduceIte]
    rw [show jn.numerator.natAbs = jn.numerator.toNat from by omega]
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (printNat_ne_nil jn.numerator.toNat)
    have hc_digit := printNat_first_digit jn.numerator.toNat c cs hcs
    rw [hcs, List.cons_append]
    show parseJsonNumber (c :: (cs ++ rest)) = some (jn, rest)
    unfold parseJsonNumber
    split
    · rename_i rest' heq
      exfalso; have := (List.cons.inj heq).1; rw [this] at hc_digit
      exact absurd hc_digit (by decide)
    · have h_eq : c :: (cs ++ rest) = (printNat jn.numerator.toNat).toList ++ rest := by
        rw [hcs, List.cons_append]
      simp only [h_eq, decimalParseNat_printNat _ _ hrest_nd,
          parseJsonNumberTail_int _ _ _ hne hndot]
      -- Goal: some (⟨(toNat .. : Int), 1, _⟩, rest) = some (jn, rest)
      have htn : (jn.numerator.toNat : Int) = jn.numerator := by omega
      cases jn with | mk num den hd =>
        simp only at hden htn; subst hden; simp [htn]

/-! ### Decimal format parsing -/

/-- parseJsonNatAux and Decimal.parseNatAux are equivalent (both accumulate digit values). -/
private theorem parseJsonNatAux_eq_decimal (chars : List Char) (acc : Nat) (consumed : Bool) :
    parseJsonNatAux chars acc consumed = Decimal.parseNatAux chars acc consumed := by
  induction chars generalizing acc consumed with
  | nil => cases consumed <;> simp [parseJsonNatAux, Decimal.parseNatAux]
  | cons c rest ih =>
    simp only [parseJsonNatAux, Decimal.parseNatAux, Decimal.parseDigitChar]
    by_cases hd : '0' ≤ c ∧ c ≤ '9'
    · have hb : ('0' ≤ c && c ≤ '9') = true := by simp [hd.1, hd.2]
      simp only [hd]; exact ih _ _
    · have hb : ('0' ≤ c && c ≤ '9') = false := by
        cases h : ('0' ≤ c && c ≤ '9')
        · rfl
        · exfalso; simp [Bool.and_eq_true] at h; exact hd h
      simp only [hd, hb, ↓reduceIte]; cases consumed <;> rfl

/-- parseJsonNat is equivalent to Decimal.parseNat. -/
theorem parseJsonNat_eq_decimal (chars : List Char) :
    parseJsonNat chars = Decimal.parseNat chars := by
  simp [parseJsonNat, Decimal.parseNat, parseJsonNatAux_eq_decimal]

/-! ### Size function for fuel -/

mutual
def jsonSize : JsonValue → Nat
  | .null => 1
  | .bool _ => 1
  | .number _ => 1
  | .string _ => 1
  | .array elems => 2 + jsonSizeList elems
  | .object fields => 2 + jsonSizeFields fields

def jsonSizeList : List JsonValue → Nat
  | [] => 0
  | v :: vs => jsonSize v + jsonSizeList vs

def jsonSizeFields : List (String × JsonValue) → Nat
  | [] => 0
  | (_, v) :: fs => jsonSize v + jsonSizeFields fs
end

/-! ### WellFormedStrings predicate -/

mutual
def WellFormedStrings : JsonValue → Prop
  | .null => True
  | .bool _ => True
  | .number _ => True
  | .string s => ScanSafe s.toList
  | .array elems => WellFormedStringsList elems
  | .object fields => WellFormedStringsFields fields

def WellFormedStringsList : List JsonValue → Prop
  | [] => True
  | v :: vs => WellFormedStrings v ∧ WellFormedStringsList vs

def WellFormedStringsFields : List (String × JsonValue) → Prop
  | [] => True
  | (k, v) :: fs => ScanSafe k.toList ∧ WellFormedStrings v ∧ WellFormedStringsFields fs
end

/-! ### AllDenOne: all numbers in a value have denominator 1 -/

mutual
def AllDenOne : JsonValue → Prop
  | .null => True
  | .bool _ => True
  | .number n => n.denominator = 1
  | .string _ => True
  | .array elems => AllDenOneList elems
  | .object fields => AllDenOneFields fields

def AllDenOneList : List JsonValue → Prop
  | [] => True
  | v :: vs => AllDenOne v ∧ AllDenOneList vs

def AllDenOneFields : List (String × JsonValue) → Prop
  | [] => True
  | (_, v) :: fs => AllDenOne v ∧ AllDenOneFields fs
end

/-! ### Helpers for the first character of printed output -/

/-- printJsonNumber for den=1 starts with '-' or a digit. -/
theorem printJsonNumber_first_char (n : JsonNumber) (hd : n.denominator = 1)
    (c : Char) (cs : List Char) (hcs : (printJsonNumber n).toList = c :: cs) :
    c = '-' ∨ ('0' ≤ c ∧ c ≤ '9') := by
  simp only [printJsonNumber, hd, beq_self_eq_true, ↓reduceIte] at hcs
  by_cases hneg : n.numerator < 0
  · simp [hneg, String.toList_append] at hcs; left; exact hcs.1.symm
  · simp [hneg] at hcs; right
    exact printNat_first_digit n.numerator.toNat c cs
      (by rwa [show n.numerator.natAbs = n.numerator.toNat from by omega] at hcs)

/-- printJsonNumber for den=1 is nonempty. -/
theorem printJsonNumber_ne_nil (n : JsonNumber) (hd : n.denominator = 1) :
    (printJsonNumber n).toList ≠ [] := by
  simp only [printJsonNumber, hd, beq_self_eq_true, ↓reduceIte]
  by_cases hneg : n.numerator < 0
  · simp [hneg, String.toList_append]
  · simp only [hneg, ↓reduceIte]
    intro h
    have := printNat_ne_nil n.numerator.toNat
    rw [show n.numerator.natAbs = n.numerator.toNat from by omega] at h
    exact this h

/-- printJsonNumber first char is never a JSON keyword/structural char. -/
private theorem printJsonNumber_first_ne (n : JsonNumber) (hd : n.denominator = 1)
    (c : Char) (cs : List Char) (hcs : (printJsonNumber n).toList = c :: cs) :
    c ≠ 'n' ∧ c ≠ 't' ∧ c ≠ 'f' ∧ c ≠ '"' ∧ c ≠ '[' ∧ c ≠ '{' ∧ c ≠ ']' ∧ c ≠ '}' := by
  have h := printJsonNumber_first_char n hd c cs hcs
  rcases h with rfl | ⟨_, _⟩ <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try decide) <;> intro heq <;> subst heq <;> simp_all (config := { decide := true })

/-- printJsonValue v is nonempty. -/
private theorem printJsonValue_ne_nil (v : JsonValue) (hdo : AllDenOne v) :
    (printJsonValue v).toList ≠ [] := by
  cases v with
  | null => simp [printJsonValue]
  | bool b => cases b <;> simp [printJsonValue]
  | number n => simp only [printJsonValue]; exact printJsonNumber_ne_nil n (by simp [AllDenOne] at hdo; exact hdo)
  | string _ => simp [printJsonValue, String.toList_append]
  | array _ => simp [printJsonValue, String.toList_append]
  | object _ => simp [printJsonValue, String.toList_append]

/-- First char of printJsonValue v is never ']'. -/
private theorem printJsonValue_first_ne_rbracket (v : JsonValue) (hdo : AllDenOne v)
    (c : Char) (cs : List Char) (hcs : (printJsonValue v).toList = c :: cs) :
    c ≠ ']' := by
  cases v with
  | null => simp [printJsonValue] at hcs; exact hcs.1 ▸ (by decide)
  | bool b => cases b <;> simp [printJsonValue] at hcs <;> exact hcs.1 ▸ (by decide)
  | number n =>
    simp only [printJsonValue] at hcs
    exact (printJsonNumber_first_ne n (by simp [AllDenOne] at hdo; exact hdo) c cs hcs).2.2.2.2.2.2.1
  | string _ => simp [printJsonValue, String.toList_append] at hcs; exact hcs.1 ▸ (by decide)
  | array _ => simp [printJsonValue, String.toList_append] at hcs; exact hcs.1 ▸ (by decide)
  | object _ => simp [printJsonValue, String.toList_append] at hcs; exact hcs.1 ▸ (by decide)

/-- First char of printJsonValue v is never '}'. -/
private theorem printJsonValue_first_ne_rbrace (v : JsonValue) (hdo : AllDenOne v)
    (c : Char) (cs : List Char) (hcs : (printJsonValue v).toList = c :: cs) :
    c ≠ '}' := by
  cases v with
  | null => simp [printJsonValue] at hcs; exact hcs.1 ▸ (by decide)
  | bool b => cases b <;> simp [printJsonValue] at hcs <;> exact hcs.1 ▸ (by decide)
  | number n =>
    simp only [printJsonValue] at hcs
    exact (printJsonNumber_first_ne n (by simp [AllDenOne] at hdo; exact hdo) c cs hcs).2.2.2.2.2.2.2
  | string _ => simp [printJsonValue, String.toList_append] at hcs; exact hcs.1 ▸ (by decide)
  | array _ => simp [printJsonValue, String.toList_append] at hcs; exact hcs.1 ▸ (by decide)
  | object _ => simp [printJsonValue, String.toList_append] at hcs; exact hcs.1 ▸ (by decide)

/-! ### Layer 4: Mutual roundtrip theorems -/

-- Helper: printJsonArray starts with the first element's print output
private theorem printJsonArray_cons_toList (v : JsonValue) (vs : List JsonValue) :
    ∃ tail, (printJsonArray (v :: vs)).toList =
      (printJsonValue v).toList ++ tail := by
  cases vs with
  | nil => exact ⟨[], by simp [printJsonArray]⟩
  | cons w ws =>
    exact ⟨(',' :: (printJsonArray (w :: ws)).toList), by
      simp [printJsonArray, String.toList_append]⟩

mutual
theorem parseJV_printJsonValue (jv : JsonValue) (rest : List Char) (fuel : Nat)
    (hfuel : fuel ≥ jsonSize jv)
    (hwf : WellFormedStrings jv)
    (hdo : AllDenOne jv)
    (hrest : NonNumContHead rest) :
    parseJV ((printJsonValue jv).toList ++ rest) fuel = some (jv, rest) := by
  cases jv with
  | null =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [jsonSize] at hfuel; omega⟩
    simp [printJsonValue]; rw [parseJV.eq_2 _ _ (by omega)]
  | bool b =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [jsonSize] at hfuel; omega⟩
    cases b <;> simp [printJsonValue]
    · rw [parseJV.eq_4 _ _ (by omega)]
    · rw [parseJV.eq_3 _ _ (by omega)]
  | string s =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [jsonSize] at hfuel; omega⟩
    simp only [printJsonValue, WellFormedStrings] at hwf ⊢
    rw [show ("\"" ++ s ++ "\"").toList ++ rest = '"' :: (s.toList ++ '"' :: rest) by
      simp [String.toList_append, List.append_assoc]]
    rw [parseJV.eq_5 (f + 1) (s.toList ++ '"' :: rest) (by omega)]
    rw [scanStringContent_scanSafe s.toList rest hwf]
    simp [String.ofList_toList]
  | number n =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [jsonSize] at hfuel; omega⟩
    simp only [printJsonValue, AllDenOne] at hdo ⊢
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (printJsonNumber_ne_nil n hdo)
    have ⟨hnn, hnt, hnf, hnq, hnlb, hnlc, _, _⟩ := printJsonNumber_first_ne n hdo c cs hcs
    -- Rewrite to expose first char, then apply eq_10
    rw [hcs, List.cons_append]
    -- parseJV.eq_10 expects all conditions about the *full input* c :: (cs ++ rest)
    -- Each condition says the input can't match a specific pattern
    rw [parseJV.eq_10 (c :: (cs ++ rest)) (f + 1)
        (by intro r h; exact hnn (List.cons.inj h).1)   -- not 'n'ull
        (by intro r h; exact hnt (List.cons.inj h).1)   -- not 't'rue
        (by intro r h; exact hnf (List.cons.inj h).1)   -- not 'f'alse
        (by intro r h; exact hnq (List.cons.inj h).1)   -- not '"'
        (by intro r h; exact hnlb (List.cons.inj h).1)  -- not '['']'
        (by intro r h; exact hnlc (List.cons.inj h).1)  -- not '{''}'
        (by omega)                                        -- fuel > 0
        (by intro r _ h _; exact hnlb (List.cons.inj h).1)  -- not '['
        (by intro r _ h _; exact hnlc (List.cons.inj h).1)] -- not '{'
    -- Now goal: match parseJsonNumber (c :: (cs ++ rest)) with ...
    -- Need to show c :: (cs ++ rest) = (printJsonNumber n).toList ++ rest
    have h_eq : c :: (cs ++ rest) = (printJsonNumber n).toList ++ rest := by
      simp [hcs, List.cons_append]
    rw [h_eq, parseJsonNumber_printJsonNumber n rest hdo hrest]
  | array elems =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [jsonSize] at hfuel; omega⟩
    simp only [WellFormedStrings, AllDenOne] at hwf hdo
    -- printJsonValue (.array elems) = "[" ++ printJsonArray elems ++ "]"
    show parseJV (("[" ++ printJsonArray elems ++ "]").toList ++ rest) (f + 1) =
      some (.array elems, rest)
    rw [show ("[" ++ printJsonArray elems ++ "]").toList ++ rest =
        '[' :: ((printJsonArray elems).toList ++ [']'] ++ rest) by
      simp [String.toList_append, List.append_assoc]]
    cases elems with
    | nil =>
      simp only [printJsonArray, show ("" : String).toList = [] from rfl,
                  List.nil_append, List.singleton_append]
      rw [parseJV.eq_6 _ _ (by omega)]
    | cons v vs =>
      -- Non-empty array: first char is from printJsonValue v, never ']'
      -- So parseJV.eq_7 applies (not eq_6)
      obtain ⟨tail, htail⟩ := printJsonArray_cons_toList v vs
      obtain ⟨d, ds, hds⟩ := List.exists_cons_of_ne_nil (printJsonValue_ne_nil v hdo.1)
      have hd_ne_rb : d ≠ ']' := printJsonValue_first_ne_rbracket v hdo.1 d ds hds
      have hfirst : ∀ r, (printJsonArray (v :: vs)).toList ++ [']'] ++ rest ≠ ']' :: r := by
        intro r h; rw [htail, hds, List.cons_append] at h
        exact hd_ne_rb (List.cons.inj h).1
      rw [parseJV.eq_7 _ f (by intro r h; exact hfirst r h),
          parseJArr_printJsonArray (v :: vs) rest f
            (by rw [jsonSize.eq_5] at hfuel; omega)
            hwf hdo (by simp) hrest]
  | object fields =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [jsonSize] at hfuel; omega⟩
    simp only [WellFormedStrings, AllDenOne] at hwf hdo
    show parseJV (("{" ++ printJsonObject fields ++ "}").toList ++ rest) (f + 1) =
      some (.object fields, rest)
    rw [show ("{" ++ printJsonObject fields ++ "}").toList ++ rest =
        '{' :: ((printJsonObject fields).toList ++ ['}'] ++ rest) by
      simp [String.toList_append, List.append_assoc]]
    cases fields with
    | nil =>
      simp only [printJsonObject, show ("" : String).toList = [] from rfl,
                  List.nil_append, List.singleton_append]
      rw [parseJV.eq_8 _ _ (by omega)]
    | cons kv rest_fields =>
      obtain ⟨k, v⟩ := kv
      -- Non-empty object: printJsonObject starts with '"', never '}'
      have hfirst : ∀ r,
          (printJsonObject ((k, v) :: rest_fields)).toList ++ ['}'] ++ rest ≠ '}' :: r := by
        intro r h; cases rest_fields with
        | nil => simp [printJsonObject, String.toList_append] at h
        | cons _ _ => simp [printJsonObject, String.toList_append] at h
      rw [parseJV.eq_9 _ f (by intro r h; exact hfirst r h),
          parseJObj_printJsonObject ((k, v) :: rest_fields) rest f
            (by rw [jsonSize.eq_6] at hfuel; omega)
            hwf hdo (by simp) hrest]

theorem parseJArr_printJsonArray (elems : List JsonValue) (rest : List Char) (fuel : Nat)
    (hfuel : fuel ≥ jsonSizeList elems + 1)
    (hwf : WellFormedStringsList elems)
    (hdo : AllDenOneList elems)
    (hne : elems ≠ [])
    (hrest : NonNumContHead rest) :
    parseJArr ((printJsonArray elems).toList ++ [']'] ++ rest) fuel
      = some (elems, rest) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  rw [parseJArr.eq_2]
  cases elems with
  | nil => exact absurd rfl hne
  | cons v vs =>
    cases vs with
    | nil =>
      -- Single element: printJsonArray [v] = printJsonValue v
      simp only [printJsonArray, WellFormedStringsList, AllDenOneList] at *
      simp only [List.singleton_append, List.append_assoc]
      rw [parseJV_printJsonValue v (']' :: rest) f
          (by rw [jsonSizeList.eq_2] at hfuel; omega)
          hwf.1 hdo.1 (Or.inr ⟨']', rest, rfl, by decide, by decide, by decide⟩)]
      -- match on some (v, ']' :: rest) reduces to second branch
      rfl
    | cons w ws =>
      -- Multiple elements
      simp only [printJsonArray, WellFormedStringsList, AllDenOneList] at *
      rw [show (printJsonValue v ++ "," ++ printJsonArray (w :: ws)).toList ++ [']'] ++ rest =
          (printJsonValue v).toList ++ (',' :: ((printJsonArray (w :: ws)).toList ++ [']'] ++ rest)) by
        simp [String.toList_append, List.append_assoc]]
      have hv := parseJV_printJsonValue v
            (',' :: ((printJsonArray (w :: ws)).toList ++ [']'] ++ rest)) f
            (by rw [jsonSizeList.eq_2] at hfuel; omega)
            hwf.1 hdo.1 (Or.inr ⟨',', _, rfl, by decide, by decide, by decide⟩)
      have hrec := parseJArr_printJsonArray (w :: ws) rest f
            (by have h1 := jsonSizeList.eq_2 v (w :: ws)
                have h3 : jsonSize v ≥ 1 := by cases v <;> simp [jsonSize] <;> omega
                omega)
            hwf.2 hdo.2 (by simp) hrest
      simp only [hv, hrec]

theorem parseJObj_printJsonObject (fields : List (String × JsonValue)) (rest : List Char) (fuel : Nat)
    (hfuel : fuel ≥ jsonSizeFields fields + 1)
    (hwf : WellFormedStringsFields fields)
    (hdo : AllDenOneFields fields)
    (hne : fields ≠ [])
    (hrest : NonNumContHead rest) :
    parseJObj ((printJsonObject fields).toList ++ ['}'] ++ rest) fuel
      = some (fields, rest) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  cases fields with
  | nil => exact absurd rfl hne
  | cons kv rest_fields =>
    obtain ⟨k, v⟩ := kv
    cases rest_fields with
    | nil =>
      simp only [printJsonObject, WellFormedStringsFields, AllDenOneFields] at *
      rw [show ("\"" ++ k ++ "\":" ++ printJsonValue v).toList ++ ['}'] ++ rest =
          '"' :: (k.toList ++ '"' :: ':' :: ((printJsonValue v).toList ++ '}' :: rest)) by
        simp [String.toList_append, List.append_assoc]]
      rw [parseJObj.eq_2 _ f]
      have hsc := scanStringContent_scanSafe k.toList
          (':' :: ((printJsonValue v).toList ++ '}' :: rest)) hwf.1
      have hpv := parseJV_printJsonValue v ('}' :: rest) f
          (by rw [jsonSizeFields.eq_2] at hfuel; omega)
          hwf.2.1 hdo.1 (Or.inr ⟨'}', rest, rfl, by decide, by decide, by decide⟩)
      simp only [hsc, hpv, String.ofList_toList]
    | cons kv2 rest2 =>
      obtain ⟨k2, v2⟩ := kv2
      simp only [printJsonObject, WellFormedStringsFields, AllDenOneFields] at *
      rw [show ("\"" ++ k ++ "\":" ++ printJsonValue v ++ "," ++
            printJsonObject ((k2, v2) :: rest2)).toList ++ ['}'] ++ rest =
          '"' :: (k.toList ++ '"' :: ':' :: ((printJsonValue v).toList ++
            ',' :: ((printJsonObject ((k2, v2) :: rest2)).toList ++ ['}'] ++ rest))) by
        simp [String.toList_append, List.append_assoc]]
      rw [parseJObj.eq_2 _ f]
      have hsc := scanStringContent_scanSafe k.toList
          (':' :: ((printJsonValue v).toList ++ ',' ::
            ((printJsonObject ((k2, v2) :: rest2)).toList ++ ['}'] ++ rest))) hwf.1
      have hpv := parseJV_printJsonValue v
          (',' :: ((printJsonObject ((k2, v2) :: rest2)).toList ++ ['}'] ++ rest)) f
          (by rw [jsonSizeFields.eq_2] at hfuel; omega)
          hwf.2.1 hdo.1 (Or.inr ⟨',', _, rfl, by decide, by decide, by decide⟩)
      have hrec := parseJObj_printJsonObject ((k2, v2) :: rest2) rest f
          (by have h1 := jsonSizeFields.eq_2 k v ((k2, v2) :: rest2)
              have h2 := jsonSizeFields.eq_2 k2 v2 rest2
              have h3 : jsonSize v ≥ 1 := by cases v <;> simp [jsonSize] <;> omega
              omega)
          hwf.2.2 hdo.2 (by simp) hrest
      simp only [hsc, hpv, hrec, String.ofList_toList]
end
