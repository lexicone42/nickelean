/-
  Roundtrip/EscapeRoundtrip.lean

  Prove: unescapeJsonString (escapeJsonString s) = some s

  Proof layers:
  1. hexDigit/parseHexDigit roundtrip (finite cases + native_decide)
  2. parseHex4 roundtrip for \uXXXX encoding
  3. Single-char: unescapeLoop (escapeChar c ++ rest) acc = unescapeLoop rest (c :: acc)
  4. Full string by list induction
  5. Main theorem lifted to String
-/
import Nickelean.Escape

/-! ## Layer 1: Hex digit roundtrip -/

theorem parseHexDigit_hexDigit (n : Nat) (h : n < 16) :
    parseHexDigit (hexDigit n) = some n := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
         n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> native_decide

/-! ## Layer 2: Hex4 decomposition roundtrip -/

theorem hex4_decompose (n : Nat) (h : n < 65536) :
    (n / 4096 % 16) * 4096 + (n / 256 % 16) * 256 + (n / 16 % 16) * 16 + n % 16 = n := by
  omega

theorem parseHex4_roundtrip (c : Char) (hlt : c.val.toNat < 65536) :
    parseHex4
      (hexDigit (c.val.toNat / 4096 % 16))
      (hexDigit (c.val.toNat / 256 % 16))
      (hexDigit (c.val.toNat / 16 % 16))
      (hexDigit (c.val.toNat % 16))
    = some c := by
  simp only [parseHex4]
  rw [parseHexDigit_hexDigit _ (by omega)]
  rw [parseHexDigit_hexDigit _ (by omega)]
  rw [parseHexDigit_hexDigit _ (by omega)]
  rw [parseHexDigit_hexDigit _ (by omega)]
  simp only [bind, Option.bind]
  have heq := hex4_decompose c.val.toNat hlt
  have hvalid : Nat.isValidChar (c.val.toNat / 4096 % 16 * 4096 + c.val.toNat / 256 % 16 * 256 +
    c.val.toNat / 16 % 16 * 16 + c.val.toNat % 16) := by
    rw [heq]; exact c.valid
  simp only [hvalid, ↓reduceDIte]
  congr 1
  apply Char.ext
  apply UInt32.toNat_inj.mp
  exact heq

/-! ## Layer 3: Single character roundtrip -/

/-- When escapeChar produces a \uXXXX sequence and unescapeLoop processes it,
    the original character is recovered. -/
private theorem unescapeLoop_escapeCharHex (c : Char) (hlt : c.val < 0x20)
    (_hne_n : c ≠ '\n') (_hne_r : c ≠ '\r') (_hne_t : c ≠ '\t')
    (_hne_q : c ≠ '"') (_hne_b : c ≠ '\\')
    (rest : List Char) (acc : List Char) :
    unescapeLoop (escapeCharHex c ++ rest) acc = unescapeLoop rest (c :: acc) := by
  simp only [escapeCharHex, List.cons_append]
  rw [unescapeLoop.eq_10]
  have hlt' : c.val.toNat < 65536 := by
    have h32 := UInt32.lt_iff_toNat_lt.mp hlt
    simp (config := { decide := true }) at h32
    omega
  rw [parseHex4_roundtrip c hlt']
  simp [bind, Option.bind]

/-- The core inversion lemma: unescapeLoop correctly inverts one escaped
    character and continues with the rest of the input. -/
theorem unescapeLoop_escapeChar (c : Char) (rest : List Char) (acc : List Char) :
    unescapeLoop (escapeChar c ++ rest) acc = unescapeLoop rest (c :: acc) := by
  by_cases hq : c = '"'
  · subst hq; simp [escapeChar]; rw [unescapeLoop.eq_2]
  · by_cases hb : c = '\\'
    · subst hb; simp [escapeChar]; rw [unescapeLoop.eq_3]
    · by_cases hn : c = '\n'
      · subst hn; simp [escapeChar]; rw [unescapeLoop.eq_5]
      · by_cases hr : c = '\r'
        · subst hr; simp [escapeChar]; rw [unescapeLoop.eq_6]
        · by_cases ht : c = '\t'
          · subst ht; simp [escapeChar]; rw [unescapeLoop.eq_7]
          · by_cases hctl : c.val < 0x20
            · -- Control character: uses \uXXXX encoding
              have : escapeChar c = escapeCharHex c := by
                simp [escapeChar, hq, hb, hn, hr, ht, hctl]
              rw [this]
              exact unescapeLoop_escapeCharHex c hctl hn hr ht hq hb rest acc
            · -- Passthrough: character is not special
              have : escapeChar c = [c] := by
                simp [escapeChar, hq, hb, hn, hr, ht, hctl]
              rw [this, List.singleton_append]
              rw [unescapeLoop.eq_12]
              all_goals (try intros; simp_all)

/-! ## Layer 4: Full list roundtrip via accumulator -/

/-- Helper: unescapeLoop on escaped chars appended with rest.
    Processing all escaped chars leaves the accumulator with the original
    chars in reverse prepended. -/
theorem unescapeLoop_flatMap_escapeChar_acc (chars : List Char) (rest acc : List Char) :
    unescapeLoop (chars.flatMap escapeChar ++ rest) acc
    = unescapeLoop rest (chars.reverse ++ acc) := by
  induction chars generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.flatMap_cons, List.append_assoc, unescapeLoop_escapeChar]
    rw [ih (c :: acc)]
    simp [List.reverse_cons, List.append_assoc]

theorem unescapeLoop_flatMap_escapeChar (chars : List Char) :
    unescapeLoop (chars.flatMap escapeChar) [] = some chars := by
  rw [show chars.flatMap escapeChar = chars.flatMap escapeChar ++ [] from by simp]
  rw [unescapeLoop_flatMap_escapeChar_acc]
  simp [unescapeLoop.eq_1]

/-! ## Layer 5: Main escape roundtrip -/

theorem unescape_escape_roundtrip (s : String) :
    unescapeJsonString (escapeJsonString s) = some s := by
  simp only [unescapeJsonString, escapeJsonString]
  rw [String.toList_ofList]
  rw [unescapeLoop_flatMap_escapeChar]
  simp [String.ofList_toList]
