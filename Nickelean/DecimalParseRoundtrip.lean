/-
  DecimalParseRoundtrip.lean

  Proof that parseJsonNumber roundtrips with Decimal.format.
  For a well-formed Decimal d:
    parseJsonNumber ((Decimal.format d).toList ++ rest)
      = some (decimalToJsonNumber d.sign d.digits d.exponent, rest)
-/
import Nickelean.ParseJsonText

set_option linter.unusedSimpArgs false

/-! ## Helper lemmas -/

/-- Convert NonDigitHead to the parseDigitChar-based condition. -/
theorem nonDigitHead_to_parseDigitChar (rest : List Char) (h : NonDigitHead rest) :
    rest = [] ∨ (∃ c cs, rest = c :: cs ∧ Decimal.parseDigitChar c = none) := by
  rcases h with rfl | ⟨c, t, rfl, hnd⟩
  · exact Or.inl rfl
  · right; exact ⟨c, t, rfl, by
      unfold Decimal.parseDigitChar
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      split
      · next h => exact absurd h hnd
      · rfl⟩

/-- parseJsonNumberTail handles the 'e' case correctly. -/
theorem parseJsonNumberTail_e (sign : Bool) (n : Nat) (exp : Int) (rest : List Char)
    (hrest : NonDigitHead rest) :
    parseJsonNumberTail sign n ('e' :: (Decimal.intToDigits exp ++ rest)) =
      some (decimalToJsonNumber sign n exp, rest) := by
  simp only [parseJsonNumberTail]
  rw [Decimal.parseInt_intToDigits_append exp rest (nonDigitHead_to_parseDigitChar rest hrest)]

/-- parseJsonNumber on unsigned input. -/
theorem parseJsonNumber_unsigned (chars : List Char) (h : ∀ rest, chars ≠ '-' :: rest) :
    parseJsonNumber chars =
      match Decimal.parseNat chars with
      | some (n, rest) => parseJsonNumberTail false n rest
      | none => none := by
  unfold parseJsonNumber; split
  · exfalso; exact h _ rfl
  · rfl

/-- parseJsonNumber on '-' :: input. -/
theorem parseJsonNumber_signed (chars : List Char) :
    parseJsonNumber ('-' :: chars) =
      match Decimal.parseNat chars with
      | some (n, rest) => parseJsonNumberTail true n rest
      | none => none := by
  unfold parseJsonNumber; rfl

/-! ## The main roundtrip theorem -/

theorem parseJsonNumber_decimalFormat (d : Decimal) (hd : d.WellFormed) (rest : List Char)
    (hrest : NonNumContHead rest) :
    parseJsonNumber ((Decimal.format d).toList ++ rest) =
      some (decimalToJsonNumber d.sign d.digits d.exponent, rest) := by
  rcases d with ⟨sign, digits, exponent⟩
  obtain ⟨hwf_trail, hwf_exp⟩ := hd
  simp only at hwf_trail hwf_exp
  have hrest_nd := hrest.toNonDigitHead
  have hrest_pdc := nonDigitHead_to_parseDigitChar rest hrest_nd
  have hstop_e : ∀ (r : List Char),
      ('e' :: r) = [] ∨ (∃ c cs, 'e' :: r = c :: cs ∧ Decimal.parseDigitChar c = none) :=
    fun r => Or.inr ⟨'e', r, rfl, Decimal.parseDigitChar_e⟩
  by_cases hd0 : digits = 0
  · -- Case 1: digits = 0
    subst hd0; have hexp0 := hwf_exp rfl; subst hexp0
    have hint0 : Decimal.intToDigits (0 : Int) = ['0'] := by native_decide
    have hnd0 : Decimal.natToDigits 0 = ['0'] := by native_decide
    -- Rewrite format output ++ rest into the form we need for parsing
    have hpn : Decimal.parseNat (Decimal.natToDigits 0 ++ ('e' :: (Decimal.intToDigits 0 ++ rest)))
        = some (0, 'e' :: (Decimal.intToDigits 0 ++ rest)) :=
      Decimal.parseNat_natToDigits_append 0 _ (hstop_e _)
    cases sign
    · -- sign = false
      -- (Decimal.format ⟨false, 0, 0⟩).toList ++ rest = natToDigits 0 ++ ('e' :: intToDigits 0 ++ rest)
      have hfmt : (Decimal.format ⟨false, 0, 0⟩).toList ++ rest =
          Decimal.natToDigits 0 ++ ('e' :: (Decimal.intToDigits 0 ++ rest)) := by
        rw [hnd0, hint0]; simp [Decimal.format, String.toList_ofList, List.append_assoc]
      rw [hfmt, parseJsonNumber_unsigned _ (by
        intro r h; exact Decimal.natToDigits_not_starts_minus 0 _ r h)]
      rw [hpn]; exact parseJsonNumberTail_e false 0 0 rest hrest_nd
    · -- sign = true
      have hfmt : (Decimal.format ⟨true, 0, 0⟩).toList ++ rest =
          '-' :: (Decimal.natToDigits 0 ++ ('e' :: (Decimal.intToDigits 0 ++ rest))) := by
        rw [hnd0, hint0]; simp [Decimal.format, String.toList_ofList, List.append_assoc]
      rw [hfmt, parseJsonNumber_signed, hpn]
      exact parseJsonNumberTail_e true 0 0 rest hrest_nd
  · -- digits > 0
    set allDigits := Decimal.natToDigits digits with h_ad
    have had_ne : allDigits ≠ [] := h_ad ▸ Decimal.natToDigits_ne_nil digits
    have had_mem : ∀ c ∈ allDigits, ∃ d, d < 10 ∧ c = Char.ofNat (d + 48) := by
      intro c hc; rw [h_ad, Decimal.natToDigits] at hc; simp [hd0] at hc
      exact Decimal.natToDigitsAux_mem digits c hc
    obtain ⟨c, rest_digits, hcr⟩ := List.exists_cons_of_ne_nil had_ne
    obtain ⟨d1, hd1_lt, hd1_eq⟩ := had_mem c (by rw [hcr]; simp)
    subst hd1_eq
    have hc_ne_minus := Decimal.digit_char_ne_minus d1 hd1_lt
    set nDigits := allDigits.length
    set adjExp : Int := exponent + (↑nDigits - 1)
    cases rest_digits with
    | nil =>
      -- Case 2: Single digit
      have hnd : Decimal.natToDigits digits = [Char.ofNat (d1 + 48)] := by rw [← h_ad, hcr]
      have hadjExp : adjExp = exponent := by simp [adjExp, nDigits, hcr]
      have hpn : Decimal.parseNat (Decimal.natToDigits digits ++ ('e' :: (Decimal.intToDigits exponent ++ rest)))
          = some (digits, 'e' :: (Decimal.intToDigits exponent ++ rest)) :=
        Decimal.parseNat_natToDigits_append digits _ (hstop_e _)
      cases sign
      · -- sign = false, single digit
        have hfmt : (Decimal.format ⟨false, digits, exponent⟩).toList ++ rest =
            Decimal.natToDigits digits ++ ('e' :: (Decimal.intToDigits exponent ++ rest)) := by
          simp only [Decimal.format, hd0, ↓reduceIte, hnd, String.toList_ofList]
          simp [List.append_assoc, hadjExp]
        rw [hfmt, parseJsonNumber_unsigned _ (by
          intro r h; exact Decimal.natToDigits_not_starts_minus digits _ r h)]
        rw [hpn]; exact parseJsonNumberTail_e false digits exponent rest hrest_nd
      · -- sign = true, single digit
        have hfmt : (Decimal.format ⟨true, digits, exponent⟩).toList ++ rest =
            '-' :: (Decimal.natToDigits digits ++ ('e' :: (Decimal.intToDigits exponent ++ rest))) := by
          simp only [Decimal.format, hd0, ↓reduceIte, hnd, String.toList_ofList]
          simp [List.append_assoc, hadjExp]
        rw [hfmt, parseJsonNumber_signed, hpn]
        exact parseJsonNumberTail_e true digits exponent rest hrest_nd
    | cons c2 rest_digits' =>
      -- Case 3: Multi-digit
      have hnd : Decimal.natToDigits digits = Char.ofNat (d1 + 48) :: c2 :: rest_digits' := by
        rw [← h_ad, hcr]
      set tail := c2 :: rest_digits'
      have htail_ne : tail ≠ [] := by simp [tail]
      have htail_mem : ∀ ch ∈ tail, ∃ d, d < 10 ∧ ch = Char.ofNat (d + 48) :=
        fun ch hch => had_mem ch (by rw [hcr]; exact List.mem_cons_of_mem _ hch)
      have hlen : nDigits = tail.length + 1 := by simp [nDigits, hcr]
      have hadjExp : adjExp = exponent + ↑tail.length := by simp [adjExp, hlen]
      set eDigits := Decimal.intToDigits adjExp
      set eRest : List Char := 'e' :: eDigits ++ rest
      have hrest_e' : eRest = [] ∨ (∃ c cs, eRest = c :: cs ∧ Decimal.parseDigitChar c = none) :=
        Or.inr ⟨'e', _, rfl, Decimal.parseDigitChar_e⟩
      -- parseNat on d1 :: '.' :: ... stops after d1
      have hc_digit := Decimal.parseDigitChar_ofNat d1 hd1_lt
      have hpn_d1 : Decimal.parseNat (Char.ofNat (d1 + 48) :: '.' :: (tail ++ eRest)) =
          some (d1, '.' :: (tail ++ eRest)) := by
        simp only [Decimal.parseNat, Decimal.parseNatAux, hc_digit, Decimal.parseDigitChar_dot,
                   Nat.zero_mul, Nat.zero_add, ↓reduceIte]
      -- Get fracVal
      obtain ⟨fracVal, hfrac0, hfracd1⟩ :=
        Decimal.parseNatAux_acc_shift tail eRest d1 htail_mem hrest_e'
      have hparse_full := Decimal.parseNat_natToDigits_append digits eRest hrest_e'
      rw [hnd, List.cons_append] at hparse_full
      simp only [Decimal.parseNat] at hparse_full
      rw [Decimal.parseNatAux_digit d1 hd1_lt (tail ++ eRest) 0 false] at hparse_full
      simp only [Nat.zero_mul, Nat.zero_add] at hparse_full
      have hdigits_eq : d1 * 10 ^ tail.length + fracVal = digits := by
        have := hparse_full.symm.trans hfracd1; cases this; rfl
      -- parseNat on tail
      obtain ⟨cc2, rest_tail, htail_cons⟩ := List.exists_cons_of_ne_nil htail_ne
      obtain ⟨d2, hd2_lt, hd2_eq⟩ := htail_mem cc2 (by rw [htail_cons]; simp)
      have hpn_tail : Decimal.parseNat (tail ++ eRest) = some (fracVal, eRest) := by
        show Decimal.parseNatAux (tail ++ eRest) 0 false = some (fracVal, eRest)
        rw [htail_cons, List.cons_append, hd2_eq, Decimal.parseNatAux_digit d2 hd2_lt]
        simp only [Nat.zero_mul, Nat.zero_add]
        have : Decimal.parseNatAux (tail ++ eRest) 0 true
            = Decimal.parseNatAux (rest_tail ++ eRest) d2 true := by
          rw [htail_cons, List.cons_append, hd2_eq, Decimal.parseNatAux_digit d2 hd2_lt]
          simp only [Nat.zero_mul, Nat.zero_add]
        rw [← this]; exact hfrac0
      -- Length and exponent
      have hlen_calc : (tail ++ ('e' :: (Decimal.intToDigits adjExp ++ rest))).length -
          (Decimal.intToDigits adjExp ++ rest).length - 1 = tail.length := by
        simp [List.length_append, List.length_cons]; omega
      have h_expEq : adjExp - ↑tail.length = exponent := by simp [adjExp, hlen]
      -- parseJsonNumberTail for '.' case
      have hTail_dot : ∀ s, parseJsonNumberTail s d1 ('.' :: (tail ++ eRest)) =
          some (decimalToJsonNumber s digits exponent, rest) := by
        intro s
        -- Directly compute parseJsonNumberTail step by step
        -- parseJsonNumberTail s d1 ('.' :: (tail ++ eRest))
        -- Match on '.' :: fracRest where fracRest = tail ++ eRest
        -- parseNat fracRest = some (fracVal, eRest)  [by hpn_tail]
        -- eRest = 'e' :: eDigits ++ rest, so match on 'e' :: expRest
        -- expRest = eDigits ++ rest
        -- numFrac = fracRest.length - expRest.length - 1
        -- parseInt expRest = parseInt (intToDigits adjExp ++ rest)
        --                  = some (adjExp, rest)
        -- fullDigits = d1 * 10^numFrac + fracVal
        -- fullExp = adjExp - numFrac
        -- parseJsonNumberTail s d1 ('.' :: (tail ++ eRest)) unfolds to matching '.'
        -- then parseNat (tail ++ eRest) which gives some (fracVal, eRest)
        -- eRest = 'e' :: eDigits ++ rest, matching 'e' :: expRest
        -- Then parseInt (eDigits ++ rest) = some (adjExp, rest)
        -- Finally arithmetic
        have : parseJsonNumberTail s d1 ('.' :: (tail ++ eRest)) =
            (match Decimal.parseNat (tail ++ eRest) with
            | some (frac, 'e' :: expRest) =>
              let numFrac := (tail ++ eRest).length - expRest.length - 1
              match Decimal.parseInt expRest with
              | some (exp, rest') =>
                let fullDigits := d1 * 10 ^ numFrac + frac
                let fullExp := exp - (numFrac : Int)
                some (decimalToJsonNumber s fullDigits fullExp, rest')
              | none => none
            | _ => none) := by unfold parseJsonNumberTail; rfl
        rw [this, hpn_tail, show eRest = 'e' :: (eDigits ++ rest) from rfl]
        simp only []
        rw [show eDigits ++ rest = Decimal.intToDigits adjExp ++ rest from rfl,
            Decimal.parseInt_intToDigits_append adjExp rest hrest_pdc]
        simp only [hlen_calc, hdigits_eq]
        -- Reduce the match some (adjExp, rest) with ...
        simp only [h_expEq]
      cases sign
      · -- sign = false, multi-digit
        have hfmt : (Decimal.format ⟨false, digits, exponent⟩).toList ++ rest =
            Char.ofNat (d1 + 48) :: '.' :: (tail ++ eRest) := by
          simp only [Decimal.format, hd0, ↓reduceIte, hnd, String.toList_ofList]
          simp [eRest, eDigits, adjExp, nDigits, hlen, List.append_assoc]
        rw [hfmt, parseJsonNumber_unsigned _ (by intro r h; exact hc_ne_minus (List.cons.inj h).1)]
        rw [hpn_d1]; exact hTail_dot false
      · -- sign = true, multi-digit
        have hfmt : (Decimal.format ⟨true, digits, exponent⟩).toList ++ rest =
            '-' :: Char.ofNat (d1 + 48) :: '.' :: (tail ++ eRest) := by
          simp only [Decimal.format, hd0, ↓reduceIte, hnd, String.toList_ofList]
          simp [eRest, eDigits, adjExp, nDigits, hlen, List.append_assoc]
        rw [hfmt, parseJsonNumber_signed, hpn_d1]
        exact hTail_dot true
