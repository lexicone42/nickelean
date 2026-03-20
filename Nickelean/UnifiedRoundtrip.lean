/-
  NickelJson/UnifiedRoundtrip.lean

  Addresses three adversarial review concerns:

  1. **Unified number roundtrip**: A single theorem handling BOTH integer and
     float numbers through `formatSerdeNumberF64` and `parseJsonNumber`.

  2. **Exact `json_roundtrip_sorted`**: Strengthens the existential
     `∃ v', fromJson (toJsonSorted v) = some v'` to a constructive form
     `fromJson (toJsonSorted v) = some v' ∧ toJson v' = toJsonSorted v`.

  3. **Float roundtrip lifted to `parseJV`**: Shows that `parseJV` (the structural
     JSON parser) correctly handles float-formatted numbers by delegating to
     `parseJsonNumber`.
-/
import Nickelean.FullTextRoundtrip
import Nickelean.RecordOrder

set_option linter.unusedSimpArgs false

/-! ## Concern 1: Unified number roundtrip (integer + float)

  For ANY JsonNumber with a finite F64 rounding:
  - If integer (denominator = 1): exact syntactic recovery through our parser
  - If non-integer: recovery up to F64 rounding

  This is a single theorem covering both cases, eliminating the gap between
  `formatSerdeNumberF64_int_roundtrip` (integers only) and
  `float_text_roundtrip_f64` (raw F64 values only).
-/

/-- For non-integer JsonNumbers, `classifyNumberF64` produces a float,
    and parsing the serde-formatted output recovers the F64 rounding. -/
theorem number_serde_roundtrip_float (jn : JsonNumber)
    (hfin : F64.isFinite (F64.roundToNearestEven jn.toMathRat))
    (hni : ¬(jn.numerator % jn.denominator == 0))
    (hne : (Ryu.ryu (F64.roundToNearestEven jn.toMathRat) hfin).digits ≠ 0)
    (rest : List Char) (hrest : NonNumContHead rest) :
    ∃ jn',
      parseJsonNumber ((formatSerdeNumberF64 (classifyNumberF64 jn hfin)).toList ++ rest)
        = some (jn', rest) ∧
      F64.roundToNearestEven jn'.toMathRat = F64.roundToNearestEven jn.toMathRat := by
  have hclass : classifyNumberF64 jn hfin = .float (F64.roundToNearestEven jn.toMathRat) hfin := by
    unfold classifyNumberF64; simp [hni]
  rw [hclass]; simp only [formatSerdeNumberF64, formatF64]
  set x := F64.roundToNearestEven jn.toMathRat
  set d := Ryu.ryu x hfin
  refine ⟨decimalToJsonNumber d.sign d.digits d.exponent, ?_, ?_⟩
  · exact parseJsonNumber_ryu x hfin rest hrest
  · rw [decimalToJsonNumber_toMathRat]
    have h_toF64 : Decimal.toF64 d = F64.roundToNearestEven (Decimal.toRat d) := by
      simp [Decimal.toF64, hne]
    rw [← h_toF64]
    exact Ryu.ryu_roundtrip x hfin

/-- THE UNIFIED NUMBER ROUNDTRIP.

    For any JsonNumber `jn` whose F64 rounding is finite, the serde pipeline
    `formatSerdeNumberF64 ∘ classifyNumberF64` roundtrips through `parseJsonNumber`:

    - **Integer case** (denominator = 1): exact syntactic recovery `jn' = jn`
    - **Non-integer case**: F64-faithful recovery
      `F64.roundToNearestEven jn'.toMathRat = F64.roundToNearestEven jn.toMathRat`

    This is the single theorem handling mixed int+float number serialization
    that matches Nickel's actual `serialize_num` dispatch. -/
theorem number_serde_roundtrip_unified (jn : JsonNumber)
    (hfin : F64.isFinite (F64.roundToNearestEven jn.toMathRat))
    (hne : ¬(jn.numerator % jn.denominator == 0) →
           (Ryu.ryu (F64.roundToNearestEven jn.toMathRat) hfin).digits ≠ 0)
    (rest : List Char) (hrest : NonNumContHead rest) :
    ∃ jn',
      parseJsonNumber ((formatSerdeNumberF64 (classifyNumberF64 jn hfin)).toList ++ rest)
        = some (jn', rest) ∧
      (jn.denominator = 1 → jn' = jn) ∧
      (¬(jn.numerator % jn.denominator == 0) →
        F64.roundToNearestEven jn'.toMathRat = F64.roundToNearestEven jn.toMathRat) := by
  by_cases hint : jn.numerator % jn.denominator == 0
  · -- Integer case
    have hint' : (jn.numerator % ↑jn.denominator = 0) := by
      have := hint; simp [BEq.beq] at this; exact this
    set intVal := jn.numerator / jn.denominator with h_intVal
    set resultJn : JsonNumber := ⟨intVal, 1, by omega⟩
    have hden1 : resultJn.denominator = 1 := rfl
    by_cases hd1 : jn.denominator = 1
    · -- den = 1: exact recovery as jn itself
      refine ⟨jn, ?_, ?_, ?_⟩
      · exact formatSerdeNumberF64_int_roundtrip jn hd1 hfin rest hrest
      · intro _; rfl
      · intro hni; exact absurd hint hni
    · -- den ≠ 1 but den|num: recovery as resultJn = ⟨num/den, 1⟩
      -- classifyNumberF64 with hint produces the integer branch
      have hclass_neg : ∀ (hneg : intVal < 0),
          classifyNumberF64 jn hfin = .negInt intVal hneg := by
        intro hneg; unfold classifyNumberF64; simp [hint]; exact dif_pos hneg
      have hclass_pos : ¬(intVal < 0) →
          classifyNumberF64 jn hfin = .posInt intVal.toNat := by
        intro hneg; unfold classifyNumberF64; simp [hint]; exact dif_neg hneg
      refine ⟨resultJn, ?_, ?_, ?_⟩
      · -- Show that classifyNumberF64 + formatSerdeNumberF64 produces the same as printJsonNumber resultJn
        have key : (formatSerdeNumberF64 (classifyNumberF64 jn hfin)).toList ++ rest
            = (printJsonNumber resultJn).toList ++ rest := by
          have hresnum : resultJn.numerator = intVal := rfl
          by_cases hneg : intVal < 0
          · rw [hclass_neg hneg]
            simp only [formatSerdeNumberF64, printJsonNumber, hden1, beq_self_eq_true, ↓reduceIte,
                        hresnum, hneg, String.toList_append]
          · rw [hclass_pos hneg]
            simp only [formatSerdeNumberF64, printJsonNumber, hden1, beq_self_eq_true, ↓reduceIte,
                        hresnum, hneg]
            have : intVal.natAbs = intVal.toNat := by omega
            rw [this]
        rw [key]
        exact parseJsonNumber_printJsonNumber resultJn rest hden1 hrest
      · intro hd1'; exact absurd hd1' hd1
      · intro hni; exact absurd hint hni
  · -- Non-integer case
    obtain ⟨jn', hparse, hf64⟩ := number_serde_roundtrip_float jn hfin hint (hne hint) rest hrest
    exact ⟨jn', hparse, fun hd1 => by simp [hd1] at hint, fun _ => hf64⟩

/-! ## Predicate for mixed integer+float NickelValues -/

mutual
/-- Every number in a NickelValue tree has a finite F64 rounding.
    This is the minimal precondition for the unified serde roundtrip. -/
def NickelNumsValid : NickelValue → Prop
  | .null => True
  | .bool _ => True
  | .num n => F64.isFinite (F64.roundToNearestEven n.toMathRat)
  | .str _ => True
  | .array elems => NickelNumsValidList elems
  | .record fields => NickelNumsValidFields fields

def NickelNumsValidList : List NickelValue → Prop
  | [] => True
  | v :: vs => NickelNumsValid v ∧ NickelNumsValidList vs

def NickelNumsValidFields : List (String × NickelValue) → Prop
  | [] => True
  | (_, v) :: fs => NickelNumsValid v ∧ NickelNumsValidFields fs
end

/-! ## Concern 3: Float roundtrip lifted to `parseJV`

  `float_text_roundtrip_f64` works at `parseJsonNumber` level. Here we lift
  it to `parseJV`, the structural JSON parser. The key insight:
  `Decimal.format d` always starts with '-' or a digit character, never with
  a JSON keyword prefix ('n', 't', 'f') or structural char ('"', '[', '{').
  So `parseJV` falls through to its catch-all case which delegates to
  `parseJsonNumber`.
-/

/-- The first character of `Decimal.natToDigits n` is always a digit. -/
private theorem natToDigits_first_digit (n : Nat) :
    ∃ c cs, Decimal.natToDigits n = c :: cs ∧ '0' ≤ c ∧ c ≤ '9' := by
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (Decimal.natToDigits_ne_nil n)
  refine ⟨c, cs, hcs, ?_⟩
  by_cases hn : n = 0
  · subst hn; simp [Decimal.natToDigits] at hcs; obtain ⟨rfl, rfl⟩ := hcs; decide
  · have hmem : c ∈ Decimal.natToDigitsAux n [] := by
      rw [show Decimal.natToDigits n = Decimal.natToDigitsAux n [] from by
        simp [Decimal.natToDigits, hn]] at hcs
      rw [hcs]; simp
    obtain ⟨d, hd, hcd⟩ := Decimal.natToDigitsAux_mem n c hmem
    subst hcd
    have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨
           d = 7 ∨ d = 8 ∨ d = 9 := by omega
    rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      exact ⟨by native_decide, by native_decide⟩

/-- `formatF64 x hfin` output starts with '-' or a digit, never a JSON
    keyword/structural character. -/
private theorem formatF64_first_char (x : F64) (hfin : F64.isFinite x) :
    ∃ c cs, (formatF64 x hfin).toList = c :: cs ∧
      c ≠ 'n' ∧ c ≠ 't' ∧ c ≠ 'f' ∧ c ≠ '"' ∧ c ≠ '[' ∧ c ≠ '{' ∧ c ≠ ']' ∧ c ≠ '}' := by
  simp only [formatF64]
  set d := Ryu.ryu x hfin
  by_cases hs : d.sign
  · have hne : (Decimal.format d).toList ≠ [] := by
      simp [Decimal.format]; split <;> simp [hs, String.toList_ofList]
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨c, cs, hcs, ?_⟩
    have hfirst : c = '-' := by
      simp [Decimal.format] at hcs
      split at hcs <;> simp [hs, String.toList_ofList] at hcs <;> exact hcs.1.symm
    subst hfirst
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · have hsf : d.sign = false := by simp at hs; exact hs
    by_cases hd0 : d.digits = 0
    · have : (Decimal.format d).toList = ['0', 'e', '0'] := by
        simp [Decimal.format, hd0, hsf, String.toList_ofList]
      exact ⟨'0', ['e', '0'], this,
        by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · obtain ⟨dc, crest, hnd, ⟨hge, hle⟩⟩ := natToDigits_first_digit d.digits
      have hne_fmt : (Decimal.format d).toList ≠ [] := by
        simp [Decimal.format, hd0, hsf, String.toList_ofList]
      obtain ⟨fc, fcs, hfcs⟩ := List.exists_cons_of_ne_nil hne_fmt
      have hfc_eq : fc = dc := by
        simp [Decimal.format, hd0, hsf, String.toList_ofList] at hfcs
        rw [hnd] at hfcs
        cases crest with
        | nil => simp at hfcs; exact hfcs.1.symm
        | cons c2 rest' => simp at hfcs; exact hfcs.1.symm
      rw [hfc_eq] at hfcs
      refine ⟨dc, fcs, hfcs, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (intro heq; subst heq; simp (config := { decide := true }) at hge hle)

/-- `formatSerdeNumberF64 sn` output starts with '-' or a digit. -/
private theorem formatSerdeNumberF64_first_char (sn : SerdeNumberF64) :
    ∃ c cs, (formatSerdeNumberF64 sn).toList = c :: cs ∧
      c ≠ 'n' ∧ c ≠ 't' ∧ c ≠ 'f' ∧ c ≠ '"' ∧ c ≠ '[' ∧ c ≠ '{' ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases sn with
  | posInt n =>
    simp only [formatSerdeNumberF64]
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (printNat_ne_nil n)
    refine ⟨c, cs, hcs, ?_⟩
    have hcd := printNat_first_digit n c cs hcs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (intro heq; subst heq; simp (config := { decide := true }) at hcd)
  | negInt n hn =>
    simp only [formatSerdeNumberF64]
    exact ⟨'-', (printNat n.natAbs).toList, by simp [String.toList_append],
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  | float x hfin =>
    simp only [formatSerdeNumberF64]
    exact formatF64_first_char x hfin

/-- THE FLOAT ROUNDTRIP LIFTED TO `parseJV`.

    For any finite F64 x with non-zero Ryu digits, parsing its Ryu-formatted
    output with `parseJV` (the full structural JSON parser, not just
    `parseJsonNumber`) produces `.number jn` where
    `F64.roundToNearestEven jn.toMathRat = x`.

    This closes Concern 3: `parseJV` correctly delegates float-formatted
    numbers to `parseJsonNumber`. -/
theorem parseJV_formatF64 (x : F64) (hfin : F64.isFinite x)
    (hne : (Ryu.ryu x hfin).digits ≠ 0)
    (rest : List Char) (hrest : NonNumContHead rest) (fuel : Nat) (hfuel : fuel ≥ 1) :
    ∃ jn, parseJV ((formatF64 x hfin).toList ++ rest) fuel = some (.number jn, rest) ∧
          F64.roundToNearestEven jn.toMathRat = x := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨c, cs, hcs, hnn, hnt, hnf, hnq, hnlb, hnlc, _, _⟩ :=
    formatF64_first_char x hfin
  rw [hcs, List.cons_append]
  rw [parseJV.eq_10 (c :: (cs ++ rest)) (f + 1)
    (by intro r h; exact hnn (List.cons.inj h).1)
    (by intro r h; exact hnt (List.cons.inj h).1)
    (by intro r h; exact hnf (List.cons.inj h).1)
    (by intro r h; exact hnq (List.cons.inj h).1)
    (by intro r h; exact hnlb (List.cons.inj h).1)
    (by intro r h; exact hnlc (List.cons.inj h).1)
    (by omega)
    (by intro r _ h _; exact hnlb (List.cons.inj h).1)
    (by intro r _ h _; exact hnlc (List.cons.inj h).1)]
  rw [show c :: (cs ++ rest) = (formatF64 x hfin).toList ++ rest by rw [hcs, List.cons_append]]
  set d := Ryu.ryu x hfin
  have hparse := parseJsonNumber_ryu x hfin rest hrest
  simp only [formatF64] at hparse ⊢
  rw [hparse]
  refine ⟨decimalToJsonNumber d.sign d.digits d.exponent, rfl, ?_⟩
  rw [decimalToJsonNumber_toMathRat]
  have h_toF64 : Decimal.toF64 d = F64.roundToNearestEven (Decimal.toRat d) := by
    simp [Decimal.toF64, hne]
  rw [← h_toF64]
  exact Ryu.ryu_roundtrip x hfin

/-- `parseJV` on any serde-formatted number succeeds, producing `.number jn`. -/
theorem parseJV_formatSerdeNumberF64 (sn : SerdeNumberF64)
    (rest : List Char) (hrest : NonNumContHead rest) (fuel : Nat) (hfuel : fuel ≥ 1) :
    ∃ jn, parseJV ((formatSerdeNumberF64 sn).toList ++ rest) fuel
      = some (.number jn, rest) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨c, cs, hcs, hnn, hnt, hnf, hnq, hnlb, hnlc, _, _⟩ :=
    formatSerdeNumberF64_first_char sn
  rw [hcs, List.cons_append]
  rw [parseJV.eq_10 (c :: (cs ++ rest)) (f + 1)
    (by intro r h; exact hnn (List.cons.inj h).1)
    (by intro r h; exact hnt (List.cons.inj h).1)
    (by intro r h; exact hnf (List.cons.inj h).1)
    (by intro r h; exact hnq (List.cons.inj h).1)
    (by intro r h; exact hnlb (List.cons.inj h).1)
    (by intro r h; exact hnlc (List.cons.inj h).1)
    (by omega)
    (by intro r _ h _; exact hnlb (List.cons.inj h).1)
    (by intro r _ h _; exact hnlc (List.cons.inj h).1)]
  rw [show c :: (cs ++ rest) = (formatSerdeNumberF64 sn).toList ++ rest by rw [hcs, List.cons_append]]
  -- Now goal: match parseJsonNumber ... with | some (n, rest) => some (.number n, rest) | none => none
  --           = some (.number jn, rest)
  -- We need to show parseJsonNumber succeeds and then match reduces to some.
  cases sn with
  | posInt n =>
    simp only [formatSerdeNumberF64]
    have hparse := parseJsonNumber_printJsonNumber ⟨(n : Int), 1, by omega⟩ rest (rfl) hrest
    simp only [printJsonNumber, beq_self_eq_true, ↓reduceIte] at hparse
    by_cases hneg : (n : Int) < 0
    · omega
    · simp only [hneg, ↓reduceIte] at hparse
      rw [show (n : Int).natAbs = n from by omega] at hparse
      rw [hparse]
      exact ⟨⟨(n : Int), 1, by omega⟩, rfl⟩
  | negInt n hn =>
    simp only [formatSerdeNumberF64]
    have heq : ("-" ++ printNat n.natAbs) = printJsonNumber ⟨n, 1, by omega⟩ := by
      simp [printJsonNumber, hn]
    rw [heq]
    have hparse := parseJsonNumber_printJsonNumber ⟨n, 1, by omega⟩ rest (rfl) hrest
    rw [hparse]
    exact ⟨⟨n, 1, by omega⟩, rfl⟩
  | float x hfin =>
    simp only [formatSerdeNumberF64, formatF64]
    have hparse := parseJsonNumber_ryu x hfin rest hrest
    rw [hparse]
    exact ⟨_, rfl⟩

/-! ## Concern 2: Exact `json_roundtrip_sorted`

  We strengthen `∃ v', fromJson (toJsonSorted v) = some v'` to:
  `∃ v', fromJson (toJsonSorted v) = some v' ∧ toJson v' = toJsonSorted v`

  The second conjunct says `v'` is the UNIQUE NickelValue whose `toJson`
  output is exactly `toJsonSorted v`. By `json_roundtrip` injectivity,
  this determines `v'` completely.

  Proof: by mutual induction on NickelValue. The key insight:
  every field in `sortJsonFields (toJsonSortedFields fields)` originates from
  `toJsonSortedFields fields` (since sorting is a permutation), and each such
  field has the form `(escapeJsonString k, toJsonSorted v)`. By the IH,
  `fromJson (toJsonSorted v) = some v'` with `toJson v' = toJsonSorted v`.
  Since `fromJsonFields` processes each field independently via `unescapeJsonString`
  and `fromJson`, and `unescapeJsonString ∘ escapeJsonString = some`, we recover
  fields where `toJsonFields result = input`.
-/

/-- Every element of `toJsonSortedFields fields` has the form
    `(escapeJsonString k, toJsonSorted v)` for some original `(k, v)`. -/
private theorem toJsonSortedFields_elem_form
    (fs : List (String × NickelValue)) (kv : String × JsonValue)
    (hmem : kv ∈ toJsonSortedFields fs) :
    ∃ k v, kv = (escapeJsonString k, toJsonSorted v) := by
  induction fs with
  | nil => simp [toJsonSortedFields] at hmem
  | cons f rest ih =>
    obtain ⟨fk, fv⟩ := f
    simp only [toJsonSortedFields, List.mem_cons] at hmem
    rcases hmem with rfl | hmem'
    · exact ⟨fk, fv, rfl⟩
    · exact ih hmem'

/-- `fromJsonFields` recovers fields from a list where each element has the
    form `(escapeJsonString k, toJsonSorted v)`, given that `fromJson ∘ toJsonSorted`
    recovers with `toJson v' = toJsonSorted v` for each value. -/
private theorem fromJsonFields_recover_with
    (jfs : List (String × JsonValue))
    (recover : ∀ kv ∈ jfs, ∃ k v, kv = (escapeJsonString k, toJsonSorted v) ∧
      ∃ v', fromJson (toJsonSorted v) = some v' ∧ toJson v' = toJsonSorted v) :
    ∃ fs', fromJsonFields jfs = some fs' ∧ toJsonFields fs' = jfs := by
  induction jfs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons kv rest ihs =>
    obtain ⟨k, v, hkv, v', hv', hserv⟩ := recover kv (by simp)
    subst hkv
    simp only [fromJsonFields]
    rw [unescape_escape_roundtrip k, hv']
    simp [bind, Option.bind]
    obtain ⟨rest', hrest', hserrest⟩ := ihs (fun kv' hkv' => recover kv' (by simp [hkv']))
    rw [hrest']
    exact ⟨(k, v') :: rest', rfl, by simp [toJsonFields, hserv, hserrest]⟩

/-- Membership in `toJsonSortedFields` implies membership in the original list's values. -/
private theorem mem_values_of_toJsonSortedFields
    (fs : List (String × NickelValue)) (kv : String × JsonValue)
    (hmem : kv ∈ toJsonSortedFields fs) :
    ∃ k v, (k, v) ∈ fs ∧ kv = (escapeJsonString k, toJsonSorted v) := by
  induction fs with
  | nil => simp [toJsonSortedFields] at hmem
  | cons f rest ih =>
    obtain ⟨fk, fv⟩ := f
    simp only [toJsonSortedFields, List.mem_cons] at hmem
    rcases hmem with rfl | hmem'
    · exact ⟨fk, fv, by simp, rfl⟩
    · obtain ⟨k, v, hm, hf⟩ := ih hmem'
      exact ⟨k, v, by simp [hm], hf⟩

mutual
/-- Core mutual induction: `fromJson (toJsonSorted v)` recovers a value
    whose `toJson` equals `toJsonSorted v`.

    The mutual block has three theorems paralleling the nested inductive:
    - `fromJson_toJsonSorted_recover`: for `NickelValue`
    - `fromJsonList_toJsonSorted_recover`: for `List NickelValue`
    - `fromJsonFields_toJsonSorted_recover_all`: for `List (String × NickelValue)`

    The fields theorem provides the IH for ALL values in the field list,
    enabling the record case to work through `fromJsonFields_recover_with`. -/
theorem fromJson_toJsonSorted_recover (v : NickelValue) :
    ∃ v', fromJson (toJsonSorted v) = some v' ∧ toJson v' = toJsonSorted v := by
  cases v with
  | null => exact ⟨.null, rfl, rfl⟩
  | bool b => exact ⟨.bool b, rfl, rfl⟩
  | num n => exact ⟨.num n, rfl, rfl⟩
  | str s =>
    refine ⟨.str s, ?_, ?_⟩
    · simp [toJsonSorted, fromJson, unescape_escape_roundtrip, bind, Option.bind]
    · simp [toJson, toJsonSorted]
  | array elems =>
    obtain ⟨vs', hvs', hser⟩ := fromJsonList_toJsonSorted_recover elems
    refine ⟨.array vs', ?_, ?_⟩
    · simp only [toJsonSorted, fromJson]; rw [hvs']; simp [bind, Option.bind]
    · simp only [toJson, toJsonSorted]; exact congrArg JsonValue.array hser
  | record fields =>
    -- Use the fields-level IH which covers all values in fields
    have hih := fromJsonFields_toJsonSorted_recover_all fields
    -- Each element of sortJsonFields (toJsonSortedFields fields) comes from
    -- toJsonSortedFields fields (by mergeSort_perm), and by mem_values_of_toJsonSortedFields
    -- it originates from a (k, v) ∈ fields.
    have helem : ∀ kv ∈ sortJsonFields (toJsonSortedFields fields),
        ∃ k v, kv = (escapeJsonString k, toJsonSorted v) ∧
          ∃ v', fromJson (toJsonSorted v) = some v' ∧ toJson v' = toJsonSorted v := by
      intro kv hkv
      have hperm := List.mergeSort_perm
        (le := fun (a b : String × JsonValue) => decide (a.1 ≤ b.1))
        (toJsonSortedFields fields)
      obtain ⟨k, v, hmem_orig, hform⟩ := mem_values_of_toJsonSortedFields fields kv (hperm.mem_iff.mp hkv)
      have hv_mem : v ∈ fields.map Prod.snd :=
        List.mem_map.mpr ⟨(k, v), hmem_orig, rfl⟩
      exact ⟨k, v, hform, hih v hv_mem⟩
    obtain ⟨fs', hfs', hser⟩ := fromJsonFields_recover_with _ helem
    refine ⟨.record fs', ?_, ?_⟩
    · simp only [toJsonSorted, fromJson]; rw [hfs']; simp [bind, Option.bind]
    · simp only [toJson, toJsonSorted]; exact congrArg JsonValue.object hser

theorem fromJsonList_toJsonSorted_recover (vs : List NickelValue) :
    ∃ vs', fromJsonList (toJsonSortedList vs) = some vs' ∧
           toJsonList vs' = toJsonSortedList vs := by
  cases vs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons v rest =>
    obtain ⟨v', hv', hserv⟩ := fromJson_toJsonSorted_recover v
    obtain ⟨rest', hrest', hserrest⟩ := fromJsonList_toJsonSorted_recover rest
    refine ⟨v' :: rest', ?_, ?_⟩
    · simp only [toJsonSortedList, fromJsonList]; rw [hv']; simp [bind, Option.bind]; rw [hrest']
    · simp only [toJsonList, toJsonSortedList, List.cons.injEq]; exact ⟨hserv, hserrest⟩

/-- The IH for all values in a field list: for every `(k, v)` in `fields`,
    the recovery theorem holds for `v`. Structural recursion on the field list. -/
theorem fromJsonFields_toJsonSorted_recover_all
    (fields : List (String × NickelValue))
    (v : NickelValue)
    (hmem : v ∈ fields.map Prod.snd) :
    ∃ v', fromJson (toJsonSorted v) = some v' ∧ toJson v' = toJsonSorted v := by
  cases fields with
  | nil => simp at hmem
  | cons kv rest =>
    simp only [List.map_cons, List.mem_cons] at hmem
    rcases hmem with rfl | hmem'
    · exact fromJson_toJsonSorted_recover kv.2
    · exact fromJsonFields_toJsonSorted_recover_all rest v hmem'
end

/-- THE EXACT SORTED ROUNDTRIP.

    Strengthens `json_roundtrip_sorted` from existential to constructive:
    `fromJson (toJsonSorted v)` produces a definite value `v'` satisfying
    `toJson v' = toJsonSorted v`.

    This means `v'` is the UNIQUE NickelValue whose `toJson` serialization
    equals the sorted serialization of `v`. By `json_roundtrip` injectivity
    (`fromJson ∘ toJson = some`), this `v'` is completely determined.

    The relationship:
    - `toJsonSorted v` = sorted serialization of `v`
    - `v'` = deserialization of the sorted serialization
    - `toJson v'` = re-serialization agrees with the sorted serialization
    - `fromJson (toJson v') = some v'` (by `json_roundtrip`) -/
theorem json_roundtrip_sorted_exact (v : NickelValue) :
    ∃ v', fromJson (toJsonSorted v) = some v' ∧ toJson v' = toJsonSorted v :=
  fromJson_toJsonSorted_recover v

/-- Corollary: the sorted roundtrip value is a fixed point of `fromJson ∘ toJson`. -/
theorem json_roundtrip_sorted_fixpoint (v : NickelValue) :
    ∃ v', fromJson (toJsonSorted v) = some v' ∧
          fromJson (toJson v') = some v' := by
  obtain ⟨v', hfrom, _⟩ := json_roundtrip_sorted_exact v
  exact ⟨v', hfrom, json_roundtrip v'⟩
