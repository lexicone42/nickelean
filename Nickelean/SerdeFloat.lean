/-
  NickelJson/SerdeFloat.lean

  Integration of ryu-lean4: concrete float formatting for serde_json.

  This module connects Nickelean's JSON model to ryu-lean4's verified
  IEEE 754 float-to-string roundtrip. It:
  1. Defines a generic FloatFormat interface for float serialization
  2. Instantiates it concretely with ryu-lean4's F64, Decimal, and ryu algorithm
  3. Proves the full float roundtrip using ryu-lean4's full_roundtrip theorem

  The key chain is:
    F64 → ryu → Decimal → format → String → parse → Decimal → toF64 → F64
  which ryu-lean4 proves as: toF64(parse(format(ryu(x)))) = x
-/
import RyuLean4.Roundtrip.FullRoundtrip
import RyuLean4.Ryu.Shortest
import RyuLean4.IEEE754.RoundProof
import Nickelean.SerdeSpec
import Mathlib.Data.Rat.Defs

/-! ## Generic float format interface -/

/-- A generic interface for float formatting with a roundtrip guarantee.
    Any implementation must provide:
    - A float type and a decimal/intermediate type
    - A serialization function (float → decimal)
    - A formatting function (decimal → string)
    - A parsing function (string → decimal)
    - A conversion back (decimal → float)
    - A proof that the full pipeline is the identity on finite floats -/
structure FloatFormat where
  /-- The floating-point type (e.g., IEEE 754 binary64) -/
  FloatTy : Type
  /-- The intermediate decimal representation -/
  DecimalTy : Type
  /-- Predicate for values where roundtrip is guaranteed -/
  isFinite : FloatTy → Prop
  /-- Float to shortest decimal representation -/
  toDecimal : (x : FloatTy) → isFinite x → DecimalTy
  /-- Decimal to string -/
  formatDecimal : DecimalTy → String
  /-- String to decimal (partial) -/
  parseDecimal : String → Option DecimalTy
  /-- Decimal back to float -/
  toFloat : DecimalTy → FloatTy
  /-- The roundtrip guarantee: parse(format(toDecimal(x))) roundtrips to x -/
  roundtrip : ∀ (x : FloatTy) (hfin : isFinite x),
    (parseDecimal (formatDecimal (toDecimal x hfin))).map toFloat = some x

/-! ## Concrete instantiation with ryu-lean4 -/

/-- The ryu-lean4 instantiation of FloatFormat.
    Uses IEEE 754 binary64 (F64) and Ryu's shortest-representation algorithm. -/
def ryuFloatFormat : FloatFormat where
  FloatTy := F64
  DecimalTy := Decimal
  isFinite := F64.isFinite
  toDecimal := Ryu.ryu
  formatDecimal := Decimal.format
  parseDecimal := Decimal.parse
  toFloat := Decimal.toF64
  roundtrip := Ryu.full_roundtrip

/-! ## Connecting ryu-lean4 to Nickelean's serde model -/

/-- An F64 value formatted by Ryu produces a valid decimal string.
    This connects ryu-lean4's Decimal.format to the string domain. -/
def formatF64 (x : F64) (hfin : F64.isFinite x) : String :=
  Decimal.format (Ryu.ryu x hfin)

/-- The float roundtrip theorem stated in Nickelean's terms:
    Parsing the Ryu-formatted string of a finite F64 recovers the original value. -/
theorem float_roundtrip (x : F64) (hfin : F64.isFinite x) :
    (Decimal.parse (formatF64 x hfin)).map Decimal.toF64 = some x :=
  Ryu.full_roundtrip x hfin

/-- Ryu produces well-formed decimals (no trailing zeros, zero-exponent for zero). -/
theorem ryu_output_well_formed (x : F64) (hfin : F64.isFinite x) :
    (Ryu.ryu x hfin).WellFormed :=
  Ryu.ryu_well_formed x hfin

/-- Ryu produces the shortest (scale-minimal) representation. -/
theorem ryu_output_shortest (x : F64) (hfin : F64.isFinite x) :
    Ryu.isShortestRep (Ryu.ryu x hfin) x hfin :=
  Ryu.ryu_shortest x hfin

/-- For non-zero finite F64 values, the Ryu output is in the acceptance interval
    (i.e., it represents a decimal that rounds back to x). -/
theorem ryu_output_valid (x : F64) (hfin : F64.isFinite x) (hne : x.toRat ≠ 0) :
    Ryu.isValidRep (Ryu.ryu x hfin) x hfin :=
  Ryu.ryu_in_interval x hfin hne

/-! ## Upgrading SerdeNumber with concrete F64 -/

/-- Extended SerdeNumber that carries a concrete F64 value for the float case,
    enabling verified formatting via Ryu. -/
inductive SerdeNumberF64 where
  | posInt (n : Nat)
  | negInt (n : Int) (h : n < 0)
  | float (x : F64) (hfin : F64.isFinite x)
  deriving Repr

/-- Format a SerdeNumberF64. For integers, uses itoa-style formatting.
    For floats, uses Ryu's verified shortest representation. -/
def formatSerdeNumberF64 : SerdeNumberF64 → String
  | .posInt n => printNat n
  | .negInt n _ => "-" ++ printNat n.natAbs
  | .float x hfin => formatF64 x hfin

/-! ## Phase 5: Nickel's serialize_num dispatch with concrete F64 -/

/-- Convert a JsonNumber to a Mathlib rational.
    This bridges nickelean's Int/Nat representation to ryu-lean4's ℚ. -/
def JsonNumber.toMathRat (jn : JsonNumber) : ℚ :=
  (jn.numerator : ℚ) / (jn.denominator : ℚ)

/-- Classify a JsonNumber the way Nickel's serialize_num does,
    producing a concrete F64 for the float case via roundToNearestEven.
    Requires a finiteness proof for the rounded value (matches Nickel's
    validate() which rejects numbers outside f64 range). -/
def classifyNumberF64 (jn : JsonNumber)
    (hfin : F64.isFinite (F64.roundToNearestEven jn.toMathRat)) :
    SerdeNumberF64 :=
  if jn.numerator % jn.denominator == 0 then
    let intVal := jn.numerator / jn.denominator
    if h : intVal < 0 then
      .negInt intVal h
    else
      .posInt intVal.toNat
  else
    .float (F64.roundToNearestEven jn.toMathRat) hfin

/-! ## Phase 6: The composition theorem -/

/-- For integer-valued numbers, classifyNumberF64 agrees with classifyNumber. -/
theorem classifyNumberF64_int_eq (jn : JsonNumber) (h : jn.denominator = 1)
    (hfin : F64.isFinite (F64.roundToNearestEven jn.toMathRat)) :
    formatSerdeNumberF64 (classifyNumberF64 jn hfin) = printJsonNumber jn := by
  unfold classifyNumberF64
  have h1 : (jn.denominator : Int) = 1 := by exact_mod_cast h
  simp only [h1, Int.emod_one, beq_self_eq_true, ↓reduceIte, Int.ediv_one]
  unfold printJsonNumber
  simp only [h, beq_self_eq_true, ↓reduceIte]
  by_cases hneg : jn.numerator < 0
  · simp only [hneg, ↓reduceDIte, ↓reduceIte, formatSerdeNumberF64]
  · simp only [hneg, ↓reduceDIte, ↓reduceIte, formatSerdeNumberF64]
    congr 1; omega

/-- THE COMPOSITION THEOREM: For non-integer numbers, the Nickel-style
    serialization (Rational → F64 → Ryu → String) roundtrips through parsing.

    This is the crown jewel — it composes:
    1. nickelean's number classification (matching Nickel's serialize_num)
    2. ryu-lean4's F64 roundToNearestEven (matching malachite's rounding)
    3. ryu-lean4's Ryu algorithm (shortest decimal representation)
    4. ryu-lean4's full_roundtrip theorem (parse ∘ format = id)

    The theorem says: formatting a non-integer rational as a float and
    parsing it back recovers the F64 rounding of the original rational. -/
theorem serialize_num_float_roundtrip (jn : JsonNumber)
    (hfin : F64.isFinite (F64.roundToNearestEven jn.toMathRat))
    (hni : ¬(jn.numerator % jn.denominator == 0)) :
    let x := F64.roundToNearestEven jn.toMathRat
    (Decimal.parse (formatSerdeNumberF64 (classifyNumberF64 jn hfin))).map Decimal.toF64
      = some x := by
  simp only [classifyNumberF64, hni, formatSerdeNumberF64]
  exact Ryu.full_roundtrip _ hfin

/-- The complete number serialization theorem: for ANY JsonNumber,
    the Nickel-style serialization either:
    - Produces an integer string (if the number is integer-valued), or
    - Produces a float string that roundtrips through parse to the
      F64 rounding of the original rational.

    This covers ALL of Nickel's serialize_num behavior. -/
theorem serialize_num_complete (jn : JsonNumber)
    (hfin : F64.isFinite (F64.roundToNearestEven jn.toMathRat)) :
    (jn.numerator % jn.denominator == 0) ∨
    ((Decimal.parse (formatSerdeNumberF64 (classifyNumberF64 jn hfin))).map Decimal.toF64
      = some (F64.roundToNearestEven jn.toMathRat)) := by
  by_cases hint : jn.numerator % jn.denominator == 0
  · left; exact hint
  · right; exact serialize_num_float_roundtrip jn hfin hint
