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
import Nickelean.SerdeSpec

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
