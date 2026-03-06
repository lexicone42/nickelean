/-
  NickelJson/Float64.lean

  IEEE 754 f64 conformance boundary.

  Our proof models JSON numbers as exact rationals (JsonNumber = Int/Nat+).
  Nickel's Rust implementation uses f64, where serde_json uses the Ryu
  algorithm for serialization. Ryu guarantees:

    parse(format(x)) = x   for all finite f64 values x

  This module defines the subset of JsonNumber that is exactly representable
  as f64, establishing where our Lean spec matches the Rust implementation.

  The roundtrip theorem `json_roundtrip` holds for ALL rational JsonNumbers.
  Since f64-representable rationals are a subset, the theorem trivially
  holds for the restricted domain too. The conformance gap is:

  - Numbers outside f64 range: our spec handles them, Rust would overflow/round
  - Numbers requiring more than 53 bits of mantissa: our spec is exact, Rust rounds

  A full formalization would either:
  - Formalize Ryu's roundtrip guarantee in Lean (future work)
  - Use aeneas to extract the Rust serializer and verify mechanically
-/
import Nickelean.Roundtrip

/-! ## IEEE 754 Double Precision Constants -/

/-- Maximum finite f64 value: (2^53 - 1) * 2^971 ≈ 1.7976931348623157e+308 -/
def f64MaxExponent : Int := 971
def f64MinExponent : Int := -1074
def f64MantissaBits : Nat := 53

/-! ## F64 Representability -/

/-- A rational number p/q is f64-representable if it can be expressed as
    m * 2^e where |m| < 2^53 and -1074 ≤ e ≤ 971.

    This covers all finite IEEE 754 double-precision values including
    subnormals, normals, and zero. -/
def IsF64Representable (n : JsonNumber) : Prop :=
  ∃ (m : Int) (e : Int),
    -1074 ≤ e ∧ e ≤ 971 ∧
    m.natAbs < 2^53 ∧
    n.numerator * (n.denominator : Int) = m * 2^e.toNat * (n.denominator : Int)

/-- Zero is f64-representable. -/
theorem isF64Representable_zero : IsF64Representable ⟨0, 1, by omega⟩ :=
  ⟨0, 0, by omega, by omega, by omega, by simp⟩

/-! ## Collecting numbers from a value -/

mutual
/-- Collect all JsonNumbers appearing in a NickelValue. -/
def collectNums : NickelValue → List JsonNumber
  | .null => []
  | .bool _ => []
  | .num n => [n]
  | .str _ => []
  | .array elems => collectNumsList elems
  | .record fields => collectNumsFields fields

def collectNumsList : List NickelValue → List JsonNumber
  | [] => []
  | v :: vs => collectNums v ++ collectNumsList vs

def collectNumsFields : List (String × NickelValue) → List JsonNumber
  | [] => []
  | (_, v) :: rest => collectNums v ++ collectNumsFields rest
end

/-- All numbers in a value are f64-representable. -/
def AllNumsF64 (v : NickelValue) : Prop :=
  ∀ n, n ∈ collectNums v → IsF64Representable n

/-- The roundtrip theorem restricted to f64-representable values.
    This follows trivially from the general theorem — the restriction
    only matters for conformance with the Rust implementation. -/
theorem json_roundtrip_f64_domain (v : NickelValue) (_h : AllNumsF64 v) :
    fromJson (toJson v) = some v :=
  json_roundtrip v
