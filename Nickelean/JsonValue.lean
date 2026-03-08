/-
  NickelJson/JsonValue.lean

  JSON abstract syntax tree. This is the "wire format" — the intermediate
  representation between NickelValue and serialized JSON text.

  Numbers are modeled as integer numerator / positive denominator (rationals).
  This sidesteps IEEE 754 issues for the initial proof. The conformance layer
  (Layer 3) documents where f64 diverges.
-/

/-- A JSON number represented as a rational: numerator / denominator. -/
structure JsonNumber where
  numerator : Int
  denominator : Nat
  den_pos : denominator > 0
  deriving Repr

/-- Syntactic equality: 1/2 ≠ 2/4. This is intentional — the roundtrip
    theorem preserves the exact representation, not the rational value.
    For semantic equality, normalize to lowest terms first. -/
instance : BEq JsonNumber where
  beq a b := a.numerator == b.numerator && a.denominator == b.denominator

instance : DecidableEq JsonNumber := fun a b => by
  cases a; cases b
  simp [JsonNumber.mk.injEq]
  exact inferInstance

/-- JSON value AST, mirroring the JSON spec (RFC 8259). -/
inductive JsonValue where
  | null
  | bool (b : Bool)
  | number (n : JsonNumber)
  | string (s : String)
  | array (elems : List JsonValue)
  | object (fields : List (String × JsonValue))
  deriving Repr, BEq
