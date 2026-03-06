/-
  NickelJson/Value.lean

  The Nickel value type — the subset of Nickel's runtime values that can be
  serialized to JSON. This is the domain of the roundtrip theorem.

  Mirrors the relevant variants of `nickel_lang_core::term::RichTerm` after
  evaluation, restricted to JSON-serializable forms.
-/
import Nickelean.JsonValue

/-- A Nickel value that can be serialized to JSON. -/
inductive NickelValue where
  | null
  | bool (b : Bool)
  | num (n : JsonNumber)
  | str (s : String)
  | array (elems : List NickelValue)
  | record (fields : List (String × NickelValue))
  deriving Repr, BEq
