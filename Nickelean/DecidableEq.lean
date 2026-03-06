/-
  NickelJson/DecidableEq.lean

  DecidableEq instances for JsonValue and NickelValue.
  These can't be auto-derived due to nested inductives (List JsonValue, etc.)
  so we define them manually via mutual recursion.
-/
import Nickelean.Value

mutual
private def jsonValueDecEq : (a b : JsonValue) → Decidable (a = b)
  | .null, .null => isTrue rfl
  | .bool a, .bool b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun h' => by cases h'; exact h rfl)
  | .number a, .number b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun h' => by cases h'; exact h rfl)
  | .string a, .string b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun h' => by cases h'; exact h rfl)
  | .array as_, .array bs =>
    match jsonValueListDecEq as_ bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun h' => by cases h'; exact h rfl)
  | .object as_, .object bs =>
    match jsonValueFieldsDecEq as_ bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun h' => by cases h'; exact h rfl)
  -- Cross-constructor cases: all false
  | .null, .bool _ => isFalse JsonValue.noConfusion
  | .null, .number _ => isFalse JsonValue.noConfusion
  | .null, .string _ => isFalse JsonValue.noConfusion
  | .null, .array _ => isFalse JsonValue.noConfusion
  | .null, .object _ => isFalse JsonValue.noConfusion
  | .bool _, .null => isFalse JsonValue.noConfusion
  | .bool _, .number _ => isFalse JsonValue.noConfusion
  | .bool _, .string _ => isFalse JsonValue.noConfusion
  | .bool _, .array _ => isFalse JsonValue.noConfusion
  | .bool _, .object _ => isFalse JsonValue.noConfusion
  | .number _, .null => isFalse JsonValue.noConfusion
  | .number _, .bool _ => isFalse JsonValue.noConfusion
  | .number _, .string _ => isFalse JsonValue.noConfusion
  | .number _, .array _ => isFalse JsonValue.noConfusion
  | .number _, .object _ => isFalse JsonValue.noConfusion
  | .string _, .null => isFalse JsonValue.noConfusion
  | .string _, .bool _ => isFalse JsonValue.noConfusion
  | .string _, .number _ => isFalse JsonValue.noConfusion
  | .string _, .array _ => isFalse JsonValue.noConfusion
  | .string _, .object _ => isFalse JsonValue.noConfusion
  | .array _, .null => isFalse JsonValue.noConfusion
  | .array _, .bool _ => isFalse JsonValue.noConfusion
  | .array _, .number _ => isFalse JsonValue.noConfusion
  | .array _, .string _ => isFalse JsonValue.noConfusion
  | .array _, .object _ => isFalse JsonValue.noConfusion
  | .object _, .null => isFalse JsonValue.noConfusion
  | .object _, .bool _ => isFalse JsonValue.noConfusion
  | .object _, .number _ => isFalse JsonValue.noConfusion
  | .object _, .string _ => isFalse JsonValue.noConfusion
  | .object _, .array _ => isFalse JsonValue.noConfusion

private def jsonValueListDecEq : (a b : List JsonValue) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => nomatch h)
  | _ :: _, [] => isFalse (fun h => nomatch h)
  | a :: as_, b :: bs =>
    match jsonValueDecEq a b, jsonValueListDecEq as_ bs with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h, _ => isFalse (fun h' => by cases h'; exact h rfl)
    | _, isFalse h => isFalse (fun h' => by cases h'; exact h rfl)

private def jsonValueFieldsDecEq :
    (a b : List (String × JsonValue)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => nomatch h)
  | _ :: _, [] => isFalse (fun h => nomatch h)
  | (k1, v1) :: as_, (k2, v2) :: bs =>
    match instDecidableEqString k1 k2, jsonValueDecEq v1 v2, jsonValueFieldsDecEq as_ bs with
    | isTrue hk, isTrue hv, isTrue hr => isTrue (hk ▸ hv ▸ hr ▸ rfl)
    | isFalse h, _, _ => isFalse (fun h' => by
        cases h'; exact h rfl)
    | _, isFalse h, _ => isFalse (fun h' => by
        cases h'; exact h rfl)
    | _, _, isFalse h => isFalse (fun h' => by
        cases h'; exact h rfl)
end

instance : DecidableEq JsonValue := jsonValueDecEq

-- NickelValue DecidableEq follows the same pattern
mutual
private def nickelValueDecEq : (a b : NickelValue) → Decidable (a = b)
  | .null, .null => isTrue rfl
  | .bool a, .bool b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun h' => by cases h'; exact h rfl)
  | .num a, .num b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun h' => by cases h'; exact h rfl)
  | .str a, .str b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun h' => by cases h'; exact h rfl)
  | .array as_, .array bs =>
    match nickelValueListDecEq as_ bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun h' => by cases h'; exact h rfl)
  | .record as_, .record bs =>
    match nickelValueFieldsDecEq as_ bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun h' => by cases h'; exact h rfl)
  | .null, .bool _ => isFalse NickelValue.noConfusion
  | .null, .num _ => isFalse NickelValue.noConfusion
  | .null, .str _ => isFalse NickelValue.noConfusion
  | .null, .array _ => isFalse NickelValue.noConfusion
  | .null, .record _ => isFalse NickelValue.noConfusion
  | .bool _, .null => isFalse NickelValue.noConfusion
  | .bool _, .num _ => isFalse NickelValue.noConfusion
  | .bool _, .str _ => isFalse NickelValue.noConfusion
  | .bool _, .array _ => isFalse NickelValue.noConfusion
  | .bool _, .record _ => isFalse NickelValue.noConfusion
  | .num _, .null => isFalse NickelValue.noConfusion
  | .num _, .bool _ => isFalse NickelValue.noConfusion
  | .num _, .str _ => isFalse NickelValue.noConfusion
  | .num _, .array _ => isFalse NickelValue.noConfusion
  | .num _, .record _ => isFalse NickelValue.noConfusion
  | .str _, .null => isFalse NickelValue.noConfusion
  | .str _, .bool _ => isFalse NickelValue.noConfusion
  | .str _, .num _ => isFalse NickelValue.noConfusion
  | .str _, .array _ => isFalse NickelValue.noConfusion
  | .str _, .record _ => isFalse NickelValue.noConfusion
  | .array _, .null => isFalse NickelValue.noConfusion
  | .array _, .bool _ => isFalse NickelValue.noConfusion
  | .array _, .num _ => isFalse NickelValue.noConfusion
  | .array _, .str _ => isFalse NickelValue.noConfusion
  | .array _, .record _ => isFalse NickelValue.noConfusion
  | .record _, .null => isFalse NickelValue.noConfusion
  | .record _, .bool _ => isFalse NickelValue.noConfusion
  | .record _, .num _ => isFalse NickelValue.noConfusion
  | .record _, .str _ => isFalse NickelValue.noConfusion
  | .record _, .array _ => isFalse NickelValue.noConfusion

private def nickelValueListDecEq : (a b : List NickelValue) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => nomatch h)
  | _ :: _, [] => isFalse (fun h => nomatch h)
  | a :: as_, b :: bs =>
    match nickelValueDecEq a b, nickelValueListDecEq as_ bs with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h, _ => isFalse (fun h' => by cases h'; exact h rfl)
    | _, isFalse h => isFalse (fun h' => by cases h'; exact h rfl)

private def nickelValueFieldsDecEq :
    (a b : List (String × NickelValue)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => nomatch h)
  | _ :: _, [] => isFalse (fun h => nomatch h)
  | (k1, v1) :: as_, (k2, v2) :: bs =>
    match instDecidableEqString k1 k2, nickelValueDecEq v1 v2, nickelValueFieldsDecEq as_ bs with
    | isTrue hk, isTrue hv, isTrue hr => isTrue (hk ▸ hv ▸ hr ▸ rfl)
    | isFalse h, _, _ => isFalse (fun h' => by cases h'; exact h rfl)
    | _, isFalse h, _ => isFalse (fun h' => by cases h'; exact h rfl)
    | _, _, isFalse h => isFalse (fun h' => by cases h'; exact h rfl)
end

instance : DecidableEq NickelValue := nickelValueDecEq
