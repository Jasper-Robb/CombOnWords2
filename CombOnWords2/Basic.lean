import CombOnWords2.simp_attr
import MathlibExtras.LibrarySearch

abbrev Word (α : Type*) [Fintype α] := FreeMonoid α

variable {α : Type*} [Fintype α] 

@[word_to_list]
def Word.toList (w : Word α) : List α := w

@[word_to_list]
def Word.one_eq_nil : (1 : Word α) = ([] : List α) := rfl

@[word_to_list]
theorem word_mul_eq_list_append (v w : Word α)
    : v * w = v.toList ++ w.toList :=
  rfl

@[word_to_list]
def FreeMonoidToList : FreeMonoid β = List β := rfl

def Word.length' : Word α →* Multiplicative ℕ where
  toFun    := List.length
  map_one' := List.length_nil
  map_mul' := List.length_append

def Word.length (w : Word α) : ℕ := Word.length' w

-- Macro for length w as |w|
macro:max atomic("|" noWs) a:term noWs "|" : term => `(Word.length $a)
def FreeMonoid.length.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()

@[word_to_list]
theorem word_length_eq_list_length (w : Word α) : w.length = List.length w :=
  rfl

def Word.join : FreeMonoid (Word α) →* Word α where
  toFun    := List.join
  map_one' := List.join_nil
  map_mul' := List.join_append

@[word_to_list]
theorem word_join_eq_list_join (w : FreeMonoid (Word α)) : w.join = List.join w :=
  rfl

def Word.take (a : ℕ) (w : Word α) : Word α := List.take a w

@[word_to_list]
theorem word_take_eq_list_take (a : ℕ) (w : Word α) : w.take a = List.take a w :=
  rfl

def Word.drop (a : ℕ) (w : Word α) : Word α := List.drop a w

@[word_to_list]
theorem word_drop_eq_list_drop (a : ℕ) (w : Word α) : w.drop a = List.drop a w :=
  rfl

def Overlap (w : Word α) : Prop :=
  ∃ (B : Word α), B ≠ 1 ∧ w = B * B * B.take 1

theorem chapter1_q2 (u : Word α) (hu : Overlap u)
    : ∃ (v w z : Word α), u = w * v ∧ u = z * w ∧ |w| > |v| := by
  rcases hu with ⟨B, hBl, hBr⟩
  apply Exists.intro <| B.drop 1 * B.take 1
  apply Exists.intro <| B * B.take 1
  apply Exists.intro <| B
  apply And.intro
  · conv => rw [← mul_assoc]; rhs; lhs; rw [mul_assoc]
    simpa only [word_to_list, List.take_append_drop]
  apply And.intro
  · rwa [← mul_assoc]
  · simpa [word_to_list] using Nat.sub_lt (List.length_pos.mpr hBl) Nat.one_pos

theorem chapter1_q3 (u : Word α) (hu : Overlap u)
    : (∃ (x : Word α), x ≠ 1 ∧ u = x * x * x) ∨ 
      (∃ (x y : Word α), x ≠ 1 ∧ y ≠ 1 ∧ u = x * y * x * y * x) := by
  rcases hu with ⟨B, hBr, hBl⟩
  cases eq_or_ne |B| 1 with
  | inl h =>
    apply Or.inl
    apply Exists.intro B
    apply And.intro
    · exact List.length_pos.mp <| Nat.lt_of_sub_eq_succ h
    · simpa [hBl] using List.take_length_le <| Nat.le_of_eq h
  | inr h =>
    apply Or.inr
    apply Exists.intro <| B.take 1
    apply Exists.intro <| B.drop 1
    apply And.intro
    · apply List.length_pos.mp
      simpa [word_to_list] using List.length_pos.mpr hBr
    apply And.intro
    · apply List.length_pos.mp
      simpa [word_to_list] using Nat.lt_of_le_of_ne (List.length_pos.mpr hBr) h.symm
    · conv => rhs; lhs; rw [mul_assoc]
      simpa only [word_to_list, List.take_append_drop]
