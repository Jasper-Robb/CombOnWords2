import CombOnWords2.FreeMonoid
import MathlibExtras.LibrarySearch

abbrev Word (α : Type*) [Fintype α] := FreeMonoid α

variable {α : Type*} [Fintype α] 

def Overlap (w : Word α) : Prop :=
  ∃ (B : Word α), 0 < |B| ∧ w = B * B * B.take 1

theorem chapter1_question2 (u : Word α) (hu : Overlap u)
    : ∃ (v w z : Word α), u = w * v ∧ u = z * w ∧ |w| > |v| := by
  rcases hu with ⟨B, hBl, hBr⟩
  apply Exists.intro <| B.drop 1 * B.take 1
  apply Exists.intro <| B * B.take 1
  apply Exists.intro <| B
  apply And.intro
  · conv => rw [← mul_assoc]; rhs; lhs; rw [mul_assoc]
    simpa only [freemonoid_to_list, List.take_append_drop]
  apply And.intro
  · rwa [← mul_assoc]
  · simpa [freemonoid_to_list] using Nat.sub_lt hBl Nat.one_pos

theorem chapter1_question3 (u : Word α) (hu : Overlap u)
    : (∃ (x : Word α), 0 < |x| ∧ u = x * x * x) ∨ 
      (∃ (x y : Word α), 0 < |x| ∧ 0 < |y| ∧ u = x * y * x * y * x) := by
  rcases hu with ⟨B, hBr, hBl⟩
  cases eq_or_ne |B| 1 with
  | inl h =>
    apply Or.inl
    apply Exists.intro B
    apply And.intro
    · exact hBr
    · simpa [hBl] using List.take_length_le <| Nat.le_of_eq h
  | inr h =>
    apply Or.inr
    apply Exists.intro <| B.take 1
    apply Exists.intro <| B.drop 1
    apply And.intro
    · simpa [freemonoid_to_list]
    apply And.intro
    · simpa [freemonoid_to_list] using Nat.lt_of_le_of_ne hBr h.symm
    · conv => rhs; lhs; rw [mul_assoc]
      simpa only [freemonoid_to_list, List.take_append_drop]
