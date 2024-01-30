import CombOnWords2.FreeMonoid
import MathlibExtras.LibrarySearch

abbrev Word (α : Type*) [Fintype α] := FreeMonoid α

variable {α : Type*} [Fintype α] 

def Overlap (w : Word α) : Prop :=
  ∃ (B : Word α), 0 < |B| ∧ w = B * B * B.take 1

def HasOverlap (w : Word α) : Prop :=
  ∃ (B : Word α), 0 < |B| ∧ B * B * B.take 1 <:*: w

def μ : Monoid.End (Word (Fin 2)) := 
  FreeMonoid.join ∘* FreeMonoid.map (fun x => if x = 0 then [0, 1] else [1, 0])

theorem μ_nonerasing : FreeMonoid.NonErasing μ := by
  apply FreeMonoid.join_map_nonerasing
  intro x
  fin_cases x <;> exact Nat.succ_pos 1

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

theorem chapter1_question4 (v : Word (Fin 2)) (hv : HasOverlap v)
    : HasOverlap (μ v) := by
  rcases hv with ⟨B, hBl, hBr⟩
  apply Exists.intro <| μ B
  apply And.intro
  · exact μ_nonerasing B hBl
  · have : μ B * μ B * (μ B).take 1 <*: μ B * μ B * μ (B.take 1) := by
      apply (List.prefix_append_right_inj (μ B * μ B)).mpr
      cases B with
      | nil => contradiction
      | cons x xs =>
        conv => lhs; change (μ (FreeMonoid.ofList (x :: xs))).take 1
        rw [FreeMonoid.ofList_cons, map_mul]
        simp only [freemonoid_to_list, List.take_cons_succ, List.take_zero]
        rw [List.take_append_of_le_length]
        · fin_cases x <;> decide
        · fin_cases x <;> decide
    apply List.IsInfix.trans (List.IsPrefix.isInfix this)
    simp only [← map_mul]
    exact FreeMonoid.is_infix_congr hBr μ
