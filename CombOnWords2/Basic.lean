import CombOnWords2.FreeMonoid
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Parity

abbrev Word (α : Type*) [Fintype α] := FreeMonoid α


variable {α : Type*} [Fintype α] 


def toWord (n : ℕ) (l : List (Fin n)) : Word (Fin n) := l

infix:75 " $↑ " => toWord


def Overlap (w : Word α) : Prop :=
  ∃ (B : Word α), 0 < |B| ∧ w = B * B * B.take 1

def HasOverlap (w : Word α) : Prop :=
  ∃ (B : Word α), 0 < |B| ∧ B * B * B.take 1 <:*: w


theorem length_odd_of_overlap (w : Word α) (hw : Overlap w) : Odd |w| := by
  rcases hw with ⟨B, hBl, hBr⟩
  change 1 ≤ List.length B at hBl
  simp only [freemonoid_to_list, hBr, List.length_append, 
             ← Nat.two_mul, List.length_take, Nat.min_eq_left hBl]
  exists |B|

theorem overlap_iff (u : Word α) : Overlap u ↔ 2 < |u| ∧ u = u.take (|u| / 2) ^ 2 * u.take 1 := by
  constructor
  · intro ⟨B, hBl, hBr⟩
    simp only [freemonoid_to_list] at *
    constructor
    · simp only [hBr, List.length_append, List.length_take, Nat.min_eq_left hBl]
      apply lt_add_of_tsub_lt_right
      simpa [← Nat.two_mul] using one_lt_mul_of_lt_of_le Nat.one_lt_two hBl
    · change 1 ≤ List.length B at hBl
      have huB₁ : List.take (List.length u / 2) u = B := by
        rw [hBr, List.append_assoc, List.take_append_of_le_length]
        all_goals simp only [List.length_append, List.length_take, Nat.min_eq_left hBl,
                             ← add_assoc, ← Nat.two_mul, zero_lt_two, Nat.add_div, 
                             Nat.mul_div_right, Nat.mul_mod_right]
        apply List.take_length
        rfl
      have huB₂ : List.take 1 u = List.take 1 B := by
        rwa [hBr, List.append_assoc, List.take_append_of_le_length]
      rwa [sq, huB₁, huB₂]
  · intro ⟨hlu, hu⟩
    exists u.take (|u| / 2)
    simp only [freemonoid_to_list, sq] at *
    constructor
    · simp only [List.length_take, lt_min_iff]
      exact ⟨Nat.div_pos (Nat.le_of_lt hlu) Nat.two_pos, Nat.zero_lt_of_lt hlu⟩
    · nth_rewrite 1 [hu]
      rw [List.append_right_inj, List.take_take, Nat.min_eq_left]
      exact @Nat.div_le_div_right 2 |u| 2 <| Nat.le_of_lt hlu

theorem factor_no_overlap_of_no_overlap (v w : Word α) (hw : ¬HasOverlap w) (hvw : v <:*: w)
    : ¬HasOverlap v :=
  fun ⟨B, hBl, hBr⟩ => hw <| Exists.intro B <| ⟨hBl, List.IsInfix.trans hBr hvw⟩


theorem chapter1_question2 (u : Word α) (hu : Overlap u)
    : ∃ (v w z : Word α), u = w * v ∧ u = z * w ∧ |w| > |v| := by
  rcases hu with ⟨B, hBl, hBr⟩
  exists (B.drop 1 * B.take 1), (B * B.take 1), B
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
    exists B
    apply And.intro
    · exact hBr
    · simpa [hBl] using List.take_length_le <| Nat.le_of_eq h
  | inr h =>
    apply Or.inr
    exists (B.take 1), (B.drop 1)
    apply And.intro
    · simpa [freemonoid_to_list]
    apply And.intro
    · simpa [freemonoid_to_list] using Nat.lt_of_le_of_ne hBr h.symm
    · conv => rhs; lhs; rw [mul_assoc]
      simpa only [freemonoid_to_list, List.take_append_drop]


def μ : Monoid.End (Word (Fin 2)) := 
  FreeMonoid.join ∘* FreeMonoid.map (fun x => if x = 0 then [0, 1] else [1, 0])

theorem μ_nonerasing : FreeMonoid.NonErasing μ :=
  FreeMonoid.join_map_nonerasing fun x => by fin_cases x <;> exact Nat.succ_pos 1

theorem chapter1_question4 (v : Word (Fin 2)) (hv : HasOverlap v)
    : HasOverlap (μ v) := by
  rcases hv with ⟨B, hBl, hBr⟩
  exists μ B
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
        all_goals fin_cases x <;> decide
    apply List.IsInfix.trans <| List.IsPrefix.isInfix this
    simpa only [← map_mul] using FreeMonoid.is_infix_congr hBr μ


def complement : Monoid.End (Word (Fin 2)) :=
  FreeMonoid.map fun x => (1 - x)

prefix:100 "~" => complement

@[simp]
theorem complement_complement (w : Word (Fin 2)) : ~(~w) = w := by
  change (complement ∘* complement) w = (MonoidHom.id (Word (Fin 2))) w
  congr
  exact FreeMonoid.hom_eq fun x => by fin_cases x <;> rfl

@[simp]
theorem length_complement (w : Word (Fin 2)) : |~w| = |w| :=
  List.length_map w (fun x => 1 - x)

def X : ℕ → Word (Fin 2)
  | 0   => [0]
  | n+1 => X n * ~X n

theorem chapter1_question7 (n : ℕ)
    : (μ^n : Monoid.End (Word (Fin 2))) [0] = X n ∧ 
      (μ^n : Monoid.End (Word (Fin 2))) [1] = ~X n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    apply And.intro
    · exact calc 
      (μ^k.succ) [0] = (μ^k) (μ [0])               := by rw [pow_succ' μ k]; rfl
                   _ = (μ^k) [0, 1]                := by rfl
                   _ = (μ^k) (2 $↑ [0] * 2 $↑ [1]) := by rfl
                   _ = (μ^k) [0] * (μ^k) [1]       := by rw [map_mul]; rfl
                   _ = X k * ~X k                  := by rw [ih.left, ih.right]
                   _ = X k.succ                    := by rfl
    · exact calc 
      (μ^k.succ) [1] = (μ^k) (μ [1])               := by rw [pow_succ' μ k]; rfl
                   _ = (μ^k) [1, 0]                := by rfl
                   _ = (μ^k) (2 $↑ [1] * 2 $↑ [0]) := by rfl
                   _ = (μ^k) [1] * (μ^k) [0]       := by rw [map_mul]; rfl
                   _ = ~X k * X k                  := by rw [ih.right, ih.left]
                   _ = ~X k * ~(~X k)              := by rw [complement_complement] 
                   _ = ~(X k * ~X k)               := by rw [← map_mul]
                   _ = ~X k.succ                   := by rfl

