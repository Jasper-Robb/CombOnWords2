import CombOnWords2.FreeMonoid
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.SuccPred


def allFreeMonoidsOfLength (α : Type*) [h : Fintype α] (n : ℕ) : Multiset (FreeMonoid α) :=
  (@Vector.fintype α h n).elems.val.map Vector.toList

def allFreeMonoidsMaxLength (α : Type*) [Fintype α] : (n : ℕ) → Multiset (FreeMonoid α)
  | 0 => 0
  | n+1 => allFreeMonoidsMaxLength α n + allFreeMonoidsOfLength α n


open FreeMonoid


variable {α : Type*} [Fintype α] 


def toFinFreeMonoid (n : ℕ) (l : List (Fin n)) : FreeMonoid (Fin n) := l

infix:75 " $↑ " => toFinFreeMonoid


theorem length_mem_allFreeMonoidsOfLength (n : ℕ) : ∀ w ∈ allFreeMonoidsOfLength α n, |w| = n := by
  simpa [allFreeMonoidsOfLength] using fun a _ ↦ a.prop

theorem length_mem_allFreeMonoidsMaxLength (n : ℕ) : ∀ w ∈ allFreeMonoidsMaxLength α n, |w| < n := by
  induction n with
  | zero => simp [allFreeMonoidsMaxLength, freemonoid_to_list]
  | succ n ih =>
    simp only [allFreeMonoidsMaxLength, Multiset.mem_add]
    rintro a (hal | har)
    · exact Nat.lt.step (ih a hal)
    · exact Nat.lt_succ.mpr <| Nat.le_of_eq <| length_mem_allFreeMonoidsOfLength n a har


theorem mem_allWordsOfLength (n : ℕ) (w : FreeMonoid α) (hw : |w| = n) : w ∈ allFreeMonoidsOfLength α n := by
  simpa [allFreeMonoidsOfLength] using Exists.intro ⟨w, hw⟩ ⟨Fintype.complete _, rfl⟩

theorem mem_allWordsMaxLength (n : ℕ) (w : FreeMonoid α) (hw : |w| < n) : w ∈ allFreeMonoidsMaxLength α n := by
  induction n with
  | zero => exact (Nat.not_lt_zero _ hw).elim
  | succ n ih =>
    rw [allFreeMonoidsMaxLength, Multiset.mem_add]
    cases Order.lt_succ_iff_eq_or_lt.mp hw with
    | inl hl => exact Or.inr <| mem_allWordsOfLength n w hl
    | inr hr => exact Or.inl <| ih hr
    

theorem mem_allWordsOfLength_iff (n : ℕ) (w : FreeMonoid α) : |w| = n ↔ w ∈ allFreeMonoidsOfLength α n :=
  ⟨mem_allWordsOfLength n w, length_mem_allFreeMonoidsOfLength n w⟩

theorem mem_allWordsMaxLength_iff (n : ℕ) (w : FreeMonoid α) : |w| < n ↔ w ∈ allFreeMonoidsMaxLength α n :=
  ⟨mem_allWordsMaxLength n w, length_mem_allFreeMonoidsMaxLength n w⟩


instance [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |w| = n ∧ p w) := by
  conv => rhs; rhs; intro w; rw [mem_allWordsOfLength_iff]
  exact Multiset.decidableExistsMultiset

instance [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |w| < n ∧ p w) := by
  conv => rhs; rhs; intro w; rw [mem_allWordsMaxLength_iff]
  exact Multiset.decidableExistsMultiset

instance [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |w| ≤ n ∧ p w) := by
  conv => rhs; rhs; intro w; rw [← Nat.lt_succ, mem_allWordsMaxLength_iff]
  exact Multiset.decidableExistsMultiset

instance [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |w| = n → p w) := by
  conv => rhs; intro w; rw [mem_allWordsOfLength_iff]
  exact Multiset.decidableForallMultiset

instance [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |w| < n → p w) := by
  conv => rhs; intro w; rw [mem_allWordsMaxLength_iff]
  exact Multiset.decidableForallMultiset

instance [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |w| ≤ n → p w) := by
  conv => rhs; intro w; rw [← Nat.lt_succ, mem_allWordsMaxLength_iff]
  exact Multiset.decidableForallMultiset


theorem chapter1_question2 (u : FreeMonoid α) (hu : Overlap u)
    : ∃ (v w z : FreeMonoid α), u = w * v ∧ u = z * w ∧ |w| > |v| := by
  rcases hu with ⟨B, hBl, hBr⟩
  exists (B.drop 1 * B.take 1), (B * B.take 1), B
  apply And.intro
  · conv => rw [← mul_assoc]; rhs; lhs; rw [mul_assoc]
    simpa only [freemonoid_to_list, List.take_append_drop]
  apply And.intro
  · rwa [← mul_assoc]
  · simpa [freemonoid_to_list] using Nat.sub_lt hBl Nat.one_pos


theorem chapter1_question3 (u : FreeMonoid α) (hu : Overlap u)
    : (∃ (x : FreeMonoid α), 0 < |x| ∧ u = x * x * x) ∨ 
      (∃ (x y : FreeMonoid α), 0 < |x| ∧ 0 < |y| ∧ u = x * y * x * y * x) := by
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


def μ : Monoid.End (FreeMonoid (Fin 2)) := 
  join ∘* map (fun x => if x = 0 then [0, 1] else [1, 0])

theorem μ_nonerasing : NonErasing μ :=
  join_map_nonerasing fun x => by fin_cases x <;> exact Nat.two_pos

theorem chapter1_question4 (v : FreeMonoid (Fin 2)) (hv : HasOverlap v)
    : HasOverlap (μ v) := by
  rcases hv with ⟨u, ⟨B, hBl, hBr⟩, hur⟩
  exists μ B * μ B * (μ B).take 1
  constructor
  · exact Exists.intro (μ B) ⟨μ_nonerasing B hBl, rfl⟩
  · have : μ B * μ B * (μ B).take 1 <*: μ u := by
      simp only [hBr, map_mul]
      apply (List.prefix_append_right_inj (μ B * μ B)).mpr
      cases B with
      | nil => contradiction
      | cons x xs =>
        conv => lhs; change (μ (ofList (x :: xs))).take 1
        rw [ofList_cons, map_mul]
        simp only [freemonoid_to_list, List.take_cons_succ, List.take_zero]
        rw [List.take_append_of_le_length]
        all_goals fin_cases x <;> decide
    exact List.IsInfix.trans (List.IsPrefix.isInfix this) <| is_infix_congr hur μ


def complement : Monoid.End (FreeMonoid (Fin 2)) :=
  map fun x => (1 - x)

prefix:100 "~" => complement

@[simp]
theorem complement_complement (w : FreeMonoid (Fin 2)) : ~(~w) = w := by
  change (complement ∘* complement) w = (MonoidHom.id (FreeMonoid (Fin 2))) w
  congr
  exact hom_eq fun x => by fin_cases x <;> rfl

@[simp]
theorem length_complement (w : FreeMonoid (Fin 2)) : |~w| = |w| :=
  List.length_map w (fun x => 1 - x)

def X : ℕ → FreeMonoid (Fin 2)
  | 0   => [0]
  | n+1 => X n * ~X n

theorem chapter1_question7 (n : ℕ)
    : (μ^n : Monoid.End (FreeMonoid (Fin 2))) [0] = X n ∧ 
      (μ^n : Monoid.End (FreeMonoid (Fin 2))) [1] = ~X n := by
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

