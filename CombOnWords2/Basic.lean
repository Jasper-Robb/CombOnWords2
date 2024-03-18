import CombOnWords2.FreeMonoid
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Fintype.Vector


section Defs


variable (α : Type*) [h : Fintype α]


abbrev Word := FreeMonoid α

def AllWordsOfLength (n : ℕ) : Multiset (Word α) :=
  (@Vector.fintype α h n).elems.val.map Vector.toList

def AllWordsMaxLength : ℕ → Multiset (Word α)
  | 0 => {[]}
  | n+1 => AllWordsMaxLength n + AllWordsOfLength α (n+1)

def WordMax (n : ℕ) :=
  {w : Word α // |w| < n}


end Defs


variable {α : Type*} [Fintype α] 


def toWord (n : ℕ) (l : List (Fin n)) : Word (Fin n) := l

infix:75 " $↑ " => toWord


theorem length_of_mem_of_allWordsOfLength (n : ℕ) : ∀ a ∈ AllWordsOfLength α n, |a| = n := by
  unfold AllWordsOfLength
  rw [Multiset.forall_mem_map_iff]
  exact fun x _ ↦ Vector.toList_length x

theorem length_of_mem_of_allWordsMaxLength (n : ℕ) : ∀ a ∈ AllWordsMaxLength α n, |a| ≤ n := by
  induction n with
  | zero => 
    unfold AllWordsMaxLength
    simp [freemonoid_to_list]
  | succ n ih =>
    unfold AllWordsMaxLength
    simp only [Multiset.mem_add]
    rintro a (hal | har)
    · exact Nat.le_step (ih a hal)
    · exact (Nat.le_iff_lt_or_eq).mpr <| Or.inr <| length_of_mem_of_allWordsOfLength (n+1) a har

theorem nodup_allWordsOfLength (n : ℕ) : Multiset.Nodup (AllWordsOfLength α n) :=
  Multiset.Nodup.map_on (fun x _ y _ a ↦ Vector.eq x y a) Fintype.elems.nodup 

theorem nodup_allWordsMaxLength (n : ℕ) : Multiset.Nodup (AllWordsMaxLength α n) := by
  induction n with
  | zero => 
    unfold AllWordsMaxLength
    simp
  | succ n ih =>
    apply (Multiset.Nodup.add_iff ih (nodup_allWordsOfLength (n + 1))).mpr
    intro a h1 h2
    have hla1 := length_of_mem_of_allWordsMaxLength n a h1
    have hla2 := length_of_mem_of_allWordsOfLength (n+1) a h2
    rw [hla2, Nat.succ_le] at hla1
    exact LT.lt.false hla1


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

theorem overlap_iff (u : Word α) : 2 < |u| ∧ u = u.take (|u| / 2) ^ 2 * u.take 1 ↔ Overlap u := by
  constructor
  · intro ⟨hlu, hu⟩
    exists u.take (|u| / 2)
    simp only [freemonoid_to_list, sq] at *
    constructor
    · simp only [List.length_take, lt_min_iff]
      exact ⟨Nat.div_pos (Nat.le_of_lt hlu) Nat.two_pos, Nat.zero_lt_of_lt hlu⟩
    · nth_rewrite 1 [hu]
      rw [List.append_right_inj, List.take_take, Nat.min_eq_left]
      exact @Nat.div_le_div_right 2 |u| 2 <| Nat.le_of_lt hlu
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

theorem has_overlap_iff (w : Word α) : (∃ u, Overlap u ∧ u <:*: w) ↔ HasOverlap w := by
  constructor
  · intro ⟨_, ⟨B, hBl, hBr⟩, _⟩
    exists B
    exact ⟨hBl, by rwa [← hBr]⟩
  · intro ⟨B, _, hBr⟩
    exists B * B * B.take 1
    exact ⟨by exists B;, hBr⟩

theorem has_overlap_iff' (w : Word α) :
    (∃ u ∈ w.infixes, Overlap u) ↔ HasOverlap w := by
  constructor
  · intro ⟨u, hul, hur⟩
    apply (has_overlap_iff w).mp
    exists u
    exact ⟨hur, (List.mem_infixes u w).mp hul⟩
  · intro h
    rcases (has_overlap_iff w).mpr h with ⟨u, hul, hur⟩
    exists u
    exact ⟨(List.mem_infixes u w).mpr hur, hul⟩

theorem factor_no_overlap_of_no_overlap (v w : Word α) (hw : ¬HasOverlap w) (hvw : v <:*: w)
    : ¬HasOverlap v :=
  fun ⟨B, hBl, hBr⟩ => hw <| Exists.intro B <| ⟨hBl, List.IsInfix.trans hBr hvw⟩


instance [DecidableEq α] (u : Word α) : Decidable (Overlap u) := 
  decidable_of_decidable_of_iff <| overlap_iff u

instance [DecidableEq α] (u : Word α) : Decidable (HasOverlap u) :=
  decidable_of_decidable_of_iff <| has_overlap_iff' u


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
  FreeMonoid.join_map_nonerasing fun x => by fin_cases x <;> exact Nat.two_pos

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

