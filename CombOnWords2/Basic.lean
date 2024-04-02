import CombOnWords2.FreeMonoid
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.SuccPred


def allFreeMonoidsOfLength (α : Type*) [h : Fintype α] (n : ℕ) : Multiset (FreeMonoid α) :=
  (@Vector.fintype α h n).elems.val.map Vector.toList

def allFreeMonoidsMaxLength (α : Type*) [Fintype α] : ℕ → Multiset (FreeMonoid α)
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


theorem mem_allFreeMonoidsOfLength (n : ℕ) (w : FreeMonoid α) (hw : |w| = n) : w ∈ allFreeMonoidsOfLength α n := by
  simpa [allFreeMonoidsOfLength] using ⟨⟨w, hw⟩, ⟨Fintype.complete _, rfl⟩⟩

theorem mem_allFreeMonoidsMaxLength (n : ℕ) (w : FreeMonoid α) (hw : |w| < n) : w ∈ allFreeMonoidsMaxLength α n := by
  induction n with
  | zero => exact (Nat.not_lt_zero _ hw).elim
  | succ n ih =>
    rw [allFreeMonoidsMaxLength, Multiset.mem_add]
    cases Order.lt_succ_iff_eq_or_lt.mp hw with
    | inl hl => exact Or.inr <| mem_allFreeMonoidsOfLength n w hl
    | inr hr => exact Or.inl <| ih hr
    

theorem mem_allFreeMonoidsOfLength_iff (n : ℕ) (w : FreeMonoid α) : w ∈ allFreeMonoidsOfLength α n ↔ |w| = n :=
  ⟨length_mem_allFreeMonoidsOfLength n w, mem_allFreeMonoidsOfLength n w⟩

theorem mem_allFreeMonoidsMaxLength_iff (n : ℕ) (w : FreeMonoid α) : w ∈ allFreeMonoidsMaxLength α n ↔ |w| < n :=
  ⟨length_mem_allFreeMonoidsMaxLength n w, mem_allFreeMonoidsMaxLength n w⟩


instance {p : β → Prop} [DecidablePred p] {m : Multiset β} : Decidable (∃ x ∈ m, p x) :=
  Multiset.decidableExistsMultiset

instance {p : β → Prop} [DecidablePred p] {m : Multiset β} : Decidable (∀ x ∈ m, p x) :=
  Multiset.decidableForallMultiset


instance [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |w| = n ∧ p w) :=
  decidable_of_decidable_of_iff <| 
    exists_congr fun w ↦ and_congr_left fun _ ↦ mem_allFreeMonoidsOfLength_iff n w

instance [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |w| < n ∧ p w) :=
  decidable_of_decidable_of_iff <| 
    exists_congr fun w ↦ and_congr_left fun _ ↦ mem_allFreeMonoidsMaxLength_iff n w

instance [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |w| ≤ n ∧ p w) :=
  decidable_of_decidable_of_iff <| 
    exists_congr fun w ↦ and_congr_left fun _ ↦ (mem_allFreeMonoidsMaxLength_iff (n+1) w).trans Nat.lt_succ

instance [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |w| = n → p w) :=
  decidable_of_decidable_of_iff <| 
    forall_congr' fun w ↦ imp_congr_left <| mem_allFreeMonoidsOfLength_iff n w

instance [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |w| < n → p w) :=
  decidable_of_decidable_of_iff <| 
    forall_congr' fun w ↦ imp_congr_left <| mem_allFreeMonoidsMaxLength_iff n w

instance [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |w| ≤ n → p w) :=
  decidable_of_decidable_of_iff <| 
    forall_congr' fun w ↦ imp_congr_left <| (mem_allFreeMonoidsMaxLength_iff (n+1) w).trans Nat.lt_succ


theorem chapter1_question2 (u : FreeMonoid α) (hu : Overlap u)
    : ∃ (v w z : FreeMonoid α), u = w * v ∧ u = z * w ∧ |w| > |v| := by
  obtain ⟨B, hBl, hBr⟩ := hu
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
  obtain ⟨B, hBl, hBr⟩ := hu
  cases eq_or_ne |B| 1 with
  | inl h => exact Or.inl <| Exists.intro B ⟨hBl, by simpa [hBr] using List.take_length_le <| Nat.le_of_eq h⟩
  | inr h =>
    apply Or.inr
    exists (B.take 1), (B.drop 1)
    constructor <;> try constructor
    · simpa [freemonoid_to_list]
    · simpa [freemonoid_to_list] using Nat.lt_of_le_of_ne hBl h.symm
    · conv => rhs; lhs; rw [mul_assoc]
      simpa only [freemonoid_to_list, List.take_append_drop]


def μ : Monoid.End (FreeMonoid (Fin 2)) := 
  join ∘* map fun x => if x = 0 then [0, 1] else [1, 0]

theorem μ_nonerasing : NonErasing μ :=
  join_map_nonerasing fun x => by fin_cases x <;> exact Nat.two_pos

theorem chapter1_question4 (v : FreeMonoid (Fin 2)) (hv : HasOverlap v) : HasOverlap (μ v) := by
  obtain ⟨u, ⟨B, hBl, hBr⟩, hur⟩ := hv
  exists μ B * μ B * (μ B).take 1
  constructor
  · exact ⟨(μ B), ⟨μ_nonerasing B hBl, rfl⟩⟩
  · suffices μ B * μ B * (μ B).take 1 <*: μ u by
      exact List.IsInfix.trans (List.IsPrefix.isInfix this) <| is_infix_congr hur μ
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


theorem exists_longest_μ_infix (w : FreeMonoid (Fin 2)) 
    : ∃ v, μ v <:*: w ∧ ∀ v₂ : FreeMonoid (Fin 2), |v| < |v₂| → ¬μ v₂ <:*: w :=
  sorry

theorem chapter1_question5 (w : FreeMonoid (Fin 2)) (hw : ¬HasOverlap w)
    : ∃ u ∈ ([[], [0], [1], [0, 0], [1, 1]] : List (FreeMonoid (Fin 2))),
      ∃ z ∈ ([[], [0], [1], [0, 0], [1, 1]] : List (FreeMonoid (Fin 2))),
      ∃ v : FreeMonoid (Fin 2), ¬HasOverlap v ∧ w = u * μ v * z := by
  have claim0 : ∀ fm : FreeMonoid (Fin 2), |fm| = 6 → ¬HasOverlap fm → ∃ x : FreeMonoid (Fin 2), μ x <:*: fm ∧ 1 < |x| := by
    conv => 
      intro fm h1 h2; rhs; intro x 
      rw [is_infix_iff_list_is_infix, iff_and_self.mpr <| (nonerasing_iff.mp μ_nonerasing x).trans ∘ List.IsInfix.length_le]
    simp only [and_assoc]
    --decide
    admit
  have claim1 : ∀ fm : FreeMonoid (Fin 2), 6 ≤ |fm| → ¬HasOverlap fm → ∃ x : FreeMonoid (Fin 2), μ x <:*: fm ∧ 1 < |x| := by
    intro fm hlfm hfm
    have : fm.take 6 <:*: fm := List.IsPrefix.isInfix <| List.take_prefix _ fm
    obtain ⟨x, hx, hlx⟩ := claim0 (fm.take 6) (List.length_take_of_le hlfm) <| factor_no_overlap_of_no_overlap this hfm
    exact ⟨x, ⟨List.IsInfix.trans hx this, hlx⟩⟩
  cases Nat.lt_or_ge |w| 6 with
  | inl hlw =>
    conv =>
      rhs; intro u; rhs; rhs; intro z; rhs; rhs; intro v
      rw [iff_and_self.mpr <| (nonerasing_iff.mp μ_nonerasing v).trans ∘ prod3_length_le₂ w u (μ v) z]
    conv =>
      rhs; intro u; rhs; rhs; intro z; rhs; rhs; intro v;
      rw [and_comm, and_assoc]
    revert hlw hw
    rw [forall_comm]
    revert w
    --decide 
    admit
  | inr hlw =>
    obtain ⟨v, hvl, hvr⟩ := exists_longest_μ_infix w
    have claim2_1 : ∀ u z : FreeMonoid (Fin 2), u * μ v * z = w → ∀ x : Fin 2, ¬(μ (of x)) <:* u := by
      intro u z h x ⟨s, hs⟩
      suffices w = s * μ (of x * v) * z by
        exact hvr (of x * v) (Nat.lt.base |v|) ⟨s, ⟨z, this.symm⟩⟩
      exact calc
        w = u * μ v * z            := by exact h.symm
        _ = s * μ (of x) * μ v * z := by rw [← hs]; 
        _ = s * μ (of x * v) * z   := by conv => lhs; lhs; rw [mul_assoc, ← map_mul]
    have claim2_2 : ∀ u z : FreeMonoid (Fin 2), u * μ v * z = w → ∀ x : Fin 2, ¬(μ (of x)) <*: z := by
      intro u z h x ⟨t, ht⟩
      suffices w = u * μ (v * of x) * t by
        exact hvr (v * of x) (by simp [freemonoid_to_list]) ⟨u, ⟨t, this.symm⟩⟩
      exact calc
        w = u * μ v * z            := by exact h.symm
        _ = u * μ v * μ (of x) * t := by rw [← ht, ← mul_assoc]
        _ = u * μ (v * of x) * t   := by conv => lhs; lhs; rw [mul_assoc, ← map_mul]
    have hv0 : 1 < |v| := by
      by_contra hvnl
      rw [not_lt] at hvnl 
      obtain ⟨v', hvl', hvr'⟩ := claim1 w hlw hw
      exact hvr v' (Nat.lt_of_le_of_lt hvnl hvr') hvl'
    have claim3_1 : ∀ u z : FreeMonoid (Fin 2), u * μ v * z = w → |u| < 3 := by
      intro u z huz
      by_contra hu1
      rw [Nat.not_lt, ← Nat.lt_succ] at hu1
      have hc2 : ∀ x : Fin 2, ¬μ (of x) <:* (u.rtake 3) := 
        fun x hxu ↦ claim2_1 u z huz x <| List.IsSuffix.trans hxu <| List.rtake_suffix 3 u
      have hc3 : ¬HasOverlap (u.rtake 3 * μ (v.take 2)) := by
        refine factor_no_overlap_of_no_overlap ?_ hw
        exists u.rdrop 3, μ (v.drop 2) * z
        simp only [← mul_assoc]
        conv => lhs; lhs; rw [mul_assoc, ← map_mul]
        simpa only [freemonoid_to_list, List.rdrop_append_rtake, List.take_append_drop]
      have hu2 : u.rtake 3 ∈ [[0,0,0],[0,0,1],[0,1,0],[0,1,1],[1,0,0],[1,0,1],[1,1,0],[1,1,1]] := 
        mem_allFreeMonoidsOfLength 3 (u.rtake 3) <| List.length_rtake_of_le <| Nat.lt_succ.mp hu1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu2
      have hv1 : v.take 2 ∈ [[0,0],[0,1],[1,0],[1,1]] :=
        mem_allFreeMonoidsOfLength 2 (v.take 2) <| List.length_take_of_le hv0
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv1
      rcases hu2 with (hu2' | hu2' | hu2' | hu2' | hu2' | hu2' | hu2' | hu2')
      all_goals try apply hc2 ⟨0, Nat.two_pos⟩;    rw [hu2']; decide
      all_goals try apply hc2 ⟨1, Nat.one_lt_two⟩; rw [hu2']; decide
      all_goals rcases hv1 with (hv1' | hv1' | hv1' | hv1')
      all_goals apply hc3; rw [hu2', hv1']; decide
    have claim3_2 : ∀ u z : FreeMonoid (Fin 2), u * μ v * z = w → |z| < 3 := by
      intro u z huz
      by_contra hz1
      rw [Nat.not_lt, ← Nat.lt_succ] at hz1
      have hc1 : ∀ x : Fin 2, ¬μ (of x) <*: (z.take 3) := 
        fun x hxu ↦ claim2_2 u z huz x <| List.IsPrefix.trans hxu <| List.take_prefix 3 z
      have hc2 : ¬HasOverlap (μ (v.rtake 2) * z.take 3) := by
        refine factor_no_overlap_of_no_overlap ?_ hw
        exists u * μ (v.rdrop 2), z.drop 3
        conv => lhs; lhs; rw [← mul_assoc]; lhs; rw [mul_assoc, ← map_mul]
        simp only [freemonoid_to_list, List.rdrop_append_rtake]
        rwa [List.append_assoc, List.take_append_drop]
      have hz2 : z.take 3 ∈ [[0,0,0],[0,0,1],[0,1,0],[0,1,1],[1,0,0],[1,0,1],[1,1,0],[1,1,1]] := 
        mem_allFreeMonoidsOfLength 3 (z.take 3) <| List.length_take_of_le <| Nat.lt_succ.mp hz1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz2
      have hv2 : v.rtake 2 ∈ [[0,0],[0,1],[1,0],[1,1]] :=
        mem_allFreeMonoidsOfLength 2 (v.rtake 2) <| List.length_rtake_of_le hv0
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv2
      rcases hz2 with (hz2' | hz2' | hz2' | hz2' | hz2' | hz2' | hz2' | hz2')
      all_goals try apply hc1 ⟨0, Nat.two_pos⟩;    rw [hz2']; decide
      all_goals try apply hc1 ⟨1, Nat.one_lt_two⟩; rw [hz2']; decide
      all_goals rcases hv2 with (hv2' | hv2' | hv2' | hv2')
      all_goals apply hc2; rw [hz2', hv2']; decide
    have hvno: ¬HasOverlap v := factor_no_overlap_of_no_overlap hvl hw ∘ (chapter1_question4 v)
    obtain ⟨u, z, huz⟩ := hvl
    exists u; constructor <;> try exists z; constructor
    · have : u ≠ [0, 1] := fun hu ↦ claim2_1 u z huz ⟨0, Nat.two_pos⟩ (by rw [hu]; decide)
      have : u ≠ [1, 0] := fun hu ↦ claim2_1 u z huz ⟨1, Nat.one_lt_two⟩ (by rw [hu]; decide)
      have := mem_allFreeMonoidsMaxLength 3 u <| claim3_1 u z huz
      fin_cases this <;> first | decide | contradiction
    · have : z ≠ [0, 1] := fun hz ↦ claim2_2 u z huz ⟨0, Nat.two_pos⟩ (by rw [hz]; decide)
      have : z ≠ [1, 0] := fun hz ↦ claim2_2 u z huz ⟨1, Nat.one_lt_two⟩ (by rw [hz]; decide)
      have := mem_allFreeMonoidsMaxLength 3 z <| claim3_2 u z huz
      fin_cases this <;> first | decide | contradiction
    · exact ⟨v, hvno, huz.symm⟩


def complement : Monoid.End (FreeMonoid (Fin 2)) :=
  map fun x => 1 - x

prefix:100 "~" => complement

@[simp]
theorem complement_complement (w : FreeMonoid (Fin 2)) : ~(~w) = w := by
  change (complement ∘* complement) w = (MonoidHom.id (FreeMonoid (Fin 2))) w
  congr
  exact hom_eq fun x => by fin_cases x <;> rfl

@[simp]
theorem length_complement (w : FreeMonoid (Fin 2)) : |~w| = |w| :=
  List.length_map w _

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

