import CombOnWords2.Decidable
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Parity


open FreeMonoid


variable {α β : Type*} [Fintype α] [Fintype β] 


def toFinFreeMonoid (n : ℕ) (l : List (Fin n)) : FreeMonoid (Fin n) := l

infix:75 " $↑ " => toFinFreeMonoid


theorem nil_in_allFreeMonoidsMaxLength (n : ℕ) (hn : 0 < n) : [] ∈ allFreeMonoidsMaxLength α n := by
  cases n with
  | zero => contradiction
  | succ n =>
    apply mem_allFreeMonoidsMaxLength
    simp [freemonoid_to_list]


theorem chapter1_question2 (u : FreeMonoid α) (hu : Overlap u)
    : ∃ (v w z : FreeMonoid α), u = w * v ∧ u = z * w ∧ |w| > |v| := by
  obtain ⟨B, hBl, hBr⟩ := hu
  exists (B.drop 1 * B.take 1), (B * B.take 1), B
  constructor <;> try constructor
  · conv => rw [← mul_assoc]; rhs; lhs; rw [mul_assoc]
    simpa only [freemonoid_to_list, List.take_append_drop]
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
  bind fun x => if x = 0 then [0, 1] else [1, 0]

theorem μ_nonerasing : NonErasing μ :=
  bind_nonerasing fun x => by fin_cases x <;> exact Nat.two_pos

instance : IsNonErasing μ where
  nonerasing := μ_nonerasing

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


def complement : Monoid.End (FreeMonoid (Fin 2)) :=
  map (1 - ·)

prefix:100 "~" => complement

@[simp]
theorem complement_complement (w : FreeMonoid (Fin 2)) : ~(~w) = w := by
  change (complement ∘* complement) w = (MonoidHom.id (FreeMonoid (Fin 2))) w
  congr
  exact hom_eq fun x => by fin_cases x <;> rfl

@[simp]
theorem length_complement (w : FreeMonoid (Fin 2)) : |~w| = |w| :=
  List.length_map w _


theorem μ_of_reverse (x : Fin 2) : (μ (of x)).reverse = ~μ (of x) := by
  fin_cases x <;> rfl

theorem μ_reverse (w : FreeMonoid (Fin 2)) : (μ w).reverse = ~μ w.reverse := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    change FreeMonoid (Fin 2) at xs
    change (μ (of x * xs)).reverse = ~μ (of x * xs).reverse
    simp only [map_mul, reverse_mul, μ_of_reverse, ih]
    simp [freemonoid_to_list]

theorem μ_of_complement (x : Fin 2) : ~μ (of x) = μ (~(of x)) := by
  fin_cases x <;> rfl

theorem μ_complement (w : FreeMonoid (Fin 2)) : ~μ w = μ (~w) := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    change FreeMonoid (Fin 2) at xs
    change ~μ (of x * xs) = μ (~(of x * xs))
    simp only [map_mul, μ_of_complement, ih]


def lengthLe (fm₁ fm₂ : FreeMonoid α) : Prop := 
  |fm₁| ≤ |fm₂| 

instance : @DecidableRel (FreeMonoid α) lengthLe :=
  fun (fm₁ fm₂ : FreeMonoid α) ↦ Nat.decLe |fm₁| |fm₂|

instance : IsTotal (FreeMonoid α) lengthLe :=
  ⟨fun (fm₁ fm₂ : FreeMonoid α) ↦ Nat.le_or_le |fm₁| |fm₂|⟩

instance : IsTrans (FreeMonoid α) lengthLe :=
  ⟨fun _ _ _ ↦ Nat.le_trans⟩

theorem exists_longest_μ_infix (w : FreeMonoid (Fin 2)) 
    : ∃ v, μ v <:*: w ∧ ∀ v₂ : FreeMonoid (Fin 2), |v| < |v₂| → ¬μ v₂ <:*: w := by
  let l := List.insertionSort lengthLe
    (List.filter (μ · <:*: w)
    (Multiset.toList (allFreeMonoidsMaxLength (Fin 2) (|w| + 1))))
  have hl : l ≠ [] := by
    suffices [] ∈ l by exact List.ne_nil_of_mem this
    rw [List.elem_sort_iff_elem _ [] lengthLe, List.mem_filter, Multiset.mem_toList]
    exact ⟨nil_in_allFreeMonoidsMaxLength (|w| + 1) (Nat.succ_pos |w|), by simpa using List.nil_infix w⟩
  exists l.getLast hl
  constructor
  · apply List.getLast_if_all (μ · <:*: w) l hl
    intro x hx
    rw [List.elem_sort_iff_elem] at hx
    have := List.of_mem_filter hx
    exact of_decide_eq_true this
  · intro fm hfm hfm2
    have : |fm| ≤ |w| := 
      Nat.le_trans (nonerasing_iff.mp μ_nonerasing fm) (List.IsInfix.length_le hfm2)
    have : fm ∈ l := by
      rw [List.elem_sort_iff_elem, List.mem_filter, Multiset.mem_toList]
      rw [← Nat.lt_succ] at this
      exact ⟨mem_allFreeMonoidsMaxLength (|w| + 1) fm this, decide_eq_true hfm2⟩
    obtain ⟨n, hn⟩ := List.get_of_mem this
    rw [List.getLast_eq_get, ← hn] at hfm
    have : |l.get n| ≤ |l.get ⟨l.length - 1, Nat.sub_lt (List.length_pos.2 hl) Nat.one_pos⟩| := by
      apply @List.Sorted.rel_get_of_le (FreeMonoid (Fin 2)) lengthLe
      exacts [List.sorted_insertionSort lengthLe _, Nat.le_sub_one_of_lt (Fin.prop n)]
    exact LT.lt.false (Nat.lt_of_lt_of_le hfm this)


namespace Question5

theorem claim1 (w : FreeMonoid (Fin 2)) (hlw : 6 ≤ |w|) (hw : ¬HasOverlap w)
    : ∃ v : FreeMonoid (Fin 2), μ v <:*: w ∧ 1 < |v| := by
  have h₁ : ∀ w : FreeMonoid (Fin 2), |w| = 6 → ¬HasOverlap w → ∃ x : FreeMonoid (Fin 2), μ x <:*: w ∧ 1 < |x| := by
    decide
  have h₂ : w.take 6 <:*: w := List.IsPrefix.isInfix <| List.take_prefix _ w
  obtain ⟨x, hx, hlx⟩ := h₁ (w.take 6) (List.length_take_of_le hlw) <| factor_no_overlap_of_no_overlap h₂ hw
  exact ⟨x, ⟨List.IsInfix.trans hx h₂, hlx⟩⟩

theorem claim2₁ (u v z w : FreeMonoid (Fin 2)) (hv : ∀ v₂ : FreeMonoid (Fin 2), |v| < |v₂| → ¬μ v₂ <:*: w)
    (h : u * μ v * z = w) : ∀ x, ¬μ (of x) <:* u := by
  intro x ⟨s, hs⟩
  suffices w = s * μ (of x * v) * z by
    exact hv (of x * v) (Nat.lt.base |v|) ⟨s, z, this.symm⟩
  exact calc
    w = u * μ v * z            := by exact h.symm
    _ = s * μ (of x) * μ v * z := by rw [← hs] 
    _ = s * μ (of x * v) * z   := by conv => lhs; lhs; rw [mul_assoc, ← map_mul]

theorem claim2₂ (u v z w : FreeMonoid (Fin 2)) (hv : ∀ v₂ : FreeMonoid (Fin 2), |v| < |v₂| → ¬μ v₂ <:*: w)
    (h : u * μ v * z = w) : ∀ x, ¬μ (of x) <*: z := by
  intro x ⟨t, ht⟩
  suffices w = u * μ (v * of x) * t by
    exact hv (v * of x) (by simp [freemonoid_to_list]) ⟨u, t, this.symm⟩
  exact calc
    w = u * μ v * z            := by exact h.symm
    _ = u * μ v * μ (of x) * t := by rw [← ht, ← mul_assoc] 
    _ = u * μ (v * of x) * t   := by conv => lhs; lhs; rw [mul_assoc, ← map_mul]

theorem claim3₁ (u v z w : FreeMonoid (Fin 2)) (hw₁ : ¬HasOverlap w) (hw₂ : u * μ v * z = w)
    (hv₁ : ∀ v₂ : FreeMonoid (Fin 2), |v| < |v₂| → ¬μ v₂ <:*: w) (hv₂ : 1 < |v|) : |u| < 3 := by
  by_contra hu₁
  rw [Nat.not_lt, ← Nat.lt_succ] at hu₁
  have hc₁ : ¬HasOverlap (u.rtake 3) := by 
    refine factor_no_overlap_of_no_overlap ?_ hw₁
    exists u.rdrop 3, μ v * z
    simp only [freemonoid_to_list, List.append_assoc] at hw₂
    simpa only [freemonoid_to_list, List.rdrop_append_rtake]
  have hc₂ : ∀ x : Fin 2, ¬μ (of x) <:* (u.rtake 3) := 
    fun x hxu ↦ claim2₁ u v z w hv₁ hw₂ x <| List.IsSuffix.trans hxu <| List.rtake_suffix 3 u
  have hc₃ : ¬HasOverlap (u.rtake 3 * μ (v.take 2)) := by
    refine factor_no_overlap_of_no_overlap ?_ hw₁
    exists u.rdrop 3, μ (v.drop 2) * z
    simp only [← mul_assoc]
    conv => lhs; lhs; rw [mul_assoc, ← map_mul]
    simpa only [freemonoid_to_list, List.rdrop_append_rtake, List.take_append_drop]
  have hu₂ : u.rtake 3 ∈ [[0,0,0],[0,0,1],[0,1,0],[0,1,1],[1,0,0],[1,0,1],[1,1,0],[1,1,1]] := 
    mem_allFreeMonoidsOfLength 3 (u.rtake 3) <| List.length_rtake_of_le <| Nat.lt_succ.mp hu₁
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu₂
  have hv₃ : v.take 2 ∈ [[0,0],[0,1],[1,0],[1,1]] :=
    mem_allFreeMonoidsOfLength 2 (v.take 2) <| List.length_take_of_le hv₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv₃
  rcases hu₂ with (hu₂' | hu₂' | hu₂' | hu₂' | hu₂' | hu₂' | hu₂' | hu₂')
  all_goals try apply hc₁;                     rw [hu₂']; decide
  all_goals try apply hc₂ ⟨0, Nat.two_pos⟩;    rw [hu₂']; decide
  all_goals try apply hc₂ ⟨1, Nat.one_lt_two⟩; rw [hu₂']; decide
  all_goals rcases hv₃ with (hv₃' | hv₃' | hv₃' | hv₃')
  all_goals apply hc₃; rw [hu₂', hv₃']; decide

theorem claim3₂ (u v z w : FreeMonoid (Fin 2)) (hw₁ : ¬HasOverlap w) (hw₂ : u * μ v * z = w)
    (hv₁ : ∀ v₂ : FreeMonoid (Fin 2), |v| < |v₂| → ¬μ v₂ <:*: w) (hv₂ : 1 < |v|) : |z| < 3 := by
  rw [← length_reverse]
  apply claim3₁ z.reverse (~v.reverse) u.reverse w.reverse
  · rwa [← has_overlap_reverse_iff]
  · simp [← hw₂, reverse_mul, μ_reverse, μ_complement, ← mul_assoc]
  · rw [length_complement, length_reverse]
    intro v₂ _ _
    apply hv₁ (~v₂.reverse)
    · rwa [length_complement, length_reverse]
    · rwa [← μ_complement, ← μ_reverse, ← reverse_infix, reverse_reverse]
  · simpa

end Question5


open Question5

theorem chapter1_question5 (w : FreeMonoid (Fin 2)) (hw : ¬HasOverlap w)
    : ∃ u ∈ ([[], [0], [1], [0, 0], [1, 1]] : List (FreeMonoid (Fin 2))),
      ∃ z ∈ ([[], [0], [1], [0, 0], [1, 1]] : List (FreeMonoid (Fin 2))),
      ∃ v : FreeMonoid (Fin 2), w = u * μ v * z ∧ ¬HasOverlap v := by
  cases Nat.lt_or_ge |w| 6 with
  | inl hlw =>
    revert w
    conv => 
      intro w; rw [forall_comm]; intro h1 h2; rhs; intro u; rhs; rhs; intro z; rhs; rhs; intro v; lhs; 
      rw [show w = u * μ v * z ↔ μ v <:*: w ∧ w = u * μ v * z from ⟨fun h ↦ ⟨⟨u, z, h.symm⟩, h⟩, And.right⟩]
    simp only [and_assoc]
    decide
  | inr hlw =>
    obtain ⟨v, hvl, hvr⟩ := exists_longest_μ_infix w
    have hlv : 1 < |v| := by
      by_contra hvnl
      rw [not_lt] at hvnl 
      obtain ⟨v', hvl', hvr'⟩ := claim1 w hlw hw
      exact hvr v' (Nat.lt_of_le_of_lt hvnl hvr') hvl'
    have hvno: ¬HasOverlap v := factor_no_overlap_of_no_overlap hvl hw ∘ (chapter1_question4 v)
    obtain ⟨u, z, huz⟩ := hvl
    exists u; constructor <;> try exists z; constructor
    · have : u ≠ [0, 1] := fun hu ↦ claim2₁ u v z w hvr huz ⟨0, Nat.two_pos⟩ (by rw [hu]; decide)
      have : u ≠ [1, 0] := fun hu ↦ claim2₁ u v z w hvr huz ⟨1, Nat.one_lt_two⟩ (by rw [hu]; decide)
      have := mem_allFreeMonoidsMaxLength 3 u <| claim3₁ u v z w hw huz hvr hlv
      fin_cases this <;> first | decide | contradiction
    · have : z ≠ [0, 1] := fun hz ↦ claim2₂ u v z w hvr huz ⟨0, Nat.two_pos⟩ (by rw [hz]; decide)
      have : z ≠ [1, 0] := fun hz ↦ claim2₂ u v z w hvr huz ⟨1, Nat.one_lt_two⟩ (by rw [hz]; decide)
      have := mem_allFreeMonoidsMaxLength 3 z <| claim3₂ u v z w hw huz hvr hlv
      fin_cases this <;> first | decide | contradiction
    · exact ⟨v, huz.symm, hvno⟩


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

