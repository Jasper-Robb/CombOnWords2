import Mathlib.Data.List.Infix
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.Sort


namespace List


def infixes (l : List α) : List (List α) :=
  [] :: (l.tails.map (tail ∘ inits)).join

theorem mem_infixes (s t : List α) : s ∈ t.infixes ↔ s <:+: t := by
  rw [infix_iff_prefix_suffix]
  constructor
  · intro h
    rcases mem_cons.mp h with ⟨s, hsl⟩ | hsr
    · exists []
      exact ⟨nil_prefix [], nil_suffix t⟩ 
    · obtain ⟨a, hal, har⟩ := mem_join.mp hsr
      obtain ⟨b, hbl, hbr⟩ := mem_map.mp hal
      exists b
      constructor
      · rw [← hbr] at har
        exact (mem_inits s b).mp <| mem_of_mem_tail har
      · exact (mem_tails b t).mp hbl
  · intro ⟨a, hal, har⟩
    apply mem_cons.mpr
    cases s with
    | nil => exact Or.inl rfl
    | cons x xs =>
      right
      simp only [mem_join, mem_map, mem_tails, Function.comp_apply, exists_exists_and_eq_and]
      exists a
      constructor
      · assumption
      · rw [← mem_inits] at hal
        apply mem_of_ne_of_mem <| cons_ne_nil x xs
        cases a <;> assumption


theorem length_rtake_of_le {l : List α} (h : n ≤ l.length) : (l.rtake n).length = n := by
  simpa [rtake_eq_reverse_take_reverse]

theorem rtake_suffix (n : ℕ) (l : List α) : l.rtake n <:+ l := by
  simpa only [rtake] using drop_suffix _ _

theorem rdrop_append_rtake (l : List α) : l.rdrop n ++ l.rtake n = l := by
  simp [rdrop, rtake]


@[simp]
theorem reverse_take_one (l : List α) : (l.take 1).reverse = l.take 1 := by
  cases (Nat.le_one_iff_eq_zero_or_eq_one.mp <| length_take_le 1 l) with
  | inl h =>
    rw [length_eq_zero.mp h]
    rfl
  | inr h =>
    obtain ⟨x, hx⟩ := length_eq_one.mp h
    rw [hx]
    rfl



theorem getLast_if_all (p : α → Prop) (l : List α) (hl : l ≠ []) : (∀ x ∈ l, p x) → p (l.getLast hl) :=
  (· (List.getLast l hl) (List.getLast_mem hl))

theorem elem_sort_iff_elem (l : List α) (x : α) (r : α → α → Prop) [DecidableRel r] 
    : x ∈ l.insertionSort r ↔ x ∈ l :=
  List.Perm.mem_iff (List.perm_insertionSort r l)

theorem ne_nil_iff_exists_elem (l : List α) : l ≠ [] ↔ ∃ x, x ∈ l :=
  ⟨List.exists_mem_of_ne_nil l, fun ⟨_, hx⟩ => List.ne_nil_of_mem hx⟩

theorem filter_ne_nil_iff_elem (p : α → Prop) [DecidablePred p] (l : List α) 
    : (∃ x ∈ l, p x) ↔ l.filter p ≠ [] := by
  simp only [ne_nil_iff_exists_elem, List.mem_filter, decide_eq_true_eq]


end List
