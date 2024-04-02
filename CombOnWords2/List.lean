import Mathlib.Data.List.Infix
import Mathlib.Data.List.DropRight

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
      apply Or.inr
      simp only [mem_join, mem_map, mem_tails, Function.comp_apply, exists_exists_and_eq_and]
      exists a
      constructor
      · assumption
      · rw [← mem_inits] at hal
        apply mem_of_ne_of_mem <| cons_ne_nil x xs
        cases a <;> assumption


theorem length_rtake_eq_length_take (l : List α) (n : ℕ) : (l.rtake n).length = (l.take n).length := by
  simp [rtake_eq_reverse_take_reverse]

theorem length_rtake_of_le {l : List α} (h : n ≤ l.length) : (l.rtake n).length = n := by
  simpa [rtake_eq_reverse_take_reverse]

theorem rtake_suffix (n : ℕ) (l : List α) : l.rtake n <:+ l := by
  simpa only [rtake] using drop_suffix _ _

theorem rdrop_append_rtake (l : List α) : l.rdrop n ++ l.rtake n = l := by
  simp [rdrop, rtake]

end List
