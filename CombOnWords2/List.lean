import Mathlib.Data.List.Infix

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
    · rcases mem_join.mp hsr with ⟨a, hal, har⟩
      rcases mem_map.mp hal with ⟨b, hbl, hbr⟩
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

end List
