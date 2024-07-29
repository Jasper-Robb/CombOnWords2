import Mathlib.Data.Stream.Init
import CombOnWords2.List


namespace Stream'


theorem get_take {s : Stream' α} {i n : ℕ} (hi : i < n)
    : (s.take n).get ⟨i, Nat.lt_of_lt_of_eq hi (Stream'.length_take n s).symm⟩ = s.get i := by
  apply Option.some_injective _
  rw [← List.get?_eq_get, Stream'.get?_take hi]


namespace of_stream'_lists

theorem claim1 {u : Stream' (List α)} (hu : ∀ i, u i <<+: u i.succ)
    : ∀ i j, i < j → u i <<+: u j := by
  intro i j hij
  induction j with
  | zero => contradiction
  | succ j ih =>
    rw [Nat.lt_succ] at hij
    cases Nat.lt_or_eq_of_le hij with
    | inl h => exact List.IsProperPrefix.trans (ih h) (hu j)
    | inr h => exact List.ppx_of_px_of_ppx (List.prefix_of_eq 
      (congrArg u h)) (hu j)

theorem claim2 {u : Stream' (List α)} (h : ∀ i, u i <<+: u i.succ)
    : ∀ i, i < (u i.succ).length := by
  intro i
  induction i with
  | zero => exact Nat.zero_lt_of_lt (List.IsProperPrefix.length_lt (h 0))
  | succ i ih => exact Nat.lt_of_le_of_lt ih (List.IsProperPrefix.length_lt (h i.succ))

end of_stream'_lists


theorem of_stream'_lists (u : Stream' (List α)) (h₁ : ∀ i, u i <<+: u i.succ)
    : ∃ w : Stream' α, ∀ i, w.take (u i).length = u i := by
  exists fun i ↦ (u i.succ).get ⟨i, of_stream'_lists.claim2 h₁ i⟩
  intro i
  apply List.ext_get (Stream'.length_take _ _)
  intro n _ hn
  rw [Stream'.get_take hn, Stream'.get]
  cases Nat.lt_or_ge n i with
  | inl h =>
    rw [List.get_eq_of_prefix]
    cases Nat.lt_or_eq_of_le h with
    | inl h => exact List.prefix_of_proper_prefix <| 
        of_stream'_lists.claim1 h₁ n.succ i h
    | inr h => rw [h]; exact List.prefix_rfl
  | inr h =>
    change i ≤ n at h
    rw [← Nat.lt_succ] at h
    rw [eq_comm, List.get_eq_of_prefix]
    exact List.prefix_of_proper_prefix <| of_stream'_lists.claim1 h₁ i n.succ h


end Stream'
