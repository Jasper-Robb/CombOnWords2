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


theorem prefix_append_of_prefix {l₁ l₂ : List α} (l₃ : List α) (h : l₁ <+: l₂)
    : l₁ <+: l₂ ++ l₃ := by
  obtain ⟨t, ht⟩ := h
  exists t ++ l₃
  rw [← append_assoc, ht]

theorem prefix_of_prefix_append {l₁ l₂ l₃ : List α} (h₁ : l₂ <+: l₁ ++ l₃) (h₂ : l₁.length ≤ l₂.length)
    : l₁ <+: l₂ := by
  obtain ⟨t, ht⟩ := h₁
  have := congrArg (take l₁.length) ht.symm
  simp only [take_left, take_append_of_le_length h₂] at this
  exact prefix_iff_eq_take.mpr this


theorem eq_take_iff {l1 : List α} (l2 : List α) {k : ℕ} (h : k ≤ l1.length)
    : l2 = l1.take k ↔ l2 <+: l1 ∧ l2.length = k := by
  constructor
  · intro h2
    rw [h2]
    exact ⟨take_prefix k l1, length_take_of_le h⟩
  · intro ⟨⟨t, ht⟩, h2⟩
    rw [← ht, take_left' h2]


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


def IsStrictPrefix (l₁ l₂ : List α) : Prop :=
  ∃ t ≠ [], l₁ ++ t = l₂

def IsStrictSuffix (l₁ l₂ : List α) : Prop :=
  ∃ s ≠ [], s ++ l₁ = l₂

def IsStrictInfix (l₁ l₂ : List α) : Prop :=
  ∃ s t, s ≠ [] ∧ t ≠ [] ∧ s ++ l₁ ++ t = l₂


infixl:50 " <<+: " => IsStrictPrefix
infixl:50 " <<:+ " => IsStrictSuffix
infixl:50 " <<:+: " => IsStrictInfix


namespace IsStrictPrefix


theorem iff_prefix_len_lt (l₁ l₂ : List α)
    : l₁ <<+: l₂ ↔ l₁ <+: l₂ ∧ l₁.length < l₂.length := by
  constructor
  · intro ⟨t, htl, htr⟩
    constructor
    · exact ⟨t, htr⟩
    · rw [← htr, length_append]
      exact Nat.lt_add_of_pos_right (length_pos.mpr htl)
  · intro ⟨⟨t, ht⟩, h⟩
    exists t
    constructor
    · rw [← ht, length_append] at h
      exact length_pos.mp (Nat.pos_of_lt_add_right h)
    · exact ht

theorem iff_prefix_ne (l₁ l₂ : List α)
    : l₁ <<+: l₂ ↔ l₁ <+: l₂ ∧ l₁ ≠ l₂ := by
  constructor
  · intro ⟨t, htl, htr⟩
    constructor
    · exact ⟨t, htr⟩
    · suffices l₁.length ≠ l₂.length by exact this ∘ (congrArg length)
      rw [← htr, length_append]
      exact Nat.ne_of_lt (Nat.lt_add_of_pos_right (length_pos.mpr htl))
  · exact fun ⟨⟨t, ht⟩, h⟩ ↦ ⟨t, ⟨fun hc ↦ h (by rw [← ht, hc, append_nil]), ht⟩⟩


theorem trans {l₁ l₂ l₃ : List α} (h₁ : l₁ <<+: l₂) (h₂ : l₂ <<+: l₃)
    : (l₁ <<+: l₃) := by
  obtain ⟨t₁, htl₁, htr₁⟩ := h₁
  obtain ⟨t₂, _, htr₂⟩ := h₂
  exists t₁ ++ t₂
  constructor
  · exact append_ne_nil_of_left_ne_nil t₁ _ htl₁
  · rw [← append_assoc, htr₁, htr₂]


theorem length_lt {l₁ l₂ : List α} (h : l₁ <<+: l₂) : l₁.length < l₂.length :=
  ((iff_prefix_len_lt l₁ l₂).mp h).right


instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ <<+: l₂) :=
  decidable_of_decidable_of_iff <| (iff_prefix_len_lt l₁ l₂).symm


end IsStrictPrefix


theorem s_prefix_of_append {l₁ : List α} (l₂ : List α) (h : l₁ ≠ [])
    : l₂ <<+: l₂ ++ l₁ :=
  ⟨l₁, h, rfl⟩

theorem s_prefix_of_s_prefix_append {l₁ l₂ l₃ : List α} (h₁ : l₂ <<+: l₁ ++ l₃)
    (h₂ : l₁.length < l₂.length) : l₁ <<+: l₂ :=
  (IsStrictPrefix.iff_prefix_len_lt l₁ l₂).mpr ⟨prefix_of_prefix_append
    (((IsStrictPrefix.iff_prefix_len_lt l₂ (l₁ ++ l₃)).mp h₁).left) <| Nat.le_of_lt h₂, h₂⟩

theorem prefix_of_s_prefix {l₁ l₂ : List α} : l₁ <<+: l₂ → l₁ <+: l₂ :=
  fun ⟨t, _, htr⟩ ↦ ⟨t, htr⟩

theorem spx_of_px_of_spx {l₁ l₂ l₃ : List α} (h₁ : l₁ <+: l₂) (h₂ : l₂ <<+: l₃)
    : l₁ <<+: l₃ := by
  obtain ⟨t₁, ht⟩ := h₁
  obtain ⟨t₂, htl, htr⟩ := h₂
  exists t₁ ++ t₂
  constructor
  · exact append_ne_nil_of_ne_nil_right t₁ t₂ htl
  · rw [← append_assoc, ht, htr]


theorem prefix_of_eq {l₁ l₂ : List α} (h : l₁ = l₂) : l₁ <+: l₂ := by
  rw [h]; exact prefix_rfl

theorem suffix_of_eq {l₁ l₂ : List α} (h : l₁ = l₂) : l₁ <:+ l₂ := by
  rw [h]; exact suffix_rfl

theorem infix_of_eq {l₁ l₂ : List α} (h : l₁ = l₂) : l₁ <:+: l₂ := by
  rw [h]; exact infix_rfl


theorem get?_eq_of_prefix {l₁ l₂ : List α} (h : l₁ <+: l₂) {n : ℕ} (hn : n < l₁.length)
    : l₁.get? n = l₂.get? n := by
  obtain ⟨t, ht⟩ := h
  rw [← ht, List.get?_append hn]

theorem get_eq_of_prefix {l₁ l₂ : List α} (h : l₁ <+: l₂) {n : ℕ} (hn : n < l₁.length)
    : l₁.get ⟨n, hn⟩ = l₂.get ⟨n, Nat.lt_of_lt_of_le hn (IsPrefix.length_le h)⟩ := by
  apply Option.some_injective _
  simpa [← List.get?_eq_get] using get?_eq_of_prefix h hn


theorem prefix_of_proper_prefix {l₁ l₂ : List α} : l₁ <<+: l₂ → l₁ <+: l₂ :=
  fun ⟨t, _, htr⟩ ↦ ⟨t, htr⟩


end List
