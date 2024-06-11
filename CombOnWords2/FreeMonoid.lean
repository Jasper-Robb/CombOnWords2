import CombOnWords2.simp_attr
import CombOnWords2.List
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.List.Join
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.ModEq


infixr:90 " ∘* " => MonoidHom.comp


namespace FreeMonoid


@[freemonoid_to_list]
def toList' (fm : FreeMonoid α) : List α := fm

@[freemonoid_to_list]
theorem one_eq_list_nil : (1 : FreeMonoid α) = ([] : List α) := rfl

@[freemonoid_to_list]
theorem of_eq_list_singleton {x : α} : of x = [x] := rfl

@[freemonoid_to_list]
theorem mul_eq_list_append (fm₁ fm₂ : FreeMonoid α)
    : fm₁ * fm₂ = fm₁.toList' ++ fm₂.toList' :=
  rfl

@[freemonoid_to_list]
theorem map_eq_list_map (f : α → β) (fm : FreeMonoid α)
    : map f fm = List.map f fm := 
  rfl


instance : Membership α (FreeMonoid α) :=
  ⟨List.Mem⟩

instance [Repr α] : Repr (FreeMonoid α) :=
  inferInstanceAs <| Repr (List α)

instance [DecidableEq α] : DecidableEq (FreeMonoid α) :=
  inferInstanceAs <| DecidableEq (List α)

instance [DecidableEq α] (a : α) (fm : FreeMonoid α) : Decidable (a ∈ fm) :=
  inferInstanceAs <| Decidable (a ∈ FreeMonoid.toList fm)


def length (fm : FreeMonoid α) : ℕ := 
  List.length fm

-- Macro for length fm as |fm|
macro:max atomic("|" noWs) a:term noWs "|" : term => `(length $a)
def FreeMonoid.length.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()

@[freemonoid_to_list]
theorem length_eq_list_length (fm : FreeMonoid α) : fm.length = List.length fm :=
  rfl

@[simp]
theorem length_mul (fm₁ fm₂ : FreeMonoid α) : (fm₁ * fm₂).length = fm₁.length + fm₂.length :=
  List.length_append fm₁ fm₂


@[freemonoid_to_list]
def join : FreeMonoid (FreeMonoid α) →* FreeMonoid α where
  toFun    := List.join
  map_one' := List.join_nil
  map_mul' := List.join_append


@[freemonoid_to_list]
def bind (f : α → FreeMonoid β) : FreeMonoid α →* FreeMonoid β where
  toFun    := fun fm ↦ List.bind fm f
  map_one' := List.nil_bind f
  map_mul' := fun fm₁ fm₂ ↦ List.append_bind fm₁ fm₂ f


@[freemonoid_to_list]
def take (a : ℕ) (fm : FreeMonoid α) : FreeMonoid α := List.take a fm

@[freemonoid_to_list]
def rtake (a : ℕ) (fm : FreeMonoid α) : FreeMonoid α := List.rtake fm a

@[freemonoid_to_list]
def drop (a : ℕ) (fm : FreeMonoid α) : FreeMonoid α := List.drop a fm

@[freemonoid_to_list]
def rdrop (a : ℕ) (fm : FreeMonoid α) : FreeMonoid α := List.rdrop fm a

@[freemonoid_to_list]
def reverse (fm : FreeMonoid α) : FreeMonoid α := List.reverse fm



@[simp]
theorem reverse_mul (fm₁ fm₂ : FreeMonoid α) : (fm₁ * fm₂).reverse = fm₂.reverse * fm₁.reverse :=
  List.reverse_append fm₁ fm₂

@[simp]
theorem length_reverse (fm : FreeMonoid α) : |fm.reverse| = |fm| := 
  List.length_reverse fm

@[simp]
theorem reverse_reverse (fm : FreeMonoid α) : fm.reverse.reverse = fm :=
  List.reverse_reverse fm


def NonErasing (f : FreeMonoid α →* FreeMonoid β) : Prop :=
  ∀ (fm : FreeMonoid α), 0 < |fm| → 0 < |f fm|

class IsNonErasing (f : FreeMonoid α →* FreeMonoid β) : Prop where
  nonerasing : NonErasing f


theorem nonerasing_iff {f : FreeMonoid α →* FreeMonoid β}
    : NonErasing f ↔ (∀ fm : FreeMonoid α, |fm| ≤ |f fm|) := by
  constructor
  · intro h fm
    induction' fm using FreeMonoid.recOn
    case h0 => exact tsub_add_cancel_iff_le.mp rfl
    case ih x xs ih => simpa using Nat.add_le_add (h [x] Nat.one_pos) ih
  · exact fun h fm hfm => Nat.lt_of_lt_of_le hfm <| h fm

theorem nonerasing_length_le (f : FreeMonoid α →* FreeMonoid β) [hf : IsNonErasing f] 
    : ∀ (fm : FreeMonoid α), |fm| ≤ |f fm| :=
  nonerasing_iff.mp hf.nonerasing

theorem nonerasing_length_le' (f : FreeMonoid α →* FreeMonoid β) [IsNonErasing f]
    : ∀ (fm : FreeMonoid α) (n : ℕ), |f fm| ≤ n → |fm| ≤ n :=
  fun fm₁ _ ↦ Nat.le_trans (nonerasing_length_le f fm₁)

theorem nonerasing_length_lt' (f : FreeMonoid α →* FreeMonoid β) [IsNonErasing f]
    : ∀ (fm : FreeMonoid α) (n : ℕ), |f fm| < n → |fm| < n :=
  fun fm _ ↦ Nat.lt_of_le_of_lt (nonerasing_length_le f fm)


theorem map_nonerasing {f : α → β} : NonErasing <| map f := 
  fun _ _ ↦ by simpa [freemonoid_to_list]

theorem bind_nonerasing {f : α → FreeMonoid β} (hf : ∀ x, 0 < |f x|)
    : NonErasing <| bind f := by
  rintro (_ | l) _
  · contradiction
  · simpa [freemonoid_to_list] using Or.inl <| hf l 


def Uniform (f : FreeMonoid α →* FreeMonoid β) (c : ℕ) : Prop :=
  ∀ fm, |f fm| = c * |fm|

class IsUniform (f : FreeMonoid α →* FreeMonoid β) (c : ℕ) : Prop where
  uniform : Uniform f c


theorem map_uniform {f : α → β} : Uniform (map f) 1 := by
  simp [Uniform, freemonoid_to_list]

theorem bind_uniform {f : α → FreeMonoid β} {c : ℕ} (hf : ∀ x, |f x| = c) : Uniform (bind f) c := by
  change ∀ x, (List.length ∘ f) x = c at hf
  simpa [Uniform, freemonoid_to_list, funext hf] using fun _ ↦ mul_comm _ _
  

theorem length_pow_uniform (f : Monoid.End (FreeMonoid α)) (c : ℕ) [hf : IsUniform f c]
    (n : ℕ) (fm : FreeMonoid α) : |(f^n : Monoid.End _) fm| = c^n * |fm| := by
  induction n with
  | zero => simp
  | succ k ih => 
    rw [pow_succ, pow_succ, Monoid.coe_mul, Function.comp_apply, hf.uniform _, ih, mul_assoc]

theorem length_of_length_uniform (f : FreeMonoid α →* FreeMonoid β) {c : ℕ}
    [hf : IsUniform f c] (hc : 0 < c) (fm : FreeMonoid α) : |fm| = |f fm| / c := by
  rw [hf.uniform, mul_comm, Nat.mul_div_left _ hc]

theorem length_lt_of_lt_length_uniform (f : FreeMonoid α →* FreeMonoid β) (c : ℕ)
    [hf : IsUniform f c] {n : ℕ} {fm : FreeMonoid α} (h : n < |f fm|) : n / c < |fm| :=
  Nat.div_lt_of_lt_mul <| by rwa [← hf.uniform]

theorem length_lt_of_pow (f : Monoid.End (FreeMonoid α)) (c : ℕ) [IsUniform f c]
    {n i : ℕ} (hi : i < c^n) : i < |(f^n : Monoid.End _) [x]| := by
  simpa [length_pow_uniform f c n [x], freemonoid_to_list]


theorem morphism_to_bind (f : FreeMonoid α →* FreeMonoid β) : f = bind (f ∘ of) :=
  hom_eq <| by simp [freemonoid_to_list]


def IsPrefix (fm₁ : FreeMonoid α) (fm₂ : FreeMonoid α) : Prop :=
  ∃ t, fm₁ * t = fm₂

def IsSuffix (fm₁ : FreeMonoid α) (fm₂ : FreeMonoid α) : Prop :=
  ∃ s, s * fm₁ = fm₂

def IsInfix (fm₁ : FreeMonoid α) (fm₂ : FreeMonoid α) : Prop :=
  ∃ s t, s * fm₁ * t = fm₂


infixl:50 " <*: " => IsPrefix
infixl:50 " <:* " => IsSuffix
infixl:50 " <:*: " => IsInfix


instance [DecidableEq α] (fm₁ fm₂ : FreeMonoid α) : Decidable (fm₁ <*: fm₂) :=
  inferInstanceAs <| Decidable (fm₁ <+: fm₂)

instance [DecidableEq α] (fm₁ fm₂ : FreeMonoid α) : Decidable (fm₁ <:* fm₂) :=
  inferInstanceAs <| Decidable (fm₁ <:+ fm₂)

instance [DecidableEq α] (fm₁ fm₂ : FreeMonoid α) : Decidable (fm₁ <:*: fm₂) :=
  inferInstanceAs <| Decidable (fm₁ <:+: fm₂)


@[freemonoid_to_list]
theorem is_prefix_iff_list_is_prefix (fm₁ fm₂ : FreeMonoid α) 
    : fm₁ <*: fm₂ ↔ fm₁ <+: fm₂ := 
  Iff.rfl

@[freemonoid_to_list]
theorem is_suffix_iff_list_is_suffix (fm₁ fm₂ : FreeMonoid α) 
    : fm₁ <:* fm₂ ↔ fm₁ <:+ fm₂ :=
  Iff.rfl

@[freemonoid_to_list]
theorem is_infix_iff_list_is_infix (fm₁ fm₂ : FreeMonoid α) 
    : fm₁ <:*: fm₂ ↔ fm₁ <:+: fm₂ := 
  Iff.rfl


@[simp]
theorem reverse_infix (fm₁ fm₂ : FreeMonoid α) : fm₁.reverse <:*: fm₂.reverse ↔ fm₁ <:*: fm₂ :=
  List.reverse_infix


theorem is_prefix_congr {fm₁ fm₂ : FreeMonoid α} (h : fm₁ <*: fm₂) (f : FreeMonoid α →* FreeMonoid β)
    : (f fm₁) <*: (f fm₂) := by
  obtain ⟨t, _⟩ := h
  exists f t
  rw [← map_mul]
  congr

theorem is_suffix_congr {fm₁ fm₂ : FreeMonoid α} (h : fm₁ <:* fm₂) (f : FreeMonoid α →* FreeMonoid β)
    : (f fm₁) <:* (f fm₂) := by
  obtain ⟨s, _⟩ := h
  exists f s
  rw [← map_mul]
  congr

theorem is_infix_congr {fm₁ fm₂ : FreeMonoid α} (h : fm₁ <:*: fm₂) (f : FreeMonoid α →* FreeMonoid β)
    : (f fm₁) <:*: (f fm₂) := by
  obtain ⟨s, t, _⟩ := h
  exists f s, f t
  simp only [← map_mul]
  congr


def RightExtensions (fm : FreeMonoid α) : Set (FreeMonoid α) :=
  {p | fm <*: p}

def LeftExtensions (fm : FreeMonoid α) : Set (FreeMonoid α) :=
  {s | fm <:* s}

def Extensions (fm : FreeMonoid α) : Set (FreeMonoid α) :=
  RightExtensions fm ∪ LeftExtensions fm 


@[freemonoid_to_list]
def inits : FreeMonoid α → FreeMonoid (FreeMonoid α) :=
  List.inits

@[freemonoid_to_list]
def tails : FreeMonoid α → FreeMonoid (FreeMonoid α) :=
  List.tails

@[freemonoid_to_list]
def infixes : FreeMonoid α → FreeMonoid (FreeMonoid α) :=
  List.infixes


def Overlap (fm : FreeMonoid α) : Prop :=
  ∃ B : FreeMonoid α, 0 < |B| ∧ fm = B * B * B.take 1

def HasOverlap (fm : FreeMonoid α) : Prop :=
  ∃ u : FreeMonoid α, Overlap u ∧ u <:*: fm


theorem overlap_of_nonerasing {f : FreeMonoid α →* FreeMonoid β} [hf : IsNonErasing f]
    {fm : FreeMonoid α} (hfm : HasOverlap fm) : HasOverlap (f fm) := by
  obtain ⟨u, ⟨B, hBl, hBr⟩, hur⟩ := hfm
  exists f B * f B * (f B).take 1
  constructor
  · exact ⟨f B, hf.nonerasing B hBl, rfl⟩
  · suffices f B * f B * (f B).take 1 <*: f u by
      exact List.IsInfix.trans (List.IsPrefix.isInfix this) <| is_infix_congr hur f
    simp only [hBr, map_mul]
    cases' B using FreeMonoid.casesOn
    case h0 => contradiction
    case ih x xs =>
      rw [map_mul]
      simp only [freemonoid_to_list, List.singleton_append, List.take_cons_succ, List.take_zero,
                 List.prefix_append_right_inj]
      rw [List.take_append_of_le_length]
      · exact List.take_prefix _ _
      · exact hf.nonerasing [x] (by simp [freemonoid_to_list])


theorem overlap_reverse (fm : FreeMonoid α) (hfm : Overlap fm) : Overlap fm.reverse := by
  obtain ⟨B, hBl, hBr⟩ := hfm
  exists B.take 1 * B.reverse.rdrop 1
  constructor
  · simpa [freemonoid_to_list] using Or.inl hBl
  · simp only [← mul_assoc]
    simp only [freemonoid_to_list]
    rw [List.take_append_of_le_length, List.take_take, min_self]
    · conv => rhs; rw [List.append_assoc]; lhs; rw [List.append_assoc]
      have : List.rdrop (List.reverse B) 1 ++ List.take 1 B = List.reverse B := by
        rw [← List.reverse_eq_iff, List.reverse_append, List.rdrop_eq_reverse_drop_reverse,
            List.reverse_reverse, List.reverse_reverse, List.reverse_take_one, List.take_append_drop]
      simp [this, hBr, freemonoid_to_list, List.reverse_append]
    · rwa [List.length_take, Nat.min_eq_left]

theorem overlap_reverse_iff (fm : FreeMonoid α) : Overlap fm ↔ Overlap fm.reverse := by
  constructor
  · exact overlap_reverse fm
  · intro h
    rw [← reverse_reverse fm]
    exact overlap_reverse (reverse fm) h

theorem has_overlap_reverse (fm : FreeMonoid α) : HasOverlap fm → HasOverlap fm.reverse :=
  fun ⟨u, hul, hur⟩ ↦ ⟨u.reverse, ⟨overlap_reverse u hul, List.reverse_infix.mpr hur⟩⟩

theorem has_overlap_reverse_iff (fm : FreeMonoid α) : HasOverlap fm ↔ HasOverlap fm.reverse := by
  constructor
  · exact has_overlap_reverse fm
  · intro h
    rw [← reverse_reverse fm]
    exact has_overlap_reverse (reverse fm) h


theorem overlap_iff (u : FreeMonoid α) : 2 < |u| ∧ u = u.take (|u| / 2) ^ 2 * u.take 1 ↔ Overlap u := by
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

theorem has_overlap_iff (fm : FreeMonoid α) 
    : (∃ u ∈ fm.infixes, Overlap u) ↔ HasOverlap fm :=
  ⟨fun ⟨u, hul, hur⟩ ↦ ⟨u, ⟨hur, (List.mem_infixes u fm).mp hul⟩⟩,
   fun ⟨u, hul, hur⟩ ↦ ⟨u, ⟨(List.mem_infixes u fm).mpr hur, hul⟩⟩⟩

theorem factor_no_overlap_of_no_overlap {fm₁ fm₂ : FreeMonoid α} (hvw : fm₁ <:*: fm₂) (hw : ¬HasOverlap fm₂)
    : ¬HasOverlap fm₁ :=
  fun ⟨u, hul, hur⟩ => hw ⟨u, ⟨hul, List.IsInfix.trans hur hvw⟩⟩


instance [DecidableEq α] (fm : FreeMonoid α) : Decidable (Overlap fm) := 
  decidable_of_decidable_of_iff <| overlap_iff fm

instance [DecidableEq α] (u : FreeMonoid α) : Decidable (HasOverlap u) :=
  decidable_of_decidable_of_iff <| has_overlap_iff u

