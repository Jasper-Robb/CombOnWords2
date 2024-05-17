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


def length' : FreeMonoid α →* Multiplicative ℕ where
  toFun    := List.length
  map_one' := List.length_nil
  map_mul' := List.length_append

def length (fm : FreeMonoid α) : ℕ := length' fm

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


def NonErasing (f : FreeMonoid α →* FreeMonoid β) : Prop :=
  ∀ (fm : FreeMonoid α), 0 < |fm| → 0 < |f fm|

class IsNonErasing (f : FreeMonoid α →* FreeMonoid β) : Prop where
  nonerasing : NonErasing f


structure NonErasingHomomorphism (α β : Type*) where
  toFun : FreeMonoid α →* FreeMonoid β
  nonerasing : @NonErasing α β toFun

structure NonErasingEndomorphism (α : Type*) where
  toFun : Monoid.End (FreeMonoid α)
  nonerasing : @NonErasing α α toFun

infixr:25 " [→*] " => NonErasingHomomorphism


instance : CoeFun (NonErasingHomomorphism α β) (fun _ ↦ FreeMonoid α → FreeMonoid β) where
  coe m := m.toFun

instance : CoeFun (NonErasingEndomorphism α) (fun _ ↦ FreeMonoid α → FreeMonoid α) where
  coe m := m.toFun


theorem nonerasing_iff {f : FreeMonoid α →* FreeMonoid β}
    : NonErasing f ↔ (∀ fm : FreeMonoid α, |fm| ≤ |f fm|) := by
  constructor
  · intro h fm
    induction fm with
    | nil => exact tsub_add_cancel_iff_le.mp rfl
    | cons x xs ih =>
      conv => lhs; change length' <| of x * ofList xs
      conv => rhs; change length' <| f <| of x * ofList xs
      simpa only [map_mul] using Nat.add_le_add (h [x] Nat.one_pos) ih
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


theorem prod2_length_le (fm : FreeMonoid α) (fm₁ fm₂ : FreeMonoid α) (h : fm = fm₁ * fm₂) 
    : |fm₁| ≤ |fm| ∧ |fm₂| ≤ |fm| := by
  apply congr_arg length at h
  simp only [freemonoid_to_list, List.length_append] at h
  constructor
  · exact Nat.le.intro h.symm
  · rw [add_comm] at h
    exact Nat.le.intro h.symm

theorem prod2_length_le₁ (fm : FreeMonoid α) (fm₁ fm₂ : FreeMonoid α) (h : fm = fm₁ * fm₂) 
    : |fm₁| ≤ |fm| :=
  (prod2_length_le fm fm₁ fm₂ h).left

theorem prod2_length_le₂ (fm : FreeMonoid α) (fm₁ fm₂ : FreeMonoid α) (h : fm = fm₁ * fm₂) 
    : |fm₂| ≤ |fm| :=
  (prod2_length_le fm fm₁ fm₂ h).right


theorem prod3_length_le (fm : FreeMonoid α) (fm₁ fm₂ fm₃ : FreeMonoid α) (h : fm = fm₁ * fm₂ * fm₃) 
    : |fm₁| ≤ |fm| ∧ |fm₂| ≤ |fm| ∧ |fm₃| ≤ |fm| := by
  apply congr_arg length at h
  simp only [freemonoid_to_list, List.length_append] at h
  constructor
  · rw [add_assoc] at h
    exact Nat.le.intro h.symm
  constructor
  · rw [add_comm, ← add_assoc, add_comm] at h
    exact Nat.le.intro h.symm
  · rw [add_comm] at h
    exact Nat.le.intro h.symm

theorem prod3_length_le₁ (fm : FreeMonoid α) (fm₁ fm₂ fm₃ : FreeMonoid α) (h : fm = fm₁ * fm₂ * fm₃) 
    : |fm₁| ≤ |fm| :=
  (prod3_length_le fm fm₁ fm₂ fm₃ h).left

theorem prod3_length_le₂ (fm : FreeMonoid α) (fm₁ fm₂ fm₃ : FreeMonoid α) (h : fm = fm₁ * fm₂ * fm₃) 
    : |fm₂| ≤ |fm| :=
  (prod3_length_le fm fm₁ fm₂ fm₃ h).right.left

theorem prod3_length_le₃ (fm : FreeMonoid α) (fm₁ fm₂ fm₃ : FreeMonoid α) (h : fm = fm₁ * fm₂ * fm₃) 
    : |fm₃| ≤ |fm| :=
  (prod3_length_le fm fm₁ fm₂ fm₃ h).right.right

