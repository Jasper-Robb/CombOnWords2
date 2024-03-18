import CombOnWords2.simp_attr
import CombOnWords2.List
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.List.Join


infixr:90 " ∘* " => MonoidHom.comp


namespace FreeMonoid


@[freemonoid_to_list]
def toList' (fm : FreeMonoid α) : List α := fm

@[freemonoid_to_list]
def one_eq_list_nil : (1 : FreeMonoid α) = ([] : List α) := rfl

@[freemonoid_to_list]
theorem mul_eq_list_append (fm₁ fm₂ : FreeMonoid α)
    : fm₁ * fm₂ = fm₁.toList' ++ fm₂.toList' :=
  rfl

@[freemonoid_to_list]
theorem map_eq_list_map (f : α → β) (fm : FreeMonoid α)
    : map f fm = List.map f fm := 
  rfl


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
def take (a : ℕ) (fm : FreeMonoid α) : FreeMonoid α := List.take a fm

@[freemonoid_to_list]
def drop (a : ℕ) (fm : FreeMonoid α) : FreeMonoid α := List.drop a fm


def NonErasing (f : FreeMonoid α →* FreeMonoid β) : Prop :=
    ∀ (fm : FreeMonoid α), 0 < |fm| → 0 < |f fm|

instance : LE (Multiplicative ℕ) := inferInstanceAs (LE ℕ)

theorem nonerasing_iff (f : FreeMonoid α →* FreeMonoid β)
    : NonErasing f ↔ (∀ fm, |fm| ≤ |f fm|) := by
  constructor
  · intro h fm
    induction fm with
    | nil => exact tsub_add_cancel_iff_le.mp rfl
    | cons x xs ih =>
      change length' (of x * ofList xs) ≤ length' (f (of x * ofList xs))
      simpa only [map_mul] using Nat.add_le_add (h [x] Nat.one_pos) ih
  · exact fun h fm hfm => Nat.lt_of_lt_of_le hfm <| h fm


def IsPrefix (fm₁ : FreeMonoid α) (fm₂ : FreeMonoid α) : Prop :=
  ∃ t, fm₁ * t = fm₂

def IsSuffix (fm₁ : FreeMonoid α) (fm₂ : FreeMonoid α) : Prop :=
  ∃ s, s * fm₁ = fm₂

def IsInfix (fm₁ : FreeMonoid α) (fm₂ : FreeMonoid α) : Prop :=
  ∃ s t, s * fm₁ * t = fm₂

infixl:50 " <*: " => IsPrefix
infixl:50 " <:* " => IsSuffix
infixl:50 " <:*: " => IsInfix


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
  rcases h with ⟨t, _⟩
  exists f t
  rw [← map_mul]
  congr

theorem is_suffix_congr {fm₁ fm₂ : FreeMonoid α} (h : fm₁ <:* fm₂) (f : FreeMonoid α →* FreeMonoid β)
    : (f fm₁) <:* (f fm₂) := by
  rcases h with ⟨s, _⟩
  exists f s
  rw [← map_mul]
  congr

theorem is_infix_congr {fm₁ fm₂ : FreeMonoid α} (h : fm₁ <:*: fm₂) (f : FreeMonoid α →* FreeMonoid β)
    : (f fm₁) <:*: (f fm₂) := by
  rcases h with ⟨s, t, _⟩
  exists f s, f t
  repeat rw [← map_mul]
  congr


def RightExtensions (fm : FreeMonoid α) : Set (FreeMonoid α) :=
  {p | fm <*: p}

def LeftExtensions (fm : FreeMonoid α) : Set (FreeMonoid α) :=
  {s | fm <:* s}

def Extensions (fm : FreeMonoid α) : Set (FreeMonoid α) :=
  RightExtensions fm ∪ LeftExtensions fm 


@[freemonoid_to_list]
def inits (fm : FreeMonoid α) : FreeMonoid (FreeMonoid α) :=
  List.inits fm

@[freemonoid_to_list]
def tails (fm : FreeMonoid α) : FreeMonoid (FreeMonoid α) :=
  List.tails fm

@[freemonoid_to_list]
def infixes (fm : FreeMonoid α) : FreeMonoid (FreeMonoid α) :=
  List.infixes fm


theorem map_nonerasing {f : α → β} : NonErasing <| map f := by
  intro _ _
  simpa [freemonoid_to_list]

theorem join_map_nonerasing {f : α → FreeMonoid β} (hf : ∀ x, 0 < |f x|)
    : NonErasing <| join ∘* map f := by
  rintro (_ | l) _
  · contradiction
  · simpa [freemonoid_to_list] using Or.inl <| hf l


section instances

variable {α : Type*} [DecidableEq α] [Repr α]

instance : Repr (FreeMonoid α) :=
  inferInstanceAs <| Repr (List α)

instance : Membership α (FreeMonoid α) :=
  ⟨List.Mem⟩

instance : DecidableEq (FreeMonoid α) :=
  inferInstanceAs <| DecidableEq (List α)

instance (a : α) (fm : FreeMonoid α) : Decidable (a ∈ fm) :=
  inferInstanceAs <| Decidable (a ∈ FreeMonoid.toList fm)

instance (fm₁ fm₂ : FreeMonoid α) : Decidable (fm₁ <:* fm₂) :=
  inferInstanceAs <| Decidable (fm₁ <:+ fm₂)

instance (fm₁ fm₂ : FreeMonoid α) : Decidable (fm₁ <*: fm₂) :=
  inferInstanceAs <| Decidable (fm₁ <+: fm₂)

instance (fm₁ fm₂ : FreeMonoid α) : Decidable (fm₁ <:*: fm₂) :=
  inferInstanceAs <| Decidable (fm₁ <:+: fm₂)

end instances


theorem prod2_length_le (fm : FreeMonoid α) (fm₁ fm₂ : FreeMonoid α) (h : fm = fm₁ * fm₂) 
    : |fm₁| ≤ |fm| ∧ |fm₂| ≤ |fm| := by
  apply congr_arg length at h
  simp only [freemonoid_to_list, List.length_append] at h
  constructor
  · exact Nat.le.intro h.symm
  · rw [add_comm] at h
    exact Nat.le.intro h.symm

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

