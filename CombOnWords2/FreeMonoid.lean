import CombOnWords2.simp_attr
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

def join : FreeMonoid (FreeMonoid α) →* FreeMonoid α where
  toFun    := List.join
  map_one' := List.join_nil
  map_mul' := List.join_append

@[freemonoid_to_list]
theorem join_eq_list_join (fm : FreeMonoid (FreeMonoid α)) : join fm = List.join fm :=
  rfl

def take (a : ℕ) (fm : FreeMonoid α) : FreeMonoid α := List.take a fm

@[freemonoid_to_list]
theorem take_eq_list_take (a : ℕ) (fm : FreeMonoid α) : fm.take a = List.take a fm :=
  rfl

def drop (a : ℕ) (fm : FreeMonoid α) : FreeMonoid α := List.drop a fm

@[freemonoid_to_list]
theorem drop_eq_list_drop (a : ℕ) (fm : FreeMonoid α) : fm.drop a = List.drop a fm :=
  rfl

def NonErasing (f : FreeMonoid α →* FreeMonoid β) : Prop :=
    ∀ (fm : FreeMonoid α), 0 < |fm| → 0 < |f fm|

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

theorem map_nonerasing {f : α → β} : NonErasing <| map f := by
  intro fm hfm
  simpa only [freemonoid_to_list, List.length_map]

theorem join_map_nonerasing {f : α → FreeMonoid β} (hf : ∀ x, 0 < |f x|)
    : NonErasing <| join ∘* map f := by
  intro fm hfm
  cases fm with
  | nil => contradiction
  | cons x xs => simpa [freemonoid_to_list] using Or.inl <| hf x

section instances

variable {α : Type*} [DecidableEq α]

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
