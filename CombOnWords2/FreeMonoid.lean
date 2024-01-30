import CombOnWords2.simp_attr
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.List.Join

namespace FreeMonoid

infixr:90 " ∘* " => MonoidHom.comp

@[freemonoid_to_list]
def toList' (w : FreeMonoid α) : List α := w

@[freemonoid_to_list]
def one_eq_list_nil : (1 : FreeMonoid α) = ([] : List α) := rfl

@[freemonoid_to_list]
theorem mul_eq_list_append (v w : FreeMonoid α)
    : v * w = v.toList' ++ w.toList' :=
  rfl

@[freemonoid_to_list]
theorem map_eq_list_map (f : α → β) (fm : FreeMonoid α)
    : map f fm = List.map f fm := 
  rfl

def length' : FreeMonoid α →* Multiplicative ℕ where
  toFun    := List.length
  map_one' := List.length_nil
  map_mul' := List.length_append

def length (w : FreeMonoid α) : ℕ := length' w

-- Macro for length w as |w|
macro:max atomic("|" noWs) a:term noWs "|" : term => `(length $a)
def FreeMonoid.length.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()

@[freemonoid_to_list]
theorem length_eq_list_length (w : FreeMonoid α) : w.length = List.length w :=
  rfl

def join : FreeMonoid (FreeMonoid α) →* FreeMonoid α where
  toFun    := List.join
  map_one' := List.join_nil
  map_mul' := List.join_append

@[freemonoid_to_list]
theorem join_eq_list_join (w : FreeMonoid (FreeMonoid α)) : join w = List.join w :=
  rfl

def take (a : ℕ) (w : FreeMonoid α) : FreeMonoid α := List.take a w

@[freemonoid_to_list]
theorem take_eq_list_take (a : ℕ) (w : FreeMonoid α) : w.take a = List.take a w :=
  rfl

def drop (a : ℕ) (w : FreeMonoid α) : FreeMonoid α := List.drop a w

@[freemonoid_to_list]
theorem drop_eq_list_drop (a : ℕ) (w : FreeMonoid α) : w.drop a = List.drop a w :=
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
  apply Exists.intro <| f t
  rw [← map_mul]
  congr

theorem is_suffix_congr {fm₁ fm₂ : FreeMonoid α} (h : fm₁ <:* fm₂) (f : FreeMonoid α →* FreeMonoid β)
    : (f fm₁) <:* (f fm₂) := by
  rcases h with ⟨s, _⟩
  apply Exists.intro <| f s
  rw [← map_mul]
  congr

theorem is_infix_congr {fm₁ fm₂ : FreeMonoid α} (h : fm₁ <:*: fm₂) (f : FreeMonoid α →* FreeMonoid β)
    : (f fm₁) <:*: (f fm₂) := by
  rcases h with ⟨s, t, _⟩
  apply Exists.intro <| f s
  apply Exists.intro <| f t
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
