import CombOnWords2.simp_attr
import CombOnWords2.List
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.List.Infix


infixr:90 " ∘* " => MonoidHom.comp


namespace FreeMonoid


section Init


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
def length.unexpander : Lean.PrettyPrinter.Unexpander
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


end Init -- Close section


section NonErasing


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


end NonErasing -- Close section


section Uniform


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


end Uniform -- Close section


theorem morphism_to_bind (f : FreeMonoid α →* FreeMonoid β) : f = bind (f ∘ of) :=
  hom_eq <| by simp [freemonoid_to_list]


section Infix


def IsPrefix (fm₁ : FreeMonoid α) (fm₂ : FreeMonoid α) : Prop :=
  ∃ t, fm₁ * t = fm₂

def IsSuffix (fm₁ : FreeMonoid α) (fm₂ : FreeMonoid α) : Prop :=
  ∃ s, s * fm₁ = fm₂

def IsInfix (fm₁ : FreeMonoid α) (fm₂ : FreeMonoid α) : Prop :=
  ∃ s t, s * fm₁ * t = fm₂


def IsPPrefix (fm₁ fm₂ : FreeMonoid α) : Prop :=
  ∃ t ≠ 1, fm₁ * t = fm₂

def IsPSuffix (fm₁ fm₂ : FreeMonoid α) : Prop :=
  ∃ s ≠ 1, s * fm₁ = fm₂

def IsPInfix (fm₁ fm₂ : FreeMonoid α) : Prop :=
  ∃ s t, s ≠ 1 ∧ t ≠ 1 ∧ s * fm₁ * t = fm₂


infixl:50 " ≤ₚ " => IsPrefix
infixl:50 " ≤ₛ " => IsSuffix
infixl:50 " ≤ᵢ " => IsInfix

infixl:50 " <ₚ " => IsPPrefix
infixl:50 " <ₛ " => IsPSuffix
infixl:50 " <ᵢ " => IsPInfix


instance [DecidableEq α] (fm₁ fm₂ : FreeMonoid α) : Decidable (fm₁ ≤ₚ fm₂) :=
  inferInstanceAs <| Decidable (fm₁ <+: fm₂)

instance [DecidableEq α] (fm₁ fm₂ : FreeMonoid α) : Decidable (fm₁ ≤ₛ fm₂) :=
  inferInstanceAs <| Decidable (fm₁ <:+ fm₂)

instance [DecidableEq α] (fm₁ fm₂ : FreeMonoid α) : Decidable (fm₁ ≤ᵢ fm₂) :=
  inferInstanceAs <| Decidable (fm₁ <:+: fm₂)


@[freemonoid_to_list]
theorem is_prefix_iff_list_is_prefix (fm₁ fm₂ : FreeMonoid α) 
    : fm₁ ≤ₚ fm₂ ↔ fm₁ <+: fm₂ := 
  Iff.rfl

@[freemonoid_to_list]
theorem is_suffix_iff_list_is_suffix (fm₁ fm₂ : FreeMonoid α) 
    : fm₁ ≤ₛ fm₂ ↔ fm₁ <:+ fm₂ :=
  Iff.rfl

@[freemonoid_to_list]
theorem is_infix_iff_list_is_infix (fm₁ fm₂ : FreeMonoid α) 
    : fm₁ ≤ᵢ fm₂ ↔ fm₁ <:+: fm₂ := 
  Iff.rfl


@[freemonoid_to_list]
theorem is_p_prefix_iff_list_is_p_prefix (fm₁ fm₂ : FreeMonoid α)
    : fm₁ <ₚ fm₂ ↔ fm₁ <<+: fm₂ :=
  Iff.rfl

@[freemonoid_to_list]
theorem is_p_suffix_iff_list_is_p_suffix (fm₁ fm₂ : FreeMonoid α)
    : fm₁ <ₛ fm₂ ↔ fm₁ <<:+ fm₂ :=
  Iff.rfl

@[freemonoid_to_list]
theorem is_p_infix_iff_list_is_p_infix (fm₁ fm₂ : FreeMonoid α)
    : fm₁ <ᵢ fm₂ ↔ fm₁ <<:+: fm₂ :=
  Iff.rfl


@[simp]
theorem reverse_infix (fm₁ fm₂ : FreeMonoid α) : fm₁.reverse ≤ᵢ fm₂.reverse ↔ fm₁ ≤ᵢ fm₂ :=
  List.reverse_infix


theorem is_prefix_congr {fm₁ fm₂ : FreeMonoid α} (h : fm₁ ≤ₚ fm₂) (f : FreeMonoid α →* FreeMonoid β)
    : (f fm₁) ≤ₚ (f fm₂) := by
  obtain ⟨t, _⟩ := h
  exists f t
  rw [← map_mul]
  congr

theorem is_suffix_congr {fm₁ fm₂ : FreeMonoid α} (h : fm₁ ≤ₛ fm₂) (f : FreeMonoid α →* FreeMonoid β)
    : (f fm₁) ≤ₛ (f fm₂) := by
  obtain ⟨s, _⟩ := h
  exists f s
  rw [← map_mul]
  congr

theorem is_infix_congr {fm₁ fm₂ : FreeMonoid α} (h : fm₁ ≤ᵢ fm₂) (f : FreeMonoid α →* FreeMonoid β)
    : (f fm₁) ≤ᵢ (f fm₂) := by
  obtain ⟨s, t, _⟩ := h
  exists f s, f t
  simp only [← map_mul]
  congr


@[freemonoid_to_list]
def inits : FreeMonoid α → FreeMonoid (FreeMonoid α) :=
  List.inits

@[freemonoid_to_list]
def tails : FreeMonoid α → FreeMonoid (FreeMonoid α) :=
  List.tails

@[freemonoid_to_list]
def infixes : FreeMonoid α → FreeMonoid (FreeMonoid α) :=
  List.infixes


theorem mem_inits (u v : FreeMonoid α) : u ∈ v.inits ↔ u ≤ₚ v :=
  List.mem_inits u v

theorem mem_tails (u v : FreeMonoid α) : u ∈ v.tails ↔ u ≤ₛ v :=
  List.mem_tails u v

theorem mem_infixes (u v : FreeMonoid α) : u ∈ v.infixes ↔ u ≤ᵢ v :=
  List.mem_infixes u v


end Infix -- Close section


section Overlap


def Overlap (fm : FreeMonoid α) : Prop :=
  ∃ B : FreeMonoid α, 0 < |B| ∧ fm = B * B * B.take 1

def HasOverlap (fm : FreeMonoid α) : Prop :=
  ∃ u : FreeMonoid α, Overlap u ∧ u ≤ᵢ fm


theorem overlap_of_nonerasing {f : FreeMonoid α →* FreeMonoid β} [hf : IsNonErasing f]
    {fm : FreeMonoid α} (hfm : HasOverlap fm) : HasOverlap (f fm) := by
  obtain ⟨u, ⟨B, hBl, hBr⟩, hur⟩ := hfm
  exists f B * f B * (f B).take 1
  constructor
  · exact ⟨f B, hf.nonerasing B hBl, rfl⟩
  · suffices f B * f B * (f B).take 1 ≤ₚ f u by
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

theorem factor_no_overlap_of_no_overlap {fm₁ fm₂ : FreeMonoid α} (hvw : fm₁ ≤ᵢ fm₂) (hw : ¬HasOverlap fm₂)
    : ¬HasOverlap fm₁ :=
  fun ⟨u, hul, hur⟩ => hw ⟨u, ⟨hul, List.IsInfix.trans hur hvw⟩⟩


instance [DecidableEq α] (fm : FreeMonoid α) : Decidable (Overlap fm) := 
  decidable_of_decidable_of_iff <| overlap_iff fm

instance [DecidableEq α] (u : FreeMonoid α) : Decidable (HasOverlap u) :=
  decidable_of_decidable_of_iff <| has_overlap_iff u


end Overlap


end FreeMonoid -- Close namespace


section Decidable


variable {α β : Type*} [Fintype α] [Fintype β] 


open FreeMonoid


def allFreeMonoidsOfLength (α : Type*) [h : Fintype α] (n : ℕ) : Multiset (FreeMonoid α) :=
  (@Vector.fintype α h n).elems.val.map Vector.toList

def allFreeMonoidsMaxLength (α : Type*) [Fintype α] : ℕ → Multiset (FreeMonoid α)
  | 0 => 0
  | n+1 => allFreeMonoidsMaxLength α n + allFreeMonoidsOfLength α n


theorem length_mem_allFreeMonoidsOfLength (n : ℕ) : ∀ w ∈ allFreeMonoidsOfLength α n, |w| = n := by
  simpa [allFreeMonoidsOfLength] using fun a _ ↦ a.prop

theorem length_mem_allFreeMonoidsMaxLength (n : ℕ) : ∀ w ∈ allFreeMonoidsMaxLength α n, |w| < n := by
  induction n with
  | zero => simp [allFreeMonoidsMaxLength, freemonoid_to_list]
  | succ n ih =>
    simp only [allFreeMonoidsMaxLength, Multiset.mem_add]
    rintro a (hal | har)
    · exact Nat.lt.step (ih a hal)
    · exact Nat.lt_succ.mpr <| Nat.le_of_eq <| length_mem_allFreeMonoidsOfLength n a har


theorem mem_allFreeMonoidsOfLength (n : ℕ) (w : FreeMonoid α) (hw : |w| = n) : w ∈ allFreeMonoidsOfLength α n := by
  simpa [allFreeMonoidsOfLength] using ⟨⟨w, hw⟩, ⟨Fintype.complete _, rfl⟩⟩

theorem mem_allFreeMonoidsMaxLength (n : ℕ) (w : FreeMonoid α) (hw : |w| < n) : w ∈ allFreeMonoidsMaxLength α n := by
  induction n with
  | zero => exact (Nat.not_lt_zero _ hw).elim
  | succ n ih =>
    rw [allFreeMonoidsMaxLength, Multiset.mem_add]
    cases Order.lt_succ_iff_eq_or_lt.mp hw with
    | inl hl => exact Or.inr <| mem_allFreeMonoidsOfLength n w hl
    | inr hr => exact Or.inl <| ih hr
    

theorem mem_allFreeMonoidsOfLength_iff (n : ℕ) (w : FreeMonoid α) : w ∈ allFreeMonoidsOfLength α n ↔ |w| = n :=
  ⟨length_mem_allFreeMonoidsOfLength n w, mem_allFreeMonoidsOfLength n w⟩

theorem mem_allFreeMonoidsMaxLength_iff (n : ℕ) (w : FreeMonoid α) : w ∈ allFreeMonoidsMaxLength α n ↔ |w| < n :=
  ⟨length_mem_allFreeMonoidsMaxLength n w, mem_allFreeMonoidsMaxLength n w⟩


theorem nodup_allFreeMonoidsOfLength (n : ℕ) : (allFreeMonoidsOfLength α n).Nodup :=
  Multiset.Nodup.map Vector.eq Fintype.elems.nodup

theorem nodup_allFreeMonoidsMaxLength (n : ℕ) : (allFreeMonoidsMaxLength α n).Nodup := by
  induction n with
  | zero => exact Multiset.nodup_zero
  | succ n ih =>
    rw [allFreeMonoidsMaxLength, Multiset.nodup_add]
    constructor <;> try constructor
    · exact ih
    · exact nodup_allFreeMonoidsOfLength n
    · exact fun fm hfm₁ hfm₂ ↦
        LT.lt.false <| Eq.trans_lt (length_mem_allFreeMonoidsOfLength n fm hfm₂).symm <|
          length_mem_allFreeMonoidsMaxLength n fm hfm₁


def allFreeMonoidsOfLength' (α : Type*) [Fintype α] (n : ℕ) : Finset (FreeMonoid α) :=
  ⟨allFreeMonoidsOfLength α n, nodup_allFreeMonoidsOfLength n⟩

def allFreeMonoidsMaxLength' (α : Type*) [Fintype α] (n : ℕ) : Finset (FreeMonoid α) :=
  ⟨allFreeMonoidsMaxLength α n, nodup_allFreeMonoidsMaxLength n⟩


theorem mem_allFreeMonoidsOfLength'_iff (n : ℕ) (w : FreeMonoid α) : w ∈ allFreeMonoidsOfLength' α n ↔ |w| = n :=
  mem_allFreeMonoidsOfLength_iff n w

theorem mem_allFreeMonoidsMaxLength'_iff (n : ℕ) (w : FreeMonoid α) : w ∈ allFreeMonoidsMaxLength' α n ↔ |w| < n :=
  mem_allFreeMonoidsMaxLength_iff n w


instance [DecidablePred p] {m : Multiset β} : Decidable (∃ x ∈ m, p x) :=
  Multiset.decidableExistsMultiset

instance [DecidablePred p] {m : Multiset β} : Decidable (∀ x ∈ m, p x) :=
  Multiset.decidableForallMultiset


instance [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |w| = n ∧ p w) :=
  decidable_of_decidable_of_iff <| 
    exists_congr fun w ↦ and_congr_left fun _ ↦ mem_allFreeMonoidsOfLength_iff n w

instance [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |w| < n ∧ p w) :=
  decidable_of_decidable_of_iff <| 
    exists_congr fun w ↦ and_congr_left fun _ ↦ mem_allFreeMonoidsMaxLength_iff n w

instance [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |w| ≤ n ∧ p w) :=
  decidable_of_decidable_of_iff <| 
    exists_congr fun w ↦ and_congr_left fun _ ↦ (mem_allFreeMonoidsMaxLength_iff (n+1) w).trans Nat.lt_succ

instance [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |w| = n → p w) :=
  decidable_of_decidable_of_iff <| 
    forall_congr' fun w ↦ imp_congr_left <| mem_allFreeMonoidsOfLength_iff n w

instance [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |w| < n → p w) :=
  decidable_of_decidable_of_iff <| 
    forall_congr' fun w ↦ imp_congr_left <| mem_allFreeMonoidsMaxLength_iff n w

instance [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |w| ≤ n → p w) :=
  decidable_of_decidable_of_iff <| 
    forall_congr' fun w ↦ imp_congr_left <| (mem_allFreeMonoidsMaxLength_iff (n+1) w).trans Nat.lt_succ


instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∃ w , w ≤ₚ fm ∧ p w) :=
  decidable_of_decidable_of_iff <| exists_congr fun w ↦ and_congr_left fun _ ↦ List.mem_inits w fm

instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∃ w, w ≤ₛ fm ∧ p w) :=
  decidable_of_decidable_of_iff <| exists_congr fun w ↦ and_congr_left fun _ ↦ List.mem_tails w fm

instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∃ w, w ≤ᵢ fm ∧ p w) :=
  decidable_of_decidable_of_iff <| exists_congr fun w ↦ and_congr_left fun _ ↦ List.mem_infixes w fm

instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∀ w, w ≤ₚ fm → p w) :=
  decidable_of_decidable_of_iff <| forall_congr' fun w ↦ imp_congr_left <| List.mem_inits w fm

instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∀ w, w ≤ₛ fm → p w) :=
  decidable_of_decidable_of_iff <| forall_congr' fun w ↦ imp_congr_left <| List.mem_tails w fm

instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∀ w, w ≤ᵢ fm → p w) :=
  decidable_of_decidable_of_iff <| forall_congr' fun w ↦ imp_congr_left <| List.mem_infixes w fm


instance [IsNonErasing f] [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |f w| < n ∧ p w) :=
  decidable_of_decidable_of_iff <|
    show (∃ w : FreeMonoid α, |w| < n ∧ |f w| < n ∧ p w) ↔ (∃ w, |f w| < n ∧ p w) from
      ⟨fun ⟨w, _, hw₂, hw₃⟩ ↦ Exists.intro w ⟨hw₂, hw₃⟩,
        fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, ⟨nonerasing_length_lt' f w n hw₁, hw₁, hw₂⟩⟩⟩

instance [IsNonErasing f] [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |f w| ≤ n ∧ p w) :=
  decidable_of_decidable_of_iff <|
    show (∃ w : FreeMonoid α, |w| ≤ n ∧ |f w| ≤ n ∧ p w) ↔ (∃ w, |f w| ≤ n ∧ p w) from
      ⟨fun ⟨w, _, hw₂, hw₃⟩ ↦ Exists.intro w ⟨hw₂, hw₃⟩,
        fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, ⟨nonerasing_length_le' f w n hw₁, hw₁, hw₂⟩⟩⟩

instance [IsNonErasing f] [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |f w| < n → p w) :=
  decidable_of_decidable_of_iff <|
    show (∀ w : FreeMonoid α, |w| < n → |f w| < n → p w) ↔ (∀ w, |f w| < n → p w) from
      ⟨fun h₁ w h₂ ↦ h₁ w (nonerasing_length_lt' f w n h₂) h₂, fun h₁ w _ h₃ ↦ h₁ w h₃⟩

instance [IsNonErasing f] [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |f w| ≤ n → p w) :=
  decidable_of_decidable_of_iff <|
    show (∀ w : FreeMonoid α, |w| ≤ n → |f w| ≤ n → p w) ↔ (∀ w, |f w| ≤ n → p w) from
      ⟨fun h₁ w h₂ ↦ h₁ w (nonerasing_length_le' f w n h₂) h₂, fun h₁ w _ h₃ ↦ h₁ w h₃⟩


instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {fm : FreeMonoid β}
    : Decidable (∃ w : FreeMonoid α, f w ≤ₚ fm ∧ p w) :=
  decidable_of_decidable_of_iff <|
    show (∃ w : FreeMonoid α, |w| ≤ |fm| ∧ f w ≤ₚ fm ∧ p w) ↔ (∃ w, f w ≤ₚ fm ∧ p w) from
      ⟨fun ⟨w, _, hw₂, hw₃⟩ ↦ Exists.intro w ⟨hw₂, hw₃⟩,
        fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, ⟨Nat.le_trans (nonerasing_length_le f w) (List.IsPrefix.length_le hw₁), hw₁, hw₂⟩⟩⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {fm : FreeMonoid β}
    : Decidable (∃ w : FreeMonoid α, f w ≤ₛ fm ∧ p w) :=
  decidable_of_decidable_of_iff <|
    show (∃ w : FreeMonoid α, |w| ≤ |fm| ∧ f w ≤ₛ fm ∧ p w) ↔ (∃ w, f w ≤ₛ fm ∧ p w) from
      ⟨fun ⟨w, _, hw₂, hw₃⟩ ↦ Exists.intro w ⟨hw₂, hw₃⟩,
        fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, ⟨Nat.le_trans (nonerasing_length_le f w) (List.IsSuffix.length_le hw₁), hw₁, hw₂⟩⟩⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {fm : FreeMonoid β}
    : Decidable (∃ w : FreeMonoid α, f w ≤ᵢ fm ∧ p w) :=
  decidable_of_decidable_of_iff <|
    show (∃ w : FreeMonoid α, |w| ≤ |fm| ∧ f w ≤ᵢ fm ∧ p w) ↔ (∃ w, f w ≤ᵢ fm ∧ p w) from
      ⟨fun ⟨w, _, hw₂, hw₃⟩ ↦ Exists.intro w ⟨hw₂, hw₃⟩,
        fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, ⟨Nat.le_trans (nonerasing_length_le f w) (List.IsInfix.length_le hw₁), hw₁, hw₂⟩⟩⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {fm : FreeMonoid β}
    : Decidable (∀ w : FreeMonoid α, f w ≤ₚ fm → p w) :=
  decidable_of_decidable_of_iff <|
    show (∀ w : FreeMonoid α, |w| ≤ |fm| → f w ≤ₚ fm → p w) ↔ (∀ w, f w ≤ₚ fm → p w) from
      ⟨fun h w hw ↦ h w (Nat.le_trans (nonerasing_length_le f w) (List.IsPrefix.length_le hw)) hw,
        fun h w _ hw₂ ↦ h w hw₂⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {fm : FreeMonoid β}
    : Decidable (∀ w : FreeMonoid α, f w ≤ₛ fm → p w) :=
  decidable_of_decidable_of_iff <|
    show (∀ w : FreeMonoid α, |w| ≤ |fm| → f w ≤ₛ fm → p w) ↔ (∀ w, f w ≤ₛ fm → p w) from
      ⟨fun h w hw ↦ h w (Nat.le_trans (nonerasing_length_le f w) (List.IsSuffix.length_le hw)) hw,
        fun h w _ hw₂ ↦ h w hw₂⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {fm : FreeMonoid β}
    : Decidable (∀ w : FreeMonoid α, f w ≤ᵢ fm → p w) :=
  decidable_of_decidable_of_iff <|
    show (∀ w : FreeMonoid α, |w| ≤ |fm| → f w ≤ᵢ fm → p w) ↔ (∀ w, f w ≤ᵢ fm → p w) from
      ⟨fun h w hw ↦ h w (Nat.le_trans (nonerasing_length_le f w) (List.IsInfix.length_le hw)) hw,
        fun h w _ hw₂ ↦ h w hw₂⟩


end Decidable -- Close section


section PDF_Questions


open FreeMonoid


variable {α β : Type*} [Fintype α] [Fintype β] 


def toFinFreeMonoid (n : ℕ) (l : List (Fin n)) : FreeMonoid (Fin n) := l

infix:75 " $↑ " => toFinFreeMonoid


theorem chapter1_question2 (u : FreeMonoid α) (hu : Overlap u)
    : ∃ (v w z : FreeMonoid α), u = w * v ∧ u = z * w ∧ |w| > |v| := by
  obtain ⟨B, hBl, hBr⟩ := hu
  exists (B.drop 1 * B.take 1), (B * B.take 1), B
  constructor <;> try constructor
  · conv => rw [← mul_assoc]; rhs; lhs; rw [mul_assoc]
    simpa only [freemonoid_to_list, List.take_append_drop]
  · rwa [← mul_assoc]
  · simpa [freemonoid_to_list] using Nat.sub_lt hBl Nat.one_pos


theorem chapter1_question3 (u : FreeMonoid α) (hu : Overlap u)
    : (∃ (x : FreeMonoid α), 0 < |x| ∧ u = x * x * x) ∨ 
      (∃ (x y : FreeMonoid α), 0 < |x| ∧ 0 < |y| ∧ u = x * y * x * y * x) := by
  obtain ⟨B, hBl, hBr⟩ := hu
  cases eq_or_ne |B| 1 with
  | inl h => 
    left
    exact ⟨B, hBl, by simpa [hBr] using List.take_length_le <| Nat.le_of_eq h⟩
  | inr h =>
    right
    exists (B.take 1), (B.drop 1)
    constructor <;> try constructor
    · simpa [freemonoid_to_list]
    · simpa [freemonoid_to_list] using Nat.lt_of_le_of_ne hBl h.symm
    · conv => rhs; lhs; rw [mul_assoc]
      simpa only [freemonoid_to_list, List.take_append_drop]


def μ : Monoid.End (FreeMonoid (Fin 2)) := 
  bind fun x ↦ [x, 1 - x]

theorem μ_nonerasing : NonErasing μ :=
  bind_nonerasing fun x ↦ by fin_cases x <;> exact Nat.two_pos

instance : IsNonErasing μ :=
  ⟨μ_nonerasing⟩

theorem chapter1_question4 (v : FreeMonoid (Fin 2)) (hv : HasOverlap v) : HasOverlap (μ v) :=
  overlap_of_nonerasing hv


def complement : Monoid.End (FreeMonoid (Fin 2)) :=
  map (1 - ·)

prefix:100 "~" => complement

@[simp]
theorem complement_complement (w : FreeMonoid (Fin 2)) : ~(~w) = w := by
  change (complement ∘* complement) w = (MonoidHom.id _) w
  exact DFunLike.congr_fun (hom_eq fun x ↦ by fin_cases x <;> rfl) w

@[simp]
theorem length_complement (w : FreeMonoid (Fin 2)) : |~w| = |w| :=
  List.length_map _ _


theorem μ_of_reverse (x : Fin 2) : (μ (of x)).reverse = ~μ (of x) := by
  fin_cases x <;> rfl

theorem μ_reverse (w : FreeMonoid (Fin 2)) : (μ w).reverse = ~μ w.reverse := by
  induction' w using FreeMonoid.recOn
  case h0 => rfl
  case ih x xs ih =>
    simp only [map_mul, reverse_mul, μ_of_reverse, ih]
    simp [freemonoid_to_list]

theorem μ_complement (w : FreeMonoid (Fin 2)) : ~μ w = μ (~w) := by
  change (complement ∘* μ) w = (μ ∘* complement) w
  exact DFunLike.congr_fun (hom_eq fun x ↦ by fin_cases x <;> rfl) w


theorem nil_in_allFreeMonoidsMaxLength (n : ℕ) (hn : 0 < n) : [] ∈ allFreeMonoidsMaxLength α n := by
  cases n with
  | zero => contradiction
  | succ n =>
    apply mem_allFreeMonoidsMaxLength
    simp [freemonoid_to_list]

def lengthLe (fm₁ fm₂ : FreeMonoid α) : Prop := 
  |fm₁| ≤ |fm₂| 

instance : @DecidableRel (FreeMonoid α) lengthLe :=
  fun (fm₁ fm₂ : FreeMonoid α) ↦ Nat.decLe |fm₁| |fm₂|

instance : IsTotal (FreeMonoid α) lengthLe :=
  ⟨fun (fm₁ fm₂ : FreeMonoid α) ↦ Nat.le_or_le |fm₁| |fm₂|⟩

instance : IsTrans (FreeMonoid α) lengthLe :=
  ⟨fun _ _ _ ↦ Nat.le_trans⟩

theorem exists_longest_μ_infix (w : FreeMonoid (Fin 2)) 
    : ∃ v, μ v ≤ᵢ w ∧ ∀ v₂ : FreeMonoid (Fin 2), |v| < |v₂| → ¬μ v₂ ≤ᵢ w := by
  let l := List.insertionSort lengthLe
    (List.filter (μ · ≤ᵢ w)
    (Multiset.toList (allFreeMonoidsMaxLength (Fin 2) (|w| + 1))))
  have hl : l ≠ [] := by
    suffices [] ∈ l by exact List.ne_nil_of_mem this
    rw [List.elem_sort_iff_elem _ [] lengthLe, List.mem_filter, Multiset.mem_toList]
    exact ⟨nil_in_allFreeMonoidsMaxLength (|w| + 1) (Nat.succ_pos |w|), by simpa using List.nil_infix w⟩
  exists l.getLast hl
  constructor
  · apply List.getLast_if_all (μ · ≤ᵢ w) l hl
    intro x hx
    rw [List.elem_sort_iff_elem] at hx
    have := List.of_mem_filter hx
    exact of_decide_eq_true this
  · intro fm hfm hfm2
    have : |fm| ≤ |w| := 
      Nat.le_trans (nonerasing_iff.mp μ_nonerasing fm) (List.IsInfix.length_le hfm2)
    have : fm ∈ l := by
      rw [List.elem_sort_iff_elem, List.mem_filter, Multiset.mem_toList]
      rw [← Nat.lt_succ] at this
      exact ⟨mem_allFreeMonoidsMaxLength (|w| + 1) fm this, decide_eq_true hfm2⟩
    obtain ⟨n, hn⟩ := List.get_of_mem this
    rw [List.getLast_eq_get, ← hn] at hfm
    have : |l.get n| ≤ |l.get ⟨l.length - 1, Nat.sub_lt (List.length_pos.2 hl) Nat.one_pos⟩| := by
      apply @List.Sorted.rel_get_of_le (FreeMonoid (Fin 2)) lengthLe
      exacts [List.sorted_insertionSort lengthLe _, Nat.le_sub_one_of_lt (Fin.prop n)]
    exact LT.lt.false (Nat.lt_of_lt_of_le hfm this)


namespace Question5


theorem claim1 {w : FreeMonoid (Fin 2)} (hlw : 6 ≤ |w|) (hw : ¬HasOverlap w)
    : ∃ v : FreeMonoid (Fin 2), μ v ≤ᵢ w ∧ 1 < |v| := by
  have h₁ : ∀ w : FreeMonoid (Fin 2), |w| = 6 → ¬HasOverlap w → ∃ x : FreeMonoid (Fin 2), μ x ≤ᵢ w ∧ 1 < |x| := by
    decide
  have h₂ : w.take 6 ≤ᵢ w := List.IsPrefix.isInfix <| List.take_prefix _ w
  obtain ⟨x, hx, hlx⟩ := h₁ (w.take 6) (List.length_take_of_le hlw) <| factor_no_overlap_of_no_overlap h₂ hw
  exact ⟨x, ⟨List.IsInfix.trans hx h₂, hlx⟩⟩

theorem claim2₁ {u v z w : FreeMonoid (Fin 2)} (hv : ∀ v₂ : FreeMonoid (Fin 2), |v| < |v₂| → ¬μ v₂ ≤ᵢ w)
    (h : u * μ v * z = w) : ∀ x, ¬μ (of x) ≤ₛ u := by
  intro x ⟨s, hs⟩
  suffices w = s * μ (of x * v) * z by
    exact hv (of x * v) (Nat.lt.base |v|) ⟨s, z, this.symm⟩
  exact calc
    w = u * μ v * z            := by exact h.symm
    _ = s * μ (of x) * μ v * z := by rw [← hs] 
    _ = s * μ (of x * v) * z   := by conv => lhs; lhs; rw [mul_assoc, ← map_mul]

theorem claim2₂ {u v z w : FreeMonoid (Fin 2)} (hv : ∀ v₂ : FreeMonoid (Fin 2), |v| < |v₂| → ¬μ v₂ ≤ᵢ w)
    (h : u * μ v * z = w) : ∀ x, ¬μ (of x) ≤ₚ z := by
  intro x ⟨t, ht⟩
  suffices w = u * μ (v * of x) * t by
    exact hv (v * of x) (by simp [freemonoid_to_list]) ⟨u, t, this.symm⟩
  exact calc
    w = u * μ v * z            := by exact h.symm
    _ = u * μ v * μ (of x) * t := by rw [← ht, ← mul_assoc] 
    _ = u * μ (v * of x) * t   := by conv => lhs; lhs; rw [mul_assoc, ← map_mul]

theorem claim3₁ {u v z w : FreeMonoid (Fin 2)} (hw₁ : ¬HasOverlap w) (hw₂ : u * μ v * z = w)
    (hv₁ : ∀ v₂ : FreeMonoid (Fin 2), |v| < |v₂| → ¬μ v₂ ≤ᵢ w) (hv₂ : 1 < |v|) : |u| < 3 := by
  by_contra hu₁
  rw [Nat.not_lt, ← Nat.lt_succ] at hu₁
  have hc₁ : ¬HasOverlap (u.rtake 3) := by 
    refine factor_no_overlap_of_no_overlap ?_ hw₁
    exists u.rdrop 3, μ v * z
    simp only [freemonoid_to_list, List.append_assoc] at hw₂
    simpa only [freemonoid_to_list, List.rdrop_append_rtake]
  have hc₂ : ∀ x : Fin 2, ¬μ (of x) ≤ₛ (u.rtake 3) := 
    fun x hxu ↦ claim2₁ hv₁ hw₂ x <| List.IsSuffix.trans hxu <| List.rtake_suffix 3 u
  have hc₃ : ¬HasOverlap (u.rtake 3 * μ (v.take 2)) := by
    refine factor_no_overlap_of_no_overlap ?_ hw₁
    exists u.rdrop 3, μ (v.drop 2) * z
    simp only [← mul_assoc]
    conv => lhs; lhs; rw [mul_assoc, ← map_mul]
    simpa only [freemonoid_to_list, List.rdrop_append_rtake, List.take_append_drop]
  have hu₂ : u.rtake 3 ∈ [[0,0,0],[0,0,1],[0,1,0],[0,1,1],[1,0,0],[1,0,1],[1,1,0],[1,1,1]] := 
    mem_allFreeMonoidsOfLength 3 (u.rtake 3) <| List.length_rtake_of_le <| Nat.lt_succ.mp hu₁
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu₂
  have hv₃ : v.take 2 ∈ [[0,0],[0,1],[1,0],[1,1]] :=
    mem_allFreeMonoidsOfLength 2 (v.take 2) <| List.length_take_of_le hv₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv₃
  rcases hu₂ with (hu₂' | hu₂' | hu₂' | hu₂' | hu₂' | hu₂' | hu₂' | hu₂')
  all_goals try apply hc₁;                     rw [hu₂']; decide
  all_goals try apply hc₂ ⟨0, Nat.two_pos⟩;    rw [hu₂']; decide
  all_goals try apply hc₂ ⟨1, Nat.one_lt_two⟩; rw [hu₂']; decide
  all_goals rcases hv₃ with (hv₃' | hv₃' | hv₃' | hv₃')
  all_goals apply hc₃; rw [hu₂', hv₃']; decide

theorem claim3₂ {u v z w : FreeMonoid (Fin 2)} (hw₁ : ¬HasOverlap w) (hw₂ : u * μ v * z = w)
    (hv₁ : ∀ v₂ : FreeMonoid (Fin 2), |v| < |v₂| → ¬μ v₂ ≤ᵢ w) (hv₂ : 1 < |v|) : |z| < 3 := by
  rw [← length_reverse]
  apply @claim3₁ z.reverse (~v.reverse) u.reverse w.reverse
  · rwa [← has_overlap_reverse_iff]
  · simp [← hw₂, reverse_mul, μ_reverse, μ_complement, ← mul_assoc]
  · rw [length_complement, length_reverse]
    intro v₂ _ _
    apply hv₁ (~v₂.reverse)
    · rwa [length_complement, length_reverse]
    · rwa [← μ_complement, ← μ_reverse, ← reverse_infix, reverse_reverse]
  · simpa


theorem chapter1_question5 (w : FreeMonoid (Fin 2)) (hw : ¬HasOverlap w)
    : ∃ u ∈ ([[], [0], [1], [0, 0], [1, 1]] : List (FreeMonoid (Fin 2))),
      ∃ z ∈ ([[], [0], [1], [0, 0], [1, 1]] : List (FreeMonoid (Fin 2))),
      ∃ v : FreeMonoid (Fin 2), w = u * μ v * z ∧ ¬HasOverlap v := by
  cases Nat.lt_or_ge |w| 6 with
  | inl hlw =>
    revert w
    conv => 
      intro w; rw [forall_comm]; intro h1 h2; rhs; intro u; rhs; rhs; intro z; rhs; rhs; intro v; lhs; 
      rw [show w = u * μ v * z ↔ μ v ≤ᵢ w ∧ w = u * μ v * z from ⟨fun h ↦ ⟨⟨u, z, h.symm⟩, h⟩, And.right⟩]
    simp only [and_assoc]
    decide
  | inr hlw =>
    obtain ⟨v, hvl, hvr⟩ := exists_longest_μ_infix w
    have hlv : 1 < |v| := by
      by_contra hvnl
      rw [not_lt] at hvnl 
      obtain ⟨v', hvl', hvr'⟩ := claim1 hlw hw
      exact hvr v' (Nat.lt_of_le_of_lt hvnl hvr') hvl'
    have hvno : ¬HasOverlap v := factor_no_overlap_of_no_overlap hvl hw ∘ (chapter1_question4 v)
    obtain ⟨u, z, huz⟩ := hvl
    exists u; constructor <;> try exists z; constructor
    · have : u ≠ [0, 1] := fun hu ↦ claim2₁ hvr huz ⟨0, Nat.two_pos⟩ (by rw [hu]; decide)
      have : u ≠ [1, 0] := fun hu ↦ claim2₁ hvr huz ⟨1, Nat.one_lt_two⟩ (by rw [hu]; decide)
      have := mem_allFreeMonoidsMaxLength 3 u <| claim3₁ hw huz hvr hlv
      fin_cases this <;> first | decide | contradiction
    · have : z ≠ [0, 1] := fun hz ↦ claim2₂ hvr huz ⟨0, Nat.two_pos⟩ (by rw [hz]; decide)
      have : z ≠ [1, 0] := fun hz ↦ claim2₂ hvr huz ⟨1, Nat.one_lt_two⟩ (by rw [hz]; decide)
      have := mem_allFreeMonoidsMaxLength 3 z <| claim3₂ hw huz hvr hlv
      fin_cases this <;> first | decide | contradiction
    · exact ⟨v, huz.symm, hvno⟩


end Question5


def X : ℕ → FreeMonoid (Fin 2)
  | 0   => [0]
  | n+1 => X n * ~X n

theorem μ_pow_complement (k : ℕ) (fm : FreeMonoid (Fin 2))
    : (μ^k : Monoid.End _) (~fm) = ~(μ^k : Monoid.End _) fm := by
  induction k <;> simp [*, pow_succ, μ_complement]

theorem chapter1_question7 (n : ℕ) : (μ^n : Monoid.End _) [0] = X n := by
  induction n with
  | zero => rfl
  | succ k ih => exact calc 
    (μ^k.succ) [0] = (μ^k) (μ [0])               := by rw [pow_succ']; rfl
                 _ = (μ^k) (2 $↑ [0] * 2 $↑ [1]) := by rfl
                 _ = (μ^k) [0] * (μ^k) (~[0])    := by rw [map_mul]; rfl
                 _ = (μ^k) [0] * ~(μ^k) [0]      := by rw [μ_pow_complement]
                 _ = X k * ~X k                  := by rw [ih]
                 _ = X k.succ                    := by rfl


end PDF_Questions -- Close section
