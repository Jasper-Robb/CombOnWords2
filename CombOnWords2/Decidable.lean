import CombOnWords2.FreeMonoid
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.SuccPred


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


instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∃ w , w <*: fm ∧ p w) :=
  decidable_of_decidable_of_iff <| exists_congr fun w ↦ and_congr_left fun _ ↦ List.mem_inits w fm

instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∃ w, w <:* fm ∧ p w) :=
  decidable_of_decidable_of_iff <| exists_congr fun w ↦ and_congr_left fun _ ↦ List.mem_tails w fm

instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∃ w, w <:*: fm ∧ p w) :=
  decidable_of_decidable_of_iff <| exists_congr fun w ↦ and_congr_left fun _ ↦ List.mem_infixes w fm

instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∀ w, w <*: fm → p w) :=
  decidable_of_decidable_of_iff <| forall_congr' fun w ↦ imp_congr_left <| List.mem_inits w fm

instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∀ w, w <:* fm → p w) :=
  decidable_of_decidable_of_iff <| forall_congr' fun w ↦ imp_congr_left <| List.mem_tails w fm

instance [DecidablePred p] {fm : FreeMonoid α} : Decidable (∀ w, w <:*: fm → p w) :=
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
    : Decidable (∃ w : FreeMonoid α, f w <*: fm ∧ p w) :=
  decidable_of_decidable_of_iff <|
    show (∃ w : FreeMonoid α, |w| ≤ |fm| ∧ f w <*: fm ∧ p w) ↔ (∃ w, f w <*: fm ∧ p w) from
      ⟨fun ⟨w, _, hw₂, hw₃⟩ ↦ Exists.intro w ⟨hw₂, hw₃⟩,
        fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, ⟨Nat.le_trans (nonerasing_length_le f w) (List.IsPrefix.length_le hw₁), hw₁, hw₂⟩⟩⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {fm : FreeMonoid β}
    : Decidable (∃ w : FreeMonoid α, f w <:* fm ∧ p w) :=
  decidable_of_decidable_of_iff <|
    show (∃ w : FreeMonoid α, |w| ≤ |fm| ∧ f w <:* fm ∧ p w) ↔ (∃ w, f w <:* fm ∧ p w) from
      ⟨fun ⟨w, _, hw₂, hw₃⟩ ↦ Exists.intro w ⟨hw₂, hw₃⟩,
        fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, ⟨Nat.le_trans (nonerasing_length_le f w) (List.IsSuffix.length_le hw₁), hw₁, hw₂⟩⟩⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {fm : FreeMonoid β}
    : Decidable (∃ w : FreeMonoid α, f w <:*: fm ∧ p w) :=
  decidable_of_decidable_of_iff <|
    show (∃ w : FreeMonoid α, |w| ≤ |fm| ∧ f w <:*: fm ∧ p w) ↔ (∃ w, f w <:*: fm ∧ p w) from
      ⟨fun ⟨w, _, hw₂, hw₃⟩ ↦ Exists.intro w ⟨hw₂, hw₃⟩,
        fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, ⟨Nat.le_trans (nonerasing_length_le f w) (List.IsInfix.length_le hw₁), hw₁, hw₂⟩⟩⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {fm : FreeMonoid β}
    : Decidable (∀ w : FreeMonoid α, f w <*: fm → p w) :=
  decidable_of_decidable_of_iff <|
    show (∀ w : FreeMonoid α, |w| ≤ |fm| → f w <*: fm → p w) ↔ (∀ w, f w <*: fm → p w) from
      ⟨fun h w hw ↦ h w (Nat.le_trans (nonerasing_length_le f w) (List.IsPrefix.length_le hw)) hw,
        fun h w _ hw₂ ↦ h w hw₂⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {fm : FreeMonoid β}
    : Decidable (∀ w : FreeMonoid α, f w <:* fm → p w) :=
  decidable_of_decidable_of_iff <|
    show (∀ w : FreeMonoid α, |w| ≤ |fm| → f w <:* fm → p w) ↔ (∀ w, f w <:* fm → p w) from
      ⟨fun h w hw ↦ h w (Nat.le_trans (nonerasing_length_le f w) (List.IsSuffix.length_le hw)) hw,
        fun h w _ hw₂ ↦ h w hw₂⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {fm : FreeMonoid β}
    : Decidable (∀ w : FreeMonoid α, f w <:*: fm → p w) :=
  decidable_of_decidable_of_iff <|
    show (∀ w : FreeMonoid α, |w| ≤ |fm| → f w <:*: fm → p w) ↔ (∀ w, f w <:*: fm → p w) from
      ⟨fun h w hw ↦ h w (Nat.le_trans (nonerasing_length_le f w) (List.IsInfix.length_le hw)) hw,
        fun h w _ hw₂ ↦ h w hw₂⟩



