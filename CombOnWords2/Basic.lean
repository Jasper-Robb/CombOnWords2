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
def toList' (w : FreeMonoid α) : List α := w

@[freemonoid_to_list]
theorem one_eq_list_nil : (1 : FreeMonoid α) = ([] : List α) := rfl

@[freemonoid_to_list]
theorem of_eq_list_singleton {x : α} : of x = [x] := rfl

@[freemonoid_to_list]
theorem mul_eq_list_append (u v : FreeMonoid α)
    : u * v = u.toList' ++ v.toList' :=
  rfl

@[freemonoid_to_list]
theorem map_eq_list_map (f : α → β) (w : FreeMonoid α)
    : map f w = List.map f w :=
  rfl


instance : Membership α (FreeMonoid α) :=
  ⟨List.Mem⟩

instance [Repr α] : Repr (FreeMonoid α) :=
  inferInstanceAs <| Repr (List α)

instance [DecidableEq α] : DecidableEq (FreeMonoid α) :=
  inferInstanceAs <| DecidableEq (List α)

instance [DecidableEq α] (x : α) (w : FreeMonoid α) : Decidable (x ∈ w) :=
  inferInstanceAs <| Decidable (x ∈ FreeMonoid.toList w)


def length (w : FreeMonoid α) : ℕ :=
  List.length w

-- Macro for length fm as |fm|
macro:max atomic("|" noWs) a:term noWs "|" : term => `(length $a)
def length.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()


@[freemonoid_to_list]
theorem length_eq_list_length (w : FreeMonoid α) : |w| = List.length w :=
  rfl

@[simp]
theorem length_mul (u v : FreeMonoid α) : |u * v| = |u| + |v| :=
  List.length_append u v

@[simp]
theorem length_pow (u : FreeMonoid α) (k : ℕ) : |u ^ k| = k * |u| := by
  induction k with
  | zero => simp only [Nat.zero_eq, pow_zero, zero_mul]; rfl
  | succ k' ih => simp [pow_succ, ih, Nat.add_comm u.length, Nat.succ_mul]


@[freemonoid_to_list]
def join : FreeMonoid (FreeMonoid α) →* FreeMonoid α where
  toFun    := List.join
  map_one' := List.join_nil
  map_mul' := List.join_append


@[freemonoid_to_list]
def bind (f : α → FreeMonoid β) : FreeMonoid α →* FreeMonoid β where
  toFun    := fun w ↦ List.bind w f
  map_one' := List.nil_bind f
  map_mul' := fun u v ↦ List.append_bind u v f


@[freemonoid_to_list]
def take (a : ℕ) (w : FreeMonoid α) : FreeMonoid α := List.take a w


@[freemonoid_to_list]
def rtake (a : ℕ) (w : FreeMonoid α) : FreeMonoid α := List.rtake w a


@[freemonoid_to_list]
def drop (a : ℕ) (w : FreeMonoid α) : FreeMonoid α := List.drop a w


@[freemonoid_to_list]
def rdrop (a : ℕ) (w : FreeMonoid α) : FreeMonoid α := List.rdrop w a


@[freemonoid_to_list]
def reverse (w : FreeMonoid α) : FreeMonoid α := List.reverse w


@[simp]
theorem reverse_mul (u v : FreeMonoid α) : (u * v).reverse = v.reverse * u.reverse :=
  List.reverse_append u v

@[simp]
theorem length_reverse (w : FreeMonoid α) : |w.reverse| = |w| :=
  List.length_reverse w

@[simp]
theorem reverse_reverse (w : FreeMonoid α) : w.reverse.reverse = w :=
  List.reverse_reverse w


end Init -- Close section


section NonErasing


def NonErasing (f : FreeMonoid α →* FreeMonoid β) : Prop :=
  ∀ (w : FreeMonoid α), 0 < |w| → 0 < |f w|

class IsNonErasing (f : FreeMonoid α →* FreeMonoid β) : Prop where
  nonerasing : NonErasing f


theorem nonerasing_iff {f : FreeMonoid α →* FreeMonoid β}
    : NonErasing f ↔ (∀ w : FreeMonoid α, |w| ≤ |f w|) := by
  constructor
  · intro h w
    induction' w using FreeMonoid.recOn
    case h0 => exact tsub_add_cancel_iff_le.mp rfl
    case ih x xs ih => simpa using Nat.add_le_add (h [x] Nat.one_pos) ih
  · exact fun h fm hfm => Nat.lt_of_lt_of_le hfm <| h fm

theorem nonerasing_length_le (f : FreeMonoid α →* FreeMonoid β) [hf : IsNonErasing f]
    : ∀ (w : FreeMonoid α), |w| ≤ |f w| :=
  nonerasing_iff.mp hf.nonerasing

theorem nonerasing_length_le' (f : FreeMonoid α →* FreeMonoid β) [IsNonErasing f]
    : ∀ (w : FreeMonoid α) (n : ℕ), |f w| ≤ n → |w| ≤ n :=
  fun u _ ↦ Nat.le_trans (nonerasing_length_le f u)

theorem nonerasing_length_lt' (f : FreeMonoid α →* FreeMonoid β) [IsNonErasing f]
    : ∀ (w : FreeMonoid α) (n : ℕ), |f w| < n → |w| < n :=
  fun fm _ ↦ Nat.lt_of_le_of_lt (nonerasing_length_le f fm)


theorem map_nonerasing {f : α → β} : NonErasing <| map f :=
  fun _ _ ↦ by simpa [freemonoid_to_list]

theorem bind_nonerasing {f : α → FreeMonoid β} (hf : ∀ x, 0 < |f x|)
    : NonErasing <| bind f := by
  rintro (_ | x) _
  · contradiction
  · simpa [freemonoid_to_list] using Or.inl <| hf x


end NonErasing -- Close section


section Uniform


def Uniform (f : FreeMonoid α →* FreeMonoid β) (c : ℕ) : Prop :=
  ∀ w, |f w| = c * |w|

class IsUniform (f : FreeMonoid α →* FreeMonoid β) (c : ℕ) : Prop where
  uniform : Uniform f c


theorem map_uniform {f : α → β} : Uniform (map f) 1 := by
  simp [Uniform, freemonoid_to_list]

theorem bind_uniform {f : α → FreeMonoid β} {c : ℕ} (hf : ∀ x, |f x| = c) : Uniform (bind f) c := by
  change ∀ x, (List.length ∘ f) x = c at hf
  simpa [Uniform, freemonoid_to_list, funext hf] using fun _ ↦ mul_comm _ _


theorem length_pow_uniform (f : Monoid.End (FreeMonoid α)) (c : ℕ) [hf : IsUniform f c]
    (n : ℕ) (w : FreeMonoid α) : |(f^n : Monoid.End _) w| = c^n * |w| := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Monoid.coe_mul, Function.comp_apply, hf.uniform _, ih, mul_assoc]

theorem length_of_length_uniform (f : FreeMonoid α →* FreeMonoid β) {c : ℕ}
    [hf : IsUniform f c] (hc : 0 < c) (w : FreeMonoid α) : |w| = |f w| / c := by
  rw [hf.uniform, mul_comm, Nat.mul_div_left _ hc]

theorem length_lt_of_lt_length_uniform (f : FreeMonoid α →* FreeMonoid β) (c : ℕ)
    [hf : IsUniform f c] {n : ℕ} {w : FreeMonoid α} (h : n < |f w|) : n / c < |w| :=
  Nat.div_lt_of_lt_mul <| by rwa [← hf.uniform]

theorem length_lt_of_pow (f : Monoid.End (FreeMonoid α)) (c : ℕ) [IsUniform f c]
    {n i : ℕ} (hi : i < c^n) : i < |(f^n : Monoid.End _) [x]| := by
  simpa [length_pow_uniform f c n [x], freemonoid_to_list]


end Uniform -- Close section


theorem morphism_to_bind (f : FreeMonoid α →* FreeMonoid β) : f = bind (f ∘ of) :=
  hom_eq <| by simp [freemonoid_to_list]


section Infix


def IsPrefix (u v : FreeMonoid α) : Prop :=
  ∃ t, u * t = v

def IsSuffix (u v : FreeMonoid α) : Prop :=
  ∃ s, s * u = v

def IsInfix (u v : FreeMonoid α) : Prop :=
  ∃ s t, s * u * t = v


def IsStrictPrefix (u v : FreeMonoid α) : Prop :=
  ∃ t ≠ 1, u * t = v

def IsStrictSuffix (u v : FreeMonoid α) : Prop :=
  ∃ s ≠ 1, s * u = v

def IsStrictInfix (u v : FreeMonoid α) : Prop :=
  ∃ s t, s ≠ 1 ∧ t ≠ 1 ∧ s * u * t = v


infixl:50 " ≤ₚ " => IsPrefix
infixl:50 " ≤ₛ " => IsSuffix
infixl:50 " ≤ᵢ " => IsInfix

infixl:50 " <ₚ " => IsStrictPrefix
infixl:50 " <ₛ " => IsStrictSuffix
infixl:50 " <ᵢ " => IsStrictInfix


instance [DecidableEq α] (u v : FreeMonoid α) : Decidable (u ≤ₚ v) :=
  inferInstanceAs <| Decidable (u <+: v)

instance [DecidableEq α] (u v : FreeMonoid α) : Decidable (u ≤ₛ v) :=
  inferInstanceAs <| Decidable (u <:+ v)

instance [DecidableEq α] (u v : FreeMonoid α) : Decidable (u ≤ᵢ v) :=
  inferInstanceAs <| Decidable (u <:+: v)


@[freemonoid_to_list]
theorem is_prefix_iff_list_is_prefix (u v : FreeMonoid α)
    : u ≤ₚ v ↔ u <+: v :=
  Iff.rfl

@[freemonoid_to_list]
theorem is_suffix_iff_list_is_suffix (u v : FreeMonoid α)
    : u ≤ₛ v ↔ u <:+ v :=
  Iff.rfl

@[freemonoid_to_list]
theorem is_infix_iff_list_is_infix (u v : FreeMonoid α)
    : u ≤ᵢ v ↔ u <:+: v :=
  Iff.rfl


@[freemonoid_to_list]
theorem is_s_prefix_iff_list_is_s_prefix (u v : FreeMonoid α)
    : u <ₚ v ↔ u <<+: v :=
  Iff.rfl

@[freemonoid_to_list]
theorem is_s_suffix_iff_list_is_s_suffix (u v : FreeMonoid α)
    : u <ₛ v ↔ u <<:+ v :=
  Iff.rfl

@[freemonoid_to_list]
theorem is_s_infix_iff_list_is_s_infix (u v : FreeMonoid α)
    : u <ᵢ v ↔ u <<:+: v :=
  Iff.rfl


@[simp]
theorem reverse_infix (u v : FreeMonoid α) : u.reverse ≤ᵢ v.reverse ↔ u ≤ᵢ v :=
  List.reverse_infix


theorem is_prefix_congr {u v : FreeMonoid α} (h : u ≤ₚ v) (f : FreeMonoid α →* FreeMonoid β)
    : (f u) ≤ₚ (f v) := by
  obtain ⟨t, _⟩ := h
  exists f t
  rw [← map_mul]
  congr

theorem is_suffix_congr {u v : FreeMonoid α} (h : u ≤ₛ v) (f : FreeMonoid α →* FreeMonoid β)
    : (f u) ≤ₛ (f v) := by
  obtain ⟨s, _⟩ := h
  exists f s
  rw [← map_mul]
  congr

theorem is_infix_congr {u v : FreeMonoid α} (h : u ≤ᵢ v) (f : FreeMonoid α →* FreeMonoid β)
    : (f u) ≤ᵢ (f v) := by
  obtain ⟨s, t, _⟩ := h
  exists f s, f t
  simp only [← map_mul]
  congr


theorem non_erasing_nil {w : FreeMonoid α} (hw : w ≠ 1) (f : FreeMonoid α →* FreeMonoid β)
    [hf : IsNonErasing f] : f w ≠ 1 := by
  rw [one_eq_list_nil, ← List.length_pos] at hw ⊢
  exact hf.nonerasing _ hw


theorem is_s_prefix_congr {u v : FreeMonoid α} (h : u <ₚ v) (f : FreeMonoid α →* FreeMonoid β)
    [hf : IsNonErasing f] : (f u) <ₚ (f v) := by
  obtain ⟨t, ht, _⟩ := h
  exists f t
  exact ⟨non_erasing_nil ht f, by rw [← map_mul]; congr⟩

theorem is_s_suffix_congr {u v : FreeMonoid α} (h : u <ₛ v) (f : FreeMonoid α →* FreeMonoid β)
    [hf : IsNonErasing f] : (f u) <ₛ (f v) := by
  obtain ⟨s, hs, _⟩ := h
  exists f s
  exact ⟨non_erasing_nil hs f, by rw [← map_mul]; congr⟩

theorem is_s_infix_congr {u v : FreeMonoid α} (h : u <ᵢ v) (f : FreeMonoid α →* FreeMonoid β)
    [hf : IsNonErasing f] : (f u) <ᵢ (f v) := by
  obtain ⟨t, s, ht, hs, _⟩ := h
  exists f t, f s
  exact ⟨non_erasing_nil ht f, non_erasing_nil hs f, by simp only [← map_mul]; congr⟩


theorem is_s_prefix_congr' {u v : FreeMonoid α} (h : u <ₚ v) (f : FreeMonoid α →* FreeMonoid β)
    : (f u) ≤ₚ (f v) := by
  obtain ⟨t, _, _⟩ := h
  exists f t
  rw [← map_mul]
  congr

theorem is_s_suffix_congr' {u v : FreeMonoid α} (h : u <ₛ v) (f : FreeMonoid α →* FreeMonoid β)
    : (f u) ≤ₛ (f v) := by
  obtain ⟨s, _, _⟩ := h
  exists f s
  rw [← map_mul]
  congr

theorem is_s_infix_congr' {u v : FreeMonoid α} (h : u <ᵢ v) (f : FreeMonoid α →* FreeMonoid β)
    : (f u) ≤ᵢ (f v) := by
  obtain ⟨t, s, _, _, _⟩ := h
  exists f t, f s
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


section Border


def Border (b w : FreeMonoid α) : Prop :=
  b ≤ₚ w ∧ b ≤ₛ w ∧ b ≠ w ∧ b ≠ 1

infixl:50 " <b " => Border

instance [DecidableEq α] {b w : FreeMonoid α} : Decidable (b <b w) :=
  And.decidable


theorem ne_nil_of_bordered {b w : FreeMonoid α} : b <b w → w ≠ 1 :=
  fun ⟨h1, _, _, h4⟩ ↦ List.length_pos.mp <| Nat.lt_of_lt_of_le
    (List.length_pos.mpr h4) (List.length_le_of_sublist (List.IsPrefix.sublist h1))

theorem border_congr {b w : FreeMonoid α} (h : b <b w) (f : FreeMonoid α →* FreeMonoid β)
    [hf : IsNonErasing f] : (f b) <b (f w) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  apply And.intro <;> try apply And.intro <;> try apply And.intro
  · exact is_prefix_congr h1 f
  · exact is_suffix_congr h2 f
  · obtain ⟨s, hs⟩ := h1
    rw [← hs, map_mul, ne_eq, self_eq_mul_right]
    intro hfs
    suffices s ≠ 1 by exact (non_erasing_nil this f) hfs
    intro hs'
    simp only [hs', mul_one] at hs
    contradiction
  · exact non_erasing_nil h4 f

theorem border_reverse {b w : FreeMonoid α} : b <b w → b.reverse <b w.reverse :=
  fun ⟨h1, h2, h3, h4⟩ ↦ ⟨List.reverse_prefix.mpr h2, List.reverse_suffix.mpr h1,
    fun hc ↦ h3 <| List.reverse_injective hc, fun hc ↦ h4 <| List.reverse_eq_nil_iff.mp hc⟩


end Border


section Periodic


theorem pow_prefix_pow (w : FreeMonoid α) {k n : ℕ} (h : k ≤ n)
    : w^k ≤ₚ w^n := by
  rw [(Nat.sub_eq_iff_eq_add' h).mp rfl]
  simp [pow_add, freemonoid_to_list]

theorem pow_mul_take_prefix_pow (w : FreeMonoid α) {k m n : ℕ} (h : k < n)
    : w^k * w.take m ≤ₚ w^n := by
  rw [(Nat.sub_eq_iff_eq_add' (Nat.le_of_lt h)).mp rfl]
  simp only [take, mul_eq_list_append, toList', pow_add, is_prefix_iff_list_is_prefix,
             List.prefix_append_right_inj]
  rw [(Nat.sub_eq_iff_eq_add' (Nat.sub_pos_of_lt h)).mp rfl, pow_add, pow_one]
  suffices List.take m w <+: w by exact List.prefix_append_of_prefix _ this
  exact List.take_prefix m w

theorem take_of_pow {r : FreeMonoid α} {n k : ℕ} (h : k ≤ n * |r|)
    : (r^n).take k = r^(k / |r|) * r.take (k % |r|) := by
  cases Nat.eq_zero_or_pos |r| with
  | inl hr =>
    simp only [show r = 1 from List.length_eq_zero.mp hr, one_pow, one_mul]
    simp [freemonoid_to_list]
  | inr hr =>
    rw [← length_pow] at h
    apply ((List.eq_take_iff _ h).mpr _).symm
    rw [length_pow] at h
    constructor
    · rw [← is_prefix_iff_list_is_prefix]
      cases Nat.eq_or_lt_of_le h with
      | inl h' =>
        have : k % |r| = 0 := by
          rw [h']
          exact Nat.mul_mod_left n (length r)
        rw [Nat.div_eq_of_eq_mul_left hr h', this]
        simpa [freemonoid_to_list] using List.prefix_rfl
      | inr h' => exact pow_mul_take_prefix_pow _ <| (Nat.div_lt_iff_lt_mul hr).mpr h'
    · simp only [← length_eq_list_length, length_mul, length_pow]
      simp only [length_eq_list_length, take]
      rw [List.length_take_of_le]
      · exact Nat.div_add_mod' k (List.length r)
      · exact Nat.le_of_lt <| Nat.mod_lt k hr


end Periodic


section Overlap


def Overlap (w : FreeMonoid α) : Prop :=
  ∃ B : FreeMonoid α, 0 < |B| ∧ w = B * B * B.take 1

def HasOverlap (w : FreeMonoid α) : Prop :=
  ∃ u : FreeMonoid α, Overlap u ∧ u ≤ᵢ w


theorem overlap_of_nonerasing {f : FreeMonoid α →* FreeMonoid β} [hf : IsNonErasing f]
    {w : FreeMonoid α} (hw : HasOverlap w) : HasOverlap (f w) := by
  obtain ⟨u, ⟨B, hBl, hBr⟩, hur⟩ := hw
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


theorem overlap_reverse (w : FreeMonoid α) (hw : Overlap w) : Overlap w.reverse := by
  obtain ⟨B, hBl, hBr⟩ := hw
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

theorem overlap_reverse_iff (w : FreeMonoid α) : Overlap w ↔ Overlap w.reverse := by
  constructor
  · exact overlap_reverse w
  · intro h
    rw [← reverse_reverse w]
    exact overlap_reverse (reverse w) h

theorem has_overlap_reverse (w : FreeMonoid α) : HasOverlap w → HasOverlap w.reverse :=
  fun ⟨u, hul, hur⟩ ↦ ⟨u.reverse, ⟨overlap_reverse u hul, List.reverse_infix.mpr hur⟩⟩

theorem has_overlap_reverse_iff (w : FreeMonoid α) : HasOverlap w ↔ HasOverlap w.reverse := by
  constructor
  · exact has_overlap_reverse w
  · intro h
    rw [← reverse_reverse w]
    exact has_overlap_reverse (reverse w) h


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

theorem has_overlap_iff (w : FreeMonoid α)
    : (∃ u ∈ w.infixes, Overlap u) ↔ HasOverlap w :=
  ⟨fun ⟨u, hul, hur⟩ ↦ ⟨u, ⟨hur, (List.mem_infixes u w).mp hul⟩⟩,
   fun ⟨u, hul, hur⟩ ↦ ⟨u, ⟨(List.mem_infixes u w).mpr hur, hul⟩⟩⟩

theorem factor_no_overlap_of_no_overlap {u v : FreeMonoid α} (hvw : u ≤ᵢ v) (hw : ¬HasOverlap v)
    : ¬HasOverlap u :=
  fun ⟨u, hul, hur⟩ => hw ⟨u, ⟨hul, List.IsInfix.trans hur hvw⟩⟩


instance [DecidableEq α] (w : FreeMonoid α) : Decidable (Overlap w) :=
  decidable_of_decidable_of_iff <| overlap_iff w

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
    · exact fun w hw₁ hw₂ ↦
        LT.lt.false <| Eq.trans_lt (length_mem_allFreeMonoidsOfLength n w hw₂).symm <|
          length_mem_allFreeMonoidsMaxLength n w hw₁


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


instance [DecidablePred p] {w : FreeMonoid α} : Decidable (∃ w' , w' ≤ₚ w ∧ p w') :=
  decidable_of_decidable_of_iff <| exists_congr fun w' ↦ and_congr_left fun _ ↦ List.mem_inits w' w

instance [DecidablePred p] {w : FreeMonoid α} : Decidable (∃ w', w' ≤ₛ w ∧ p w') :=
  decidable_of_decidable_of_iff <| exists_congr fun w' ↦ and_congr_left fun _ ↦ List.mem_tails w' w

instance [DecidablePred p] {w : FreeMonoid α} : Decidable (∃ w', w' ≤ᵢ w ∧ p w') :=
  decidable_of_decidable_of_iff <| exists_congr fun w' ↦ and_congr_left fun _ ↦ List.mem_infixes w' w

instance [DecidablePred p] {w : FreeMonoid α} : Decidable (∀ w', w' ≤ₚ w → p w') :=
  decidable_of_decidable_of_iff <| forall_congr' fun w' ↦ imp_congr_left <| List.mem_inits w' w

instance [DecidablePred p] {w : FreeMonoid α} : Decidable (∀ w', w' ≤ₛ w → p w') :=
  decidable_of_decidable_of_iff <| forall_congr' fun w' ↦ imp_congr_left <| List.mem_tails w' w

instance [DecidablePred p] {w : FreeMonoid α} : Decidable (∀ w', w' ≤ᵢ w → p w') :=
  decidable_of_decidable_of_iff <| forall_congr' fun w' ↦ imp_congr_left <| List.mem_infixes w' w


instance [IsNonErasing f] [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |f w| < n ∧ p w) :=
  decidable_of_decidable_of_iff <|
    show (∃ w : FreeMonoid α, |w| < n ∧ |f w| < n ∧ p w) ↔ (∃ w, |f w| < n ∧ p w) from
      ⟨fun ⟨w, _, hw₂, hw₃⟩ ↦ ⟨w, ⟨hw₂, hw₃⟩⟩,
        fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, ⟨nonerasing_length_lt' f w n hw₁, hw₁, hw₂⟩⟩⟩

instance [IsNonErasing f] [DecidablePred p] : Decidable (∃ w : FreeMonoid α, |f w| ≤ n ∧ p w) :=
  decidable_of_decidable_of_iff <|
    show (∃ w : FreeMonoid α, |w| ≤ n ∧ |f w| ≤ n ∧ p w) ↔ (∃ w, |f w| ≤ n ∧ p w) from
      ⟨fun ⟨w, _, hw₂, hw₃⟩ ↦ ⟨w, ⟨hw₂, hw₃⟩⟩,
        fun ⟨w, hw₁, hw₂⟩ ↦ ⟨w, ⟨nonerasing_length_le' f w n hw₁, hw₁, hw₂⟩⟩⟩

instance [IsNonErasing f] [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |f w| < n → p w) :=
  decidable_of_decidable_of_iff <|
    show (∀ w : FreeMonoid α, |w| < n → |f w| < n → p w) ↔ (∀ w, |f w| < n → p w) from
      ⟨fun h₁ w h₂ ↦ h₁ w (nonerasing_length_lt' f w n h₂) h₂, fun h₁ w _ h₃ ↦ h₁ w h₃⟩

instance [IsNonErasing f] [DecidablePred p] : Decidable (∀ w : FreeMonoid α, |f w| ≤ n → p w) :=
  decidable_of_decidable_of_iff <|
    show (∀ w : FreeMonoid α, |w| ≤ n → |f w| ≤ n → p w) ↔ (∀ w, |f w| ≤ n → p w) from
      ⟨fun h₁ w h₂ ↦ h₁ w (nonerasing_length_le' f w n h₂) h₂, fun h₁ w _ h₃ ↦ h₁ w h₃⟩


instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {w : FreeMonoid β}
    : Decidable (∃ w' : FreeMonoid α, f w' ≤ₚ w ∧ p w') :=
  decidable_of_decidable_of_iff <|
    show (∃ w' : FreeMonoid α, |w'| ≤ |w| ∧ f w' ≤ₚ w ∧ p w') ↔ (∃ w', f w' ≤ₚ w ∧ p w') from
      ⟨fun ⟨w', _, hw'₂, hw'₃⟩ ↦ ⟨w', ⟨hw'₂, hw'₃⟩⟩,
        fun ⟨w', hw'₁, hw'₂⟩ ↦ ⟨w', ⟨Nat.le_trans (nonerasing_length_le f w') (List.IsPrefix.length_le hw'₁), hw'₁, hw'₂⟩⟩⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {w : FreeMonoid β}
    : Decidable (∃ w' : FreeMonoid α, f w' ≤ₛ w ∧ p w') :=
  decidable_of_decidable_of_iff <|
    show (∃ w' : FreeMonoid α, |w'| ≤ |w| ∧ f w' ≤ₛ w ∧ p w') ↔ (∃ w', f w' ≤ₛ w ∧ p w') from
      ⟨fun ⟨w', _, hw'₂, hw'₃⟩ ↦ ⟨w', ⟨hw'₂, hw'₃⟩⟩,
        fun ⟨w', hw'₁, hw'₂⟩ ↦ ⟨w', ⟨Nat.le_trans (nonerasing_length_le f w') (List.IsSuffix.length_le hw'₁), hw'₁, hw'₂⟩⟩⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {w : FreeMonoid β}
    : Decidable (∃ w' : FreeMonoid α, f w' ≤ᵢ w ∧ p w') :=
  decidable_of_decidable_of_iff <|
    show (∃ w' : FreeMonoid α, |w'| ≤ |w| ∧ f w' ≤ᵢ w ∧ p w') ↔ (∃ w', f w' ≤ᵢ w ∧ p w') from
      ⟨fun ⟨w', _, hw'₂, hw'₃⟩ ↦ ⟨w', ⟨hw'₂, hw'₃⟩⟩,
        fun ⟨w', hw'₁, hw'₂⟩ ↦ ⟨w', ⟨Nat.le_trans (nonerasing_length_le f w') (List.IsInfix.length_le hw'₁), hw'₁, hw'₂⟩⟩⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {w : FreeMonoid β}
    : Decidable (∀ w' : FreeMonoid α, f w' ≤ₚ w → p w') :=
  decidable_of_decidable_of_iff <|
    show (∀ w' : FreeMonoid α, |w'| ≤ |w| → f w' ≤ₚ w → p w') ↔ (∀ w', f w' ≤ₚ w → p w') from
      ⟨fun h w' hw' ↦ h w' (Nat.le_trans (nonerasing_length_le f w') (List.IsPrefix.length_le hw')) hw',
        fun h w' _ hw'₂ ↦ h w' hw'₂⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {w : FreeMonoid β}
    : Decidable (∀ w' : FreeMonoid α, f w' ≤ₛ w → p w') :=
  decidable_of_decidable_of_iff <|
    show (∀ w' : FreeMonoid α, |w'| ≤ |w| → f w' ≤ₛ w → p w') ↔ (∀ w', f w' ≤ₛ w → p w') from
      ⟨fun h w' hw' ↦ h w' (Nat.le_trans (nonerasing_length_le f w') (List.IsSuffix.length_le hw')) hw',
        fun h w' _ hw'₂ ↦ h w' hw'₂⟩

instance [DecidableEq β] {f : FreeMonoid α →* FreeMonoid β} [IsNonErasing f] [DecidablePred p] {w : FreeMonoid β}
    : Decidable (∀ w' : FreeMonoid α, f w' ≤ᵢ w → p w') :=
  decidable_of_decidable_of_iff <|
    show (∀ w' : FreeMonoid α, |w'| ≤ |w| → f w' ≤ᵢ w → p w') ↔ (∀ w', f w' ≤ᵢ w → p w') from
      ⟨fun h w' hw' ↦ h w' (Nat.le_trans (nonerasing_length_le f w') (List.IsInfix.length_le hw')) hw',
        fun h w' _ hw'₂ ↦ h w' hw'₂⟩


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
