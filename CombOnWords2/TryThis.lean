import CombOnWords2.Basic
import MathlibExtras.LibrarySearch

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

def a := 3
def fm : FreeMonoid Nat := [1, 2, 3]
def fm2 : FreeMonoid Nat := [1, 2, 3]

#eval a ∈ fm
#eval fm = fm2
#eval [1, 2, 3] <+: [0, 1, 2, 3, 4]
#eval [2, 3] <:+: [1, 2, 3, 4]
#eval fm <*: fm2
