import CombOnWords2.Basic
import MathlibExtras.LibrarySearch

variable {α β : Type*}
variable [Fintype α] [Fintype β]

theorem complement_complement2 (w : Word (Fin 2)) : ~(~w) = w := by
  sorry

theorem word_morphism_eq (f g : Word α →* Word β) (h : ∀ (x : α), f (FreeMonoid.of x) = g (FreeMonoid.of x))
    : f = g := by
  exact FreeMonoid.hom_eq h

