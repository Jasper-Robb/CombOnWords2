import CombOnWords2.Basic
import MathlibExtras.LibrarySearch

example : (complement ∘* complement) w = complement (complement w) := by
  simp only [MonoidHom.coe_comp, Function.comp_apply]

example [Fintype α] (w : Word α) : (MonoidHom.id (Word α)) w = w := by simp only [MonoidHom.id_apply]
