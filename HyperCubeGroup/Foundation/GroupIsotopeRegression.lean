import HyperCubeGroup.Foundation.GroupIsotope

namespace GroupIsotopeRegression

def minOperation : BinOp 2 := ⟨min⟩

theorem minOperation_isAssociativeIsotope : IsAssociativeIsotope minOperation := by
  refine ⟨minOperation, ?_, Equiv.refl _, Equiv.refl _, Equiv.refl _, ?_⟩
  · intro first second third
    exact min_assoc first second third
  · intro first second
    rfl

theorem minOperation_not_isGroupIsotope : ¬ IsGroupIsotope minOperation := by
  intro hgroup
  have hinjective := (hgroup.isQuasigroup.left_cancel (0 : Fin 2)).1
  have hcollision : minOperation.op 0 0 = minOperation.op 0 1 := by decide
  have heq : (0 : Fin 2) = 1 := hinjective hcollision
  exact (by decide : (0 : Fin 2) ≠ 1) heq

end GroupIsotopeRegression