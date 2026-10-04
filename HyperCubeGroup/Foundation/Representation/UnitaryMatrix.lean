import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic

namespace HyperCubeGroup.ThreeFamilySynchronization

/-- Bundled complex unitary matrices in dimension d. -/
abbrev UnitaryMatrix (d : ℕ) := ↥(Matrix.unitaryGroup (Fin d) ℂ)

end HyperCubeGroup.ThreeFamilySynchronization