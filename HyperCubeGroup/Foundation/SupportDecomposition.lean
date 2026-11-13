import HyperCubeGroup.Foundation.Decomposition
import HyperCubeGroup.Foundation.SupportGeometry

noncomputable section

variable {n : ℕ} [NeZero n]

/-- The objective decomposes using only nonzero norms on supported triples. -/
theorem support_decomposition (Θ : HCParams n) (f : BinOp n)
    (hnd : SupportNondegenerate Θ f) :
    objective Θ f = inverseScalePenalty Θ f + misalignmentPenalty Θ f :=
  decomposition_of_support_nondegenerate Θ f hnd

/-- Collinearity and the supported identities are equivalent without global assumptions. -/
theorem support_perfectCollinearity_iff_identities (Θ : HCParams n) (f : BinOp n)
    (hnd : SupportNondegenerate Θ f) :
    PerfectCollinearity Θ f ↔ CollinearIdentities Θ f := by
  clear hnd
  exact perfectCollinearity_iff_identities_without_nondegeneracy Θ f

/-- The supported identities imply perfect collinearity without norm assumptions. -/
theorem support_identities_implies_perfectCollinearity (Θ : HCParams n) (f : BinOp n)
    (hids : CollinearIdentities Θ f) : PerfectCollinearity Θ f :=
  (perfectCollinearity_iff_identities_without_nondegeneracy Θ f).mpr hids

/-- Under collinearity, the real objective equals its inverse-scale penalty. -/
theorem support_collinear_objective_eq_inverseScalePenalty (Θ : HCParams n) (f : BinOp n)
    (hnd : SupportNondegenerate Θ f) (hcol : PerfectCollinearity Θ f) :
    (objective Θ f).re = (inverseScalePenalty Θ f).re := by
  have hdecomp := support_decomposition Θ f hnd
  rw [show misalignmentPenalty Θ f = 0 from hcol, add_zero] at hdecomp
  exact congrArg Complex.re hdecomp
