import HyperCubeGroup.Foundation.Representation.UnitaryMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Algebra.Group.Commute.Units

/-! # Making an invertible matrix intertwiner unitary

For unitary families, the positive square root of S†S commutes with the source
family. Multiplication by its inverse gives a unitary intertwiner. No character
theorem or regular-representation assumption is used in this analytic step.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Matrix MatrixOrder ComplexOrder
namespace HyperCubeGroup.Manuscript
open ThreeFamilySynchronization
variable {G : Type*} {d : ℕ}

theorem adjoint_intertwines {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {S : Matrix (Fin d) (Fin d) ℂ} (h : S * A = B * S) :
    S.conjTranspose * B = A * S.conjTranspose := by
  have hAA : A * A.conjTranspose = 1 := hA.2
  have hBB : B.conjTranspose * B = 1 := hB.1
  have hs := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_mul] at hs
  calc
    _ = A * (A.conjTranspose * S.conjTranspose) * B := by
      rw [← mul_assoc A, hAA, one_mul]
    _ = A * (S.conjTranspose * B.conjTranspose) * B := by rw [hs]
    _ = _ := by rw [mul_assoc, mul_assoc, hBB, mul_one]

theorem gram_commutes {A B S : Matrix (Fin d) (Fin d) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin d) ℂ) (h : S * A = B * S) :
    Commute (S.conjTranspose * S) A := by
  change (S.conjTranspose * S) * A = A * (S.conjTranspose * S)
  rw [mul_assoc, h, ← mul_assoc, adjoint_intertwines hA hB h, mul_assoc]

/-- Polar normalization preserves every intertwining equation simultaneously. -/
theorem unitary_intertwiner_of_invertible
    (A B : G → UnitaryMatrix d) (S : Matrix (Fin d) (Fin d) ℂ)
    (hS : IsUnit S)
    (hint : ∀ g, S * (A g : Matrix (Fin d) (Fin d) ℂ) =
      (B g : Matrix (Fin d) (Fin d) ℂ) * S) :
    ∃ V : UnitaryMatrix d, ∀ g,
      (V : Matrix (Fin d) (Fin d) ℂ) * (A g : Matrix (Fin d) (Fin d) ℂ) =
        (B g : Matrix (Fin d) (Fin d) ℂ) * (V : Matrix (Fin d) (Fin d) ℂ) := by
  let H : Matrix (Fin d) (Fin d) ℂ := S.conjTranspose * S
  have hH : 0 ≤ H := (Matrix.posSemidef_conjTranspose_mul_self S).nonneg
  have hHu : IsUnit H := hS.star.mul hS
  let T : Matrix (Fin d) (Fin d) ℂ := CFC.sqrt H
  have hT : 0 ≤ T := CFC.sqrt_nonneg H
  have hTu : IsUnit T := (CFC.isUnit_sqrt_iff H hH).2 hHu
  let t : (Matrix (Fin d) (Fin d) ℂ)ˣ := hTu.unit
  let Ti : Matrix (Fin d) (Fin d) ℂ := ↑(t⁻¹)
  have ht : (t : Matrix (Fin d) (Fin d) ℂ) = T := hTu.unit_spec
  have hts : star t = t := by
    apply Units.ext
    change star (t : Matrix (Fin d) (Fin d) ℂ) = _
    rw [ht]
    exact (CFC.sqrt_nonneg H).isSelfAdjoint.star_eq
  have hti : Ti.conjTranspose = Ti := by
    change ((star (t⁻¹) : (Matrix (Fin d) (Fin d) ℂ)ˣ) : Matrix (Fin d) (Fin d) ℂ) = _
    rw [star_inv, hts]
  have hsq : (t : Matrix (Fin d) (Fin d) ℂ) * t = H := by
    rw [ht]
    exact CFC.sqrt_mul_sqrt_self H hH
  have hv : S * Ti ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.2
    change (S * Ti).conjTranspose * (S * Ti) = 1
    rw [Matrix.conjTranspose_mul, hti]
    calc
      _ = Ti * H * Ti := by dsimp [H]; simp only [mul_assoc]
      _ = 1 := by rw [← hsq]; simp [Ti, ← mul_assoc]
  refine ⟨⟨S * Ti, hv⟩, ?_⟩
  intro g
  have hc : Commute T (A g : Matrix (Fin d) (Fin d) ℂ) := by
    dsimp [T]
    rw [CFC.sqrt_eq_cfc]
    exact (gram_commutes (A g).property (B g).property (hint g)).cfc_nnreal _
  have hct : Commute (t : Matrix (Fin d) (Fin d) ℂ) (A g : Matrix (Fin d) (Fin d) ℂ) := by
    rw [ht]; exact hc
  have hci : Commute Ti (A g : Matrix (Fin d) (Fin d) ℂ) := Commute.units_inv_left hct
  change (S * Ti) * (A g : Matrix (Fin d) (Fin d) ℂ) = _
  rw [mul_assoc, hci.eq, ← mul_assoc, hint g, mul_assoc]

end HyperCubeGroup.Manuscript
