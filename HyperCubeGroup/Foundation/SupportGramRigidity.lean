import HyperCubeGroup.Foundation.SupportInverseRank
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : ℕ} [NeZero n]

theorem support_normalized_gram_posSemidef (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.PosSemidef ((1 / frobNormSq M) • (M * M.conjTranspose)) := by
  have hreal : frobNormSq M = ((frobNormSq M).re : ℂ) := by
    apply Complex.ext <;> simp [frobNormSq_real]
  have hscalar : (0 : ℂ) ≤ 1 / frobNormSq M := by
    rw [hreal, ← Complex.ofReal_one, ← Complex.ofReal_div]
    rw [Complex.le_def]
    exact ⟨one_div_nonneg.mpr (frobNormSq_nonneg M), rfl⟩
  exact (Matrix.posSemidef_self_mul_conjTranspose M).smul hscalar

theorem support_gram_posSemidef (Θ : HCParams n) :
    Matrix.PosSemidef (supportGram Θ) := by
  exact support_normalized_gram_posSemidef (Θ.B 0)

theorem support_local_grams_posSemidef (Θ : HCParams n) (f : BinOp n) :
    ∀ a b : Fin n, Matrix.PosSemidef (gramA Θ a) ∧
      Matrix.PosSemidef (gramB Θ b) ∧ Matrix.PosSemidef (gramC Θ (f.op a b)) := by
  intro a b
  exact ⟨support_normalized_gram_posSemidef (Θ.A a),
    support_normalized_gram_posSemidef (Θ.B b),
    support_normalized_gram_posSemidef (Θ.C (f.op a b))⟩

omit [NeZero n] in
theorem normalized_gram_swap (M : Matrix (Fin n) (Fin n) ℂ) (scalar : ℂ)
    (hgram : scalar • (M.conjTranspose * M) = 1) :
    scalar • (M * M.conjTranspose) = 1 := by
  have hleft : (scalar • M.conjTranspose) * M = 1 := by
    simpa only [Matrix.smul_mul] using hgram
  have hright : M * (scalar • M.conjTranspose) = 1 :=
    mul_eq_one_comm.mp hleft
  simpa only [Matrix.mul_smul] using hright

theorem support_kappa_one_iff_local_grams_identity (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f)
    (htrace : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) ≠ 0)
    (κ : ℝ) (hpos : 0 < κ)
    (hconst : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = (κ : ℂ)) :
    κ = 1 ↔ ∀ a b : Fin n,
      gramA Θ a = 1 ∧ gramB Θ b = 1 ∧ gramC Θ (f.op a b) = 1 := by
  have hnd := support_nondegenerate_of_nonzero Θ f htrace
  have hids := (support_perfectCollinearity_iff_identities Θ f hnd).mp hcol
  obtain ⟨hB, hA⟩ := support_gram_eq Θ f hids htrace
  constructor
  · intro hunit
    have hZ := (support_kappa_one_iff_gram_identity Θ f hcol htrace κ hpos hconst).mp hunit
    have hgramA : ∀ a : Fin n, gramA Θ a = 1 := by
      intro a
      exact normalized_gram_swap (Θ.A a) (1 / frobNormSq (Θ.A a))
        ((hA a).trans hZ)
    have hgramB : ∀ b : Fin n, gramB Θ b = 1 :=
      fun b => (hB b).trans hZ
    intro a b
    refine ⟨hgramA a, hgramB b, ?_⟩
    rw [(support_local_gram_identities Θ f hids htrace a b).2.2]
    simpa only [Matrix.conjTranspose_conjTranspose] using
      normalized_gram_swap (Θ.B b).conjTranspose (1 / frobNormSq (Θ.B b))
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hgramB b)
  · intro hlocal
    apply (support_kappa_one_iff_gram_identity Θ f hcol htrace κ hpos hconst).mpr
    exact (hlocal 0 0).2.1

theorem support_kappa_one_iff_local_normalized_grams_identity
    (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f)
    (htrace : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) ≠ 0)
    (κ : ℝ) (hpos : 0 < κ)
    (hconst : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = (κ : ℂ)) :
    κ = 1 ↔ ∀ a b : Fin n,
      gramA Θ a = 1 ∧ gramB Θ b = 1 ∧ gramC Θ (f.op a b) = 1 ∧
      (1 / frobNormSq (Θ.A a)) • ((Θ.A a).conjTranspose * Θ.A a) = 1 ∧
      (1 / frobNormSq (Θ.B b)) • ((Θ.B b).conjTranspose * Θ.B b) = 1 ∧
      (1 / frobNormSq (Θ.C (f.op a b))) •
        ((Θ.C (f.op a b)).conjTranspose * Θ.C (f.op a b)) = 1 := by
  have hnd := support_nondegenerate_of_nonzero Θ f htrace
  have hids := (support_perfectCollinearity_iff_identities Θ f hnd).mp hcol
  have hiff := support_kappa_one_iff_local_grams_identity Θ f hcol htrace κ hpos hconst
  constructor
  · intro hunit a b
    obtain ⟨hA, hB, hC⟩ := hiff.mp hunit a b
    obtain ⟨hAC, hBA, hCB⟩ := support_local_gram_identities Θ f hids htrace a b
    exact ⟨hA, hB, hC, hBA.symm.trans hB, hCB.symm.trans hC, hAC.symm.trans hA⟩
  · intro hlocal
    apply hiff.mpr
    intro a b
    obtain ⟨hA, hB, hC, _⟩ := hlocal a b
    exact ⟨hA, hB, hC⟩

end