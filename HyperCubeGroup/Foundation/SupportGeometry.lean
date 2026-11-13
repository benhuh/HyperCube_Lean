import HyperCubeGroup.Foundation.CollinearManifold
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Trace

open Matrix BigOperators

noncomputable section

variable {n : ℕ} [NeZero n]

theorem support_nondegenerate_of_nonzero (Θ : HCParams n) (f : BinOp n)
    (trace : ∀ a b, hcProduct Θ a b (f.op a b) ≠ 0) :
    SupportNondegenerate Θ f := by
  have local_nonzero : ∀ a b, frobNormSq (Θ.A a) ≠ 0 ∧
      frobNormSq (Θ.B b) ≠ 0 ∧ frobNormSq (Θ.C (f.op a b)) ≠ 0 := by
    intro a b
    refine ⟨?_, ?_, ?_⟩ <;> intro hzero
    · have h := (frobNormSq_eq_zero_iff _).mp hzero
      apply trace a b
      simp [hcProduct, h]
    · have h := (frobNormSq_eq_zero_iff _).mp hzero
      apply trace a b
      simp [hcProduct, h]
    · have h := (frobNormSq_eq_zero_iff _).mp hzero
      apply trace a b
      simp [hcProduct, h]
  exact ⟨fun a => (local_nonzero a 0).1,
    fun b => (local_nonzero 0 b).2.1,
    fun a b => (local_nonzero a b).2.2⟩

omit [NeZero n] in
theorem support_local_gram_identities (Θ : HCParams n) (f : BinOp n)
    (identities : CollinearIdentities Θ f)
    (trace : ∀ a b, hcProduct Θ a b (f.op a b) ≠ 0) (a b : Fin n) :
      gramA Θ a = (1 / frobNormSq (Θ.C (f.op a b))) •
        ((Θ.C (f.op a b)).conjTranspose * Θ.C (f.op a b)) ∧
    gramB Θ b = (1 / frobNormSq (Θ.A a)) •
        ((Θ.A a).conjTranspose * Θ.A a) ∧
    gramC Θ (f.op a b) = (1 / frobNormSq (Θ.B b)) •
        ((Θ.B b).conjTranspose * Θ.B b) := by
  have hfirst := (Matrix.mul_assoc (Θ.A a) (Θ.B b) (Θ.C (f.op a b))).symm
  rw [identities.idA a b, identities.idC a b] at hfirst
  have hsecond := (Matrix.mul_assoc (Θ.B b) (Θ.C (f.op a b)) (Θ.A a)).symm
  rw [identities.idB a b, identities.idA a b] at hsecond
  have hthird := (Matrix.mul_assoc (Θ.C (f.op a b)) (Θ.A a) (Θ.B b)).symm
  rw [identities.idC a b, identities.idB a b] at hthird
  simp only [Matrix.mul_smul, Matrix.smul_mul, div_eq_mul_inv,
    SemigroupAction.mul_smul] at hfirst hsecond hthird
  exact ⟨by simpa only [gramA, one_div] using
      (smul_right_injective _ (trace a b)) hfirst,
    by simpa only [gramB, one_div] using
      (smul_right_injective _ (trace a b)) hsecond,
    by simpa only [gramC, one_div] using
      (smul_right_injective _ (trace a b)) hthird⟩

def supportGram (Θ : HCParams n) : Matrix (Fin n) (Fin n) ℂ :=
  gramB Θ 0

theorem support_gram_eq (Θ : HCParams n) (f : BinOp n)
    (identities : CollinearIdentities Θ f)
    (trace : ∀ a b, hcProduct Θ a b (f.op a b) ≠ 0) :
    (∀ b, gramB Θ b = supportGram Θ) ∧
    (∀ a, (1 / frobNormSq (Θ.A a)) •
      ((Θ.A a).conjTranspose * Θ.A a) = supportGram Θ) := by
  have local_eq := fun a b => (support_local_gram_identities Θ f identities trace a b).2.1
  refine ⟨?_, ?_⟩
  · intro b
    exact (local_eq 0 b).trans (local_eq 0 0).symm
  · intro a
    exact (local_eq a 0).symm

theorem support_gram_trace (Θ : HCParams n) (f : BinOp n)
    (trace : ∀ a b, hcProduct Θ a b (f.op a b) ≠ 0) :
    (supportGram Θ).trace = (n : ℂ) := by
  have hnd := support_nondegenerate_of_nonzero Θ f trace
  unfold supportGram gramB
  rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]
  have hnorm : ((Θ.B 0).conjTranspose * Θ.B 0).trace =
      (n : ℂ) * frobNormSq (Θ.B 0) := by
    unfold frobNormSq frobInner
    field_simp [(Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : ℂ) ≠ 0)]
  rw [hnorm]
  field_simp [hnd.B_pos 0]

theorem support_gram_hermitian (Θ : HCParams n) :
    (supportGram Θ).conjTranspose = supportGram Θ := by
  simp only [supportGram, gramB, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    star_div₀, star_one, star_frobNormSq]

theorem support_shared_gram_matrices (Θ : HCParams n) (f : BinOp n)
    (identities : CollinearIdentities Θ f)
    (trace : ∀ a b, hcProduct Θ a b (f.op a b) ≠ 0) :
    ∃ Z : Matrix (Fin n) (Fin n) ℂ,
      (∀ b, gramB Θ b = Z) ∧
      (∀ a, (1 / frobNormSq (Θ.A a)) •
        ((Θ.A a).conjTranspose * Θ.A a) = Z) ∧
      (1 / (n : ℂ)) * Z.trace = 1 ∧ Z.conjTranspose = Z := by
  obtain ⟨hB, hA⟩ := support_gram_eq Θ f identities trace
  refine ⟨supportGram Θ, hB, hA, ?_, support_gram_hermitian Θ⟩
  rw [support_gram_trace Θ f trace]
  field_simp [(Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : ℂ) ≠ 0)]

theorem support_gram_square_inverse (Θ : HCParams n) (f : BinOp n)
    (identities : CollinearIdentities Θ f)
    (trace : ∀ a b, hcProduct Θ a b (f.op a b) ≠ 0) (a b : Fin n) :
    supportGram Θ * supportGram Θ =
      (kappaTriple Θ a b (f.op a b))⁻¹ • supportGram Θ := by
  obtain ⟨hB, hA⟩ := support_gram_eq Θ f identities trace
  let prediction := hcProduct Θ a b (f.op a b)
  let α := frobNormSq (Θ.A a)
  let β := frobNormSq (Θ.B b)
  let γ := frobNormSq (Θ.C (f.op a b))
  have hZB : supportGram Θ = (1 / β) • (Θ.B b * (Θ.B b).conjTranspose) :=
    (hB b).symm
  have hZA : supportGram Θ = (1 / α) • ((Θ.A a).conjTranspose * Θ.A a) :=
    (hA a).symm
  have hBtAt : (Θ.B b).conjTranspose * (Θ.A a).conjTranspose =
      (starRingEnd ℂ prediction / γ) • Θ.C (f.op a b) := by
    rw [← Matrix.conjTranspose_mul, identities.idC a b,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose]
    simp only [star_div₀, star_frobNormSq]
    rfl
  have hkey : Θ.B b * (Θ.B b).conjTranspose *
      ((Θ.A a).conjTranspose * Θ.A a) =
      (starRingEnd ℂ prediction / γ * prediction) • supportGram Θ := by
    calc
      _ = Θ.B b * (((Θ.B b).conjTranspose * (Θ.A a).conjTranspose) * Θ.A a) := by
        simp only [Matrix.mul_assoc]
      _ = (starRingEnd ℂ prediction / γ) •
          (Θ.B b * (Θ.C (f.op a b) * Θ.A a)) := by
        rw [hBtAt, Matrix.smul_mul, Matrix.mul_smul]
      _ = (starRingEnd ℂ prediction / γ) •
          ((prediction / β) • (Θ.B b * (Θ.B b).conjTranspose)) := by
        rw [identities.idB a b, Matrix.mul_smul]
      _ = _ := by
        rw [hZB]
        simp only [smul_smul]
        congr 1
        ring
  calc
    _ = ((1 / β) * (1 / α)) •
        (Θ.B b * (Θ.B b).conjTranspose * ((Θ.A a).conjTranspose * Θ.A a)) := by
      conv_lhs => lhs; rw [hZB]
      conv_lhs => rhs; rw [hZA]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = _ := by
      rw [hkey, smul_smul]
      congr 1
      dsimp [kappaTriple, α, β, γ, prediction]
      field_simp

theorem support_kappaTriple_real (Θ : HCParams n) (a b c : Fin n) :
    kappaTriple Θ a b c =
      (((frobNormSq (Θ.A a)).re * (frobNormSq (Θ.B b)).re *
        (frobNormSq (Θ.C c)).re / ‖hcProduct Θ a b c‖ ^ 2 : ℝ) : ℂ) := by
  have hreal : ∀ factor : Matrix (Fin n) (Fin n) ℂ,
      frobNormSq factor = ((frobNormSq factor).re : ℂ) := by
    intro factor
    apply Complex.ext <;> simp [frobNormSq_real]
  unfold kappaTriple
  rw [hreal (Θ.A a), hreal (Θ.B b), hreal (Θ.C c),
    mul_comm (hcProduct Θ a b c), ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem support_normalized_rank_constant (Θ : HCParams n) (f : BinOp n)
    (identities : CollinearIdentities Θ f)
    (trace : ∀ a b, hcProduct Θ a b (f.op a b) ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
      ∀ a b, kappaTriple Θ a b (f.op a b) = (κ : ℂ) := by
  have hnd := support_nondegenerate_of_nonzero Θ f trace
  have htr := support_gram_trace Θ f trace
  have hsq := support_gram_square_inverse Θ f identities trace
  let κ : ℝ := (frobNormSq (Θ.A 0)).re * (frobNormSq (Θ.B 0)).re *
    (frobNormSq (Θ.C (f.op 0 0))).re / ‖hcProduct Θ 0 0 (f.op 0 0)‖ ^ 2
  have hκpos : 0 < κ := by
    exact div_pos (mul_pos (mul_pos
      (frobNormSq_re_pos_of_ne_zero _ (hnd.A_pos 0))
      (frobNormSq_re_pos_of_ne_zero _ (hnd.B_pos 0)))
      (frobNormSq_re_pos_of_ne_zero _ (hnd.C_pos 0 0)))
      (pow_pos (norm_pos_iff.mpr (trace 0 0)) _)
  have hconst : ∀ a b, kappaTriple Θ a b (f.op a b) = (κ : ℂ) := by
    intro a b
    have hscalar := congrArg Matrix.trace ((hsq a b).symm.trans (hsq 0 0))
    simp only [Matrix.trace_smul, smul_eq_mul, htr] at hscalar
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    exact (inv_injective (mul_right_cancel₀ hn hscalar)).trans
      (support_kappaTriple_real Θ 0 0 (f.op 0 0))
  have hnormSub : frobNormSq (1 - supportGram Θ) = ((κ⁻¹ - 1 : ℝ) : ℂ) := by
    unfold frobNormSq frobInner
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, support_gram_hermitian]
    have hexpand : (1 - supportGram Θ) * (1 - supportGram Θ) =
        1 - supportGram Θ - supportGram Θ + supportGram Θ * supportGram Θ := by
      simp only [sub_mul, mul_sub, Matrix.mul_one, Matrix.one_mul]
      abel
    rw [hexpand, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_one, Fintype.card_fin, htr, hsq 0 0, hconst,
      Matrix.trace_smul, smul_eq_mul]
    rw [htr]
    push_cast
    field_simp [(Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : ℂ) ≠ 0),
      (Complex.ofReal_ne_zero.mpr hκpos.ne' : (κ : ℂ) ≠ 0)]
    ring
  have hnonneg := frobNormSq_nonneg (1 - supportGram Θ)
  rw [hnormSub, Complex.ofReal_re] at hnonneg
  have hκle : κ ≤ 1 := by
    have hinv : 1 ≤ 1 / κ := by simpa only [one_div] using (by linarith : 1 ≤ κ⁻¹)
    simpa only [one_mul] using (le_div_iff₀ hκpos).mp hinv
  exact ⟨κ, hκpos, hκle, hconst⟩

theorem support_gram_projection_identity (Θ : HCParams n) (f : BinOp n)
    (identities : CollinearIdentities Θ f)
    (trace : ∀ a b, hcProduct Θ a b (f.op a b) ≠ 0) (a b : Fin n) :
    supportGram Θ = kappaTriple Θ a b (f.op a b) •
      (supportGram Θ * supportGram Θ) := by
  have hnd := support_nondegenerate_of_nonzero Θ f trace
  have hκne : kappaTriple Θ a b (f.op a b) ≠ 0 := by
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (hnd.A_pos a) (hnd.B_pos b)) (hnd.C_pos a b))
      (mul_ne_zero (trace a b) ((map_ne_zero (starRingEnd ℂ)).mpr (trace a b)))
  rw [support_gram_square_inverse Θ f identities trace, smul_smul,
    mul_inv_cancel₀ hκne, one_smul]

omit [NeZero n] in
private theorem support_rank_smul (scalar : ℂ) (hne : scalar ≠ 0)
    (M : Matrix (Fin n) (Fin n) ℂ) : (scalar • M).rank = M.rank := by
  apply le_antisymm
  · simpa only [Matrix.smul_mul, Matrix.one_mul] using
      Matrix.rank_mul_le_right (scalar • (1 : Matrix (Fin n) (Fin n) ℂ)) M
  · have h := Matrix.rank_mul_le_right
      (scalar⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ)) (scalar • M)
    simpa only [Matrix.smul_mul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ hne, one_smul] using h

omit [NeZero n] in
private theorem support_trace_eq_rank_of_idempotent
    (P : Matrix (Fin n) (Fin n) ℂ) (hidempotent : P * P = P) :
    P.trace = (P.rank : ℂ) := by
  have hproj : LinearMap.IsProj (LinearMap.range P.mulVecLin) P.mulVecLin :=
    (LinearMap.isProj_range_iff_isIdempotentElem P.mulVecLin).mpr (by
      change P.mulVecLin.comp P.mulVecLin = P.mulVecLin
      rw [← Matrix.mulVecLin_mul, hidempotent])
  simpa only [Matrix.rank, ← Matrix.toLin'_apply', Matrix.trace_toLin'_eq] using
    hproj.trace

theorem support_gram_rank_formula (Θ : HCParams n) (f : BinOp n)
    (identities : CollinearIdentities Θ f)
    (trace : ∀ a b, hcProduct Θ a b (f.op a b) ≠ 0)
    (κ : ℝ) (positive : 0 < κ)
    (constant : ∀ a b, kappaTriple Θ a b (f.op a b) = (κ : ℂ)) :
    (n : ℝ) * κ = ((supportGram Θ).rank : ℝ) := by
  have hprojection : supportGram Θ = (κ : ℂ) •
      (supportGram Θ * supportGram Θ) := by
    simpa only [constant] using support_gram_projection_identity Θ f identities trace 0 0
  have hidempotent : ((κ : ℂ) • supportGram Θ) * ((κ : ℂ) • supportGram Θ) =
      (κ : ℂ) • supportGram Θ := by
    rw [Matrix.smul_mul, Matrix.mul_smul, ← hprojection]
  have hscalar : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have htrace := support_trace_eq_rank_of_idempotent
    ((κ : ℂ) • supportGram Θ) hidempotent
  rw [Matrix.trace_smul, smul_eq_mul, support_gram_trace Θ f trace,
    support_rank_smul (κ : ℂ) hscalar] at htrace
  have hreal := congrArg Complex.re htrace
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero, mul_comm] using hreal

open scoped ComplexOrder in
theorem support_slice_ranks (Θ : HCParams n) (f : BinOp n)
    (identities : CollinearIdentities Θ f)
    (trace : ∀ a b, hcProduct Θ a b (f.op a b) ≠ 0) :
    (∀ a, (Θ.A a).rank = (supportGram Θ).rank) ∧
    (∀ b, (Θ.B b).rank = (supportGram Θ).rank) ∧
    (∀ a b, (Θ.C (f.op a b)).rank = (supportGram Θ).rank) := by
  have hnd := support_nondegenerate_of_nonzero Θ f trace
  obtain ⟨hB, hA⟩ := support_gram_eq Θ f identities trace
  have rankA : ∀ a, (Θ.A a).rank = (supportGram Θ).rank := by
    intro a
    rw [← hA a, support_rank_smul _ (one_div_ne_zero (hnd.A_pos a)),
      Matrix.rank_conjTranspose_mul_self]
  have rankB : ∀ b, (Θ.B b).rank = (supportGram Θ).rank := by
    intro b
    rw [← hB b, gramB, support_rank_smul _ (one_div_ne_zero (hnd.B_pos b)),
      Matrix.rank_self_mul_conjTranspose]
  refine ⟨rankA, rankB, ?_⟩
  intro a b
  have hlocal := congrArg Matrix.rank
    (support_local_gram_identities Θ f identities trace a b).1
  simp only [gramA, support_rank_smul _ (one_div_ne_zero (hnd.A_pos a)),
    support_rank_smul _ (one_div_ne_zero (hnd.C_pos a b)),
    Matrix.rank_self_mul_conjTranspose, Matrix.rank_conjTranspose_mul_self] at hlocal
  exact hlocal.symm.trans (rankA a)

theorem support_rank_identification (Θ : HCParams n) (f : BinOp n)
    (identities : CollinearIdentities Θ f)
    (trace : ∀ a b, hcProduct Θ a b (f.op a b) ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
      (∀ a b, kappaTriple Θ a b (f.op a b) = (κ : ℂ)) ∧
      (n : ℝ) * κ = ((supportGram Θ).rank : ℝ) ∧
      (∀ a, (Θ.A a).rank = (supportGram Θ).rank) ∧
      (∀ b, (Θ.B b).rank = (supportGram Θ).rank) ∧
      (∀ a b, (Θ.C (f.op a b)).rank = (supportGram Θ).rank) := by
  obtain ⟨κ, hpositive, hbound, hconstant⟩ :=
    support_normalized_rank_constant Θ f identities trace
  obtain ⟨rankA, rankB, rankC⟩ := support_slice_ranks Θ f identities trace
  exact ⟨κ, hpositive, hbound, hconstant,
    support_gram_rank_formula Θ f identities trace κ hpositive hconstant,
    rankA, rankB, rankC⟩

end
