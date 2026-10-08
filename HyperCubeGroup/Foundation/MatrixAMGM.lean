/-
  HyperCubeGroup.Foundation.MatrixAMGM

  The Matrix AM-GM inequality,
  for arbitrary complex trace, with arbitrary complex amplitude rigidity
  and the unit-trace specialization `tr(XYZ) = 1`.
  This is the irreducible
  "textbook input" from which the unconditional lower bound
  `ℋ(Θ) ≥ 3n²` and its equality rigidity follow on any quasigroup.

  Status:

    * `matrix_amgm_general`        — arbitrary-amplitude bound, including zero trace.
    * `matrix_amgm_amplitude_witness` — nonnegative amplitude witness with
      common Gram scale and exact operator product rigidity at positive amplitude.
    * `matrix_amgm_general_equality_iff` — equality classification at arbitrary
      complex trace, with separate zero and nonzero branches.
    * `matrix_amgm_at_one`         — proved (Tier 2A complete) via
        Schur triangulation of the 3n×3n block-cyclic matrix.
    * `matrix_amgm_at_one_equality` — proved via the equality case
      of the upper-triangular Schur trace bound.

  The full proof is in `BlockCyclic.lean` and `Spectral.lean`:
    * `matrix_unitary_schur_form` (proved)
    * `IsUpperTriangular.norm_trace_cubed_pow_four_le` (proved)
    * `frobNormSq_F_unitary_conj_sq`, `trace_unitary_conj_cb` (proved)
    * `frobNormSq_F_blockCyclicFin_sq`, `trace_blockCyclicFin_cb` (proved)
    * `matrix_schur_trace_bound_xyz` (proved): the unnormalised form.

  Sketch of the proof (paper, see appendix):
  Define the block-cyclic `M ∈ ℂ^{3n × 3n}` with `M_{12} = X, M_{23} = Y,
  M_{31} = Z` and the other six blocks zero. Then
    `M²` has blocks `(XY, YZ, ZX)` in positions `(0,2), (1,0), (2,1)`,
    `M³` is block-diagonal `(XYZ, YZX, ZXY)`,
  giving `‖M²‖²_F = ‖XY‖² + ‖YZ‖² + ‖ZX‖²` and `Tr(M³) = 3 · Tr(XYZ)` by
  trace cyclicity. Apply Schur: `T = Uᴴ M U` is upper triangular, and
  unitary invariance gives `‖T²‖²_F = ‖M²‖²_F`, `Tr(T³) = Tr(M³)`. For
  upper triangular `T`, `(T³)_ii = T_ii³`, so the triangle inequality and
  iterated Cauchy-Schwarz give `|Tr(T³)|⁴ ≤ N · (‖T²‖²_F)³` (with
  `N = 3n`). Specialising and using `Tr(XYZ) = n` yields the conclusion.
-/

import HyperCubeGroup.Foundation.BlockCyclic
import HyperCubeGroup.Foundation.Plancherel
import Mathlib.Analysis.Complex.Polynomial.Basic

open Matrix BigOperators Finset Complex

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## Matrix AM–GM (proved via Schur triangulation in BlockCyclic.lean) -/

/-- Bridge: `(frobNormSq A).re = (1/n) · frobNormSq_F A` (the
    normalised Frobenius² is the unnormalised sum of squared moduli
    divided by `n`). -/
theorem frobNormSq_re_eq_frobNormSq_F_div
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (frobNormSq A).re = (1 / n : ℝ) * frobNormSq_F A := by
  unfold frobNormSq frobInner
  rw [Complex.mul_re]
  have h1 : (1 / (n : ℂ)).re = (1 / n : ℝ) := by
    simp [Complex.div_re, Complex.normSq_natCast]
  have h2 : (1 / (n : ℂ)).im = 0 := by
    simp [Complex.div_im, Complex.normSq_natCast]
  rw [h1, h2, frobNormSq_F_eq_trace_re A]
  ring

/-- Matrix AM-GM for arbitrary complex normalized trace, including zero trace. -/
theorem matrix_amgm_general
    (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    3 * ‖(1 / (n : ℂ)) * (X * Y * Z).trace‖ ^ (4 / 3 : ℝ) ≤
      (frobNormSq (X * Y)).re + (frobNormSq (Y * Z)).re +
        (frobNormSq (Z * X)).re := by
  let amplitude : ℝ := ‖(1 / (n : ℂ)) * (X * Y * Z).trace‖
  let sensitivity : ℝ := (frobNormSq (X * Y)).re +
    (frobNormSq (Y * Z)).re + (frobNormSq (Z * X)).re
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hamplitude : 0 ≤ amplitude := norm_nonneg _
  have hsensitivity : 0 ≤ sensitivity :=
    add_nonneg (add_nonneg (frobNormSq_nonneg _) (frobNormSq_nonneg _))
      (frobNormSq_nonneg _)
  have htrace : ‖(X * Y * Z).trace‖ = (n : ℝ) * amplitude := by
    dsimp [amplitude]
    simp only [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    field_simp
  have hsum : frobNormSq_F (X * Y) + frobNormSq_F (Y * Z) +
      frobNormSq_F (Z * X) = (n : ℝ) * sensitivity := by
    dsimp [sensitivity]
    rw [frobNormSq_re_eq_frobNormSq_F_div,
      frobNormSq_re_eq_frobNormSq_F_div, frobNormSq_re_eq_frobNormSq_F_div]
    field_simp
  have hbound := matrix_schur_trace_bound_xyz X Y Z
  rw [norm_mul, show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num, htrace, hsum] at hbound
  have hcube : 27 * amplitude ^ 4 ≤ sensitivity ^ 3 := by
    have hfactor : (n : ℝ) ^ 4 * (27 * amplitude ^ 4) ≤
        (n : ℝ) ^ 4 * sensitivity ^ 3 := by
      nlinarith [hbound]
    exact le_of_mul_le_mul_left hfactor (by positivity)
  have hpower : (3 * amplitude ^ (4 / 3 : ℝ)) ^ 3 = 27 * amplitude ^ 4 := by
    rw [mul_pow, ← Real.rpow_mul_natCast hamplitude]
    norm_num
  have hle : 3 * amplitude ^ (4 / 3 : ℝ) ≤ sensitivity := by
    by_contra hnot
    have hlt : sensitivity < 3 * amplitude ^ (4 / 3 : ℝ) := lt_of_not_ge hnot
    have hltcube := pow_lt_pow_left₀ hlt hsensitivity (by norm_num : (3 : ℕ) ≠ 0)
    rw [hpower] at hltcube
    linarith
  exact hle

/-- **Matrix AM–GM at unit normalised trace.**
    For any `X, Y, Z ∈ ℂ^{n × n}` satisfying
    `(1/n) · Tr(X · Y · Z) = 1`,
    the cyclic Frobenius² sum of pairwise products is at least 3.

    Proof: from the Schur trace bound
      `‖3 · Tr(XYZ)‖⁴ ≤ (3n) · (‖XY‖²_F + ‖YZ‖²_F + ‖ZX‖²_F)³`,
    plug in `Tr(XYZ) = n`, divide by `(3n)`, take cube roots, then
    convert to normalised Frobenius² (which divides each term by `n`). -/
theorem matrix_amgm_at_one
    (X Y Z : Matrix (Fin n) (Fin n) ℂ)
    (h : (1 / (n : ℂ)) * (X * Y * Z).trace = 1) :
    (frobNormSq (X * Y)).re +
    (frobNormSq (Y * Z)).re +
    (frobNormSq (Z * X)).re ≥ 3 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hnnonneg : (0 : ℝ) ≤ n := le_of_lt hnpos
  -- Step 1: Tr(XYZ) = n.
  have hTr : (X * Y * Z).trace = (n : ℂ) := by
    have := h
    field_simp at this
    linear_combination this
  -- Step 2: ‖3 · Tr(XYZ)‖⁴ = (3n)⁴.
  have hLHS : ‖3 * (X * Y * Z).trace‖ ^ 4 = (3 * n : ℝ) ^ 4 := by
    rw [hTr]
    rw [show (3 : ℂ) * (n : ℂ) = ((3 * n : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * n)]
  -- Step 3: From the Schur bound, (3n)^4 ≤ (3n) · S^3.
  let S : ℝ := frobNormSq_F (X * Y) + frobNormSq_F (Y * Z) + frobNormSq_F (Z * X)
  have hSpos : 0 ≤ S := by
    have h1 := frobNormSq_F_nonneg (X * Y)
    have h2 := frobNormSq_F_nonneg (Y * Z)
    have h3 := frobNormSq_F_nonneg (Z * X)
    show 0 ≤ frobNormSq_F (X * Y) + frobNormSq_F (Y * Z) + frobNormSq_F (Z * X)
    linarith
  have hbound : (3 * n : ℝ) ^ 4 ≤ (3 * n : ℝ) * S ^ 3 := by
    rw [← hLHS]
    exact matrix_schur_trace_bound_xyz X Y Z
  -- Step 4: Cancel one factor of (3n) > 0 from both sides.
  have h3n_pos : (0 : ℝ) < 3 * n := by positivity
  have h3n_cube_le_S_cube : (3 * n : ℝ) ^ 3 ≤ S ^ 3 := by
    have hmul : (3 * n : ℝ) * (3 * n : ℝ) ^ 3 ≤ (3 * n : ℝ) * S ^ 3 := by
      rw [show (3 * n : ℝ) * (3 * n : ℝ) ^ 3 = (3 * n : ℝ) ^ 4 from by ring]
      exact hbound
    exact le_of_mul_le_mul_left hmul h3n_pos
  -- Step 5: Take cube roots: 3n ≤ S.
  have h3n_le_S : (3 * n : ℝ) ≤ S := by
    by_contra hneg
    push_neg at hneg
    have : S ^ 3 < (3 * n : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hneg hSpos (by norm_num : (3 : ℕ) ≠ 0)
    linarith
  -- Step 6: Convert from S to normalised: each (frobNormSq A).re = (1/n) · frobNormSq_F A.
  have hbridge : ∀ A : Matrix (Fin n) (Fin n) ℂ,
      (frobNormSq A).re = (1 / n : ℝ) * frobNormSq_F A :=
    fun A => frobNormSq_re_eq_frobNormSq_F_div A
  rw [hbridge, hbridge, hbridge]
  rw [show (1 / n : ℝ) * frobNormSq_F (X * Y) +
          (1 / n : ℝ) * frobNormSq_F (Y * Z) +
          (1 / n : ℝ) * frobNormSq_F (Z * X) =
          (1 / n : ℝ) * S from by show _ = _; ring]
  -- Goal: (1/n) * S ≥ 3. From 3*n ≤ S, multiply by 1/n (positive).
  calc (1 / n : ℝ) * S
      ≥ (1 / n : ℝ) * (3 * n : ℝ) := by
        apply mul_le_mul_of_nonneg_left h3n_le_S
        positivity
    _ = 3 := by field_simp

/-- **Equality case of `matrix_amgm_at_one`.**
    If the cyclic sum equals 3 at unit normalised trace, then each
    pairwise product is unitary and `X · Y · Z = I`.

    Proof: from the chain equality (LHS = RHS in `matrix_amgm_at_one`'s
    underlying inequality), Schur triangulation gives `T = Uᴴ M U`
    upper triangular, and the composition lemma
    `IsUpperTriangular.diagonal_of_chain_eq_at_real_pos` gives `T`
    diagonal of cube roots of unity. Then
    `isDiagonal_pow_three_one_mul_conjTranspose_eq_one` gives
    `T · Tᴴ = I`, hence `M · Mᴴ = I` (lifting via the unitary U), and
    finally the structural correspondence
    `blockCyclicFin_mul_conjTranspose_eq_one_iff` gives `X, Y, Z`
    unitary; and `blockCyclicFin_cb_eq_one_iff` gives `XYZ = 1`. -/
theorem matrix_amgm_at_one_equality
    (X Y Z : Matrix (Fin n) (Fin n) ℂ)
    (h : (1 / (n : ℂ)) * (X * Y * Z).trace = 1)
    (heq : (frobNormSq (X * Y)).re +
           (frobNormSq (Y * Z)).re +
           (frobNormSq (Z * X)).re = 3) :
    X * X.conjTranspose = 1 ∧
    Y * Y.conjTranspose = 1 ∧
    Z * Z.conjTranspose = 1 ∧
    X * Y * Z = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hN_pos_nat : 0 < 3 * n := by omega
  have hN_pos : (0 : ℝ) < (3 * n : ℕ) := by exact_mod_cast hN_pos_nat
  -- Step 1: Tr(XYZ) = n.
  have hTr : (X * Y * Z).trace = (n : ℂ) := by
    field_simp at h; linear_combination h
  -- Step 2: (||XY||²_F + ||YZ||²_F + ||ZX||²_F) = 3n.
  have hSF : frobNormSq_F (X * Y) + frobNormSq_F (Y * Z) + frobNormSq_F (Z * X) =
             (3 * n : ℕ) := by
    have hbridge : ∀ A : Matrix (Fin n) (Fin n) ℂ,
        (frobNormSq A).re = (1 / n : ℝ) * frobNormSq_F A :=
      fun A => frobNormSq_re_eq_frobNormSq_F_div A
    rw [hbridge, hbridge, hbridge] at heq
    have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos_nat
    field_simp at heq
    push_cast; linarith
  -- Step 3: Schur on blockCyclicFin X Y Z.
  obtain ⟨U, hUU, hUU', hUTri⟩ :=
    matrix_unitary_schur_form (blockCyclicFin X Y Z)
  set T : Matrix (Fin (3 * n)) (Fin (3 * n)) ℂ :=
    Uᴴ * blockCyclicFin X Y Z * U with hT_def
  -- Step 4: Tr(T^3) = (3n : ℂ).
  have hTrT3 : (T * T * T).trace = ((3 * n : ℕ) : ℂ) := by
    rw [hT_def]
    rw [trace_unitary_conj_cb hUU']
    rw [trace_blockCyclicFin_cb]
    rw [hTr]; push_cast; ring
  -- Step 5: frobNormSq_F (T*T) = 3n.
  have hF_TT : frobNormSq_F (T * T) = ((3 * n : ℕ) : ℝ) := by
    rw [hT_def]
    rw [frobNormSq_F_unitary_conj_sq hUU hUU']
    rw [frobNormSq_F_blockCyclicFin_sq]
    exact hSF
  -- Step 6: Chain equality at bookends.
  have h_chain_eq : ‖(T * T * T).trace‖ ^ 4 =
                    ((3 * n : ℕ) : ℝ) * frobNormSq_F (T * T) ^ 3 := by
    rw [hTrT3, hF_TT]
    rw [Complex.norm_natCast]
    push_cast; ring
  -- Step 7: Apply composition lemma.
  obtain ⟨h_T3_one, h_T_diag⟩ :=
    hUTri.diagonal_of_chain_eq_at_real_pos hN_pos_nat hTrT3 h_chain_eq
  -- Step 8: T*Tᴴ = 1 from T diagonal of cube roots.
  have hTTH : T * Tᴴ = 1 :=
    isDiagonal_pow_three_one_mul_conjTranspose_eq_one h_T_diag h_T3_one
  -- Step 9: blockCyclicFin · (blockCyclicFin)ᴴ = 1.
  have hM_eq : blockCyclicFin X Y Z = U * T * Uᴴ := by
    rw [hT_def]
    rw [show U * (Uᴴ * blockCyclicFin X Y Z * U) * Uᴴ =
         (U * Uᴴ) * blockCyclicFin X Y Z * (U * Uᴴ) from by
          simp only [Matrix.mul_assoc]]
    rw [hUU', Matrix.one_mul, Matrix.mul_one]
  have hM_unit : blockCyclicFin X Y Z * (blockCyclicFin X Y Z)ᴴ = 1 := by
    rw [hM_eq]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    -- Goal: U * T * Uᴴ * (U * (Tᴴ * Uᴴ)) = 1
    rw [show U * T * Uᴴ * (U * (Tᴴ * Uᴴ)) = U * T * (Uᴴ * U) * Tᴴ * Uᴴ from by
          simp only [Matrix.mul_assoc]]
    rw [hUU, Matrix.mul_one]
    rw [show U * T * Tᴴ * Uᴴ = U * (T * Tᴴ) * Uᴴ from by
          simp only [Matrix.mul_assoc]]
    rw [hTTH, Matrix.mul_one]
    exact hUU'
  -- Step 10: T^3 = 1 (T diagonal of cube roots), so blockCyclicFin^3 = 1.
  -- Helper: T diagonal ⇒ T*T diagonal with diag T_ii^2.
  have hTT_diag : ∀ i j : Fin (3 * n), i ≠ j → (T * T) i j = 0 := by
    intros i j hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intros k _
    by_cases hik : i = k
    · subst hik; rw [h_T_diag i j hij]; ring
    · rw [h_T_diag i k hik]; ring
  have hTT_diag_eq : ∀ i : Fin (3 * n), (T * T) i i = (T i i) ^ 2 := by
    intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single i ?_ ?_]
    · ring
    · intros k _ hki; rw [h_T_diag i k (Ne.symm hki)]; ring
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hT3_id : T * T * T = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single i ?_ ?_]
      · rw [hTT_diag_eq i, show (T i i) ^ 2 * T i i = (T i i) ^ 3 from by ring,
            h_T3_one i]
        simp [Matrix.one_apply]
      · intros k _ hki; rw [h_T_diag k i hki]; ring
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · -- i ≠ j: 1 i j = 0, and the sum vanishes.
      rw [show (1 : Matrix (Fin (3 * n)) (Fin (3 * n)) ℂ) i j = 0 from
        Matrix.one_apply_ne hij]
      apply Finset.sum_eq_zero
      intros k _
      by_cases hik : i = k
      · subst hik; rw [h_T_diag i j hij]; ring
      · rw [hTT_diag i k hik]; ring
  -- Step 11: blockCyclicFin · blockCyclicFin · blockCyclicFin = 1.
  have hM3_id :
      blockCyclicFin X Y Z * blockCyclicFin X Y Z * blockCyclicFin X Y Z = 1 := by
    rw [hM_eq]
    rw [show (U * T * Uᴴ) * (U * T * Uᴴ) * (U * T * Uᴴ) =
         U * T * (Uᴴ * U) * T * (Uᴴ * U) * T * Uᴴ from by
          simp only [Matrix.mul_assoc]]
    rw [hUU, Matrix.mul_one, Matrix.mul_one]
    rw [show U * T * T * T * Uᴴ = U * (T * T * T) * Uᴴ from by
          simp only [Matrix.mul_assoc]]
    rw [hT3_id, Matrix.mul_one, hUU']
  -- Step 12: Apply blockCyclicFin correspondences.
  have hXYZ_unit := (blockCyclicFin_mul_conjTranspose_eq_one_iff X Y Z).mp hM_unit
  have hXYZ_one := (blockCyclicFin_cb_eq_one_iff X Y Z).mp hM3_id
  exact ⟨hXYZ_unit.1, hXYZ_unit.2.1, hXYZ_unit.2.2, hXYZ_one.1⟩

/-! ## Arbitrary complex prediction amplitude -/

omit [NeZero n] in
private theorem gram_eq_norm_sq_of_inv_smul_unitary
    (z : ℂ) (hz : z ≠ 0) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : (z⁻¹ • M) * (z⁻¹ • M).conjTranspose = 1) :
    M * M.conjTranspose =
      ((‖z‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul] at hM
  change ((starRingEnd ℂ) z⁻¹ * z⁻¹) • (M * M.conjTranspose) = 1 at hM
  have hcoef : starRingEnd ℂ z⁻¹ * z⁻¹ =
      (((‖z‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
    rw [map_inv₀, ← mul_inv, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  rw [hcoef] at hM
  have hnormR : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hnorm : (((‖z‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := ofReal_ne_zero.mpr hnormR
  calc
    M * M.conjTranspose =
        ((‖z‖ ^ 2 : ℝ) : ℂ) •
          ((((‖z‖ ^ 2 : ℝ) : ℂ))⁻¹ • (M * M.conjTranspose)) := by
            rw [smul_inv_smul₀ hnorm]
    _ = ((‖z‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by rw [hM]

private theorem frobNormSq_inv_cube_root_pair_re
    (z : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (frobNormSq ((z⁻¹ * z⁻¹) • M)).re =
      ‖z‖⁻¹ ^ 4 * (frobNormSq M).re := by
  rw [frobNormSq_smul]
  have hc : (z⁻¹ * z⁻¹) * starRingEnd ℂ (z⁻¹ * z⁻¹) =
      (((‖z‖⁻¹ ^ 4 : ℝ) : ℂ)) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
    rw [Complex.normSq_mul, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
    norm_num
    ring
  rw [hc, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Every complex normalized trace has a nonnegative amplitude `x`. The cyclic
    sensitivity is at least `3x⁴`, and equality at positive amplitude forces
    all three factors to share Gram scale `x² I` and to satisfy the exact operator product. -/
theorem matrix_amgm_amplitude_witness
    (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ x : ℝ,
      0 ≤ x ∧
      ‖(1 / (n : ℂ)) * (X * Y * Z).trace‖ = x ^ 3 ∧
      (frobNormSq (X * Y)).re +
        (frobNormSq (Y * Z)).re +
        (frobNormSq (Z * X)).re ≥ 3 * x ^ 4 ∧
      (0 < x →
        (frobNormSq (X * Y)).re +
          (frobNormSq (Y * Z)).re +
          (frobNormSq (Z * X)).re = 3 * x ^ 4 →
        X * X.conjTranspose =
          ((x ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
        Y * Y.conjTranspose =
          ((x ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
        Z * Z.conjTranspose =
          ((x ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
        X * Y * Z = ((1 / (n : ℂ)) * (X * Y * Z).trace) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  let t : ℂ := (1 / (n : ℂ)) * (X * Y * Z).trace
  obtain ⟨z, hzpow⟩ := IsAlgClosed.exists_pow_nat_eq t (show 0 < 3 by norm_num)
  by_cases ht : t = 0
  · refine ⟨0, le_rfl, ?_, ?_, ?_⟩
    · change ‖t‖ = (0 : ℝ) ^ 3
      rw [ht, norm_zero]
      norm_num
    · norm_num
      exact add_nonneg
        (add_nonneg (frobNormSq_nonneg _) (frobNormSq_nonneg _))
        (frobNormSq_nonneg _)
    · norm_num
  · have hz : z ≠ 0 := by
      intro hz0
      rw [hz0, zero_pow (show 3 ≠ 0 by norm_num)] at hzpow
      exact ht hzpow.symm
    let x : ℝ := ‖z‖
    have hx : 0 < x := norm_pos_iff.mpr hz
    refine ⟨x, hx.le, ?_, ?_, ?_⟩
    · dsimp only [x]
      change ‖t‖ = ‖z‖ ^ 3
      rw [← hzpow, norm_pow]
    · let X' := z⁻¹ • X
      let Y' := z⁻¹ • Y
      let Z' := z⁻¹ • Z
      have htrace : (1 / (n : ℂ)) * (X' * Y' * Z').trace = 1 := by
        dsimp only [X', Y', Z']
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          Matrix.trace_smul, smul_eq_mul]
        calc
          1 / (n : ℂ) * (z⁻¹ * (z⁻¹ * z⁻¹) * (X * Y * Z).trace) =
              (z⁻¹ ^ 3) * t := by simp only [t]; ring
          _ = z⁻¹ ^ 3 * z ^ 3 := by rw [hzpow]
          _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
      have hscaled := matrix_amgm_at_one X' Y' Z' htrace
      dsimp only [X', Y', Z'] at hscaled
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul] at hscaled
      rw [frobNormSq_inv_cube_root_pair_re,
        frobNormSq_inv_cube_root_pair_re,
        frobNormSq_inv_cube_root_pair_re] at hscaled
      dsimp only [x]
      field_simp at hscaled
      nlinarith
    · intro _ heq
      let X' := z⁻¹ • X
      let Y' := z⁻¹ • Y
      let Z' := z⁻¹ • Z
      have htrace : (1 / (n : ℂ)) * (X' * Y' * Z').trace = 1 := by
        dsimp only [X', Y', Z']
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          Matrix.trace_smul, smul_eq_mul]
        calc
          1 / (n : ℂ) * (z⁻¹ * (z⁻¹ * z⁻¹) * (X * Y * Z).trace) =
              (z⁻¹ ^ 3) * t := by simp only [t]; ring
          _ = z⁻¹ ^ 3 * z ^ 3 := by rw [hzpow]
          _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
      have hscaledEq :
          (frobNormSq (X' * Y')).re +
            (frobNormSq (Y' * Z')).re +
            (frobNormSq (Z' * X')).re = 3 := by
        dsimp only [X', Y', Z']
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [frobNormSq_inv_cube_root_pair_re,
          frobNormSq_inv_cube_root_pair_re,
          frobNormSq_inv_cube_root_pair_re]
        dsimp only [x] at heq
        field_simp
        nlinarith
      obtain ⟨hX', hY', hZ', hXYZ'⟩ :=
        matrix_amgm_at_one_equality X' Y' Z' htrace hscaledEq
      have hcoef : (z ^ 3) * (z⁻¹ * (z⁻¹ * z⁻¹)) = 1 := by
        calc
          (z ^ 3) * (z⁻¹ * (z⁻¹ * z⁻¹)) = (z * z⁻¹) ^ 3 := by ring
          _ = 1 ^ 3 := by rw [mul_inv_cancel₀ hz]
          _ = 1 := by ring
      have hXYZ_prod : X * Y * Z = t • (1 : Matrix (Fin n) (Fin n) ℂ) := by
        calc
          X * Y * Z = (1 : ℂ) • (X * Y * Z) := by rw [one_smul]
          _ = ((z ^ 3) * (z⁻¹ * (z⁻¹ * z⁻¹))) • (X * Y * Z) := by rw [hcoef]
          _ = (z ^ 3) • ((z⁻¹ * (z⁻¹ * z⁻¹)) • (X * Y * Z)) := by rw [← smul_smul]
          _ = (z ^ 3) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
            have hsmul_assoc : ((z⁻¹ * (z⁻¹ * z⁻¹)) • (X * Y * Z)) =
                (z⁻¹ • X) * (z⁻¹ • Y) * (z⁻¹ • Z) := by
              simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
            rw [hsmul_assoc, hXYZ']
          _ = t • (1 : Matrix (Fin n) (Fin n) ℂ) := by rw [hzpow]
      dsimp only [x]
      exact ⟨gram_eq_norm_sq_of_inv_smul_unitary z hz X hX',
        gram_eq_norm_sq_of_inv_smul_unitary z hz Y hY',
        gram_eq_norm_sq_of_inv_smul_unitary z hz Z hZ',
        hXYZ_prod⟩

/-! ## Arbitrary complex trace equality -/

private theorem amplitude_rpow_eq (x : ℝ) (hx : 0 ≤ x) :
    (x ^ 3) ^ (4 / 3 : ℝ) = x ^ 4 ∧
    (x ^ 3) ^ (2 / 3 : ℝ) = x ^ 2 := by
  constructor
  · rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
    norm_num
  · rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
    norm_num

private theorem frobNormSq_eq_of_scaled_gram
    (M : Matrix (Fin n) (Fin n) ℂ) (κ : ℂ)
    (hM : M * M.conjTranspose = κ • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    frobNormSq M = κ := by
  unfold frobNormSq frobInner
  rw [Matrix.trace_mul_comm, hM]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  field_simp
  change κ * (n : ℂ) = (n : ℂ) * κ
  ring

omit [NeZero n] in
private theorem mul_scaled_gram
    (X Y : Matrix (Fin n) (Fin n) ℂ) (κ : ℂ)
    (hX : X * X.conjTranspose = κ • (1 : Matrix (Fin n) (Fin n) ℂ))
    (hY : Y * Y.conjTranspose = κ • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    (X * Y) * (X * Y).conjTranspose =
      (κ * κ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Y Y.conjTranspose X.conjTranspose, hY]
  simp [hX, smul_smul]

/-- The cyclic normalized Frobenius sum vanishes exactly when all three
    pairwise products vanish. This is the zero-trace equality branch. -/
theorem matrix_amgm_zero_equality_iff
    (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    (frobNormSq (X * Y)).re + (frobNormSq (Y * Z)).re +
        (frobNormSq (Z * X)).re = 0 ↔
      X * Y = 0 ∧ Y * Z = 0 ∧ Z * X = 0 := by
  constructor
  · intro heq
    have hXY := frobNormSq_nonneg (X * Y)
    have hYZ := frobNormSq_nonneg (Y * Z)
    have hZX := frobNormSq_nonneg (Z * X)
    have hzero : ∀ M : Matrix (Fin n) (Fin n) ℂ,
        (frobNormSq M).re = 0 → M = 0 := by
      intro M hM
      apply (frobNormSq_eq_zero_iff M).mp
      exact Complex.ext hM (frobNormSq_real M)
    exact ⟨hzero _ (by linarith), hzero _ (by linarith), hzero _ (by linarith)⟩
  · rintro ⟨hXY, hYZ, hZX⟩
    simp [hXY, hYZ, hZX, frobNormSq_zero]

private theorem cyclic_frobNormSq_eq_of_common_scaled_gram
    (X Y Z : Matrix (Fin n) (Fin n) ℂ) (κ : ℝ)
    (hX : X * X.conjTranspose = (κ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
    (hY : Y * Y.conjTranspose = (κ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
    (hZ : Z * Z.conjTranspose = (κ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    (frobNormSq (X * Y)).re + (frobNormSq (Y * Z)).re +
      (frobNormSq (Z * X)).re = 3 * κ ^ 2 := by
  rw [frobNormSq_eq_of_scaled_gram _ _ (mul_scaled_gram X Y _ hX hY),
    frobNormSq_eq_of_scaled_gram _ _ (mul_scaled_gram Y Z _ hY hZ),
    frobNormSq_eq_of_scaled_gram _ _ (mul_scaled_gram Z X _ hZ hX)]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- At nonzero normalized trace `t`, AM-GM equality forces common Gram scale
    `‖t‖^(2/3)` and the exact operator product `XYZ = t I`. -/
theorem matrix_amgm_nonzero_equality
    (X Y Z : Matrix (Fin n) (Fin n) ℂ)
    (ht : (1 / (n : ℂ)) * (X * Y * Z).trace ≠ 0)
    (heq : (frobNormSq (X * Y)).re + (frobNormSq (Y * Z)).re +
      (frobNormSq (Z * X)).re =
        3 * ‖(1 / (n : ℂ)) * (X * Y * Z).trace‖ ^ (4 / 3 : ℝ)) :
    let t := (1 / (n : ℂ)) * (X * Y * Z).trace
    X * X.conjTranspose = ((‖t‖ ^ (2 / 3 : ℝ) : ℝ) : ℂ) • 1 ∧
    Y * Y.conjTranspose = ((‖t‖ ^ (2 / 3 : ℝ) : ℝ) : ℂ) • 1 ∧
    Z * Z.conjTranspose = ((‖t‖ ^ (2 / 3 : ℝ) : ℝ) : ℂ) • 1 ∧
    X * Y * Z = t • 1 := by
  dsimp only
  obtain ⟨x, hx, hnorm, _, hrigid⟩ := matrix_amgm_amplitude_witness X Y Z
  have hxpos : 0 < x := by
    by_contra hnot
    have hxzero : x = 0 := le_antisymm (le_of_not_gt hnot) hx
    have htzero : ‖(1 / (n : ℂ)) * (X * Y * Z).trace‖ = 0 := by
      simpa [hxzero] using hnorm
    exact ht (norm_eq_zero.mp htzero)
  obtain ⟨hfour, htwo⟩ := amplitude_rpow_eq x hx
  rw [hnorm, hfour] at heq
  obtain ⟨hX, hY, hZ, hXYZ⟩ := hrigid hxpos heq
  simpa only [hnorm, htwo] using And.intro hX (And.intro hY (And.intro hZ hXYZ))

/-- Equality in Matrix AM-GM at arbitrary complex normalized trace `t`.
    At zero trace all pairwise products vanish; at nonzero trace the factors
    share Gram scale `‖t‖^(2/3)` and their product is exactly `t I`. -/
theorem matrix_amgm_general_equality_iff
    (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    let t := (1 / (n : ℂ)) * (X * Y * Z).trace
    (frobNormSq (X * Y)).re + (frobNormSq (Y * Z)).re +
        (frobNormSq (Z * X)).re = 3 * ‖t‖ ^ (4 / 3 : ℝ) ↔
      (t = 0 ∧ X * Y = 0 ∧ Y * Z = 0 ∧ Z * X = 0) ∨
      (t ≠ 0 ∧
        X * X.conjTranspose = ((‖t‖ ^ (2 / 3 : ℝ) : ℝ) : ℂ) • 1 ∧
        Y * Y.conjTranspose = ((‖t‖ ^ (2 / 3 : ℝ) : ℝ) : ℂ) • 1 ∧
        Z * Z.conjTranspose = ((‖t‖ ^ (2 / 3 : ℝ) : ℝ) : ℂ) • 1 ∧
        X * Y * Z = t • 1) := by
  dsimp only
  let t := (1 / (n : ℂ)) * (X * Y * Z).trace
  constructor
  · intro heq
    by_cases ht : t = 0
    · left
      refine ⟨ht, (matrix_amgm_zero_equality_iff X Y Z).mp ?_⟩
      simpa only [show (1 / (n : ℂ)) * (X * Y * Z).trace = 0 from ht,
        norm_zero, Real.zero_rpow (by norm_num : (4 / 3 : ℝ) ≠ 0), mul_zero]
        using heq
    · exact Or.inr ⟨ht, matrix_amgm_nonzero_equality X Y Z ht heq⟩
  · rintro (⟨ht, hXY, hYZ, hZX⟩ | ⟨_, hX, hY, hZ, _⟩)
    · rw [(matrix_amgm_zero_equality_iff X Y Z).mpr ⟨hXY, hYZ, hZX⟩, ht]
      norm_num
    · have hsum := cyclic_frobNormSq_eq_of_common_scaled_gram X Y Z
        (‖t‖ ^ (2 / 3 : ℝ)) hX hY hZ
      rw [hsum, ← Real.rpow_mul_natCast (norm_nonneg t)]
      rw [show (2 / 3 : ℝ) * (2 : ℕ) = 4 / 3 by norm_num]

/-! ## Manuscript Matrix AM-GM -/

/-- **Matrix AM-GM** of the manuscript at the unit-normalised-trace
    case: `‖XY‖² + ‖YZ‖² + ‖ZX‖² ≥ 3` whenever `tr(XYZ) = 1`. -/
theorem matrix_amgm
    (X Y Z : Matrix (Fin n) (Fin n) ℂ)
    (h : (1 / (n : ℂ)) * (X * Y * Z).trace = 1) :
    (frobNormSq (X * Y)).re +
    (frobNormSq (Y * Z)).re +
    (frobNormSq (Z * X)).re ≥ 3 :=
  matrix_amgm_at_one X Y Z h

/-- **Matrix AM-GM equality side.** Equality in the matrix AM-GM at unit normalised
    trace forces `X, Y, Z` to be unitary and `XYZ = I`. -/
theorem matrix_amgm_equality
    (X Y Z : Matrix (Fin n) (Fin n) ℂ)
    (h : (1 / (n : ℂ)) * (X * Y * Z).trace = 1)
    (heq : (frobNormSq (X * Y)).re +
           (frobNormSq (Y * Z)).re +
           (frobNormSq (Z * X)).re = 3) :
    X * X.conjTranspose = 1 ∧
    Y * Y.conjTranspose = 1 ∧
    Z * Z.conjTranspose = 1 ∧
    X * Y * Z = 1 :=
  matrix_amgm_at_one_equality X Y Z h heq

end
