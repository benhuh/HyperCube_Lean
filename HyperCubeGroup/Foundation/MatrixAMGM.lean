/-
  HyperCubeGroup.Foundation.MatrixAMGM

  The Matrix AM-GM inequality,
  for arbitrary complex trace, with rigidity specialised to `tr(XYZ) = 1`.
  This is the irreducible
  "textbook input" from which the unconditional lower bound
  `ℋ(Θ) ≥ 3n²` and its equality rigidity follow on any quasigroup.

  Status:

    * `matrix_amgm_general`        — arbitrary-amplitude bound, including zero trace.
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
