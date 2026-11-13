import HyperCubeGroup.Foundation.GroupIsotope
import HyperCubeGroup.Foundation.Tikhonov

noncomputable section

namespace PositiveGap

open scoped Topology BigOperators

/-! ## Real feasible objective values -/

/-- Real objective values attained by exact factorizations of the operation. -/
def feasibleObjectiveValues {n : ℕ} [NeZero n] (f : BinOp n) : Set ℝ :=
  {value | ∃ Θ : HCParams n, Factorizes Θ f ∧ (objective Θ f).re = value}

/-- The explicit matrix-unit factorization gives a feasible objective value
for every binary operation of positive order. -/
theorem feasibleObjectiveValues_nonempty {n : ℕ} [NeZero n] (f : BinOp n) :
    (feasibleObjectiveValues f).Nonempty := by
  obtain ⟨Θ, hfeas⟩ := feasible_nonempty f
  exact ⟨(objective Θ f).re, Θ, hfeas, rfl⟩

/-- The universal floor is a lower bound for all feasible objective values. -/
theorem feasibleObjectiveValues_bddBelow {n : ℕ} [NeZero n] (f : BinOp n) :
    BddBelow (feasibleObjectiveValues f) := by
  refine ⟨3 * (n : ℝ) ^ 2, ?_⟩
  rintro value ⟨Θ, hfeas, rfl⟩
  exact universal_lower_bound_general f Θ hfeas

/-! ## Normalization of unused output slices -/

/-- Keep supported output slices and zero every output outside the operation's range. -/
def zeroUnusedOutputs {n : ℕ} (Θ : HCParams n) (f : BinOp n) : HCParams n := by
  classical
  exact ⟨Θ.A, Θ.B, fun c => if ∃ a b, f.op a b = c then Θ.C c else 0⟩

/-- Normalization leaves every supported output slice unchanged. -/
theorem zeroUnusedOutputs_C_supported {n : ℕ} (Θ : HCParams n) (f : BinOp n)
    (a b : Fin n) :
    (zeroUnusedOutputs Θ f).C (f.op a b) = Θ.C (f.op a b) := by
  classical
  simp [zeroUnusedOutputs, show ∃ a' b', f.op a' b' = f.op a b from ⟨a, b, rfl⟩]

/-- Zeroing unused outputs preserves factorization on all triples. -/
theorem factorizes_zeroUnusedOutputs {n : ℕ} (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) : Factorizes (zeroUnusedOutputs Θ f) f := by
  classical
  intro a b c
  by_cases hc : ∃ a' b', f.op a' b' = c
  · simpa [hcProduct, zeroUnusedOutputs, hc] using hfeas a b c
  · have hab : f.op a b ≠ c := fun heq => hc ⟨a, b, heq⟩
    simp [hcProduct, zeroUnusedOutputs, hc, structureTensor, hab]

/-- Zeroing unused outputs preserves the full support-weighted objective. -/
theorem objective_zeroUnusedOutputs {n : ℕ} (Θ : HCParams n) (f : BinOp n) :
    objective (zeroUnusedOutputs Θ f) f = objective Θ f := by
  classical
  simp only [objective_eq_sum_support, zeroUnusedOutputs_C_supported]
  rfl

/-! ## Squared-Frobenius formulation of spectral no-escape

The spectral argument uses the real-valued, unnormalised squared Frobenius
quantity `frobNormSq_F` throughout. This avoids selecting a matrix norm
instance or introducing square roots in the estimates.

`SpectralNoEscapeStatement` states the fixed-dimension result proved by
`spectral_no_escape` below. The proof derives boundedness from the cubic
trace constraint and the squared-matrix Frobenius limit.
-/

/-- The squared-Frobenius contract for a fixed positive matrix dimension.
The bound may depend on the sequence, including its finite initial segment. -/
private def SpectralNoEscapeStatement : Prop :=
  ∀ (N : ℕ), 0 < N →
    ∀ (M : ℕ → Matrix (Fin N) (Fin N) ℂ),
      (∀ k, (M k * M k * M k).trace = (N : ℂ)) →
      Filter.Tendsto (fun k => frobNormSq_F (M k * M k))
        Filter.atTop (𝓝 (N : ℝ)) →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ k, frobNormSq_F (M k) ≤ B

/-- A nonnegative squared-Frobenius bound is equivalent to an upper bound
on the corresponding real-valued range. This is the form used when negating
boundedness to construct a sequence with growing squared Frobenius values. -/
private theorem exists_frob_bound_iff_bddAbove
    {N : ℕ} (M : ℕ → Matrix (Fin N) (Fin N) ℂ) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ k, frobNormSq_F (M k) ≤ B) ↔
      BddAbove (Set.range (fun k => frobNormSq_F (M k))) := by
  constructor
  · rintro ⟨B, _, hB⟩
    refine ⟨B, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hB k
  · rintro ⟨B, hB⟩
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    intro k
    exact le_trans (hB (Set.mem_range_self k)) (le_max_right _ _)

/-! ## Algebraic helpers for spectral no-escape -/

/-- Each entry's squared complex norm is bounded by the unnormalised
squared Frobenius quantity of the full matrix. -/
private theorem entry_normSq_le_frobNormSq_F
    {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (i j : ι) :
    Complex.normSq (M i j) ≤ frobNormSq_F M := by
  classical
  unfold frobNormSq_F
  calc
    Complex.normSq (M i j) ≤ ∑ b : ι, Complex.normSq (M i b) :=
      Finset.single_le_sum (fun b _ => Complex.normSq_nonneg (M i b))
        (Finset.mem_univ j)
    _ ≤ ∑ a : ι, ∑ b : ι, Complex.normSq (M a b) :=
      Finset.single_le_sum
        (fun a _ => Finset.sum_nonneg
          (fun b _ => Complex.normSq_nonneg (M a b)))
        (Finset.mem_univ i)

/-- Unitary conjugation preserves the unnormalised squared Frobenius
quantity. The identity `U * U.conjTranspose = 1` suffices for this calculation. -/
private theorem frobNormSq_F_unitary_conj
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U M : Matrix ι ι ℂ) (hU : U * U.conjTranspose = 1) :
    frobNormSq_F (U.conjTranspose * M * U) = frobNormSq_F M := by
  rw [frobNormSq_F_unitary_mul_right (U.conjTranspose * M) U hU]
  have hUH : U.conjTranspose.conjTranspose * U.conjTranspose = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hU
  exact frobNormSq_F_unitary_mul_left U.conjTranspose M hUH

/-- The square-entry recurrence for an upper-triangular complex matrix.
The filtered sum retains exactly the entries of smaller positive separation
needed by the later bounded-superdiagonal induction. -/
private theorem upper_triangular_square_entry
    {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsUpperTriangular T) (i j : Fin N) (hij : i < j) :
    (T * T) i j =
      (T i i + T j j) * T i j +
        ∑ k ∈ Finset.univ.filter (fun k : Fin N => i < k ∧ k < j),
          T i k * T k j := by
  have hi_mem : i ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ i
  have hj_mem_erase : j ∈ (Finset.univ : Finset (Fin N)).erase i :=
    Finset.mem_erase.mpr ⟨(ne_of_lt hij).symm, Finset.mem_univ j⟩
  have hsplit_i : (∑ k : Fin N, T i k * T k j) =
      T i i * T i j + ∑ k ∈ Finset.univ.erase i, T i k * T k j := by
    rw [← Finset.add_sum_erase _ _ hi_mem]
  have hsplit_j : (∑ k ∈ Finset.univ.erase i, T i k * T k j) =
      T i j * T j j +
        ∑ k ∈ (Finset.univ.erase i).erase j, T i k * T k j := by
    rw [← Finset.add_sum_erase _ _ hj_mem_erase]
  have hmiddle :
      (∑ k ∈ (Finset.univ.erase i).erase j, T i k * T k j) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin N => i < k ∧ k < j),
          T i k * T k j := by
    symm
    apply Finset.sum_subset
    · intro k hk
      rcases (Finset.mem_filter.mp hk).2 with ⟨hik, hkj⟩
      exact Finset.mem_erase.mpr
        ⟨ne_of_lt hkj,
          Finset.mem_erase.mpr ⟨(ne_of_lt hik).symm, Finset.mem_univ k⟩⟩
    · intro k hk hk_not_between
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hki : k ≠ i :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      have hnot_between : ¬ (i < k ∧ k < j) := by
        intro hbetween
        exact hk_not_between (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hbetween⟩)
      rcases lt_trichotomy k i with hlt | heq | hik
      · rw [hT i k hlt, zero_mul]
      · exact False.elim (hki heq)
      · rcases lt_trichotomy k j with hlt | heq | hjk
        · exact False.elim (hnot_between ⟨hik, hlt⟩)
        · exact False.elim (hkj heq)
        · rw [hT k j hjk, mul_zero]
  rw [Matrix.mul_apply, hsplit_i, hsplit_j, hmiddle]
  ring

/-! ## Schur forms for a matrix sequence

Choose a Schur unitary separately at each index. No continuity or convergence
of these unitaries is asserted or needed: the later compactness argument
applies to the diagonal vectors `lam`.
-/

/-- Schur forms and their diagonal vectors for an arbitrary matrix sequence.
Besides both unitary identities, retain the Frobenius quantities of the
matrices and their squares, and express the cubic trace through the diagonal.
If the input cubic traces equal `N`, the last identity gives
`∑ i, (lam k i) ^ 3 = (N : ℂ)` by transitivity. -/
private theorem exists_schur_sequence
    {N : ℕ} (M : ℕ → Matrix (Fin N) (Fin N) ℂ) :
    ∃ (U T : ℕ → Matrix (Fin N) (Fin N) ℂ) (lam : ℕ → Fin N → ℂ),
      (∀ k, (U k).conjTranspose * U k = 1) ∧
      (∀ k, U k * (U k).conjTranspose = 1) ∧
      (∀ k, T k = (U k).conjTranspose * M k * U k) ∧
      (∀ k, IsUpperTriangular (T k)) ∧
      (∀ k i, lam k i = T k i i) ∧
      (∀ k, frobNormSq_F (T k) = frobNormSq_F (M k)) ∧
      (∀ k, frobNormSq_F (T k * T k) = frobNormSq_F (M k * M k)) ∧
      (∀ k, (∑ i : Fin N, (lam k i) ^ 3) = (M k * M k * M k).trace) := by
  classical
  choose U hU_left hU_right htri using
    (fun k : ℕ => matrix_unitary_schur_form (M k))
  let T : ℕ → Matrix (Fin N) (Fin N) ℂ :=
    fun k => (U k).conjTranspose * M k * U k
  let lam : ℕ → Fin N → ℂ := fun k i => T k i i
  refine ⟨U, T, lam, hU_left, hU_right, (fun _ => rfl), htri,
    (fun _ _ => rfl), ?_, ?_, ?_⟩
  · intro k
    exact frobNormSq_F_unitary_conj (U k) (M k) (hU_right k)
  · intro k
    exact frobNormSq_F_unitary_conj_sq
      (U := U k) (M := M k) (hU_left k) (hU_right k)
  · intro k
    calc
      (∑ i : Fin N, (lam k i) ^ 3) = (T k * T k * T k).trace :=
        (htri k).trace_mul_self_mul_self.symm
      _ = (M k * M k * M k).trace :=
        trace_unitary_conj_cb (U := U k) (M := M k) (hU_right k)

/-! ## Bounded Schur diagonals and subsequence extraction -/

/-- Convergence of the squared-matrix Frobenius quantities bounds every
diagonal entry of an upper-triangular sequence, including its initial terms.
The coarse bound `max 1 B` avoids taking fourth roots of a scalar bound `B`.
Neither a cubic-trace constraint nor boundedness of the matrices is needed. -/
private theorem exists_diagonal_bound_of_square_frob_tendsto
    {N : ℕ} (T : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (htri : ∀ k, IsUpperTriangular (T k)) {L : ℝ}
    (hconv : Filter.Tendsto (fun k => frobNormSq_F (T k * T k))
      Filter.atTop (𝓝 L)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k i, ‖T k i i‖ ≤ D := by
  classical
  obtain ⟨B, hB⟩ := hconv.bddAbove_range
  refine ⟨max 1 B, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro k i
  have hpow : ‖T k i i‖ ^ 4 ≤ B := by
    calc
      ‖T k i i‖ ^ 4 ≤ ∑ j : Fin N, ‖T k j j‖ ^ 4 :=
        Finset.single_le_sum
          (fun j _ => pow_nonneg (norm_nonneg (T k j j)) 4) (Finset.mem_univ i)
      _ ≤ frobNormSq_F (T k * T k) := (htri k).sum_norm_pow_four_le
      _ ≤ B := hB (Set.mem_range_self k)
  by_cases hsmall : ‖T k i i‖ ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  · have hlarge : 1 ≤ ‖T k i i‖ := le_of_lt (lt_of_not_ge hsmall)
    exact (le_self_pow₀ hlarge (by decide : 4 ≠ 0)).trans
      (hpow.trans (le_max_right _ _))

/-- A single strictly increasing subsequence makes all Schur diagonal
coordinates converge simultaneously. Compactness is applied only to the
diagonal vectors in `Fin N → ℂ`, whose bound was proved above.
The conclusion also retains that bound for the later entrywise induction. -/
private theorem exists_convergent_diagonal_subseq
    {N : ℕ} (T : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (htri : ∀ k, IsUpperTriangular (T k)) {L : ℝ}
    (hconv : Filter.Tendsto (fun k => frobNormSq_F (T k * T k))
      Filter.atTop (𝓝 L)) :
    ∃ D : ℝ, 0 ≤ D ∧ (∀ k i, ‖T k i i‖ ≤ D) ∧
      ∃ (zeta : Fin N → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
        Filter.Tendsto (fun k i => T (φ k) i i) Filter.atTop (𝓝 zeta) ∧
        (∀ i, Filter.Tendsto (fun k => T (φ k) i i)
          Filter.atTop (𝓝 (zeta i))) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_diagonal_bound_of_square_frob_tendsto T htri hconv
  let diag : ℕ → Fin N → ℂ := fun k i => T k i i
  have hmem : ∀ k, diag k ∈ Metric.closedBall (0 : Fin N → ℂ) D := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hD).2 (hbound k)
  obtain ⟨zeta, _, φ, hφ, hdiag⟩ :=
    (isCompact_closedBall (0 : Fin N → ℂ) D).tendsto_subseq hmem
  exact ⟨D, hD, hbound, zeta, φ, hφ, hdiag, tendsto_pi_nhds.mp hdiag⟩

/-! ## Rigidity of limiting diagonal entries -/

/-- Scalar rigidity at the normalized cubic-trace floor. The inequalities
`N^4 ≤ (∑ ‖z_i‖^3)^4 ≤ N * (∑ ‖z_i‖^4)^3 ≤ N^4` force equality.
The power-mean equality case makes the moduli constant, and equality in
the triangle inequality makes every cube a nonnegative real of norm one. -/
private theorem cube_eq_one_of_sum_cube_eq_of_sum_norm_four_le
    {N : ℕ} (hN : 0 < N) (z : Fin N → ℂ)
    (hsum : (∑ i : Fin N, z i ^ 3) = (N : ℂ))
    (hfour : (∑ i : Fin N, ‖z i‖ ^ 4) ≤ (N : ℝ)) :
    ∀ i, z i ^ 3 = 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNnonneg : (0 : ℝ) ≤ N := le_of_lt hNpos
  have hfour_nonneg : 0 ≤ ∑ i : Fin N, ‖z i‖ ^ 4 :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg (z i)) 4)
  have hthree_lower : (N : ℝ) ≤ ∑ i : Fin N, ‖z i‖ ^ 3 := by
    calc
      (N : ℝ) = ‖∑ i : Fin N, z i ^ 3‖ := by rw [hsum]; simp
      _ ≤ ∑ i : Fin N, ‖z i ^ 3‖ := norm_sum_le _ _
      _ = ∑ i : Fin N, ‖z i‖ ^ 3 := by simp only [norm_pow]
  have hmean : (∑ i : Fin N, ‖z i‖ ^ 3) ^ 4 ≤
      (N : ℝ) * (∑ i : Fin N, ‖z i‖ ^ 4) ^ 3 := by
    simpa only [Fintype.card_fin] using
      (Real.sum_pow_three_pow_four_le (fun i : Fin N => ‖z i‖)
        (fun i => norm_nonneg (z i)))
  have hupper : (N : ℝ) * (∑ i : Fin N, ‖z i‖ ^ 4) ^ 3 ≤ (N : ℝ) ^ 4 := by
    calc
      (N : ℝ) * (∑ i : Fin N, ‖z i‖ ^ 4) ^ 3 ≤ (N : ℝ) * (N : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hfour_nonneg hfour 3) hNnonneg
      _ = (N : ℝ) ^ 4 := by ring
  have hlower : (N : ℝ) ^ 4 ≤ (∑ i : Fin N, ‖z i‖ ^ 3) ^ 4 :=
    pow_le_pow_left₀ hNnonneg hthree_lower 4
  have hmean_eq : (∑ i : Fin N, ‖z i‖ ^ 3) ^ 4 =
      (N : ℝ) * (∑ i : Fin N, ‖z i‖ ^ 4) ^ 3 :=
    le_antisymm hmean (hupper.trans hlower)
  have hthree_eq : (∑ i : Fin N, ‖z i‖ ^ 3) = (N : ℝ) := by
    refine le_antisymm ?_ hthree_lower
    by_contra hnot
    have hlt : (N : ℝ) < ∑ i : Fin N, ‖z i‖ ^ 3 := lt_of_not_ge hnot
    have hpow := pow_lt_pow_left₀ hlt hNnonneg (by decide : 4 ≠ 0)
    exact (not_lt_of_ge (hmean.trans hupper)) hpow
  have hnorm_const : ∀ i j : Fin N, ‖z i‖ = ‖z j‖ := by
    apply Real.sum_pow_three_pow_four_eq_imp (fun i : Fin N => ‖z i‖)
      (fun i => norm_nonneg (z i))
    · simpa only [Fintype.card_fin] using hN
    · simpa only [Fintype.card_fin] using hmean_eq
  have hcube_norm : ∀ i : Fin N, ‖z i ^ 3‖ = 1 := by
    intro i
    have hsame : ∀ j : Fin N, ‖z j‖ = ‖z i‖ := fun j => hnorm_const j i
    have htotal : (N : ℝ) * ‖z i‖ ^ 3 = (N : ℝ) := by
      simpa only [hsame, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] using hthree_eq
    rw [norm_pow]
    apply mul_left_cancel₀ (ne_of_gt hNpos)
    simpa only [mul_one] using htotal
  have htriangle : (∑ i : Fin N, ‖z i ^ 3‖) = (∑ i : Fin N, z i ^ 3).re := by
    simpa [norm_pow, hsum] using hthree_eq
  have hreal := norm_sum_eq_re_sum_imp_each_nonneg_real
    (fun i : Fin N => z i ^ 3) htriangle
  intro i
  have habs : |(z i ^ 3).re| = 1 :=
    (Complex.abs_re_eq_norm.mpr (hreal i).1).trans (hcube_norm i)
  have hre : (z i ^ 3).re = 1 := by
    rwa [abs_of_nonneg (hreal i).2] at habs
  apply Complex.ext
  · simpa using hre
  · simpa using (hreal i).1

/-- Apply scalar rigidity to any convergent diagonal subsequence from step 4.
Finite sums commute with these limits, and strict monotonicity preserves the
limit of the squared-matrix Frobenius quantities. No convergence or bound
for the full matrices is assumed. -/
private theorem diagonal_subseq_limit_cube_eq_one
    {N : ℕ} (hN : 0 < N) (T : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (htri : ∀ k, IsUpperTriangular (T k))
    (htrace : ∀ k, (T k * T k * T k).trace = (N : ℂ))
    (hconv : Filter.Tendsto (fun k => frobNormSq_F (T k * T k))
      Filter.atTop (𝓝 (N : ℝ)))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {zeta : Fin N → ℂ}
    (hdiag : ∀ i, Filter.Tendsto (fun k => T (φ k) i i)
      Filter.atTop (𝓝 (zeta i))) :
    ∀ i, zeta i ^ 3 = 1 := by
  have hcubes : ∀ k, (∑ i : Fin N, (T (φ k) i i) ^ 3) = (N : ℂ) :=
    fun k => (htri (φ k)).trace_mul_self_mul_self.symm.trans (htrace (φ k))
  have hsum_conv : Filter.Tendsto (fun k => ∑ i : Fin N, (T (φ k) i i) ^ 3)
      Filter.atTop (𝓝 (∑ i : Fin N, zeta i ^ 3)) :=
    tendsto_finset_sum _ (fun i _ => (hdiag i).pow 3)
  have hsum : (∑ i : Fin N, zeta i ^ 3) = (N : ℂ) := by
    have hconst : Filter.Tendsto (fun k => ∑ i : Fin N, (T (φ k) i i) ^ 3)
        Filter.atTop (𝓝 (N : ℂ)) := by
      simp_rw [hcubes]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hsum_conv hconst
  have hfour_conv : Filter.Tendsto (fun k => ∑ i : Fin N, ‖T (φ k) i i‖ ^ 4)
      Filter.atTop (𝓝 (∑ i : Fin N, ‖zeta i‖ ^ 4)) :=
    tendsto_finset_sum _ (fun i _ => (hdiag i).norm.pow 4)
  have hfour : (∑ i : Fin N, ‖zeta i‖ ^ 4) ≤ (N : ℝ) :=
    le_of_tendsto_of_tendsto' hfour_conv (hconv.comp hφ.tendsto_atTop)
      (fun k => (htri (φ k)).sum_norm_pow_four_le)
  exact cube_eq_one_of_sum_cube_eq_of_sum_norm_four_le hN zeta hsum hfour

/-! ## Uniform lower bounds for diagonal pair sums -/

/-- If a finite vector sequence converges coordinatewise to cube roots of
unity, all pair sums are eventually bounded below by a single positive
constant. Choose half the minimum limiting pair-sum norm; finiteness lets
the separate eventual bounds hold simultaneously for every pair. -/
private theorem exists_eventually_pair_sum_lower_bound
    {N : ℕ} (hN : 0 < N) (lam : ℕ → Fin N → ℂ) (zeta : Fin N → ℂ)
    (hlim : ∀ i, Filter.Tendsto (fun k => lam k i) Filter.atTop (𝓝 (zeta i)))
    (hcube : ∀ i, zeta i ^ 3 = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in Filter.atTop, ∀ i j : Fin N, c ≤ ‖lam k i + lam k j‖ := by
  classical
  have hpairs : (Finset.univ : Finset (Fin N × Fin N)).Nonempty :=
    ⟨(⟨0, hN⟩, ⟨0, hN⟩), Finset.mem_univ _⟩
  obtain ⟨p, _, hp⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin N × Fin N))
    (fun p => ‖zeta p.1 + zeta p.2‖) hpairs
  have hp_pos : 0 < ‖zeta p.1 + zeta p.2‖ :=
    norm_pos_iff.mpr (cube_root_one_add_ne_zero (hcube p.1) (hcube p.2))
  refine ⟨‖zeta p.1 + zeta p.2‖ / 2, half_pos hp_pos, ?_⟩
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  have hmargin : ‖zeta p.1 + zeta p.2‖ / 2 < ‖zeta i + zeta j‖ :=
    (half_lt_self hp_pos).trans_le (hp (i, j) (Finset.mem_univ _))
  have hsum : Filter.Tendsto (fun k => ‖lam k i + lam k j‖)
      Filter.atTop (𝓝 ‖zeta i + zeta j‖) :=
    ((hlim i).add (hlim j)).norm
  exact hsum.eventually (eventually_ge_nhds hmargin)

/-- The denominator bound needed by the superdiagonal induction, on the
subsequence extracted in step 4. Step 5 supplies the limiting cube roots.
Both the positive constant and the tail index are shared by all index pairs;
the tail index refers to the subsequence parameter `k`. -/
private theorem exists_diagonal_subseq_pair_sum_lower_bound
    {N : ℕ} (hN : 0 < N) (T : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (htri : ∀ k, IsUpperTriangular (T k))
    (htrace : ∀ k, (T k * T k * T k).trace = (N : ℂ))
    (hconv : Filter.Tendsto (fun k => frobNormSq_F (T k * T k))
      Filter.atTop (𝓝 (N : ℝ)))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {zeta : Fin N → ℂ}
    (hdiag : ∀ i, Filter.Tendsto (fun k => T (φ k) i i)
      Filter.atTop (𝓝 (zeta i))) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k ≥ K, ∀ i j : Fin N,
      c ≤ ‖T (φ k) i i + T (φ k) j j‖ := by
  have hcube := diagonal_subseq_limit_cube_eq_one hN T htri htrace hconv hφ hdiag
  obtain ⟨c, hc, hbound⟩ := exists_eventually_pair_sum_lower_bound hN
    (fun k i => T (φ k) i i) zeta hdiag hcube
  exact ⟨c, hc, Filter.eventually_atTop.mp hbound⟩

/-! ## Bounds for the triangular entries (step 7) -/

/-- A coarse entry-norm bound from a squared Frobenius bound, avoiding
square roots. This will be applied to the squares of the Schur forms. -/
private theorem entry_norm_le_max_of_frob_bound
    {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) {P : ℝ}
    (hP : frobNormSq_F M ≤ P) (i j : Fin N) : ‖M i j‖ ≤ max 1 P := by
  have hsq : ‖M i j‖ ^ 2 ≤ P := by
    rw [← Complex.normSq_eq_norm_sq]
    exact (entry_normSq_le_frobNormSq_F M i j).trans hP
  by_cases hsmall : ‖M i j‖ ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  · have hlarge : 1 ≤ ‖M i j‖ := le_of_lt (lt_of_not_ge hsmall)
    exact (le_self_pow₀ hlarge (by decide : 2 ≠ 0)).trans
      (hsq.trans (le_max_right _ _))

/-- Uniform bounds on the diagonal, the square, and the inverse diagonal
pair sums give a bound on every triangular entry on the same tail.
Induction on the separation uses the bound
`max B ((P + N * B^2) / c)` at each successor step. -/
private theorem exists_upper_triangular_entry_tail_bound
    {N : ℕ} (T : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (htri : ∀ k, IsUpperTriangular (T k))
    {D P c : ℝ} (hD : 0 ≤ D) (hc : 0 < c) (K : ℕ)
    (hdiag : ∀ k i, ‖T k i i‖ ≤ D)
    (hsquare : ∀ k i j, ‖(T k * T k) i j‖ ≤ P)
    (hsep : ∀ k ≥ K, ∀ i j, c ≤ ‖T k i i + T k j j‖) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ≥ K, ∀ i j, ‖T k i j‖ ≤ B := by
  classical
  have hband : ∀ d : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ k ≥ K, ∀ i j : Fin N, j.val - i.val ≤ d → ‖T k i j‖ ≤ B := by
    intro d
    induction d with
    | zero =>
      refine ⟨D, hD, ?_⟩
      intro k _ i j hdist
      rcases lt_trichotomy i j with hij | hij | hji
      · have : i.val < j.val := hij
        omega
      · subst j
        exact hdiag k i
      · rw [htri k i j hji, norm_zero]
        exact hD
    | succ d ih =>
      obtain ⟨B, hB, hentry⟩ := ih
      refine ⟨max B ((P + (N : ℝ) * B ^ 2) / c),
        hB.trans (le_max_left _ _), ?_⟩
      intro k hk i j hdist
      by_cases hprev : j.val - i.val ≤ d
      · exact (hentry k hk i j hprev).trans (le_max_left _ _)
      have hij : i < j := by
        change i.val < j.val
        omega
      have hmiddle :
          ‖∑ l ∈ Finset.univ.filter (fun l : Fin N => i < l ∧ l < j),
            T k i l * T k l j‖ ≤ (N : ℝ) * B ^ 2 := by
        calc
          ‖∑ l ∈ Finset.univ.filter (fun l : Fin N => i < l ∧ l < j),
              T k i l * T k l j‖
              ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin N => i < l ∧ l < j),
                ‖T k i l * T k l j‖ := norm_sum_le _ _
          _ ≤ ∑ _l ∈ Finset.univ.filter (fun l : Fin N => i < l ∧ l < j), B ^ 2 := by
            apply Finset.sum_le_sum
            intro l hl
            obtain ⟨hil, hlj⟩ := (Finset.mem_filter.mp hl).2
            have hil' : i.val < l.val := hil
            have hlj' : l.val < j.val := hlj
            have hleft := hentry k hk i l (by omega)
            have hright := hentry k hk l j (by omega)
            rw [norm_mul, pow_two]
            exact mul_le_mul hleft hright (norm_nonneg _) hB
          _ ≤ ∑ _l : Fin N, B ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => sq_nonneg B)
          _ = (N : ℝ) * B ^ 2 := by simp
      have hidentity : (T k i i + T k j j) * T k i j =
          (T k * T k) i j -
            ∑ l ∈ Finset.univ.filter (fun l : Fin N => i < l ∧ l < j),
              T k i l * T k l j := by
        rw [upper_triangular_square_entry (htri k) i j hij]
        ring
      have hproduct : ‖T k i i + T k j j‖ * ‖T k i j‖ ≤ P + (N : ℝ) * B ^ 2 := by
        calc
          ‖T k i i + T k j j‖ * ‖T k i j‖ = ‖(T k i i + T k j j) * T k i j‖ :=
            (norm_mul _ _).symm
          _ = ‖(T k * T k) i j -
              ∑ l ∈ Finset.univ.filter (fun l : Fin N => i < l ∧ l < j),
                T k i l * T k l j‖ := congrArg norm hidentity
          _ ≤ ‖(T k * T k) i j‖ +
              ‖∑ l ∈ Finset.univ.filter (fun l : Fin N => i < l ∧ l < j),
                T k i l * T k l j‖ := norm_sub_le _ _
          _ ≤ P + (N : ℝ) * B ^ 2 := add_le_add (hsquare k i j) hmiddle
      have hscaled : c * ‖T k i j‖ ≤ P + (N : ℝ) * B ^ 2 :=
        (mul_le_mul_of_nonneg_right (hsep k hk i j) (norm_nonneg _)).trans hproduct
      exact ((le_div_iff₀' hc).mpr hscaled).trans (le_max_right _ _)
  obtain ⟨B, hB, hentry⟩ := hband N
  refine ⟨B, hB, ?_⟩
  intro k hk i j
  exact hentry k hk i j (by have := j.isLt; omega)

/-- Entrywise bounds yield an unnormalised squared Frobenius bound. -/
private theorem frobNormSq_F_le_of_entry_bound
    {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) {B : ℝ}
    (hentry : ∀ i j, ‖M i j‖ ≤ B) :
    frobNormSq_F M ≤ (N : ℝ) ^ 2 * B ^ 2 := by
  calc
    frobNormSq_F M = ∑ i : Fin N, ∑ j : Fin N, ‖M i j‖ ^ 2 := by
      simp only [frobNormSq_F, Complex.normSq_eq_norm_sq]
    _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
    _ = (N : ℝ) ^ 2 * B ^ 2 := by simp; ring

/-! ## Spectral no-escape (step 8) -/

/-- An unbounded real sequence has a strictly increasing subsequence whose
values exceed its natural-number index. Eventual upper bounds would bound
the whole sequence, since the omitted initial segment is finite. -/
private theorem exists_strictMono_growth_of_not_bddAbove
    (u : ℕ → ℝ) (hu : ¬ BddAbove (Set.range u)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ k : ℕ, (k : ℝ) < u (ψ k) := by
  apply Filter.extraction_forall_of_frequently (P := fun n j => (n : ℝ) < u j)
  intro k
  by_contra hnot
  have htail : ∀ᶠ j in Filter.atTop, u j ≤ (k : ℝ) := by
    simpa only [Filter.not_frequently, not_lt] using hnot
  exact hu (Filter.isBoundedUnder_of_eventually_le htail).bddAbove_range

/-- Spectral no-escape in a fixed positive dimension, with no boundedness
assumption. First select a subsequence with growing squared Frobenius values.
Extract convergent Schur diagonals, bound all triangular entries on a further
subsequence, and transfer the resulting bound back by unitary invariance.
This contradicts growth, which persists along every increasing subsequence. -/
private theorem spectral_no_escape : SpectralNoEscapeStatement := by
  intro N hN M htrace hconv
  apply (exists_frob_bound_iff_bddAbove M).2
  by_contra hunbounded
  obtain ⟨ψ, hψ, hgrow⟩ := exists_strictMono_growth_of_not_bddAbove
    (fun k => frobNormSq_F (M k)) hunbounded
  obtain ⟨U, T, _, _, hU_right, hT, htri, _, hQ, hQsq, _⟩ :=
    exists_schur_sequence (fun k => M (ψ k))
  have hTconv : Filter.Tendsto (fun k => frobNormSq_F (T k * T k))
      Filter.atTop (𝓝 (N : ℝ)) := by
    simpa only [hQsq] using (hconv.comp hψ.tendsto_atTop)
  have hTtrace : ∀ k, (T k * T k * T k).trace = (N : ℂ) := by
    intro k
    rw [hT k]
    exact (trace_unitary_conj_cb (U := U k) (M := M (ψ k)) (hU_right k)).trans
      (htrace (ψ k))
  obtain ⟨D, hD, hdiag_bound, zeta, φ, hφ, _, hdiag_lim⟩ :=
    exists_convergent_diagonal_subseq T htri hTconv
  obtain ⟨c, hc, K, hsep⟩ :=
    exists_diagonal_subseq_pair_sum_lower_bound hN T htri hTtrace hTconv hφ hdiag_lim
  obtain ⟨P, hP⟩ := hTconv.bddAbove_range
  have hsquare : ∀ k i j, ‖(T (φ k) * T (φ k)) i j‖ ≤ max 1 P := by
    intro k i j
    exact entry_norm_le_max_of_frob_bound (T (φ k) * T (φ k))
      (hP (Set.mem_range_self (φ k))) i j
  obtain ⟨B, _, hentry⟩ := exists_upper_triangular_entry_tail_bound
    (fun k => T (φ k)) (fun k => htri (φ k)) hD hc K
    (fun k i => hdiag_bound (φ k) i) hsquare hsep
  have hfrob : ∀ k ≥ K, frobNormSq_F (T (φ k)) ≤ (N : ℝ) ^ 2 * B ^ 2 :=
    fun k hk => frobNormSq_F_le_of_entry_bound (T (φ k)) (hentry k hk)
  obtain ⟨r, hr⟩ := exists_nat_gt ((N : ℝ) ^ 2 * B ^ 2)
  let k := max K r
  have hkK : K ≤ k := le_max_left _ _
  have hkr : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_max_right K r)
  have hkφ : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast (hφ.id_le k)
  have hg : (φ k : ℝ) < frobNormSq_F (T (φ k)) := by
    rw [hQ (φ k)]
    exact hgrow (φ k)
  have hlarge : (N : ℝ) ^ 2 * B ^ 2 < frobNormSq_F (T (φ k)) :=
    hr.trans (lt_of_le_of_lt hkr (lt_of_le_of_lt hkφ hg))
  exact (not_lt_of_ge (hfrob k hkK)) hlarge

/-- The three nonzero blocks have disjoint support, so the unnormalized
squared Frobenius norm of the block-cyclic matrix is their sum. -/
private theorem frobNormSq_F_blockCyclicFin {n : ℕ}
    (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq_F (blockCyclicFin X Y Z) =
      frobNormSq_F X + frobNormSq_F Y + frobNormSq_F Z := by
  unfold blockCyclicFin
  rw [frobNormSq_F_submatrix_equiv]
  simp [frobNormSq_F, blockCyclic, Fintype.sum_prod_type, Fin.sum_univ_three]

/-- Specializing spectral no-escape to the block-cyclic sequence bounds the
sum of the three squared Frobenius norms. All norms here are unnormalized. -/
private theorem block_cyclic_no_escape {n : ℕ} (hn : 0 < n)
    (X Y Z : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (htrace : ∀ k, (X k * Y k * Z k).trace = (n : ℂ))
    (hconv : Filter.Tendsto (fun k =>
      frobNormSq_F (X k * Y k) + frobNormSq_F (Y k * Z k) +
        frobNormSq_F (Z k * X k)) Filter.atTop (𝓝 (3 * (n : ℝ)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k,
      frobNormSq_F (X k) + frobNormSq_F (Y k) + frobNormSq_F (Z k) ≤ B := by
  have hMtrace : ∀ k,
      (blockCyclicFin (X k) (Y k) (Z k) * blockCyclicFin (X k) (Y k) (Z k) *
        blockCyclicFin (X k) (Y k) (Z k)).trace = (3 * n : ℕ) := by
    intro k
    rw [trace_blockCyclicFin_cb, htrace k]
    norm_num
  have hMconv : Filter.Tendsto (fun k =>
      frobNormSq_F (blockCyclicFin (X k) (Y k) (Z k) *
        blockCyclicFin (X k) (Y k) (Z k))) Filter.atTop (𝓝 ((3 * n : ℕ) : ℝ)) := by
    simpa only [frobNormSq_F_blockCyclicFin_sq, Nat.cast_mul, Nat.cast_ofNat] using hconv
  obtain ⟨B, hB, hbound⟩ := spectral_no_escape (3 * n) (by omega)
    (fun k => blockCyclicFin (X k) (Y k) (Z k)) hMtrace hMconv
  exact ⟨B, hB, fun k => by simpa only [frobNormSq_F_blockCyclicFin] using hbound k⟩

/-- Local no-escape in the normalization of the Markdown argument: normalized
trace one and cyclic product energy tending to three imply a common bound
for the squared Frobenius norms of all three matrix sequences. No boundedness
or coercivity assumption is required. -/
private theorem local_no_escape {n : ℕ} [NeZero n]
    (X Y Z : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (htrace : ∀ k, (1 / (n : ℂ)) * (X k * Y k * Z k).trace = 1)
    (hconv : Filter.Tendsto (fun k =>
      (frobNormSq_F (X k * Y k) + frobNormSq_F (Y k * Z k) +
        frobNormSq_F (Z k * X k)) / (n : ℝ)) Filter.atTop (𝓝 3)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k,
      frobNormSq_F (X k) ≤ B ∧ frobNormSq_F (Y k) ≤ B ∧ frobNormSq_F (Z k) ≤ B := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have htrace' : ∀ k, (X k * Y k * Z k).trace = (n : ℂ) := by
    intro k
    simpa only [one_div, ← mul_assoc, mul_inv_cancel₀ hnC, one_mul, mul_one] using
      congrArg (fun z : ℂ => (n : ℂ) * z) (htrace k)
  have hconv' : Filter.Tendsto (fun k =>
      frobNormSq_F (X k * Y k) + frobNormSq_F (Y k * Z k) +
        frobNormSq_F (Z k * X k)) Filter.atTop (𝓝 (3 * (n : ℝ))) := by
    simpa only [div_mul_cancel₀ _ hnR] using hconv.mul_const (n : ℝ)
  obtain ⟨B, hB, hbound⟩ := block_cyclic_no_escape hn X Y Z htrace' hconv'
  refine ⟨B, hB, fun k => ?_⟩
  have hX := frobNormSq_F_nonneg (X k)
  have hY := frobNormSq_F_nonneg (Y k)
  have hZ := frobNormSq_F_nonneg (Z k)
  have hsum := hbound k
  exact ⟨by linarith, by linarith, by linarith⟩

theorem local_no_escape_bounded {n : ℕ} [NeZero n]
    (first second third : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (htrace : ∀ index,
      (1 / (n : ℂ)) * (first index * second index * third index).trace = 1)
    (hconv : Filter.Tendsto (fun index =>
      (frobNormSq_F (first index * second index) +
        frobNormSq_F (second index * third index) +
        frobNormSq_F (third index * first index)) / (n : ℝ))
      Filter.atTop (𝓝 3)) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index,
      frobNormSq_F (first index) ≤ bound ∧
      frobNormSq_F (second index) ≤ bound ∧
      frobNormSq_F (third index) ≤ bound :=
  local_no_escape first second third htrace hconv

variable {n : ℕ} [NeZero n]

/-! ## Supported energies and the objective excess -/

/-- The cyclic product energy of the supported triple `(a, b, f.op a b)`.
The numerator uses unnormalized squared Frobenius norms, so division by
`n` gives the same normalization as `local_no_escape`. -/
private def supportedEnergy (Θ : HCParams n) (f : BinOp n) (a b : Fin n) : ℝ :=
  (frobNormSq_F (Θ.A a * Θ.B b) +
    frobNormSq_F (Θ.B b * Θ.C (f.op a b)) +
    frobNormSq_F (Θ.C (f.op a b) * Θ.A a)) / (n : ℝ)

omit [NeZero n] in
/-- Feasibility gives normalized trace one on every supported triple. -/
private theorem supported_trace_eq_one (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) (a b : Fin n) :
    (1 / (n : ℂ)) * (Θ.A a * Θ.B b * Θ.C (f.op a b)).trace = 1 := by
  simpa only [hcProduct, structureTensor, if_pos rfl] using hfeas a b (f.op a b)

/-- Express supported energy using the normalized Frobenius quantities in
`matrix_amgm` and `objective_eq_sum_support`. -/
private theorem supportedEnergy_eq_sum (Θ : HCParams n) (f : BinOp n) (a b : Fin n) :
    supportedEnergy Θ f a b =
      (frobNormSq (Θ.A a * Θ.B b)).re +
      (frobNormSq (Θ.B b * Θ.C (f.op a b))).re +
      (frobNormSq (Θ.C (f.op a b) * Θ.A a)).re := by
  simp only [supportedEnergy, frobNormSq_re_eq_frobNormSq_F_div]
  ring

/-- Every supported energy of a feasible factorization is at least three.
This needs no quasigroup or nongroup assumption on the target. -/
private theorem supported_energy_ge_three (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) (a b : Fin n) :
    3 ≤ supportedEnergy Θ f a b := by
  rw [supportedEnergy_eq_sum]
  exact matrix_amgm (Θ.A a) (Θ.B b) (Θ.C (f.op a b))
    (supported_trace_eq_one Θ f hfeas a b)

/-- The real objective is the sum of the `n^2` supported energies.
This identity holds for arbitrary parameters, without feasibility. -/
private theorem objective_re_eq_sum_supported_energy (Θ : HCParams n) (f : BinOp n) :
    (objective Θ f).re = ∑ a : Fin n, ∑ b : Fin n, supportedEnergy Θ f a b := by
  rw [objective_eq_sum_support]
  simp only [Complex.re_sum, Complex.add_re]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [supportedEnergy_eq_sum]
  ring

/-- The objective excess is exactly the sum of supported-energy excesses.
Together with `supported_energy_ge_three`, feasibility makes every summand
nonnegative; the identity itself does not require feasibility. -/
private theorem objective_excess_eq_sum_supported_excess (Θ : HCParams n) (f : BinOp n) :
    (objective Θ f).re - 3 * (n : ℝ) ^ 2 =
      ∑ a : Fin n, ∑ b : Fin n, (supportedEnergy Θ f a b - 3) := by
  rw [objective_re_eq_sum_supported_energy]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- A supported-energy excess is nonnegative and at most the total objective
excess. This follows from the finite sum identity and feasibility alone;
quasigroup coverage is only needed later to bound every slice. -/
private theorem supported_energy_excess_bounds (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) (a b : Fin n) :
    0 ≤ supportedEnergy Θ f a b - 3 ∧
      supportedEnergy Θ f a b - 3 ≤ (objective Θ f).re - 3 * (n : ℝ) ^ 2 := by
  have hnonneg : ∀ i j : Fin n, 0 ≤ supportedEnergy Θ f i j - 3 :=
    fun i j => sub_nonneg.mpr (supported_energy_ge_three Θ f hfeas i j)
  refine ⟨hnonneg a b, ?_⟩
  rw [objective_excess_eq_sum_supported_excess]
  calc
    supportedEnergy Θ f a b - 3 ≤ ∑ j : Fin n, (supportedEnergy Θ f a j - 3) :=
      Finset.single_le_sum (fun j _ => hnonneg a j) (Finset.mem_univ b)
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (supportedEnergy Θ f i j - 3) :=
      Finset.single_le_sum
        (fun i _ => Finset.sum_nonneg (fun j _ => hnonneg i j)) (Finset.mem_univ a)

/-- Along a feasible sequence whose objective approaches the floor, every
fixed supported triple has energy tending to three. Squeeze its excess
between zero and the total objective excess; no subsequence extraction or
boundedness assumption is needed. -/
private theorem supported_energy_tendsto_three (Θ : ℕ → HCParams n) (f : BinOp n)
    (hfeas : ∀ k, Factorizes (Θ k) f)
    (hconv : Filter.Tendsto (fun k => (objective (Θ k) f).re)
      Filter.atTop (𝓝 (3 * (n : ℝ) ^ 2))) (a b : Fin n) :
    Filter.Tendsto (fun k => supportedEnergy (Θ k) f a b) Filter.atTop (𝓝 3) := by
  have htotal : Filter.Tendsto (fun k => (objective (Θ k) f).re - 3 * (n : ℝ) ^ 2)
      Filter.atTop (𝓝 0) := by
    convert hconv.sub_const (3 * (n : ℝ) ^ 2) using 1
    norm_num
  have hexcess : Filter.Tendsto (fun k => supportedEnergy (Θ k) f a b - 3)
      Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htotal
      (fun k => (supported_energy_excess_bounds (Θ k) f (hfeas k) a b).1)
      (fun k => (supported_energy_excess_bounds (Θ k) f (hfeas k) a b).2)
  simpa only [sub_add_cancel, zero_add] using hexcess.add_const 3

/-! ## Bounds for supported triples and all parameter slices -/

/-- Every fixed supported triple in a feasible sequence approaching the
objective floor has a common squared Frobenius bound for all sequence terms.
This is the local no-escape lemma applied to its trace and energy limits. -/
private theorem supported_triple_frob_bounded_of_objective_tendsto_floor
    (Θ : ℕ → HCParams n) (f : BinOp n)
    (hfeas : ∀ k, Factorizes (Θ k) f)
    (hconv : Filter.Tendsto (fun k => (objective (Θ k) f).re)
      Filter.atTop (𝓝 (3 * (n : ℝ) ^ 2))) (a b : Fin n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k,
      frobNormSq_F ((Θ k).A a) ≤ B ∧
      frobNormSq_F ((Θ k).B b) ≤ B ∧
      frobNormSq_F ((Θ k).C (f.op a b)) ≤ B := by
  exact local_no_escape
    (fun k => (Θ k).A a) (fun k => (Θ k).B b) (fun k => (Θ k).C (f.op a b))
    (fun k => supported_trace_eq_one (Θ k) f (hfeas k) a b)
    (by simpa only [supportedEnergy] using
      supported_energy_tendsto_three Θ f hfeas hconv a b)

/-- Supported-triple bounds control every slice after unused outputs are zeroed. -/
private theorem normalized_sequence_slice_frob_bounded
    (Θ : ℕ → HCParams n) (f : BinOp n)
    (hfeas : ∀ k, Factorizes (Θ k) f)
    (hconv : Filter.Tendsto (fun k => (objective (Θ k) f).re)
      Filter.atTop (𝓝 (3 * (n : ℝ) ^ 2))) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ k,
      (∀ a : Fin n, frobNormSq_F ((zeroUnusedOutputs (Θ k) f).A a) ≤ S) ∧
      (∀ b : Fin n, frobNormSq_F ((zeroUnusedOutputs (Θ k) f).B b) ≤ S) ∧
      (∀ c : Fin n, frobNormSq_F ((zeroUnusedOutputs (Θ k) f).C c) ≤ S) := by
  classical
  choose B hB hbound using
    (fun a b : Fin n =>
      supported_triple_frob_bounded_of_objective_tendsto_floor Θ f hfeas hconv a b)
  let S : ℝ := ∑ a : Fin n, ∑ b : Fin n, B a b
  have hS : 0 ≤ S :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hB a b))
  have hB_le : ∀ a b : Fin n, B a b ≤ S := by
    intro a b
    calc
      B a b ≤ ∑ j : Fin n, B a j :=
        Finset.single_le_sum (fun j _ => hB a j) (Finset.mem_univ b)
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, B i j :=
        Finset.single_le_sum
          (fun i _ => Finset.sum_nonneg (fun j _ => hB i j)) (Finset.mem_univ a)
  let e : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  refine ⟨S, hS, ?_⟩
  intro k
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact ((hbound a e k).1).trans (hB_le a e)
  · intro b
    exact ((hbound e b k).2.1).trans (hB_le e b)
  · intro c
    by_cases hc : ∃ a b, f.op a b = c
    · obtain ⟨a, b, hab⟩ := hc
      rw [← hab, zeroUnusedOutputs_C_supported]
      exact ((hbound a b k).2.2).trans (hB_le a b)
    · simpa [zeroUnusedOutputs, hc, frobNormSq_F] using hS

/-- Quasigroup coverage turns the bounds for supported triples into a single
bound for every slice of a feasible sequence approaching the objective floor.
The bound is the finite sum of the nonnegative supported-triple bounds.
It may depend on the sequence; no a priori boundedness or nongroup hypothesis
is assumed. Norm conversion to `HCParams` is a separate subsequent step. -/
private theorem feasible_sequence_slice_frob_bounded
    (Θ : ℕ → HCParams n) (f : BinOp n) (hq : IsQuasigroup f)
    (hfeas : ∀ k, Factorizes (Θ k) f)
    (hconv : Filter.Tendsto (fun k => (objective (Θ k) f).re)
      Filter.atTop (𝓝 (3 * (n : ℝ) ^ 2))) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ k,
      (∀ a : Fin n, frobNormSq_F ((Θ k).A a) ≤ S) ∧
      (∀ b : Fin n, frobNormSq_F ((Θ k).B b) ≤ S) ∧
      (∀ c : Fin n, frobNormSq_F ((Θ k).C c) ≤ S) := by
  classical
  choose B hB hbound using
    (fun a b : Fin n =>
      supported_triple_frob_bounded_of_objective_tendsto_floor Θ f hfeas hconv a b)
  let S : ℝ := ∑ a : Fin n, ∑ b : Fin n, B a b
  have hS : 0 ≤ S :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hB a b))
  have hB_le : ∀ a b : Fin n, B a b ≤ S := by
    intro a b
    calc
      B a b ≤ ∑ j : Fin n, B a j :=
        Finset.single_le_sum (fun j _ => hB a j) (Finset.mem_univ b)
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, B i j :=
        Finset.single_le_sum
          (fun i _ => Finset.sum_nonneg (fun j _ => hB i j)) (Finset.mem_univ a)
  let e : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  refine ⟨S, hS, ?_⟩
  intro k
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact ((hbound a e k).1).trans (hB_le a e)
  · intro b
    exact ((hbound e b k).2.1).trans (hB_le e b)
  · intro c
    obtain ⟨b, hb⟩ := (hq.left_cancel e).2 c
    have hc := ((hbound e b k).2.2).trans (hB_le e b)
    simpa only [hb] using hc

/-! ## Explicit conversion from slice bounds to the parameter norm -/

section ParameterNormConversion

open scoped Matrix.Norms.Frobenius
omit [NeZero n]

/-- Under the Frobenius scope, the squared matrix norm is exactly the
unnormalized squared Frobenius quantity used by local no-escape. -/
private theorem matrix_frobenius_norm_sq_eq (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖M‖ ^ 2 = frobNormSq_F M := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt (by positivity)]
  simp only [frobNormSq_F, Real.rpow_two, Complex.normSq_eq_norm_sq]

/-- A squared Frobenius bound gives the corresponding matrix norm bound. -/
private theorem matrix_frobenius_norm_le_sqrt_of_frob_bound
    (M : Matrix (Fin n) (Fin n) ℂ) {S : ℝ} (hM : frobNormSq_F M ≤ S) :
    ‖M‖ ≤ Real.sqrt S := by
  calc
    ‖M‖ = Real.sqrt (‖M‖ ^ 2) := (Real.sqrt_sq (norm_nonneg M)).symm
    _ = Real.sqrt (frobNormSq_F M) := congrArg Real.sqrt (matrix_frobenius_norm_sq_eq M)
    _ ≤ Real.sqrt S := Real.sqrt_le_sqrt hM

/-- The existing `HCParams` norm is the maximum of the three finite-family
sup norms, with the Frobenius norm on each slice. It therefore has the same
upper bound as every slice; this uses the transported norm from `Tikhonov`. -/
private theorem hcParams_norm_le_of_slice_bounds (Θ : HCParams n) {R : ℝ}
    (hR : 0 ≤ R)
    (hA : ∀ a : Fin n, ‖Θ.A a‖ ≤ R)
    (hB : ∀ b : Fin n, ‖Θ.B b‖ ≤ R)
    (hC : ∀ c : Fin n, ‖Θ.C c‖ ≤ R) : ‖Θ‖ ≤ R := by
  change max ‖Θ.A‖ (max ‖Θ.B‖ ‖Θ.C‖) ≤ R
  exact max_le ((pi_norm_le_iff_of_nonneg hR).2 hA)
    (max_le ((pi_norm_le_iff_of_nonneg hR).2 hB)
      ((pi_norm_le_iff_of_nonneg hR).2 hC))

/-- A common squared Frobenius bound `S` for all slices yields the explicit
bound `sqrt S` on the actual parameter norm. Applied to each sequence term,
this is the conversion needed after `feasible_sequence_slice_frob_bounded`.
No identification with the separate sum `Tikhonov.hcNormSq` is used. -/
private theorem hcParams_norm_le_sqrt_of_slice_frob_bounds (Θ : HCParams n) {S : ℝ}
    (hA : ∀ a : Fin n, frobNormSq_F (Θ.A a) ≤ S)
    (hB : ∀ b : Fin n, frobNormSq_F (Θ.B b) ≤ S)
    (hC : ∀ c : Fin n, frobNormSq_F (Θ.C c) ≤ S) : ‖Θ‖ ≤ Real.sqrt S := by
  exact hcParams_norm_le_of_slice_bounds Θ (Real.sqrt_nonneg S)
    (fun a => matrix_frobenius_norm_le_sqrt_of_frob_bound (Θ.A a) (hA a))
    (fun b => matrix_frobenius_norm_le_sqrt_of_frob_bound (Θ.B b) (hB b))
    (fun c => matrix_frobenius_norm_le_sqrt_of_frob_bound (Θ.C c) (hC c))

end ParameterNormConversion

/-- A near-floor feasible sequence has bounded normalized parameters for any operation. -/
private theorem normalized_sequence_bounded_of_objective_tendsto_floor
    (Θ : ℕ → HCParams n) (f : BinOp n)
    (hfeas : ∀ k, Factorizes (Θ k) f)
    (hconv : Filter.Tendsto (fun k => (objective (Θ k) f).re)
      Filter.atTop (𝓝 (3 * (n : ℝ) ^ 2))) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k, ‖zeroUnusedOutputs (Θ k) f‖ ≤ R := by
  obtain ⟨S, _, hbound⟩ := normalized_sequence_slice_frob_bounded Θ f hfeas hconv
  refine ⟨Real.sqrt S, Real.sqrt_nonneg S, ?_⟩
  intro k
  obtain ⟨hA, hB, hC⟩ := hbound k
  exact hcParams_norm_le_sqrt_of_slice_frob_bounds (zeroUnusedOutputs (Θ k) f) hA hB hC

/-- For any operation, some positive-width near-floor sublevel has bounded
parameters after unused output slices are zeroed. -/
theorem normalized_feasible_near_floor_bounded (f : BinOp n) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, ∀ Θ : HCParams n,
      Factorizes Θ f → (objective Θ f).re ≤ 3 * (n : ℝ) ^ 2 + δ →
        ‖zeroUnusedOutputs Θ f‖ ≤ R := by
  classical
  by_contra hnot
  push_neg at hnot
  have hwitness : ∀ k : ℕ, ∃ Θ : HCParams n,
      Factorizes Θ f ∧
      (objective Θ f).re ≤ 3 * (n : ℝ) ^ 2 + 1 / ((k : ℝ) + 1) ∧
      (k : ℝ) < ‖zeroUnusedOutputs Θ f‖ := by
    intro k
    exact hnot (1 / ((k : ℝ) + 1)) (by positivity) (k : ℝ)
  choose Θ hfeas hupper hgrow using hwitness
  have hinv : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1))
      Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hupperlim : Filter.Tendsto
      (fun k : ℕ => 3 * (n : ℝ) ^ 2 + 1 / ((k : ℝ) + 1))
      Filter.atTop (𝓝 (3 * (n : ℝ) ^ 2)) := by
    simpa only [add_zero] using hinv.const_add (3 * (n : ℝ) ^ 2)
  have hconv : Filter.Tendsto (fun k => (objective (Θ k) f).re)
      Filter.atTop (𝓝 (3 * (n : ℝ) ^ 2)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupperlim
      (fun k => universal_lower_bound_general f (Θ k) (hfeas k)) hupper
  obtain ⟨R, _, hR⟩ := normalized_sequence_bounded_of_objective_tendsto_floor
    Θ f hfeas hconv
  obtain ⟨k, hk⟩ := exists_nat_gt R
  exact (not_lt_of_ge (hR k)) (hk.trans (hgrow k))

/-- For any operation whose feasible parameters never attain the universal
floor, a positive gap holds uniformly over all feasible parameters. -/
theorem exists_gap_of_no_floor (f : BinOp n)
    (hnoFloor : ∀ Θ : HCParams n, Factorizes Θ f →
      (objective Θ f).re ≠ 3 * (n : ℝ) ^ 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Θ : HCParams n,
      Factorizes Θ f → 3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ f).re := by
  obtain ⟨δ, hδ, R, hR⟩ := normalized_feasible_near_floor_bounded f
  have hballgap : ∃ ε : ℝ, 0 < ε ∧ ∀ Θ : HCParams n,
      Factorizes Θ f → ‖Θ‖ ≤ R →
        3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ f).re := by
    by_cases hne : ({Θ : HCParams n | Factorizes Θ f} ∩
        Metric.closedBall 0 R).Nonempty
    · obtain ⟨Θmin, hfeas, _, hmin⟩ :=
        Tikhonov.exists_minOn_feasible_ball f R hne
      refine ⟨(objective Θmin f).re - 3 * (n : ℝ) ^ 2, ?_, ?_⟩
      · exact sub_pos.mpr (lt_of_le_of_ne
          (universal_lower_bound_general f Θmin hfeas) (hnoFloor Θmin hfeas).symm)
      · intro Θ hΘ hnorm
        have := hmin Θ hΘ hnorm
        linarith
    · refine ⟨1, by norm_num, ?_⟩
      intro Θ hΘ hnorm
      exact False.elim (hne ⟨Θ, hΘ, by
        rwa [Metric.mem_closedBall, dist_zero_right]⟩)
  obtain ⟨ε, hε, hgap⟩ := hballgap
  refine ⟨min δ ε, lt_min hδ hε, ?_⟩
  intro Θ hΘ
  by_cases hle : (objective Θ f).re ≤ 3 * (n : ℝ) ^ 2 + δ
  · have hlocal := hgap (zeroUnusedOutputs Θ f)
      (factorizes_zeroUnusedOutputs Θ f hΘ) (hR Θ hΘ hle)
    rw [objective_zeroUnusedOutputs] at hlocal
    have := min_le_right δ ε
    linarith
  · have := min_le_left δ ε
    push_neg at hle
    linarith

/-- Exclusion of the universal floor gives a positive gap for the real
infimum of the nonempty feasible objective-value set, without attainment. -/
theorem exists_infimum_gap_of_no_floor (f : BinOp n)
    (hnoFloor : ∀ Θ : HCParams n, Factorizes Θ f →
      (objective Θ f).re ≠ 3 * (n : ℝ) ^ 2) :
    ∃ ε : ℝ, 0 < ε ∧
      3 * (n : ℝ) ^ 2 + ε ≤ sInf (feasibleObjectiveValues f) := by
  obtain ⟨ε, hε, hgap⟩ := exists_gap_of_no_floor f hnoFloor
  refine ⟨ε, hε, le_csInf (feasibleObjectiveValues_nonempty f) ?_⟩
  rintro value ⟨Θ, hfeas, rfl⟩
  exact hgap Θ hfeas

/-- A feasible sequence for a fixed quasigroup target whose objective tends
to the floor is bounded in the existing `HCParams` norm. The common bound
applies to every sequence term and may depend on the sequence. It is derived
from local no-escape and coverage, without a boundedness or coercivity premise. -/
private theorem feasible_sequence_bounded_of_objective_tendsto_floor
    (Θ : ℕ → HCParams n) (f : BinOp n) (hq : IsQuasigroup f)
    (hfeas : ∀ k, Factorizes (Θ k) f)
    (hconv : Filter.Tendsto (fun k => (objective (Θ k) f).re)
      Filter.atTop (𝓝 (3 * (n : ℝ) ^ 2))) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k, ‖Θ k‖ ≤ R := by
  obtain ⟨S, _, hbound⟩ := feasible_sequence_slice_frob_bounded Θ f hq hfeas hconv
  refine ⟨Real.sqrt S, Real.sqrt_nonneg S, ?_⟩
  intro k
  obtain ⟨hA, hB, hC⟩ := hbound k
  exact hcParams_norm_le_sqrt_of_slice_frob_bounds (Θ k) hA hB hC

/-- For a fixed quasigroup target, some positive-width feasible near-floor
sublevel is bounded in the existing parameter norm. No boundedness,
coercivity, or nongroup assumption is required. If every such sublevel were
unbounded, choose feasible parameters with objective at most
`3 * n^2 + 1 / (k + 1)` and norm greater than `k`. Their objectives tend to
the floor, contradicting feasible-sequence boundedness. -/
theorem feasible_near_floor_bounded (f : BinOp n) (hq : IsQuasigroup f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, ∀ Θ : HCParams n,
      Factorizes Θ f → (objective Θ f).re ≤ 3 * (n : ℝ) ^ 2 + δ → ‖Θ‖ ≤ R := by
  classical
  by_contra hnot
  push_neg at hnot
  have hwitness : ∀ k : ℕ, ∃ Θ : HCParams n,
      Factorizes Θ f ∧
      (objective Θ f).re ≤ 3 * (n : ℝ) ^ 2 + 1 / ((k : ℝ) + 1) ∧
      (k : ℝ) < ‖Θ‖ := by
    intro k
    exact hnot (1 / ((k : ℝ) + 1)) (by positivity) (k : ℝ)
  choose Θ hfeas hupper hgrow using hwitness
  have hinv : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1))
      Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hupperlim : Filter.Tendsto
      (fun k : ℕ => 3 * (n : ℝ) ^ 2 + 1 / ((k : ℝ) + 1))
      Filter.atTop (𝓝 (3 * (n : ℝ) ^ 2)) := by
    simpa only [add_zero] using hinv.const_add (3 * (n : ℝ) ^ 2)
  have hconv : Filter.Tendsto (fun k => (objective (Θ k) f).re)
      Filter.atTop (𝓝 (3 * (n : ℝ) ^ 2)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupperlim
      (fun k => universal_lower_bound_general f (Θ k) (hfeas k)) hupper
  obtain ⟨R, _, hR⟩ := feasible_sequence_bounded_of_objective_tendsto_floor
    Θ f hq hfeas hconv
  obtain ⟨k, hk⟩ := exists_nat_gt R
  exact (not_lt_of_ge (hR k)) (hk.trans (hgrow k))

/-- Pointwise strictness gives a uniform gap on any fixed closed ball. -/
theorem exists_gap_on_feasible_ball (f : BinOp n) (hq : IsQuasigroup f)
    (hnotgi : ¬ IsGroupIsotope f) (R : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Θ : HCParams n,
      Factorizes Θ f → ‖Θ‖ ≤ R →
        3 * (n : ℝ)^2 + ε ≤ (objective Θ f).re := by
  by_cases hne : ({Θ : HCParams n | Factorizes Θ f} ∩
      Metric.closedBall 0 R).Nonempty
  · obtain ⟨Θmin, hfeas, hnorm, hmin⟩ :=
      Tikhonov.exists_minOn_feasible_ball f R hne
    refine ⟨(objective Θmin f).re - 3 * (n : ℝ)^2, ?_, ?_⟩
    · exact sub_pos.mpr (strict_gap_non_group f hq hnotgi Θmin hfeas)
    · intro Θ hΘ hR
      have := hmin Θ hΘ hR
      linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro Θ hΘ hR
    exact False.elim (hne ⟨Θ, hΘ, by
      rwa [Metric.mem_closedBall, dist_zero_right]⟩)

/-- Only boundedness of one positive-width near-floor sublevel is needed;
global coercivity and global attainment are not hypotheses. -/
theorem exists_gap_of_near_floor_bounded (f : BinOp n) (hq : IsQuasigroup f)
    (hnotgi : ¬ IsGroupIsotope f)
    (hbounded : ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, ∀ Θ : HCParams n,
      Factorizes Θ f → (objective Θ f).re ≤ 3 * (n : ℝ)^2 + δ → ‖Θ‖ ≤ R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Θ : HCParams n,
      Factorizes Θ f → 3 * (n : ℝ)^2 + ε ≤ (objective Θ f).re := by
  obtain ⟨δ, hδ, R, hR⟩ := hbounded
  obtain ⟨ε, hε, hgap⟩ := exists_gap_on_feasible_ball f hq hnotgi R
  refine ⟨min δ ε, lt_min hδ hε, ?_⟩
  intro Θ hΘ
  by_cases hle : (objective Θ f).re ≤ 3 * (n : ℝ)^2 + δ
  · have hlocal := hgap Θ hΘ (hR Θ hΘ hle)
    have := min_le_right δ ε
    linarith
  · have := min_le_left δ ε
    push_neg at hle
    linarith

/-- Every quasigroup target not isotopic to a group has a positive gap
above the universal floor, uniformly over all feasible parameters. -/
theorem exists_gap (f : BinOp n) (hq : IsQuasigroup f)
    (hnotgi : ¬ IsGroupIsotope f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Θ : HCParams n,
      Factorizes Θ f →
        3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ f).re := by
  exact exists_gap_of_near_floor_bounded f hq hnotgi
    (feasible_near_floor_bounded f hq)

/-- The real feasible infimum is strictly above the universal floor for
every quasigroup target not isotopic to a group, without attainment. -/
theorem infimum_gt_floor (f : BinOp n) (hq : IsQuasigroup f)
    (hnotgi : ¬ IsGroupIsotope f) :
    3 * (n : ℝ) ^ 2 < sInf (feasibleObjectiveValues f) := by
  obtain ⟨ε, hε, hgap⟩ := exists_gap f hq hnotgi
  have hinf : 3 * (n : ℝ) ^ 2 + ε ≤ sInf (feasibleObjectiveValues f) := by
    apply le_csInf (feasibleObjectiveValues_nonempty f)
    rintro value ⟨Θ, hfeas, rfl⟩
    exact hgap Θ hfeas
  exact (lt_add_of_pos_right (3 * (n : ℝ) ^ 2) hε).trans_le hinf

/-- A finite enumeration of binary operations, transported from the finite
function space. This private definition is not registered as an instance;
the fixed-order argument can install it locally with `letI`. -/
@[implicit_reducible]
private def binOpFintype (N : ℕ) : Fintype (BinOp N) := by
  classical
  let e : (Fin N → Fin N → Fin N) ≃ BinOp N :=
    { toFun := fun op => ⟨op⟩
      invFun := fun f => f.op
      left_inv := fun _ => rfl
      right_inv := fun f => by cases f; rfl }
  letI : Fintype (BinOp N) :=
    Fintype.ofEquiv (Fin N → Fin N → Fin N) e
  exact inferInstance

/-- Enumerate exactly the quasigroup targets that are not group isotopes.
The subtype records eligibility, and the enumeration contains every such
target. The alternatives prepare the fixed-order proof: either the enumeration
is nonempty, or there are no eligible targets and its conclusion is vacuous.
All finiteness instances used here are local to the proof. -/
private theorem exists_eligible_target_enumeration (N : ℕ) :
    ∃ T : Finset {f : BinOp N // IsQuasigroup f ∧ ¬ IsGroupIsotope f},
      (∀ g, g ∈ T) ∧
        (T.Nonempty ∨ ¬ ∃ f : BinOp N, IsQuasigroup f ∧ ¬ IsGroupIsotope f) := by
  classical
  letI : Fintype (BinOp N) := binOpFintype N
  let Eligible := {f : BinOp N // IsQuasigroup f ∧ ¬ IsGroupIsotope f}
  let T : Finset Eligible := Finset.univ
  have hT : ∀ g : Eligible, g ∈ T := fun g => Finset.mem_univ g
  refine ⟨T, hT, ?_⟩
  by_cases hnonempty : T.Nonempty
  · exact Or.inl hnonempty
  · refine Or.inr ?_
    rintro ⟨f, hq, hnotgi⟩
    exact hnonempty ⟨⟨f, hq, hnotgi⟩, hT ⟨f, hq, hnotgi⟩⟩

/-- Choose a positive fixed-target gap for every eligible target of order
`n`, together with its bound for all feasible parameters. The chosen gaps may
depend on the target. This choice also makes sense for an empty eligible
subtype; nonemptiness is only needed later when taking a finite minimum. -/
private theorem exists_eligible_target_gaps :
    ∃ gap : {f : BinOp n // IsQuasigroup f ∧ ¬ IsGroupIsotope f} → ℝ,
      (∀ g, 0 < gap g) ∧
        ∀ g (Θ : HCParams n), Factorizes Θ g.val →
          3 * (n : ℝ) ^ 2 + gap g ≤ (objective Θ g.val).re := by
  classical
  choose gap hpos hgap using
    (fun g : {f : BinOp n // IsQuasigroup f ∧ ¬ IsGroupIsotope f} =>
      exists_gap g.val g.property.1 g.property.2)
  exact ⟨gap, hpos, hgap⟩

/-- The finite minimum of the chosen target gaps is positive on any
nonempty finite set of eligible targets and gives a common gap for every
target in that set. The nonemptiness premise prevents an empty minimum. -/
private theorem exists_gap_on_nonempty_eligible_finset
    (T : Finset {f : BinOp n // IsQuasigroup f ∧ ¬ IsGroupIsotope f})
    (hT : T.Nonempty) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ T, ∀ Θ : HCParams n,
      Factorizes Θ g.val →
        3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ g.val).re := by
  classical
  obtain ⟨gap, hpos, hgap⟩ := exists_eligible_target_gaps (n := n)
  refine ⟨T.inf' hT gap, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    exact fun g _ => hpos g
  · intro g hg Θ hfeas
    have hmin : T.inf' hT gap ≤ gap g := Finset.inf'_le gap hg
    exact (add_le_add (le_refl (3 * (n : ℝ) ^ 2)) hmin).trans (hgap g Θ hfeas)

/-- At each positive order, a positive gap works uniformly for all
quasigroup targets not isotopic to a group and all their feasible parameters.
If there are no eligible targets, gap one suffices vacuously. No boundedness
or target-existence premise is required. -/
theorem exists_gap_fixed_order :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : BinOp n,
      IsQuasigroup f → ¬ IsGroupIsotope f →
      ∀ Θ : HCParams n, Factorizes Θ f →
        3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ f).re := by
  obtain ⟨T, hall, hcases⟩ := exists_eligible_target_enumeration n
  rcases hcases with hnonempty | hnone
  · obtain ⟨ε, hε, hgap⟩ := exists_gap_on_nonempty_eligible_finset T hnonempty
    refine ⟨ε, hε, ?_⟩
    intro f hq hnotgi Θ hfeas
    exact hgap ⟨f, hq, hnotgi⟩ (hall ⟨f, hq, hnotgi⟩) Θ hfeas
  · refine ⟨1, by norm_num, ?_⟩
    intro f hq hnotgi
    exact False.elim (hnone ⟨f, hq, hnotgi⟩)

/-- At each positive order, one positive gap bounds the real feasible
infima of all quasigroup targets not isotopic to a group. -/
theorem exists_infimum_gap_fixed_order :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : BinOp n,
      IsQuasigroup f → ¬ IsGroupIsotope f →
        3 * (n : ℝ) ^ 2 + ε ≤ sInf (feasibleObjectiveValues f) := by
  obtain ⟨ε, hε, hgap⟩ := exists_gap_fixed_order (n := n)
  refine ⟨ε, hε, ?_⟩
  intro f hq hnotgi
  apply le_csInf (feasibleObjectiveValues_nonempty f)
  rintro value ⟨Θ, hfeas, rfl⟩
  exact hgap f hq hnotgi Θ hfeas

theorem exists_gap_fixed_order_of_no_floor :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : BinOp n,
      (∀ Θ : HCParams n, Factorizes Θ f →
        (objective Θ f).re ≠ 3 * (n : ℝ) ^ 2) →
      ∀ Θ : HCParams n, Factorizes Θ f →
        3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ f).re := by
  classical
  letI : Fintype (BinOp n) := binOpFintype n
  let Eligible := {f : BinOp n // ∀ Θ : HCParams n, Factorizes Θ f →
    (objective Θ f).re ≠ 3 * (n : ℝ) ^ 2}
  by_cases heligible : Nonempty Eligible
  · letI : Nonempty Eligible := heligible
    choose gap hpositive hgap using
      (fun target : Eligible => exists_gap_of_no_floor target.val target.property)
    have hnonempty : (Finset.univ : Finset Eligible).Nonempty := Finset.univ_nonempty
    refine ⟨Finset.univ.inf' hnonempty gap, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      exact fun target _ => hpositive target
    · intro target hnoFloor parameters hfeas
      have hminimum : Finset.univ.inf' hnonempty gap ≤ gap ⟨target, hnoFloor⟩ :=
        Finset.inf'_le gap (Finset.mem_univ _)
      have hbound := hgap ⟨target, hnoFloor⟩ parameters hfeas
      linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro target hnoFloor
    exact False.elim (heligible ⟨⟨target, hnoFloor⟩⟩)

theorem exists_infimum_gap_fixed_order_of_no_floor :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : BinOp n,
      (∀ Θ : HCParams n, Factorizes Θ f →
        (objective Θ f).re ≠ 3 * (n : ℝ) ^ 2) →
        3 * (n : ℝ) ^ 2 + ε ≤ sInf (feasibleObjectiveValues f) := by
  obtain ⟨gap, hpositive, hgap⟩ := exists_gap_fixed_order_of_no_floor (n := n)
  refine ⟨gap, hpositive, ?_⟩
  intro target hnoFloor
  apply le_csInf (feasibleObjectiveValues_nonempty target)
  rintro value ⟨parameters, hfeas, rfl⟩
  exact hgap target hnoFloor parameters hfeas

theorem floor_or_infimum_gap_fixed_order :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : BinOp n,
      (∃ Θ : HCParams n, Factorizes Θ f ∧ (objective Θ f).re = 3 * (n : ℝ) ^ 2) ∨
        3 * (n : ℝ) ^ 2 + ε ≤ sInf (feasibleObjectiveValues f) := by
  classical
  obtain ⟨gap, hpositive, hgap⟩ := exists_infimum_gap_fixed_order_of_no_floor (n := n)
  refine ⟨gap, hpositive, ?_⟩
  intro target
  by_cases hfloor : ∃ parameters : HCParams n,
      Factorizes parameters target ∧ (objective parameters target).re = 3 * (n : ℝ) ^ 2
  · exact Or.inl hfloor
  · apply Or.inr
    apply hgap target
    intro parameters hfeas hequality
    exact hfloor ⟨parameters, hfeas, hequality⟩

end PositiveGap
