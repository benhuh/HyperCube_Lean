import HyperCubeGroup.Foundation.InverseRank
import HyperCubeGroup.Foundation.SupportDecomposition

/-!
# Support-local inverse-rank bounds

Manuscript API map for arbitrary binary operations:
* Lemma 1: `support_decomposition` and
  `support_perfectCollinearity_iff_identities`.
* Lemma 2: `support_collinear_shared_gram_matrices`.
* Lemma 3: `support_collinear_normalized_rank_constant` and
  `support_collinear_rank_identification` (under `PerfectCollinearity`);
  `support_kappa_one_iff_gram_identity` characterizes full normalized rank.
* Lemma 4: `support_collinear_inverse_rank_bound_of_constant`,
  `support_collinear_inverse_rank_bound`, and
  `support_collinear_dynamic_floor_eq_iff`.

Equality balances only supported triples; unused output slices are unrestricted.
The legacy inverse-rank API is imported unchanged for its scalar helpers.
-/

open Matrix BigOperators Finset

noncomputable section

variable {n : ℕ} [NeZero n]

theorem support_collinear_shared_gram_matrices (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f)
    (htrace : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) ≠ 0) :
    ∃ Z : Matrix (Fin n) (Fin n) ℂ,
      (∀ b, gramB Θ b = Z) ∧
      (∀ a, (1 / frobNormSq (Θ.A a)) •
        ((Θ.A a).conjTranspose * Θ.A a) = Z) ∧
      (1 / (n : ℂ)) * Z.trace = 1 ∧ Z.conjTranspose = Z := by
  have hnd := support_nondegenerate_of_nonzero Θ f htrace
  exact support_shared_gram_matrices Θ f
    ((support_perfectCollinearity_iff_identities Θ f hnd).mp hcol) htrace

theorem support_collinear_normalized_rank_constant (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f)
    (htrace : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
      ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = (κ : ℂ) := by
  have hnd := support_nondegenerate_of_nonzero Θ f htrace
  exact support_normalized_rank_constant Θ f
    ((support_perfectCollinearity_iff_identities Θ f hnd).mp hcol) htrace

theorem support_collinear_rank_identification (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f)
    (htrace : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
      (∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = (κ : ℂ)) ∧
      (n : ℝ) * κ = ((supportGram Θ).rank : ℝ) ∧
      (∀ a, (Θ.A a).rank = (supportGram Θ).rank) ∧
      (∀ b, (Θ.B b).rank = (supportGram Θ).rank) ∧
      (∀ a b, (Θ.C (f.op a b)).rank = (supportGram Θ).rank) := by
  have hnd := support_nondegenerate_of_nonzero Θ f htrace
  exact support_rank_identification Θ f
    ((support_perfectCollinearity_iff_identities Θ f hnd).mp hcol) htrace

theorem support_kappa_one_iff_gram_identity (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f)
    (htrace : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) ≠ 0)
    (κ : ℝ) (hκ : 0 < κ)
    (hκconst : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = (κ : ℂ)) :
    κ = 1 ↔ supportGram Θ = 1 := by
  have hnd := support_nondegenerate_of_nonzero Θ f htrace
  have hids := (support_perfectCollinearity_iff_identities Θ f hnd).mp hcol
  have htr := support_gram_trace Θ f htrace
  have hnorm : frobNormSq (1 - supportGram Θ) = ((κ⁻¹ - 1 : ℝ) : ℂ) := by
    unfold frobNormSq frobInner
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, support_gram_hermitian]
    have hexpand : (1 - supportGram Θ) * (1 - supportGram Θ) =
        1 - supportGram Θ - supportGram Θ + supportGram Θ * supportGram Θ := by
      simp only [sub_mul, mul_sub, Matrix.mul_one, Matrix.one_mul]
      abel
    rw [hexpand, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_one, Fintype.card_fin, htr,
      support_gram_square_inverse Θ f hids htrace 0 0, hκconst,
      Matrix.trace_smul, smul_eq_mul, htr]
    push_cast
    field_simp [(Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : ℂ) ≠ 0),
      (Complex.ofReal_ne_zero.mpr hκ.ne' : (κ : ℂ) ≠ 0)]
    ring
  constructor
  · intro hunit
    have hzero : frobNormSq (1 - supportGram Θ) = 0 := by
      rw [hnorm, hunit]
      norm_num
    exact (sub_eq_zero.mp ((frobNormSq_eq_zero_iff _).mp hzero)).symm
  · intro hgram
    have hzero : frobNormSq (1 - supportGram Θ) = 0 := by
      rw [hgram, sub_self]
      exact (frobNormSq_eq_zero_iff _).mpr rfl
    rw [hnorm] at hzero
    have hinv : κ⁻¹ = 1 := sub_eq_zero.mp (Complex.ofReal_eq_zero.mp hzero)
    simpa only [inv_inv, inv_one] using congrArg (fun value : ℝ => value⁻¹) hinv

theorem support_collinear_inverse_rank_bound_of_constant (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f)
    (htrace : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) ≠ 0)
    (κ : ℝ) (hκ : 0 < κ)
    (hκconst : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = (κ : ℂ)) :
    (objective Θ f).re = (inverseScalePenalty Θ f).re ∧
    3 * κ ^ (-1 / 3 : ℝ) *
      (∑ a : Fin n, ∑ b : Fin n, ‖hcProduct Θ a b (f.op a b)‖ ^ (4 / 3 : ℝ)) ≤
        (objective Θ f).re ∧
    (3 * κ ^ (-1 / 3 : ℝ) *
      (∑ a : Fin n, ∑ b : Fin n, ‖hcProduct Θ a b (f.op a b)‖ ^ (4 / 3 : ℝ)) =
        (objective Θ f).re ↔
      ∀ a b : Fin n, frobNormSq (Θ.A a) = frobNormSq (Θ.B b) ∧
        frobNormSq (Θ.B b) = frobNormSq (Θ.C (f.op a b))) := by
  have hnd := support_nondegenerate_of_nonzero Θ f htrace
  let lower : Fin n → Fin n → ℝ := fun a b =>
    3 * κ ^ (-1 / 3 : ℝ) * ‖hcProduct Θ a b (f.op a b)‖ ^ (4 / 3 : ℝ)
  let upper : Fin n → Fin n → ℝ := fun a b =>
    ‖hcProduct Θ a b (f.op a b)‖ ^ 2 *
      (1 / (frobNormSq (Θ.A a)).re + 1 / (frobNormSq (Θ.B b)).re +
        1 / (frobNormSq (Θ.C (f.op a b))).re)
  have term_bound : ∀ a b, lower a b ≤ upper a b := by
    intro a b
    exact scalar_inverse_rank_bound
      (frobNormSq_re_pos_of_ne_zero _ (hnd.A_pos a))
      (frobNormSq_re_pos_of_ne_zero _ (hnd.B_pos b))
      (frobNormSq_re_pos_of_ne_zero _ (hnd.C_pos a b))
      (norm_pos_iff.mpr (htrace a b)) hκ (inverseRank_product Θ f κ htrace hκconst a b)
  have term_eq : ∀ a b, lower a b = upper a b ↔
      frobNormSq (Θ.A a) = frobNormSq (Θ.B b) ∧
        frobNormSq (Θ.B b) = frobNormSq (Θ.C (f.op a b)) := by
    intro a b
    have scalar_eq := scalar_inverse_rank_eq_iff
      (frobNormSq_re_pos_of_ne_zero _ (hnd.A_pos a))
      (frobNormSq_re_pos_of_ne_zero _ (hnd.B_pos b))
      (frobNormSq_re_pos_of_ne_zero _ (hnd.C_pos a b))
      (norm_pos_iff.mpr (htrace a b)) hκ (inverseRank_product Θ f κ htrace hκconst a b)
    constructor
    · intro equality
      obtain ⟨first, second⟩ := scalar_eq.mp equality
      exact ⟨Complex.ext first (by rw [frobNormSq_real, frobNormSq_real]),
        Complex.ext second (by rw [frobNormSq_real, frobNormSq_real])⟩
    · rintro ⟨first, second⟩
      exact scalar_eq.mpr ⟨congrArg Complex.re first, congrArg Complex.re second⟩
  have lower_sum : (∑ a : Fin n, ∑ b : Fin n, lower a b) =
      3 * κ ^ (-1 / 3 : ℝ) *
        (∑ a : Fin n, ∑ b : Fin n, ‖hcProduct Θ a b (f.op a b)‖ ^ (4 / 3 : ℝ)) := by
    simp only [lower, Finset.mul_sum]
  have objective_eq := support_collinear_objective_eq_inverseScalePenalty Θ f hnd hcol
  have upper_sum : (∑ a : Fin n, ∑ b : Fin n, upper a b) = (objective Θ f).re := by
    rw [objective_eq, inverseScalePenalty_re_eq_sum]
  have sum_bound : (∑ a : Fin n, ∑ b : Fin n, lower a b) ≤
      ∑ a : Fin n, ∑ b : Fin n, upper a b :=
    Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => term_bound a b))
  refine ⟨objective_eq, by simpa only [lower_sum, upper_sum] using sum_bound, ?_⟩
  rw [← lower_sum, ← upper_sum]
  constructor
  · intro equality
    have gap_nonneg : ∀ a b, 0 ≤ upper a b - lower a b :=
      fun a b => sub_nonneg.mpr (term_bound a b)
    have gap_sum : (∑ a : Fin n, ∑ b : Fin n, (upper a b - lower a b)) = 0 := by
      simp only [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr equality.symm
    intro a b
    have inner_le : upper a b - lower a b ≤
        ∑ other : Fin n, (upper a other - lower a other) :=
      Finset.single_le_sum (fun other _ => gap_nonneg a other) (Finset.mem_univ b)
    have outer_le : (∑ other : Fin n, (upper a other - lower a other)) ≤
        ∑ row : Fin n, ∑ other : Fin n, (upper row other - lower row other) :=
      Finset.single_le_sum
        (fun row _ => Finset.sum_nonneg (fun other _ => gap_nonneg row other))
        (Finset.mem_univ a)
    have zero_gap : upper a b - lower a b = 0 :=
      le_antisymm (by simpa only [gap_sum] using inner_le.trans outer_le) (gap_nonneg a b)
    exact (term_eq a b).mp (sub_eq_zero.mp zero_gap).symm
  · intro balanced
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact (term_eq a b).mpr (balanced a b)

theorem support_collinear_inverse_rank_bound (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f)
    (htrace : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
      (∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = (κ : ℂ)) ∧
      (objective Θ f).re = (inverseScalePenalty Θ f).re ∧
      3 * κ ^ (-1 / 3 : ℝ) *
        (∑ a : Fin n, ∑ b : Fin n, ‖hcProduct Θ a b (f.op a b)‖ ^ (4 / 3 : ℝ)) ≤
          (objective Θ f).re ∧
      (3 * κ ^ (-1 / 3 : ℝ) *
        (∑ a : Fin n, ∑ b : Fin n, ‖hcProduct Θ a b (f.op a b)‖ ^ (4 / 3 : ℝ)) =
          (objective Θ f).re ↔
        ∀ a b : Fin n, frobNormSq (Θ.A a) = frobNormSq (Θ.B b) ∧
          frobNormSq (Θ.B b) = frobNormSq (Θ.C (f.op a b))) := by
  have hnd := support_nondegenerate_of_nonzero Θ f htrace
  have hids := (support_perfectCollinearity_iff_identities Θ f hnd).mp hcol
  obtain ⟨κ, hκ, hκle, hκconst⟩ :=
    support_normalized_rank_constant Θ f hids htrace
  exact ⟨κ, hκ, hκle, hκconst,
    support_collinear_inverse_rank_bound_of_constant Θ f hcol htrace κ hκ hκconst⟩

theorem support_collinear_dynamic_floor_eq_iff (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f)
    (htrace : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) ≠ 0)
    (κ : ℝ) (hκ : 0 < κ) (hκle : κ ≤ 1)
    (hκconst : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = (κ : ℂ)) :
    3 * (∑ a : Fin n, ∑ b : Fin n,
      ‖hcProduct Θ a b (f.op a b)‖ ^ (4 / 3 : ℝ)) = (objective Θ f).re ↔
      κ = 1 ∧ ∀ a b : Fin n,
        frobNormSq (Θ.A a) = frobNormSq (Θ.B b) ∧
        frobNormSq (Θ.B b) = frobNormSq (Θ.C (f.op a b)) := by
  obtain ⟨_, hbound, hequality⟩ :=
    support_collinear_inverse_rank_bound_of_constant Θ f hcol htrace κ hκ hκconst
  let amplitudeSum : ℝ := ∑ a : Fin n, ∑ b : Fin n,
    ‖hcProduct Θ a b (f.op a b)‖ ^ (4 / 3 : ℝ)
  have hsumpos : 0 < amplitudeSum := by
    apply Finset.sum_pos
    · intro a _
      apply Finset.sum_pos
      · intro b _
        exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (htrace a b)) _
      · exact Finset.univ_nonempty
    · exact Finset.univ_nonempty
  constructor
  · intro hfloor
    have hunit : κ = 1 := by
      by_contra hne
      have hstrict := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hκ
        (lt_of_le_of_ne hκle hne) (by norm_num : (-1 / 3 : ℝ) < 0)
      have hgap : 3 * amplitudeSum < 3 * κ ^ (-1 / 3 : ℝ) * amplitudeSum := by
        nlinarith [mul_pos (sub_pos.mpr hstrict) hsumpos]
      change 3 * amplitudeSum = (objective Θ f).re at hfloor
      change 3 * κ ^ (-1 / 3 : ℝ) * amplitudeSum ≤ (objective Θ f).re at hbound
      linarith
    refine ⟨hunit, hequality.mp ?_⟩
    simpa [hunit] using hfloor
  · rintro ⟨hunit, hbalanced⟩
    simpa [hunit] using hequality.mpr hbalanced

end
