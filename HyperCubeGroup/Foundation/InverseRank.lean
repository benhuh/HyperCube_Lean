import HyperCubeGroup.Foundation.CollinearManifold

open Matrix BigOperators Finset

noncomputable section

variable {n : ℕ} [NeZero n]

theorem inverseRank_frobNormSq_cast (factor : Matrix (Fin n) (Fin n) ℂ) :
    ((frobNormSq factor).re : ℂ) = frobNormSq factor := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, frobNormSq_real]

theorem inverseRank_trace_norm_sq (trace : ℂ) :
    trace * starRingEnd ℂ trace = ((‖trace‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

theorem inverseRank_product (Θ : HCParams n) (f : BinOp n) (κ : ℝ)
    (htrace : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) ≠ 0)
    (hκconst : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = (κ : ℂ))
    (a b : Fin n) :
    (frobNormSq (Θ.A a)).re * (frobNormSq (Θ.B b)).re *
      (frobNormSq (Θ.C (f.op a b))).re =
        κ * ‖hcProduct Θ a b (f.op a b)‖ ^ 2 := by
  have denominator_ne : hcProduct Θ a b (f.op a b) *
      starRingEnd ℂ (hcProduct Θ a b (f.op a b)) ≠ 0 :=
    mul_ne_zero (htrace a b) ((map_ne_zero (starRingEnd ℂ)).mpr (htrace a b))
  have product := (div_eq_iff denominator_ne).mp (hκconst a b)
  rw [inverseRank_trace_norm_sq] at product
  rw [← inverseRank_frobNormSq_cast (Θ.A a),
    ← inverseRank_frobNormSq_cast (Θ.B b),
    ← inverseRank_frobNormSq_cast (Θ.C (f.op a b))] at product
  exact_mod_cast product

theorem inverseScalePenalty_re_eq_sum (Θ : HCParams n) (f : BinOp n) :
    (inverseScalePenalty Θ f).re =
      ∑ a : Fin n, ∑ b : Fin n,
        ‖hcProduct Θ a b (f.op a b)‖ ^ 2 *
          (1 / (frobNormSq (Θ.A a)).re +
           1 / (frobNormSq (Θ.B b)).re +
           1 / (frobNormSq (Θ.C (f.op a b))).re) := by
  unfold inverseScalePenalty
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  dsimp only
  rw [inverseRank_trace_norm_sq,
    ← inverseRank_frobNormSq_cast (Θ.A a),
    ← inverseRank_frobNormSq_cast (Θ.B b),
    ← inverseRank_frobNormSq_cast (Θ.C (f.op a b))]
  norm_cast

theorem collinear_objective_eq_inverseScalePenalty (Θ : HCParams n) (f : BinOp n)
    (hnd : Nondegenerate Θ) (hcol : PerfectCollinearity Θ f) :
    (objective Θ f).re = (inverseScalePenalty Θ f).re := by
  rw [decomposition Θ f hnd, hcol, add_zero]

theorem collinear_inverse_rank_bound_of_constant (Θ : HCParams n) (f : BinOp n)
  (hq : IsQuasigroup f)
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
      ∀ a b c : Fin n, frobNormSq (Θ.A a) = frobNormSq (Θ.B b) ∧
        frobNormSq (Θ.B b) = frobNormSq (Θ.C c)) := by
  have hnd := nonzero_supported_predictions_implies_nondegenerate Θ f hq htrace
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
      (frobNormSq_re_pos_of_ne_zero _ (hnd.C_pos (f.op a b)))
      (norm_pos_iff.mpr (htrace a b)) hκ (inverseRank_product Θ f κ htrace hκconst a b)
  have term_eq : ∀ a b, lower a b = upper a b ↔
      frobNormSq (Θ.A a) = frobNormSq (Θ.B b) ∧
        frobNormSq (Θ.B b) = frobNormSq (Θ.C (f.op a b)) := by
    intro a b
    have scalar_eq := scalar_inverse_rank_eq_iff
      (frobNormSq_re_pos_of_ne_zero _ (hnd.A_pos a))
      (frobNormSq_re_pos_of_ne_zero _ (hnd.B_pos b))
      (frobNormSq_re_pos_of_ne_zero _ (hnd.C_pos (f.op a b)))
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
  have objective_eq := collinear_objective_eq_inverseScalePenalty Θ f hnd hcol
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
    have supported_eq : ∀ a b, frobNormSq (Θ.A a) = frobNormSq (Θ.B b) ∧
        frobNormSq (Θ.B b) = frobNormSq (Θ.C (f.op a b)) := by
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
    intro a b c
    obtain ⟨other, hop⟩ := (hq.left_cancel a).2 c
    have first := (supported_eq a b).1
    have second := supported_eq a other
    rw [hop] at second
    exact ⟨first, first.symm.trans (second.1.trans second.2)⟩
  · intro balanced
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact (term_eq a b).mpr (balanced a b (f.op a b))

theorem collinear_inverse_rank_bound (Θ : HCParams n) (f : BinOp n)
  (hq : IsQuasigroup f)
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
        ∀ a b c : Fin n, frobNormSq (Θ.A a) = frobNormSq (Θ.B b) ∧
            frobNormSq (Θ.B b) = frobNormSq (Θ.C c)) := by
  have hnd := nonzero_supported_predictions_implies_nondegenerate Θ f hq htrace
  obtain ⟨κ, hκ, hκle, hκconst⟩ :=
    normalized_rank_constant_of_nonzero Θ f hq hnd hcol htrace
  exact ⟨κ, hκ, hκle, hκconst,
    collinear_inverse_rank_bound_of_constant Θ f hq hcol htrace κ hκ hκconst⟩

theorem collinear_dynamic_floor_eq_iff (Θ : HCParams n) (f : BinOp n)
  (hq : IsQuasigroup f)
    (hcol : PerfectCollinearity Θ f)
    (htrace : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) ≠ 0)
    (κ : ℝ) (hκ : 0 < κ) (hκle : κ ≤ 1)
    (hκconst : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = (κ : ℂ)) :
    3 * (∑ a : Fin n, ∑ b : Fin n,
      ‖hcProduct Θ a b (f.op a b)‖ ^ (4 / 3 : ℝ)) = (objective Θ f).re ↔
      κ = 1 ∧ ∀ a b c : Fin n,
        frobNormSq (Θ.A a) = frobNormSq (Θ.B b) ∧
        frobNormSq (Θ.B b) = frobNormSq (Θ.C c) := by
  obtain ⟨_, hbound, hequality⟩ :=
    collinear_inverse_rank_bound_of_constant Θ f hq hcol htrace κ hκ hκconst
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
