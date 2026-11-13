import HyperCubeGroup.Foundation.UniformGap
import HyperCubeGroup.Foundation.SupportGeometry
import HyperCubeGroup.Foundation.SupportDecomposition

open Matrix BigOperators

noncomputable section

variable {n : ℕ} [NeZero n]

/-- Unitary collinearity with unitarity required only for supported output slices. -/
structure SupportUnitaryCollinearFactorization (Θ : HCParams n) (f : BinOp n) : Prop where
  feasible : Factorizes Θ f
  collinear : PerfectCollinearity Θ f
  unitaryA : ∀ a : Fin n, Θ.A a * (Θ.A a).conjTranspose = 1
  unitaryB : ∀ b : Fin n, Θ.B b * (Θ.B b).conjTranspose = 1
  unitaryC : ∀ a b : Fin n,
    Θ.C (f.op a b) * (Θ.C (f.op a b)).conjTranspose = 1

private theorem support_unitary_norm (factor : Matrix (Fin n) (Fin n) ℂ)
    (hunitary : factor * factor.conjTranspose = 1) : frobNormSq factor = 1 := by
  unfold frobNormSq frobInner
  rw [mul_eq_one_comm.mp hunitary, Matrix.trace_one, Fintype.card_fin]
  field_simp [(Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : ℂ) ≠ 0)]

omit [NeZero n] in
private theorem support_unitary_mul (first second : Matrix (Fin n) (Fin n) ℂ)
    (hfirst : first * first.conjTranspose = 1)
    (hsecond : second * second.conjTranspose = 1) :
    (first * second) * (first * second).conjTranspose = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc second, hsecond, Matrix.one_mul, hfirst]

private theorem support_unitary_trace_eq_one (factor : Matrix (Fin n) (Fin n) ℂ)
    (hunitary : factor * factor.conjTranspose = 1)
    (htrace : (1 / (n : ℂ)) * factor.trace = 1) : factor = 1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have htr : factor.trace = (n : ℂ) := by
    rw [one_div, inv_mul_eq_div, div_eq_iff hn, one_mul] at htrace
    exact htrace
  suffices hnorm : frobNormSq (factor - 1) = 0 by
    exact sub_eq_zero.mp ((frobNormSq_eq_zero_iff _).mp hnorm)
  unfold frobNormSq frobInner
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  have hexpand : (factor.conjTranspose - 1) * (factor - 1) =
      factor.conjTranspose * factor - factor.conjTranspose - factor + 1 := by
    simp only [sub_mul, mul_sub, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [hexpand, mul_eq_one_comm.mp hunitary]
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]
  rw [Matrix.trace_conjTranspose, htr, star_natCast]
  ring

theorem SupportUnitaryCollinearFactorization.support_product
    {Θ : HCParams n} {f : BinOp n} (huc : SupportUnitaryCollinearFactorization Θ f)
    (a b : Fin n) : Θ.A a * Θ.B b * Θ.C (f.op a b) = 1 := by
  apply support_unitary_trace_eq_one
  · exact support_unitary_mul _ _
      (support_unitary_mul _ _ (huc.unitaryA a) (huc.unitaryB b)) (huc.unitaryC a b)
  · have htrace := huc.feasible a b (f.op a b)
    simpa only [hcProduct, structureTensor, if_pos rfl] using htrace

omit [NeZero n] in
private theorem support_product_pair_identities (Θ : HCParams n) (f : BinOp n)
    (hA : ∀ a, Θ.A a * (Θ.A a).conjTranspose = 1)
    (hC : ∀ a b, Θ.C (f.op a b) * (Θ.C (f.op a b)).conjTranspose = 1)
    (hproduct : ∀ a b, Θ.A a * Θ.B b * Θ.C (f.op a b) = 1) (a b : Fin n) :
    Θ.B b * Θ.C (f.op a b) = (Θ.A a).conjTranspose ∧
    Θ.C (f.op a b) * Θ.A a = (Θ.B b).conjTranspose ∧
    Θ.A a * Θ.B b = (Θ.C (f.op a b)).conjTranspose := by
  have hleft : (Θ.A a).conjTranspose * Θ.A a = 1 := mul_eq_one_comm.mp (hA a)
  have hBC : Θ.B b * Θ.C (f.op a b) = (Θ.A a).conjTranspose := by
    have h := congrArg ((Θ.A a).conjTranspose * ·) (hproduct a b)
    simpa only [← Matrix.mul_assoc, hleft, Matrix.one_mul, Matrix.mul_one] using h
  have hAB : Θ.A a * Θ.B b = (Θ.C (f.op a b)).conjTranspose := by
    have h := congrArg (· * (Θ.C (f.op a b)).conjTranspose) (hproduct a b)
    simpa only [Matrix.mul_assoc, hC a b, Matrix.mul_one, Matrix.one_mul] using h
  have hCeq : (Θ.B b).conjTranspose * (Θ.A a).conjTranspose = Θ.C (f.op a b) := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hAB
  refine ⟨hBC, ?_, hAB⟩
  rw [← hCeq, Matrix.mul_assoc, hleft, Matrix.mul_one]

private theorem support_collinear_of_unitary_product (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f)
    (hA : ∀ a, Θ.A a * (Θ.A a).conjTranspose = 1)
    (hB : ∀ b, Θ.B b * (Θ.B b).conjTranspose = 1)
    (hC : ∀ a b, Θ.C (f.op a b) * (Θ.C (f.op a b)).conjTranspose = 1)
    (hproduct : ∀ a b, Θ.A a * Θ.B b * Θ.C (f.op a b) = 1) :
    PerfectCollinearity Θ f := by
  apply support_identities_implies_perfectCollinearity
  have htrace : ∀ a b, hcProduct Θ a b (f.op a b) = 1 := by
    intro a b
    rw [hfeas]; simp [structureTensor]
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    dsimp only
    rw [htrace, support_unitary_norm _ (hA a), div_one, one_smul]
    exact (support_product_pair_identities Θ f hA hC hproduct a b).1
  · intro a b
    dsimp only
    rw [htrace, support_unitary_norm _ (hB b), div_one, one_smul]
    exact (support_product_pair_identities Θ f hA hC hproduct a b).2.1
  · intro a b
    dsimp only
    rw [htrace, support_unitary_norm _ (hC a b), div_one, one_smul]
    exact (support_product_pair_identities Θ f hA hC hproduct a b).2.2

theorem support_uc_objective_value (Θ : HCParams n) (f : BinOp n)
    (huc : SupportUnitaryCollinearFactorization Θ f) :
    (objective Θ f).re = 3 * (n : ℝ) ^ 2 := by
  have hterm : ∀ a b : Fin n,
      frobNormSq (Θ.B b * Θ.C (f.op a b)) +
      frobNormSq (Θ.C (f.op a b) * Θ.A a) +
      frobNormSq (Θ.A a * Θ.B b) = 3 := by
    intro a b
    obtain ⟨hBC, hCA, hAB⟩ := support_product_pair_identities Θ f
      huc.unitaryA huc.unitaryC huc.support_product a b
    rw [hBC, hCA, hAB, frobNormSq_conjTranspose, frobNormSq_conjTranspose,
      frobNormSq_conjTranspose, support_unitary_norm _ (huc.unitaryA a),
      support_unitary_norm _ (huc.unitaryB b), support_unitary_norm _ (huc.unitaryC a b)]
    norm_num
  rw [objective_eq_sum_support]
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  ring

theorem support_absolute_feasible_bound_rigidity (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) :
    (objective Θ f).re = 3 * (n : ℝ) ^ 2 ↔
      SupportUnitaryCollinearFactorization Θ f := by
  refine ⟨?_, support_uc_objective_value Θ f⟩
  intro hfloor
  have hlocal := equality_rigidity_general f Θ hfeas hfloor
  have hA := fun a => (hlocal a a).1
  have hB := fun b => (hlocal b b).2.1
  have hC := fun a b => (hlocal a b).2.2.1
  have hproduct := fun a b => (hlocal a b).2.2.2
  exact ⟨hfeas, support_collinear_of_unitary_product Θ f hfeas hA hB hC hproduct,
    hA, hB, hC⟩

theorem support_nondegenerate_of_factorizes (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) : SupportNondegenerate Θ f := by
  apply support_nondegenerate_of_nonzero Θ f
  intro a b
  rw [hfeas]
  simp [structureTensor]

theorem SupportUnitaryCollinearFactorization.supportNondegenerate
    {Θ : HCParams n} {f : BinOp n} (huc : SupportUnitaryCollinearFactorization Θ f) :
    SupportNondegenerate Θ f :=
  support_nondegenerate_of_factorizes Θ f huc.feasible

theorem SupportUnitaryCollinearFactorization.of_unitary_product
    (Θ : HCParams n) (f : BinOp n) (hfeas : Factorizes Θ f)
    (hA : ∀ a, Θ.A a * (Θ.A a).conjTranspose = 1)
    (hB : ∀ b, Θ.B b * (Θ.B b).conjTranspose = 1)
    (hC : ∀ a b, Θ.C (f.op a b) * (Θ.C (f.op a b)).conjTranspose = 1)
    (hproduct : ∀ a b, Θ.A a * Θ.B b * Θ.C (f.op a b) = 1) :
    SupportUnitaryCollinearFactorization Θ f :=
  ⟨hfeas, support_collinear_of_unitary_product Θ f hfeas hA hB hC hproduct, hA, hB, hC⟩

/-- Feasibility and supported unitarity already force the product identities and collinearity. -/
theorem SupportUnitaryCollinearFactorization.of_unitaries
    (Θ : HCParams n) (f : BinOp n) (hfeas : Factorizes Θ f)
    (hA : ∀ a, Θ.A a * (Θ.A a).conjTranspose = 1)
    (hB : ∀ b, Θ.B b * (Θ.B b).conjTranspose = 1)
    (hC : ∀ a b, Θ.C (f.op a b) * (Θ.C (f.op a b)).conjTranspose = 1) :
    SupportUnitaryCollinearFactorization Θ f := by
  apply SupportUnitaryCollinearFactorization.of_unitary_product Θ f hfeas hA hB hC
  intro a b
  apply support_unitary_trace_eq_one
  · exact support_unitary_mul _ _ (support_unitary_mul _ _ (hA a) (hB b)) (hC a b)
  · have htrace := hfeas a b (f.op a b)
    simpa only [hcProduct, structureTensor, if_pos rfl] using htrace

omit [NeZero n] in
theorem UnitaryCollinear.toSupport {Θ : HCParams n} {f : BinOp n}
    (huc : UnitaryCollinear Θ f) : SupportUnitaryCollinearFactorization Θ f :=
  ⟨huc.feasible, huc.collinear, huc.unitaryA, huc.unitaryB,
    fun a b => huc.unitaryC (f.op a b)⟩

theorem SupportUnitaryCollinearFactorization.of_quasigroup
    {Θ : HCParams n} {f : BinOp n} (huc : SupportUnitaryCollinearFactorization Θ f)
    (hq : IsQuasigroup f) : UnitaryCollinear Θ f := by
  refine ⟨huc.collinear, huc.feasible, huc.unitaryA, huc.unitaryB, ?_⟩
  intro output
  obtain ⟨column, hcolumn⟩ := (hq.left_cancel (0 : Fin n)).surjective output
  simpa only [hcolumn] using huc.unitaryC 0 column

theorem support_unitary_collinear_iff_unitary_collinear (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) :
    SupportUnitaryCollinearFactorization Θ f ↔ UnitaryCollinear Θ f :=
  ⟨fun huc => huc.of_quasigroup hq, UnitaryCollinear.toSupport⟩

theorem support_floor_iff_feasible_unitary_product (Θ : HCParams n) (f : BinOp n) :
    (Factorizes Θ f ∧ (objective Θ f).re = 3 * (n : ℝ) ^ 2) ↔
      Factorizes Θ f ∧
      (∀ a, Θ.A a * (Θ.A a).conjTranspose = 1) ∧
      (∀ b, Θ.B b * (Θ.B b).conjTranspose = 1) ∧
      (∀ a b, Θ.C (f.op a b) * (Θ.C (f.op a b)).conjTranspose = 1) ∧
      (∀ a b, Θ.A a * Θ.B b * Θ.C (f.op a b) = 1) := by
  constructor
  · rintro ⟨hfeas, hfloor⟩
    have huc := (support_absolute_feasible_bound_rigidity f Θ hfeas).mp hfloor
    exact ⟨hfeas, huc.unitaryA, huc.unitaryB, huc.unitaryC, huc.support_product⟩
  · rintro ⟨hfeas, hA, hB, hC, hproduct⟩
    exact ⟨hfeas, support_uc_objective_value Θ f
      (SupportUnitaryCollinearFactorization.of_unitary_product Θ f hfeas hA hB hC hproduct)⟩

theorem support_floor_iff_feasible_unitary (Θ : HCParams n) (f : BinOp n) :
    (Factorizes Θ f ∧ (objective Θ f).re = 3 * (n : ℝ) ^ 2) ↔
      Factorizes Θ f ∧
      (∀ a, Θ.A a * (Θ.A a).conjTranspose = 1) ∧
      (∀ b, Θ.B b * (Θ.B b).conjTranspose = 1) ∧
      (∀ a b, Θ.C (f.op a b) * (Θ.C (f.op a b)).conjTranspose = 1) := by
  constructor
  · rintro ⟨hfeas, hfloor⟩
    have huc := (support_absolute_feasible_bound_rigidity f Θ hfeas).mp hfloor
    exact ⟨hfeas, huc.unitaryA, huc.unitaryB, huc.unitaryC⟩
  · rintro ⟨hfeas, hA, hB, hC⟩
    exact ⟨hfeas, support_uc_objective_value Θ f
      (SupportUnitaryCollinearFactorization.of_unitaries Θ f hfeas hA hB hC)⟩

theorem support_exists_gap_of_no_unitary_collinear (f : BinOp n)
    (hexcluded : ¬ ∃ Θ : HCParams n, SupportUnitaryCollinearFactorization Θ f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Θ : HCParams n, Factorizes Θ f →
      3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ f).re := by
  apply PositiveGap.exists_gap_of_no_floor f
  intro Θ hfeas hfloor
  exact hexcluded ⟨Θ, (support_absolute_feasible_bound_rigidity f Θ hfeas).mp hfloor⟩

theorem support_exists_infimum_gap_of_no_unitary_collinear (f : BinOp n)
    (hexcluded : ¬ ∃ Θ : HCParams n, SupportUnitaryCollinearFactorization Θ f) :
    ∃ ε : ℝ, 0 < ε ∧
      3 * (n : ℝ) ^ 2 + ε ≤ sInf (PositiveGap.feasibleObjectiveValues f) := by
  apply PositiveGap.exists_infimum_gap_of_no_floor f
  intro Θ hfeas hfloor
  exact hexcluded ⟨Θ, (support_absolute_feasible_bound_rigidity f Θ hfeas).mp hfloor⟩

namespace SupportUnitaryRegression

def constantOperation : BinOp 2 := ⟨fun _ _ => 0⟩

def constantParams : HCParams 2 :=
  ⟨fun _ => 1, fun _ => 1, fun output => if output = 0 then 1 else 0⟩

theorem constantParams_factorizes : Factorizes constantParams constantOperation := by
  intro a b output
  by_cases houtput : output = 0
  · subst output
    norm_num [constantParams, constantOperation, hcProduct, structureTensor, Matrix.trace_one]
  · simp [constantParams, constantOperation, hcProduct, structureTensor,
      houtput, Ne.symm houtput]

theorem constantParams_support_unitary_collinear :
    SupportUnitaryCollinearFactorization constantParams constantOperation := by
  apply SupportUnitaryCollinearFactorization.of_unitaries
    constantParams constantOperation constantParams_factorizes
  · intro a; simp [constantParams]
  · intro b; simp [constantParams]
  · intro a b; simp [constantParams, constantOperation]

theorem constantParams_unused_output_zero : constantParams.C 1 = 0 := by
  simp [constantParams]

theorem constantParams_not_unitary_collinear :
    ¬ UnitaryCollinear constantParams constantOperation := by
  intro hlegacy
  have hzero : (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simpa only [constantParams_unused_output_zero, Matrix.conjTranspose_zero,
      Matrix.zero_mul] using hlegacy.unitaryC 1
  have hentry := congrArg (fun factor : Matrix (Fin 2) (Fin 2) ℂ => factor 0 0) hzero
  norm_num at hentry

theorem constantParams_objective_value : (objective constantParams constantOperation).re = 12 := by
  have hfloor := support_uc_objective_value constantParams constantOperation
    constantParams_support_unitary_collinear
  norm_num at hfloor
  exact hfloor

theorem support_strictly_generalizes_legacy :
    ∃ (f : BinOp 2) (Θ : HCParams 2),
      SupportUnitaryCollinearFactorization Θ f ∧ ¬ UnitaryCollinear Θ f :=
  ⟨constantOperation, constantParams, constantParams_support_unitary_collinear,
    constantParams_not_unitary_collinear⟩

end SupportUnitaryRegression

end
