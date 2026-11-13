/-
Floor attainment for arbitrary finite binary operations.

At an exactly feasible floor point, equal A slices are equivalent to identical
rows, and equal B slices are equivalent to identical columns. A cancellation
failure in one row or column propagates to a repeated entire column or row.
Consequently a target attaining the floor is either a group isotope or has
repeated rows or columns. "Redundancy" here is not a matrix-rank, tensor-rank,
homomorphism, or associative-isotope assertion.

Main results:
  * floor_group_isotope_or_redundancy
  * group_isotope_of_floor_injective_inputs
-/

import HyperCubeGroup.Foundation.GeneralCollinearity

open Matrix

noncomputable section

namespace FloorDichotomy

variable {n : ℕ} [NeZero n]

/-- Distinct labels with identical entire rows. -/
def RepeatedRows (f : BinOp n) : Prop :=
  ∃ first second : Fin n, first ≠ second ∧ ∀ column, f.op first column = f.op second column

/-- Distinct labels with identical entire columns. -/
def RepeatedColumns (f : BinOp n) : Prop :=
  ∃ first second : Fin n, first ≠ second ∧ ∀ row, f.op row first = f.op row second

theorem supported_product (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (row column : Fin n) :
    Θ.A row * Θ.B column = (Θ.C (f.op row column)).conjTranspose := by
  obtain ⟨_, _, hunit, hproduct⟩ := equality_rigidity_general f Θ hfeas hfloor row column
  have heq := congrArg (fun matrix => matrix * (Θ.C (f.op row column)).conjTranspose) hproduct
  simpa only [Matrix.mul_assoc, hunit, Matrix.mul_one, Matrix.one_mul] using heq

theorem inputA_eq_iff_rows_eq (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (first second : Fin n) :
    Θ.A first = Θ.A second ↔ ∀ column, f.op first column = f.op second column := by
  constructor
  · intro heq column
    have htrace : hcProduct Θ first column (f.op first column) =
        hcProduct Θ second column (f.op first column) := by
      simp only [hcProduct, heq]
    rw [hfeas, hfeas] at htrace
    by_contra hne
    simp [structureTensor, Ne.symm hne] at htrace
  · intro hrows
    let column : Fin n := ⟨0, NeZero.pos n⟩
    have heq : Θ.A first * Θ.B column = Θ.A second * Θ.B column := by
      rw [supported_product f Θ hfeas hfloor, supported_product f Θ hfeas hfloor, hrows]
    have hunit := (equality_rigidity_general f Θ hfeas hfloor first column).2.1
    have hcancel := congrArg (fun matrix => matrix * (Θ.B column).conjTranspose) heq
    simpa only [Matrix.mul_assoc, hunit, Matrix.mul_one] using hcancel

theorem inputB_eq_iff_columns_eq (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (first second : Fin n) :
    Θ.B first = Θ.B second ↔ ∀ row, f.op row first = f.op row second := by
  constructor
  · intro heq row
    have htrace : hcProduct Θ row first (f.op row first) =
        hcProduct Θ row second (f.op row first) := by
      simp only [hcProduct, heq]
    rw [hfeas, hfeas] at htrace
    by_contra hne
    simp [structureTensor, Ne.symm hne] at htrace
  · intro hcolumns
    let row : Fin n := ⟨0, NeZero.pos n⟩
    have heq : Θ.A row * Θ.B first = Θ.A row * Θ.B second := by
      rw [supported_product f Θ hfeas hfloor, supported_product f Θ hfeas hfloor, hcolumns]
    have hunit := mul_eq_one_comm.mp (equality_rigidity_general f Θ hfeas hfloor row first).1
    have hcancel := congrArg (fun matrix => (Θ.A row).conjTranspose * matrix) heq
    simpa only [← Matrix.mul_assoc, hunit, Matrix.one_mul] using hcancel

theorem row_collision_implies_columns_eq (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (row first second : Fin n) (hcollision : f.op row first = f.op row second) :
    ∀ otherRow, f.op otherRow first = f.op otherRow second := by
  apply (inputB_eq_iff_columns_eq f Θ hfeas hfloor first second).mp
  have heq : Θ.A row * Θ.B first = Θ.A row * Θ.B second := by
    rw [supported_product f Θ hfeas hfloor, supported_product f Θ hfeas hfloor, hcollision]
  have hunit := mul_eq_one_comm.mp (equality_rigidity_general f Θ hfeas hfloor row first).1
  have hcancel := congrArg (fun matrix => (Θ.A row).conjTranspose * matrix) heq
  simpa only [← Matrix.mul_assoc, hunit, Matrix.one_mul] using hcancel

theorem column_collision_implies_rows_eq (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (column first second : Fin n) (hcollision : f.op first column = f.op second column) :
    ∀ otherColumn, f.op first otherColumn = f.op second otherColumn := by
  apply (inputA_eq_iff_rows_eq f Θ hfeas hfloor first second).mp
  have heq : Θ.A first * Θ.B column = Θ.A second * Θ.B column := by
    rw [supported_product f Θ hfeas hfloor, supported_product f Θ hfeas hfloor, hcollision]
  have hunit := (equality_rigidity_general f Θ hfeas hfloor first column).2.1
  have hcancel := congrArg (fun matrix => matrix * (Θ.B column).conjTranspose) heq
  simpa only [Matrix.mul_assoc, hunit, Matrix.mul_one] using hcancel

theorem quasigroup_of_floor_no_redundancy (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (hrows : ¬ RepeatedRows f) (hcolumns : ¬ RepeatedColumns f) : IsQuasigroup f := by
  constructor
  · intro row
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, rfl⟩
    intro first second hcollision
    by_contra hne
    exact hcolumns ⟨first, second, hne,
      row_collision_implies_columns_eq f Θ hfeas hfloor row first second hcollision⟩
  · intro column
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, rfl⟩
    intro first second hcollision
    by_contra hne
    exact hrows ⟨first, second, hne,
      column_collision_implies_rows_eq f Θ hfeas hfloor column first second hcollision⟩

theorem group_isotope_of_floor_no_redundancy (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (hrows : ¬ RepeatedRows f) (hcolumns : ¬ RepeatedColumns f) : IsGroupIsotope f := by
  have hq := quasigroup_of_floor_no_redundancy f Θ hfeas hfloor hrows hcolumns
  have hnd := factorizes_implies_nondegenerate Θ f hq hfeas
  have hcol := equality_rigidity_implies_perfect_collinearity f Θ hfeas hnd hfloor
  exact general_collinear_implies_group_isotope f hq ⟨Θ, hcol, hfeas⟩

/-- Floor attainment forces a group isotope or an identical pair of rows or columns.
The redundant branch makes no homomorphism or associative-isotope claim. -/
theorem floor_group_isotope_or_redundancy (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2) :
    IsGroupIsotope f ∨ RepeatedRows f ∨ RepeatedColumns f := by
  by_cases hrows : RepeatedRows f
  · exact Or.inr (Or.inl hrows)
  by_cases hcolumns : RepeatedColumns f
  · exact Or.inr (Or.inr hcolumns)
  exact Or.inl (group_isotope_of_floor_no_redundancy f Θ hfeas hfloor hrows hcolumns)

/-- Injectivity of both input families rules out the redundant branch. -/
theorem group_isotope_of_floor_injective_inputs (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (hA : Function.Injective Θ.A) (hB : Function.Injective Θ.B) : IsGroupIsotope f := by
  apply group_isotope_of_floor_no_redundancy f Θ hfeas hfloor
  · rintro ⟨first, second, hne, hrows⟩
    exact hne (hA ((inputA_eq_iff_rows_eq f Θ hfeas hfloor first second).mpr hrows))
  · rintro ⟨first, second, hne, hcolumns⟩
    exact hne (hB ((inputB_eq_iff_columns_eq f Θ hfeas hfloor first second).mpr hcolumns))

end FloorDichotomy
