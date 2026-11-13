import HyperCubeGroup.Foundation.ReducedTable
import HyperCubeGroup.Foundation.SupportUnitary

/-!
Exact floor attainment through row and column equality quotients. Reduced factors
are unitary, multiply to output adjoints, and have trace-orthonormal output codes.
These data are necessary and sufficient for full exact reconstruction at the floor.
No group structure is asserted for a general reduced table, and no MDL or
reversible-computation interpretation is assumed.
-/

noncomputable section

namespace FloorDichotomy

variable {n : ℕ} [NeZero n]

structure ReducedUnitaryFactorization (f : BinOp n) where
  rowFactor : RowClass f → Matrix (Fin n) (Fin n) ℂ
  columnFactor : ColumnClass f → Matrix (Fin n) (Fin n) ℂ
  outputFactor : UsedOutput f → Matrix (Fin n) (Fin n) ℂ
  row_unitary : ∀ row, rowFactor row * (rowFactor row).conjTranspose = 1
  column_unitary : ∀ column, columnFactor column * (columnFactor column).conjTranspose = 1
  output_unitary : ∀ output, outputFactor output * (outputFactor output).conjTranspose = 1
  product : ∀ row column,
    rowFactor row * columnFactor column = (outputFactor (reducedTable f row column)).conjTranspose
  orthonormal : ∀ first second,
    (1 / (n : ℂ)) * ((outputFactor first).conjTranspose * outputFactor second).trace =
      if first = second then 1 else 0

def ReducedUnitaryFactorization.of_floor (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ) ^ 2) :
    ReducedUnitaryFactorization f := by
  classical
  let rows : RowClass f → Matrix (Fin n) (Fin n) ℂ :=
    Quotient.lift Θ.A (fun first second heq =>
      (inputA_eq_iff_rows_eq f Θ hfeas hfloor first second).mpr heq)
  let columns : ColumnClass f → Matrix (Fin n) (Fin n) ℂ :=
    Quotient.lift Θ.B (fun first second heq =>
      (inputB_eq_iff_columns_eq f Θ hfeas hfloor first second).mpr heq)
  have huc := (support_absolute_feasible_bound_rigidity f Θ hfeas).mp hfloor
  refine ⟨rows, columns, fun output => Θ.C output.val, ?_, ?_, ?_, ?_, ?_⟩
  · intro row
    induction row using Quotient.inductionOn with
    | h row => exact huc.unitaryA row
  · intro column
    induction column using Quotient.inductionOn with
    | h column => exact huc.unitaryB column
  · intro output
    obtain ⟨row, column, heq⟩ := output.property
    dsimp only
    rw [← heq]
    exact huc.unitaryC row column
  · intro row column
    induction row using Quotient.inductionOn with
    | h row =>
      induction column using Quotient.inductionOn with
      | h column => exact supported_product f Θ hfeas hfloor row column
  · exact used_output_trace_orthonormal f Θ hfeas hfloor

def ReducedUnitaryFactorization.params {f : BinOp n}
    (data : ReducedUnitaryFactorization f) : HCParams n := by
  classical
  exact {
    A := fun row => data.rowFactor (rowClass f row)
    B := fun column => data.columnFactor (columnClass f column)
    C := fun output => if hused : ∃ row column, f.op row column = output then
      data.outputFactor ⟨output, hused⟩ else 0
  }

omit [NeZero n] in
theorem ReducedUnitaryFactorization.params_factorizes {f : BinOp n}
    (data : ReducedUnitaryFactorization f) : Factorizes data.params f := by
  classical
  intro row column output
  change (1 / (n : ℂ)) *
    (data.rowFactor (rowClass f row) * data.columnFactor (columnClass f column) *
      (if hused : ∃ first second, f.op first second = output then
        data.outputFactor ⟨output, hused⟩ else 0)).trace = structureTensor f row column output
  by_cases hused : ∃ first second, f.op first second = output
  · rw [dif_pos hused, data.product]
    simpa only [structureTensor, Subtype.ext_iff, reducedTable_mk] using
      data.orthonormal (reducedTable f (rowClass f row) (columnClass f column)) ⟨output, hused⟩
  · have hne : f.op row column ≠ output := fun heq => hused ⟨row, column, heq⟩
    simp [dif_neg hused, structureTensor, hne]

theorem ReducedUnitaryFactorization.params_support_unitary {f : BinOp n}
    (data : ReducedUnitaryFactorization f) :
    SupportUnitaryCollinearFactorization data.params f := by
  apply SupportUnitaryCollinearFactorization.of_unitaries _ _ data.params_factorizes
  · intro row
    exact data.row_unitary (rowClass f row)
  · intro column
    exact data.column_unitary (columnClass f column)
  · intro row column
    classical
    dsimp only [ReducedUnitaryFactorization.params]
    simp only [dif_pos (show ∃ first second, f.op first second = f.op row column from
      ⟨row, column, rfl⟩)]
    exact data.output_unitary _

theorem ReducedUnitaryFactorization.params_floor {f : BinOp n}
    (data : ReducedUnitaryFactorization f) :
    (objective data.params f).re = 3 * (n : ℝ) ^ 2 :=
  support_uc_objective_value _ _ data.params_support_unitary

theorem floor_iff_reduced_unitary_factorization (f : BinOp n) :
    (∃ Θ : HCParams n, Factorizes Θ f ∧ (objective Θ f).re = 3 * (n : ℝ) ^ 2) ↔
      Nonempty (ReducedUnitaryFactorization f) := by
  constructor
  · rintro ⟨Θ, hfeas, hfloor⟩
    exact ⟨ReducedUnitaryFactorization.of_floor f Θ hfeas hfloor⟩
  · rintro ⟨data⟩
    exact ⟨data.params, data.params_factorizes, data.params_floor⟩

theorem ReducedUnitaryFactorization.rowFactor_injective {f : BinOp n}
    (data : ReducedUnitaryFactorization f) : Function.Injective data.rowFactor := by
  intro first second
  induction first using Quotient.inductionOn with
  | h first =>
    induction second using Quotient.inductionOn with
    | h second =>
      intro heq
      apply Quotient.sound
      exact (inputA_eq_iff_rows_eq f data.params data.params_factorizes
        data.params_floor first second).mp heq

theorem ReducedUnitaryFactorization.columnFactor_injective {f : BinOp n}
    (data : ReducedUnitaryFactorization f) : Function.Injective data.columnFactor := by
  intro first second
  induction first using Quotient.inductionOn with
  | h first =>
    induction second using Quotient.inductionOn with
    | h second =>
      intro heq
      apply Quotient.sound
      exact (inputB_eq_iff_columns_eq f data.params data.params_factorizes
        data.params_floor first second).mp heq

omit [NeZero n] in
theorem ReducedUnitaryFactorization.outputFactor_injective {f : BinOp n}
    (data : ReducedUnitaryFactorization f) : Function.Injective data.outputFactor := by
  classical
  intro first second heq
  by_contra hne
  have hcross := data.orthonormal first second
  have hself := data.orthonormal first first
  rw [← heq, if_neg hne] at hcross
  simp only [ite_true] at hself
  exact zero_ne_one (hcross.symm.trans hself)

theorem floor_factorization_descends (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ) ^ 2) :
    ∃ data : ReducedUnitaryFactorization f,
      (∀ row, data.rowFactor (rowClass f row) = Θ.A row) ∧
      (∀ column, data.columnFactor (columnClass f column) = Θ.B column) ∧
      (∀ output : UsedOutput f, data.outputFactor output = Θ.C output.val) :=
  ⟨ReducedUnitaryFactorization.of_floor f Θ hfeas hfloor,
    (fun _ => rfl), (fun _ => rfl), (fun _ => rfl)⟩

theorem reduced_unitary_factorization_iff_group_isotope (f : BinOp n)
    (hrows : ¬ RepeatedRows f) (hcolumns : ¬ RepeatedColumns f) :
    Nonempty (ReducedUnitaryFactorization f) ↔ IsGroupIsotope f := by
  constructor
  · rintro ⟨data⟩
    exact group_isotope_of_floor_no_redundancy f data.params data.params_factorizes
      data.params_floor hrows hcolumns
  · intro hgroup
    obtain ⟨Θ, huc⟩ := group_isotope_admits_unitary_collinear f hgroup.isQuasigroup hgroup
    exact ⟨ReducedUnitaryFactorization.of_floor f Θ huc.feasible
      (support_uc_objective_value Θ f huc.toSupport)⟩

theorem no_reduced_unitary_factorization_iff_gap (f : BinOp n) :
    ¬ Nonempty (ReducedUnitaryFactorization f) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ Θ : HCParams n, Factorizes Θ f →
        3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ f).re := by
  constructor
  · intro hexcluded
    apply PositiveGap.exists_gap_of_no_floor f
    intro Θ hfeas hfloor
    exact hexcluded ⟨ReducedUnitaryFactorization.of_floor f Θ hfeas hfloor⟩
  · rintro ⟨ε, hpositive, hgap⟩ ⟨data⟩
    have hbound := hgap data.params data.params_factorizes
    rw [data.params_floor] at hbound
    linarith

theorem infimum_gap_of_no_reduced_unitary_factorization (f : BinOp n)
    (hexcluded : ¬ Nonempty (ReducedUnitaryFactorization f)) :
    ∃ ε : ℝ, 0 < ε ∧
      3 * (n : ℝ) ^ 2 + ε ≤ sInf (PositiveGap.feasibleObjectiveValues f) := by
  apply PositiveGap.exists_infimum_gap_of_no_floor f
  intro Θ hfeas hfloor
  exact hexcluded ⟨ReducedUnitaryFactorization.of_floor f Θ hfeas hfloor⟩

def minimumOperation (n : ℕ) : BinOp n := ⟨min⟩

omit [NeZero n] in
theorem minimum_associative : IsAssociative (minimumOperation n) := by
  intro first second third
  exact min_assoc first second third

omit [NeZero n] in
theorem minimum_no_repeated_rows : ¬ RepeatedRows (minimumOperation n) := by
  rintro ⟨first, second, hne, hrows⟩
  apply hne
  calc
    first = min second first := by
      simpa only [minimumOperation, min_self] using hrows first
    _ = min first second := min_comm _ _
    _ = second := by
      simpa only [minimumOperation, min_self] using hrows second

omit [NeZero n] in
theorem minimum_no_repeated_columns : ¬ RepeatedColumns (minimumOperation n) := by
  rintro ⟨first, second, hne, hcolumns⟩
  apply hne
  calc
    first = min first second := by
      simpa only [minimumOperation, min_self] using hcolumns first
    _ = min second first := min_comm _ _
    _ = second := by
      simpa only [minimumOperation, min_self] using hcolumns second

theorem minimum_no_reduced_unitary_factorization (hatleast : 2 ≤ n) :
    ¬ Nonempty (ReducedUnitaryFactorization (minimumOperation n)) := by
  rintro ⟨data⟩
  let zeroLabel : Fin n := ⟨0, by omega⟩
  let oneLabel : Fin n := ⟨1, by omega⟩
  have hcollision : (minimumOperation n).op zeroLabel zeroLabel =
      (minimumOperation n).op zeroLabel oneLabel := by
    simp [minimumOperation, zeroLabel, oneLabel]
  have hpropagated := row_collision_implies_columns_eq (minimumOperation n) data.params
    data.params_factorizes data.params_floor zeroLabel zeroLabel oneLabel hcollision oneLabel
  simp [minimumOperation, zeroLabel, oneLabel] at hpropagated

theorem minimum_exists_gap (hatleast : 2 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Θ : HCParams n, Factorizes Θ (minimumOperation n) →
      3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ (minimumOperation n)).re :=
  (no_reduced_unitary_factorization_iff_gap (minimumOperation n)).mp
    (minimum_no_reduced_unitary_factorization hatleast)

theorem minimum_exists_infimum_gap (hatleast : 2 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ 3 * (n : ℝ) ^ 2 + ε ≤
      sInf (PositiveGap.feasibleObjectiveValues (minimumOperation n)) :=
  infimum_gap_of_no_reduced_unitary_factorization (minimumOperation n)
    (minimum_no_reduced_unitary_factorization hatleast)

end FloorDichotomy
