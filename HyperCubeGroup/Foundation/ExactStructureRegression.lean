import HyperCubeGroup.Foundation.ExactStructure
import HyperCubeGroup.Foundation.InputQuotients

noncomputable section

namespace FloorDichotomy.ExactStructureRegression

theorem constant_has_reduced_unitary_factorization :
    Nonempty (ReducedUnitaryFactorization SupportUnitaryRegression.constantOperation) := by
  apply (floor_iff_reduced_unitary_factorization _).mp
  exact ⟨SupportUnitaryRegression.constantParams,
    SupportUnitaryRegression.constantParams_factorizes,
    support_uc_objective_value _ _
      SupportUnitaryRegression.constantParams_support_unitary_collinear⟩

theorem constant_lift_unused_output_zero
    (data : ReducedUnitaryFactorization SupportUnitaryRegression.constantOperation) :
    data.params.C 1 = 0 := by
  simp [ReducedUnitaryFactorization.params, SupportUnitaryRegression.constantOperation]

theorem minimum_two_has_infimum_gap :
    ∃ ε : ℝ, 0 < ε ∧ 12 + ε ≤
      sInf (PositiveGap.feasibleObjectiveValues (minimumOperation 2)) := by
  have hgap := minimum_exists_infimum_gap (n := 2) (by decide)
  norm_num at hgap
  exact hgap

theorem minimum_fixed_order_infimum_gap {n : ℕ} [NeZero n] (hatleast : 2 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ 3 * (n : ℝ) ^ 2 + ε ≤
      sInf (PositiveGap.feasibleObjectiveValues (minimumOperation n)) := by
  obtain ⟨gap, hpositive, hgap⟩ :=
    PositiveGap.exists_infimum_gap_fixed_order_of_no_floor (n := n)
  refine ⟨gap, hpositive, hgap (minimumOperation n) ?_⟩
  intro parameters hfeas hfloor
  exact minimum_no_reduced_unitary_factorization hatleast
    ⟨ReducedUnitaryFactorization.of_floor _ parameters hfeas hfloor⟩

theorem order_one_floor_or_gap :
    ∃ ε : ℝ, 0 < ε ∧ ∀ target : BinOp 1,
      (∃ parameters : HCParams 1, Factorizes parameters target ∧
        (objective parameters target).re = 3) ∨
        3 + ε ≤ sInf (PositiveGap.feasibleObjectiveValues target) := by
  simpa using PositiveGap.floor_or_infimum_gap_fixed_order (n := 1)

def redundantMinimum : BinOp 3 :=
  ⟨fun row column => if row = 0 ∨ column = 0 then 0 else 1⟩

theorem redundantMinimum_repeated_rows : RepeatedRows redundantMinimum := by
  refine ⟨1, 2, by decide, ?_⟩
  decide

theorem redundantMinimum_repeated_columns : RepeatedColumns redundantMinimum := by
  refine ⟨1, 2, by decide, ?_⟩
  decide

theorem redundantMinimum_no_reduced_unitary_factorization :
    ¬ Nonempty (ReducedUnitaryFactorization redundantMinimum) := by
  rintro ⟨data⟩
  have hcollision : redundantMinimum.op 0 0 = redundantMinimum.op 0 1 := by decide
  have hdisagree : redundantMinimum.op 1 0 ≠ redundantMinimum.op 1 1 := by decide
  exact hdisagree (row_collision_implies_columns_eq redundantMinimum data.params
    data.params_factorizes data.params_floor 0 0 1 hcollision 1)

theorem redundancy_does_not_suffice :
    ∃ target : BinOp 3, RepeatedRows target ∧ RepeatedColumns target ∧
      ¬ ∃ Θ : HCParams 3, Factorizes Θ target ∧ (objective Θ target).re = 27 := by
  refine ⟨redundantMinimum, redundantMinimum_repeated_rows,
    redundantMinimum_repeated_columns, ?_⟩
  intro hfloor
  apply redundantMinimum_no_reduced_unitary_factorization
  apply (floor_iff_reduced_unitary_factorization _).mp
  norm_num
  exact hfloor

theorem canonical_quotient_encoding_bounds (target : BinOp 3) :
    Nat.card (RowClass target) ≤ Nat.card (RowClass target) ∧
      Nat.card (ColumnClass target) ≤ Nat.card (ColumnClass target) := by
  exact deterministic_encoding_card_bounds target (rowClass target) (columnClass target)
    (fun row column => (reducedTable target row column).val) (fun _ _ => rfl)

end FloorDichotomy.ExactStructureRegression