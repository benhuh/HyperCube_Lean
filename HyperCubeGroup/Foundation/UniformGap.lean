import HyperCubeGroup.Foundation.PositiveGap
import HyperCubeGroup.Foundation.ReducedTable

noncomputable section

namespace FloorDichotomy

variable {n : ℕ} [NeZero n]

theorem exists_gap_of_non_group_no_redundancy (f : BinOp n)
    (hnotgi : ¬ IsGroupIsotope f) (hrows : ¬ RepeatedRows f)
    (hcolumns : ¬ RepeatedColumns f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Θ : HCParams n, Factorizes Θ f →
      3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ f).re := by
  apply PositiveGap.exists_gap_of_no_floor f
  intro Θ hfeas hfloor
  exact hnotgi (group_isotope_of_floor_no_redundancy f Θ hfeas hfloor hrows hcolumns)

theorem exists_gap_of_stray_row_collision (f : BinOp n)
    (row otherRow first second : Fin n)
    (hcollision : f.op row first = f.op row second)
    (hdisagree : f.op otherRow first ≠ f.op otherRow second) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Θ : HCParams n, Factorizes Θ f →
      3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ f).re := by
  apply PositiveGap.exists_gap_of_no_floor f
  intro Θ hfeas hfloor
  exact hdisagree
    (row_collision_implies_columns_eq f Θ hfeas hfloor row first second hcollision otherRow)

theorem exists_gap_of_stray_column_collision (f : BinOp n)
    (column otherColumn first second : Fin n)
    (hcollision : f.op first column = f.op second column)
    (hdisagree : f.op first otherColumn ≠ f.op second otherColumn) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Θ : HCParams n, Factorizes Θ f →
      3 * (n : ℝ) ^ 2 + ε ≤ (objective Θ f).re := by
  apply PositiveGap.exists_gap_of_no_floor f
  intro Θ hfeas hfloor
  exact hdisagree
    (column_collision_implies_rows_eq f Θ hfeas hfloor column first second hcollision otherColumn)

end FloorDichotomy
