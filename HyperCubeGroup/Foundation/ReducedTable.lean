/-
Role-separated reduction of arbitrary finite operation tables.

Identical rows and columns define separate quotient sets. The reduced table
maps their product onto used outputs. At an exactly feasible floor point this
map is injective in each argument, not necessarily jointly injective, and the
three sets need not have equal cardinality. No congruence, associativity, or
quotient-group structure is asserted.

Used output matrices have orthonormal normalized trace inner products at the floor.
-/

import HyperCubeGroup.Foundation.FloorDichotomy
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section

namespace FloorDichotomy

variable {n : ℕ} [NeZero n]

def rowSetoid (f : BinOp n) : Setoid (Fin n) where
  r first second := ∀ column, f.op first column = f.op second column
  iseqv := ⟨fun _ _ => rfl, fun heq column => (heq column).symm,
    fun hfirst hsecond column => (hfirst column).trans (hsecond column)⟩

def columnSetoid (f : BinOp n) : Setoid (Fin n) where
  r first second := ∀ row, f.op row first = f.op row second
  iseqv := ⟨fun _ _ => rfl, fun heq row => (heq row).symm,
    fun hfirst hsecond row => (hfirst row).trans (hsecond row)⟩

abbrev RowClass (f : BinOp n) := Quotient (rowSetoid f)
abbrev ColumnClass (f : BinOp n) := Quotient (columnSetoid f)
abbrev UsedOutput (f : BinOp n) := {output : Fin n // ∃ row column, f.op row column = output}

def rowClass (f : BinOp n) (row : Fin n) : RowClass f := Quotient.mk _ row
def columnClass (f : BinOp n) (column : Fin n) : ColumnClass f := Quotient.mk _ column

def reducedTable (f : BinOp n) : RowClass f → ColumnClass f → UsedOutput f :=
  Quotient.lift₂ (fun row column => ⟨f.op row column, row, column, rfl⟩)
    (by
      intro firstRow firstColumn secondRow secondColumn hrows hcolumns
      apply Subtype.ext
      exact (hrows firstColumn).trans (hcolumns secondRow))

omit [NeZero n] in
theorem reducedTable_mk (f : BinOp n) (row column : Fin n) :
    (reducedTable f (rowClass f row) (columnClass f column)).val = f.op row column := rfl

theorem reducedTable_row_injective (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (row : RowClass f) : Function.Injective (reducedTable f row) := by
  induction row using Quotient.inductionOn with
  | h row =>
    intro first second
    induction first using Quotient.inductionOn with
    | h first =>
      induction second using Quotient.inductionOn with
      | h second =>
        intro heq
        apply Quotient.sound
        exact row_collision_implies_columns_eq f Θ hfeas hfloor row first second
          (congrArg Subtype.val heq)

theorem reducedTable_column_injective (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (column : ColumnClass f) : Function.Injective (fun row => reducedTable f row column) := by
  induction column using Quotient.inductionOn with
  | h column =>
    intro first second
    induction first using Quotient.inductionOn with
    | h first =>
      induction second using Quotient.inductionOn with
      | h second =>
        intro heq
        apply Quotient.sound
        exact column_collision_implies_rows_eq f Θ hfeas hfloor column first second
          (congrArg Subtype.val heq)

theorem row_collision_iff_columns_eq (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (row first second : Fin n) :
    f.op row first = f.op row second ↔ ∀ otherRow, f.op otherRow first = f.op otherRow second :=
  ⟨row_collision_implies_columns_eq f Θ hfeas hfloor row first second, fun heq => heq row⟩

theorem column_collision_iff_rows_eq (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (column first second : Fin n) :
    f.op first column = f.op second column ↔ ∀ otherColumn, f.op first otherColumn = f.op second otherColumn :=
  ⟨column_collision_implies_rows_eq f Θ hfeas hfloor column first second, fun heq => heq column⟩

omit [NeZero n] in
theorem reducedTable_surjective (f : BinOp n) :
    Function.Surjective (fun pair : RowClass f × ColumnClass f => reducedTable f pair.1 pair.2) := by
  intro output
  obtain ⟨row, column, heq⟩ := output.property
  refine ⟨(rowClass f row, columnClass f column), ?_⟩
  exact Subtype.ext heq

theorem reducedTable_card_bounds (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2) :
    max (Nat.card (RowClass f)) (Nat.card (ColumnClass f)) ≤ Nat.card (UsedOutput f) ∧
      Nat.card (UsedOutput f) ≤ Nat.card (RowClass f) * Nat.card (ColumnClass f) := by
  let label : Fin n := ⟨0, NeZero.pos n⟩
  constructor
  · apply max_le
    · exact Nat.card_le_card_of_injective _
        (reducedTable_column_injective f Θ hfeas hfloor (columnClass f label))
    · exact Nat.card_le_card_of_injective _
        (reducedTable_row_injective f Θ hfeas hfloor (rowClass f label))
  · have hbound := Nat.card_le_card_of_surjective _ (reducedTable_surjective f)
    rwa [Nat.card_prod] at hbound

theorem used_output_trace_orthonormal (f : BinOp n) (Θ : HCParams n)
    (hfeas : Factorizes Θ f) (hfloor : (objective Θ f).re = 3 * (n : ℝ)^2)
    (first second : UsedOutput f) :
    (1 / (n : ℂ)) * ((Θ.C first.val).conjTranspose * Θ.C second.val).trace =
      if first = second then 1 else 0 := by
  classical
  obtain ⟨row, column, houtput⟩ := first.property
  have hproduct := supported_product f Θ hfeas hfloor row column
  rw [houtput] at hproduct
  have htrace := hfeas row column second.val
  unfold hcProduct at htrace
  rw [hproduct] at htrace
  simpa only [structureTensor, houtput, Subtype.ext_iff] using htrace

end FloorDichotomy
