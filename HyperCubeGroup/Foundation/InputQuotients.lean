import HyperCubeGroup.Foundation.ReducedTable

/-!
Deterministic, separately encoded inputs for arbitrary finite operation tables.
Row and column equality quotients bound the required finite code alphabets.
Encodings constant on identical inputs and separating distinct table profiles
factor uniquely through these quotients by injective maps. Binary bounds concern
fixed-length separate codes only, not interactive communication or MDL.
-/

noncomputable section

namespace FloorDichotomy

variable {n : ℕ} {α β : Type*}

theorem row_encoding_eq_implies_identical_rows (f : BinOp n)
    (encRow : Fin n → α) (encCol : Fin n → β) (decode : α → β → Fin n)
    (hdecode : ∀ row column, decode (encRow row) (encCol column) = f.op row column)
    {firstRow secondRow : Fin n} (hencoding : encRow firstRow = encRow secondRow) :
    ∀ column, f.op firstRow column = f.op secondRow column := by
  intro column
  rw [← hdecode firstRow column, ← hdecode secondRow column, hencoding]

theorem column_encoding_eq_implies_identical_columns (f : BinOp n)
    (encRow : Fin n → α) (encCol : Fin n → β) (decode : α → β → Fin n)
    (hdecode : ∀ row column, decode (encRow row) (encCol column) = f.op row column)
    {firstColumn secondColumn : Fin n}
    (hencoding : encCol firstColumn = encCol secondColumn) :
    ∀ row, f.op row firstColumn = f.op row secondColumn := by
  intro row
  rw [← hdecode row firstColumn, ← hdecode row secondColumn, hencoding]

theorem rowClass_card_le_of_encoding_separates_rows (f : BinOp n)
    [Finite α] (encRow : Fin n → α)
    (hdetermines : ∀ firstRow secondRow, encRow firstRow = encRow secondRow →
      ∀ column, f.op firstRow column = f.op secondRow column) :
    Nat.card (RowClass f) ≤ Nat.card α := by
  apply Nat.card_le_card_of_injective (fun rowQuotient : RowClass f => encRow rowQuotient.out)
  intro firstClass secondClass hencoding
  have hclasses :
      (Quotient.mk (rowSetoid f) firstClass.out : RowClass f) =
        Quotient.mk (rowSetoid f) secondClass.out :=
    Quotient.sound (hdetermines firstClass.out secondClass.out hencoding)
  simpa only [Quotient.out_eq] using hclasses

theorem columnClass_card_le_of_encoding_separates_columns (f : BinOp n)
    [Finite β] (encCol : Fin n → β)
    (hdetermines : ∀ firstColumn secondColumn,
      encCol firstColumn = encCol secondColumn →
        ∀ row, f.op row firstColumn = f.op row secondColumn) :
    Nat.card (ColumnClass f) ≤ Nat.card β := by
  apply Nat.card_le_card_of_injective
    (fun columnQuotient : ColumnClass f => encCol columnQuotient.out)
  intro firstClass secondClass hencoding
  have hclasses :
      (Quotient.mk (columnSetoid f) firstClass.out : ColumnClass f) =
        Quotient.mk (columnSetoid f) secondClass.out :=
    Quotient.sound (hdetermines firstClass.out secondClass.out hencoding)
  simpa only [Quotient.out_eq] using hclasses

theorem deterministic_encoding_card_bounds (f : BinOp n)
    [Finite α] [Finite β]
    (encRow : Fin n → α) (encCol : Fin n → β) (decode : α → β → Fin n)
    (hdecode : ∀ row column, decode (encRow row) (encCol column) = f.op row column) :
    Nat.card (RowClass f) ≤ Nat.card α ∧
      Nat.card (ColumnClass f) ≤ Nat.card β := by
  constructor
  · apply rowClass_card_le_of_encoding_separates_rows f encRow
    intro firstRow secondRow hencoding
    exact row_encoding_eq_implies_identical_rows f encRow encCol decode hdecode hencoding
  · apply columnClass_card_le_of_encoding_separates_columns f encCol
    intro firstColumn secondColumn hencoding
    exact column_encoding_eq_implies_identical_columns f encRow encCol decode hdecode hencoding

theorem row_encoding_factors_uniquely (f : BinOp n) (encRow : Fin n → α)
    (hconstant : ∀ firstRow secondRow,
      (∀ column, f.op firstRow column = f.op secondRow column) →
        encRow firstRow = encRow secondRow)
    (hdetermines : ∀ firstRow secondRow, encRow firstRow = encRow secondRow →
      ∀ column, f.op firstRow column = f.op secondRow column) :
    ∃! factor : RowClass f → α,
      Function.Injective factor ∧ ∀ row, factor (rowClass f row) = encRow row := by
  let factor : RowClass f → α := Quotient.lift encRow hconstant
  refine ⟨factor, ⟨?_, ?_⟩, ?_⟩
  · intro firstClass secondClass
    induction firstClass using Quotient.inductionOn with
    | h firstRow =>
      induction secondClass using Quotient.inductionOn with
      | h secondRow =>
        intro hencoding
        exact Quotient.sound (hdetermines firstRow secondRow hencoding)
  · intro row
    rfl
  · intro otherFactor hotherFactor
    funext rowQuotient
    induction rowQuotient using Quotient.inductionOn with
    | h row => exact hotherFactor.2 row

theorem column_encoding_factors_uniquely (f : BinOp n) (encCol : Fin n → β)
    (hconstant : ∀ firstColumn secondColumn,
      (∀ row, f.op row firstColumn = f.op row secondColumn) →
        encCol firstColumn = encCol secondColumn)
    (hdetermines : ∀ firstColumn secondColumn,
      encCol firstColumn = encCol secondColumn →
        ∀ row, f.op row firstColumn = f.op row secondColumn) :
    ∃! factor : ColumnClass f → β,
      Function.Injective factor ∧ ∀ column, factor (columnClass f column) = encCol column := by
  let factor : ColumnClass f → β := Quotient.lift encCol hconstant
  refine ⟨factor, ⟨?_, ?_⟩, ?_⟩
  · intro firstClass secondClass
    induction firstClass using Quotient.inductionOn with
    | h firstColumn =>
      induction secondClass using Quotient.inductionOn with
      | h secondColumn =>
        intro hencoding
        exact Quotient.sound (hdetermines firstColumn secondColumn hencoding)
  · intro column
    rfl
  · intro otherFactor hotherFactor
    funext columnQuotient
    induction columnQuotient using Quotient.inductionOn with
    | h column => exact hotherFactor.2 column

theorem fixed_length_binary_encoding_card_bounds (f : BinOp n) (rowBits columnBits : ℕ)
    (encRow : Fin n → (Fin rowBits → Bool))
    (encCol : Fin n → (Fin columnBits → Bool))
    (decode : (Fin rowBits → Bool) → (Fin columnBits → Bool) → Fin n)
    (hdecode : ∀ row column, decode (encRow row) (encCol column) = f.op row column) :
    Nat.card (RowClass f) ≤ 2 ^ rowBits ∧
      Nat.card (ColumnClass f) ≤ 2 ^ columnBits := by
  have hcapacity : ∀ bits : ℕ, Nat.card (Fin bits → Bool) = 2 ^ bits := by
    intro bits
    rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_bool]
  simpa only [hcapacity] using
    deterministic_encoding_card_bounds f encRow encCol decode hdecode

end FloorDichotomy