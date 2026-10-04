/-
General collinearity and group isotopes, without project axioms.

On a loop, the cyclic collinearity identities express the output adjoints
as a projective representation under the associative sandwich product
`first * kernel * second`. Feasibility separates nonzero scalar multiples
of distinct output slices, forcing associativity of the loop operation.
Isotopy transports this argument to every finite quasigroup. This direct
proof does not require active-subspace restriction or unitary extension.
-/

import HyperCubeGroup.Foundation.GroupIsotope

open Matrix Complex

noncomputable section

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem feasible_output_smul_separation (Θ : HCParams n) (f : BinOp n)
    (hloop : IsLoop f) (hfeas : Factorizes Θ f)
    (first second : Fin n) (scalarFirst scalarSecond : ℂ)
    (hfirst : scalarFirst ≠ 0)
    (heq : scalarFirst • (Θ.C first).conjTranspose =
      scalarSecond • (Θ.C second).conjTranspose) :
    first = second := by
  obtain ⟨identity, hid⟩ := hloop.identity
  by_contra hne
  have hmatrix := congrArg Matrix.conjTranspose heq
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose] at hmatrix
  have htrace := congrArg (fun output : Matrix (Fin n) (Fin n) ℂ =>
    (1 / (n : ℂ)) * (Θ.A identity * Θ.B first * output).trace) hmatrix
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at htrace
  have hleft : hcProduct Θ identity first first = 1 := by
    rw [hfeas]; simp [structureTensor, (hid first).1]
  have hright : hcProduct Θ identity first second = 0 := by
    rw [hfeas]; simp [structureTensor, (hid first).1, hne]
  change (1 / (n : ℂ)) * (star scalarFirst *
      (Θ.A identity * Θ.B first * Θ.C first).trace) =
    (1 / (n : ℂ)) * (star scalarSecond *
      (Θ.A identity * Θ.B first * Θ.C second).trace) at htrace
  have hzero : star scalarFirst = 0 := by
    calc star scalarFirst = star scalarFirst * hcProduct Θ identity first first := by rw [hleft]; simp
      _ = star scalarSecond * hcProduct Θ identity first second := by
        unfold hcProduct; linear_combination htrace
      _ = 0 := by rw [hright]; simp
  exact hfirst (star_eq_zero.mp hzero)

theorem loop_collinear_associative (Θ : HCParams n) (f : BinOp n)
    (hloop : IsLoop f) (hcol : PerfectCollinearity Θ f)
    (hfeas : Factorizes Θ f) : IsAssociative f := by
  have hnd := factorizes_implies_nondegenerate Θ f hloop.toIsQuasigroup hfeas
  have hids := (perfectCollinearity_iff_identities Θ f hnd).mp hcol
  obtain ⟨identity, hid⟩ := hloop.identity
  have htrace : ∀ first second, hcProduct Θ first second (f.op first second) = 1 := by
    intro first second; rw [hfeas]; simp [structureTensor]
  let output := fun index => (Θ.C index).conjTranspose
  let kernel := (Θ.B identity).conjTranspose * (Θ.A identity).conjTranspose
  let coefficient := fun first second =>
    (frobNormSq (Θ.A first))⁻¹ * (frobNormSq (Θ.B second))⁻¹ *
      (frobNormSq (Θ.C (f.op first second)))⁻¹
  have hcoeff : ∀ first second, coefficient first second ≠ 0 := by
    intro first second
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (hnd.A_pos first))
      (inv_ne_zero (hnd.B_pos second))) (inv_ne_zero (hnd.C_pos _))
  have hproduct : ∀ first second,
      output first * kernel * output second =
        coefficient first second • output (f.op first second) := by
    intro first second
    have hfirst := congrArg Matrix.conjTranspose (hids.idA first identity)
    have hsecond := congrArg Matrix.conjTranspose (hids.idB identity second)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose] at hfirst hsecond
    have htraceFirst := htrace first identity
    have htraceSecond := htrace identity second
    simp only [(hid first).2] at htraceFirst
    simp only [(hid second).1] at htraceSecond
    simp only [(hid first).2, htraceFirst, one_div, star_inv₀, star_frobNormSq] at hfirst
    simp only [(hid second).1, htraceSecond, one_div, star_inv₀, star_frobNormSq] at hsecond
    have hthird := hids.idC first second
    simp only [htrace, one_div] at hthird
    calc output first * kernel * output second =
        (output first * (Θ.B identity).conjTranspose) *
          ((Θ.A identity).conjTranspose * output second) := by
            dsimp [kernel]; simp only [Matrix.mul_assoc]
      _ = ((frobNormSq (Θ.A first))⁻¹ • Θ.A first) *
          ((frobNormSq (Θ.B second))⁻¹ • Θ.B second) := by rw [hfirst, hsecond]
      _ = coefficient first second • output (f.op first second) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, hthird]
        simp only [smul_smul, coefficient, output, mul_assoc]
  intro first second third
  apply feasible_output_smul_separation Θ f hloop hfeas
    (f.op (f.op first second) third) (f.op first (f.op second third))
    (coefficient first second * coefficient (f.op first second) third)
    (coefficient second third * coefficient first (f.op second third))
    (mul_ne_zero (hcoeff _ _) (hcoeff _ _))
  change _ • output _ = _ • output _
  calc (coefficient first second * coefficient (f.op first second) third) •
        output (f.op (f.op first second) third) =
      (output first * kernel * output second) * kernel * output third := by
        rw [hproduct, Matrix.smul_mul, Matrix.smul_mul, hproduct, smul_smul]
    _ = output first * kernel * (output second * kernel * output third) := by
      simp only [Matrix.mul_assoc]
    _ = (coefficient second third * coefficient first (f.op second third)) •
        output (f.op first (f.op second third)) := by
      rw [hproduct, Matrix.mul_smul, hproduct, smul_smul]

theorem collinear_isotope_transfer (Θ : HCParams n) (f g : BinOp n)
    (hq : IsQuasigroup f) (hiso : IsIsotopic f g)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f) :
    ∃ transformed : HCParams n,
      PerfectCollinearity transformed g ∧ Factorizes transformed g := by
  obtain ⟨firstPerm, secondPerm, outputPerm, hiso⟩ := hiso
  let transformed := isotopeTransform Θ firstPerm.symm secondPerm.symm outputPerm.symm
  have hfact : Factorizes transformed g :=
    isotopeTransform_factorizes Θ f g firstPerm secondPerm outputPerm hiso hfeas
  have hnd := factorizes_implies_nondegenerate Θ f hq hfeas
  have hndTransformed : Nondegenerate transformed :=
    ⟨fun index => hnd.A_pos (firstPerm.symm index),
      fun index => hnd.B_pos (secondPerm.symm index),
      fun index => hnd.C_pos (outputPerm.symm index)⟩
  have hids := (perfectCollinearity_iff_identities Θ f hnd).mp hcol
  have houtput : ∀ first second,
      outputPerm.symm (g.op first second) =
        f.op (firstPerm.symm first) (secondPerm.symm second) := by
    intro first second
    rw [hiso, Equiv.symm_apply_apply]
  refine ⟨transformed, (perfectCollinearity_iff_identities transformed g hndTransformed).mpr ?_, hfact⟩
  constructor
  · intro first second
    change Θ.B (secondPerm.symm second) * Θ.C (outputPerm.symm (g.op first second)) =
      (hcProduct Θ (firstPerm.symm first) (secondPerm.symm second)
        (outputPerm.symm (g.op first second)) / frobNormSq (Θ.A (firstPerm.symm first))) •
          (Θ.A (firstPerm.symm first)).conjTranspose
    rw [houtput]
    exact hids.idA _ _
  · intro first second
    change Θ.C (outputPerm.symm (g.op first second)) * Θ.A (firstPerm.symm first) =
      (hcProduct Θ (firstPerm.symm first) (secondPerm.symm second)
        (outputPerm.symm (g.op first second)) / frobNormSq (Θ.B (secondPerm.symm second))) •
          (Θ.B (secondPerm.symm second)).conjTranspose
    rw [houtput]
    exact hids.idB _ _
  · intro first second
    change Θ.A (firstPerm.symm first) * Θ.B (secondPerm.symm second) =
      (hcProduct Θ (firstPerm.symm first) (secondPerm.symm second)
        (outputPerm.symm (g.op first second)) /
          frobNormSq (Θ.C (outputPerm.symm (g.op first second)))) •
            (Θ.C (outputPerm.symm (g.op first second))).conjTranspose
    rw [houtput]
    exact hids.idC _ _

theorem general_collinear_implies_group_isotope (f : BinOp n)
    (hq : IsQuasigroup f)
    (hexists : ∃ Θ : HCParams n, PerfectCollinearity Θ f ∧ Factorizes Θ f) :
    IsGroupIsotope f := by
  obtain ⟨Θ, hcol, hfeas⟩ := hexists
  obtain ⟨loop, hloop, hiso⟩ := quasigroup_isotopic_to_loop f hq
  obtain ⟨transformed, hcolTransformed, hfact⟩ :=
    collinear_isotope_transfer Θ f loop hq hiso hcol hfeas
  have hassoc := loop_collinear_associative transformed loop hloop hcolTransformed hfact
  obtain ⟨firstPerm, secondPerm, outputPerm, hiso⟩ := hiso
  refine ⟨loop, hassoc, firstPerm.symm, secondPerm.symm, outputPerm.symm, ?_⟩
  intro first second
  apply outputPerm.injective
  simpa only [Equiv.symm_symm, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
    (hiso (firstPerm first) (secondPerm second)).symm

theorem collinear_iff_group_isotope (f : BinOp n) (hq : IsQuasigroup f) :
    (∃ Θ : HCParams n, PerfectCollinearity Θ f ∧ Factorizes Θ f) ↔
      IsGroupIsotope f := by
  refine ⟨general_collinear_implies_group_isotope f hq, ?_⟩
  intro hgroup
  obtain ⟨Θ, hunitary⟩ := group_isotope_admits_unitary_collinear f hq hgroup
  exact ⟨Θ, hunitary.collinear, hunitary.feasible⟩

theorem general_collinear_admits_unitary (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hcol : PerfectCollinearity Θ f)
    (hfeas : Factorizes Θ f) :
    ∃ unitary : HCParams n, UnitaryCollinear unitary f :=
  group_isotope_admits_unitary_collinear f hq
    (general_collinear_implies_group_isotope f hq ⟨Θ, hcol, hfeas⟩)

theorem collinear_implies_group_isotope (f : BinOp n) (hq : IsQuasigroup f)
    (hexists : ∃ Θ : HCParams n, PerfectCollinearity Θ f ∧ Factorizes Θ f ∧
      Nondegenerate Θ) : IsGroupIsotope f := by
  obtain ⟨Θ, hcol, hfeas, _⟩ := hexists
  exact general_collinear_implies_group_isotope f hq ⟨Θ, hcol, hfeas⟩

theorem collinear_to_unitary_collinear (f : BinOp n) (hq : IsQuasigroup f)
    (Θ : HCParams n) (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f) :
    ∃ unitary : HCParams n, UnitaryCollinear unitary f :=
  general_collinear_admits_unitary Θ f hq hcol hfeas

end