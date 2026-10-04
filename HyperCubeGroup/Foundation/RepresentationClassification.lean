import HyperCubeGroup.Foundation.GroupIsotope
import HyperCubeGroup.Foundation.GeneralCollinearity
import HyperCubeGroup.Foundation.Representation.Characters
import Mathlib.Algebra.Group.MinimalAxioms

noncomputable section

open Matrix
open HyperCubeGroup.ThreeFamilySynchronization

variable {n : ℕ} [NeZero n]

/-- A synchronized feasible representation of an associative loop is unitarily
equivalent to its left regular representation. -/
theorem representation_unitary_equivalence (Θ : HCParams n) (f : BinOp n)
    (hloop : IsLoop f) (hassoc : IsAssociative f)
    (hsync : Synchronized Θ f) (hfeas : Factorizes Θ f) :
    ∃ W : Matrix (Fin n) (Fin n) ℂ,
      W ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        ∀ g, hsync.rho g = W * leftRegularRep f g * W.conjTranspose := by
  classical
  let identity := Classical.choose hloop.identity
  have identity_spec := Classical.choose_spec hloop.identity
  letI : Mul (Fin n) := ⟨f.op⟩
  letI : One (Fin n) := ⟨identity⟩
  letI : Inv (Fin n) :=
    ⟨fun a => Classical.choose ((hloop.right_cancel a).2 identity)⟩
  letI : Group (Fin n) := Group.ofLeftAxioms hassoc
    (fun a => (identity_spec a).1)
    (fun a => Classical.choose_spec ((hloop.right_cancel a).2 identity))
  have rho_mul := synchronized_homomorphism Θ f hloop hsync hfeas
  have rho_one : hsync.rho identity = 1 := by
    have hidempotent := rho_mul identity identity
    rw [(identity_spec identity).1] at hidempotent
    have hcancel := congrArg (fun matrix => (hsync.rho identity).conjTranspose * matrix)
      hidempotent
    change (hsync.rho identity).conjTranspose *
      (hsync.rho identity * hsync.rho identity) =
        (hsync.rho identity).conjTranspose * hsync.rho identity at hcancel
    rwa [← Matrix.mul_assoc, mul_eq_one_comm.mp (hsync.unitary identity),
      Matrix.one_mul] at hcancel
  have regular_one : leftRegularRep f identity = 1 := by
    have left_identity (a : Fin n) : f.op identity a = a := (identity_spec a).1
    ext row column
    simp only [leftRegularRep, Matrix.of_apply, left_identity, Matrix.one_apply]
    simp only [eq_comm]
  let synchronized : Fin n →* UnitaryMatrix n := {
    toFun := fun g => ⟨hsync.rho g,
      ⟨mul_eq_one_comm.mp (hsync.unitary g), hsync.unitary g⟩⟩
    map_one' := by
      apply Subtype.ext
      exact rho_one
    map_mul' := fun a b => by
      apply Subtype.ext
      exact (rho_mul a b).symm
  }
  let regular : Fin n →* UnitaryMatrix n := {
    toFun := fun g => ⟨leftRegularRep f g,
      ⟨mul_eq_one_comm.mp (leftRegularRep_unitary f hloop.toIsQuasigroup g),
        leftRegularRep_unitary f hloop.toIsQuasigroup g⟩⟩
    map_one' := by
      apply Subtype.ext
      exact regular_one
    map_mul' := fun a b => by
      apply Subtype.ext
      exact (leftRegularRep_hom f hloop.toIsQuasigroup hassoc a b).symm
  }
  have character_eq : ∀ g,
      (regular g : Matrix (Fin n) (Fin n) ℂ).trace =
        (synchronized g : Matrix (Fin n) (Fin n) ℂ).trace := by
    intro g
    change (leftRegularRep f g).trace = (hsync.rho g).trace
    rw [representation_unique Θ f hloop hassoc hsync hfeas g]
    have htrace := leftRegularRep_trace_product f hloop.toIsQuasigroup g identity
    simpa only [regular_one, Matrix.conjTranspose_one, Matrix.mul_one] using htrace
  obtain ⟨W, hW⟩ := HyperCubeGroup.Manuscript.unitary_equivalence_of_character_eq
    regular synchronized character_eq
  exact ⟨(W : Matrix (Fin n) (Fin n) ℂ), W.property, hW⟩

theorem loop_unitary_synchronization (Θ : HCParams n) (f : BinOp n)
    (hloop : IsLoop f) (huc : UnitaryCollinear Θ f) :
    ∃ (synced : HCParams n) (hsync : Synchronized synced f)
      (P Q : Matrix (Fin n) (Fin n) ℂ),
      Factorizes synced f ∧ P * P.conjTranspose = 1 ∧ Q * Q.conjTranspose = 1 ∧
      ∀ g, Θ.A g = P * hsync.rho g ∧ Θ.B g = hsync.rho g * Q ∧
        Θ.C g = Q.conjTranspose * (hsync.rho g).conjTranspose * P.conjTranspose := by
  classical
  obtain ⟨identity, hid⟩ := hloop.identity
  have hnd := factorizes_implies_nondegenerate Θ f hloop.toIsQuasigroup huc.feasible
  have hids := (perfectCollinearity_iff_identities Θ f hnd).mp huc.collinear
  have hAB : ∀ a b, Θ.A a * Θ.B b = (Θ.C (f.op a b)).conjTranspose := by
    intro a b
    have h := hids.idC a b
    dsimp only at h
    have hsupport : hcProduct Θ a b (f.op a b) = 1 := by
      rw [huc.feasible]; simp [structureTensor]
    rw [hsupport, frobNormSq_unitary_eq_one _ (huc.unitaryC _), div_one,
      one_smul] at h
    exact h
  let rho := fun g => (Θ.A identity).conjTranspose * Θ.A g
  let synced : HCParams n := ⟨rho, rho, fun g => (rho g).conjTranspose⟩
  have hrho : ∀ g, rho g * (rho g).conjTranspose = 1 := by
    intro g
    dsimp [rho]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (Θ.A g), huc.unitaryA,
      Matrix.one_mul, mul_eq_one_comm.mp (huc.unitaryA identity)]
  let hsync : Synchronized synced f :=
    ⟨rho, fun _ => rfl, fun _ => rfl, fun _ => rfl, hrho⟩
  have hA : ∀ g, Θ.A g = Θ.A identity * rho g := by
    intro g
    dsimp [rho]
    rw [← Matrix.mul_assoc, huc.unitaryA, Matrix.one_mul]
  have hB : ∀ g, Θ.B g = rho g * Θ.B identity := by
    intro g
    have heq : Θ.A identity * Θ.B g = Θ.A g * Θ.B identity := by
      rw [hAB, hAB, (hid g).1, (hid g).2]
    have h := congrArg (fun M => (Θ.A identity).conjTranspose * M) heq
    simpa only [← Matrix.mul_assoc, mul_eq_one_comm.mp (huc.unitaryA identity),
      Matrix.one_mul] using h
  have hC : ∀ g, Θ.C g = (Θ.B identity).conjTranspose *
      (rho g).conjTranspose * (Θ.A identity).conjTranspose := by
    intro g
    have h := congrArg Matrix.conjTranspose (hAB g identity)
    rw [(hid g).2, Matrix.conjTranspose_conjTranspose, hA g,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at h
    simpa only [Matrix.mul_assoc] using h.symm
  have hfact : Factorizes synced f := by
    intro a b c
    rw [← huc.feasible a b c]
    unfold hcProduct
    change (1 / (n : ℂ)) * (rho a * rho b * (rho c).conjTranspose).trace = _
    rw [hA a, hB b, hC c]
    have hproduct : Θ.A identity * rho a * (rho b * Θ.B identity) *
        ((Θ.B identity).conjTranspose * (rho c).conjTranspose *
          (Θ.A identity).conjTranspose) =
        Θ.A identity * (rho a * rho b * (rho c).conjTranspose) *
          (Θ.A identity).conjTranspose := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Θ.B identity), huc.unitaryB, Matrix.one_mul]
    rw [hproduct, Matrix.trace_mul_cycle (Θ.A identity)
      (rho a * rho b * (rho c).conjTranspose) (Θ.A identity).conjTranspose,
      mul_eq_one_comm.mp (huc.unitaryA identity), Matrix.one_mul]
  exact ⟨synced, hsync, Θ.A identity, Θ.B identity, hfact,
    huc.unitaryA identity, huc.unitaryB identity, fun g => ⟨hA g, hB g, hC g⟩⟩

theorem loop_unitary_collinear_classification (Θ : HCParams n) (f : BinOp n)
    (hloop : IsLoop f) (hassoc : IsAssociative f) (huc : UnitaryCollinear Θ f) :
    ∃ L R S : Matrix (Fin n) (Fin n) ℂ,
      L ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      R ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      S ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      ∀ g, Θ.A g = L * leftRegularRep f g * R.conjTranspose ∧
        Θ.B g = R * leftRegularRep f g * S.conjTranspose ∧
        Θ.C g = S * (leftRegularRep f g).conjTranspose * L.conjTranspose := by
  obtain ⟨synced, hsync, P, Q, hfact, hP, hQ, hreconstruct⟩ :=
    loop_unitary_synchronization Θ f hloop huc
  obtain ⟨W, hW, hequiv⟩ :=
    representation_unitary_equivalence synced f hloop hassoc hsync hfact
  have hPmem : P ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.mpr hP
  have hQmem : Q.conjTranspose ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change Q.conjTranspose * Q.conjTranspose.conjTranspose = 1
    simpa only [Matrix.conjTranspose_conjTranspose] using mul_eq_one_comm.mp hQ
  refine ⟨P * W, W, Q.conjTranspose * W,
    (Matrix.unitaryGroup (Fin n) ℂ).mul_mem hPmem hW, hW,
    (Matrix.unitaryGroup (Fin n) ℂ).mul_mem hQmem hW, ?_⟩
  intro g
  obtain ⟨hA, hB, hC⟩ := hreconstruct g
  rw [hequiv g] at hA hB hC
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Matrix.mul_assoc] using hA
  · simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using hB
  · simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using hC

theorem unitary_collinear_isotope_transfer (Θ : HCParams n) (f g : BinOp n)
    (hq : IsQuasigroup f) (φ ψ χ : Equiv.Perm (Fin n))
    (hiso : ∀ a b, g.op a b = χ (f.op (φ.symm a) (ψ.symm b)))
    (huc : UnitaryCollinear Θ f) :
    UnitaryCollinear (isotopeTransform Θ φ.symm ψ.symm χ.symm) g := by
  let transformed := isotopeTransform Θ φ.symm ψ.symm χ.symm
  have hfact : Factorizes transformed g :=
    isotopeTransform_factorizes Θ f g φ ψ χ hiso huc.feasible
  have hnd := factorizes_implies_nondegenerate Θ f hq huc.feasible
  have hndTransformed : Nondegenerate transformed :=
    ⟨fun a => hnd.A_pos (φ.symm a), fun b => hnd.B_pos (ψ.symm b),
      fun c => hnd.C_pos (χ.symm c)⟩
  have hids := (perfectCollinearity_iff_identities Θ f hnd).mp huc.collinear
  have houtput : ∀ a b, χ.symm (g.op a b) = f.op (φ.symm a) (ψ.symm b) := by
    intro a b
    rw [hiso, Equiv.symm_apply_apply]
  have hcol : PerfectCollinearity transformed g := by
    apply (perfectCollinearity_iff_identities transformed g hndTransformed).mpr
    constructor
    · intro a b
      change Θ.B (ψ.symm b) * Θ.C (χ.symm (g.op a b)) =
        (hcProduct Θ (φ.symm a) (ψ.symm b) (χ.symm (g.op a b)) /
          frobNormSq (Θ.A (φ.symm a))) • (Θ.A (φ.symm a)).conjTranspose
      rw [houtput]
      exact hids.idA _ _
    · intro a b
      change Θ.C (χ.symm (g.op a b)) * Θ.A (φ.symm a) =
        (hcProduct Θ (φ.symm a) (ψ.symm b) (χ.symm (g.op a b)) /
          frobNormSq (Θ.B (ψ.symm b))) • (Θ.B (ψ.symm b)).conjTranspose
      rw [houtput]
      exact hids.idB _ _
    · intro a b
      change Θ.A (φ.symm a) * Θ.B (ψ.symm b) =
        (hcProduct Θ (φ.symm a) (ψ.symm b) (χ.symm (g.op a b)) /
          frobNormSq (Θ.C (χ.symm (g.op a b)))) •
            (Θ.C (χ.symm (g.op a b))).conjTranspose
      rw [houtput]
      exact hids.idC _ _
  exact ⟨hcol, hfact, fun a => huc.unitaryA (φ.symm a),
    fun b => huc.unitaryB (ψ.symm b), fun c => huc.unitaryC (χ.symm c)⟩

theorem quasigroup_unitary_collinear_classification (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (huc : UnitaryCollinear Θ f) :
    ∃ g : BinOp n, IsLoop g ∧ IsAssociative g ∧
      ∃ φ ψ χ : Equiv.Perm (Fin n), IsIsotopic f g ∧
        (∀ a b, g.op (φ a) (ψ b) = χ (f.op a b)) ∧
        ∃ L R S : Matrix (Fin n) (Fin n) ℂ,
          L ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
          R ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
          S ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
          (∀ a, Θ.A a = L * leftRegularRep g (φ a) * R.conjTranspose) ∧
          (∀ b, Θ.B b = R * leftRegularRep g (ψ b) * S.conjTranspose) ∧
          (∀ c, Θ.C c = S * (leftRegularRep g (χ c)).conjTranspose * L.conjTranspose) := by
  classical
  obtain ⟨g, hloop, φ, ψ, χ, hiso⟩ := quasigroup_isotopic_to_loop f hq
  let transformed := isotopeTransform Θ φ.symm ψ.symm χ.symm
  have htransformed : UnitaryCollinear transformed g :=
    unitary_collinear_isotope_transfer Θ f g hq φ ψ χ hiso huc
  have hassoc := loop_collinear_associative transformed g hloop
    htransformed.collinear htransformed.feasible
  obtain ⟨L, R, S, hL, hR, hS, hnormal⟩ :=
    loop_unitary_collinear_classification transformed g hloop hassoc htransformed
  refine ⟨g, hloop, hassoc, φ, ψ, χ, ⟨φ, ψ, χ, hiso⟩, ?_,
    L, R, S, hL, hR, hS, ?_, ?_, ?_⟩
  · intro a b
    simpa only [Equiv.symm_apply_apply] using hiso (φ a) (ψ b)
  · intro a
    simpa only [transformed, isotopeTransform, Equiv.symm_apply_apply] using
      (hnormal (φ a)).1
  · intro b
    simpa only [transformed, isotopeTransform, Equiv.symm_apply_apply] using
      (hnormal (ψ b)).2.1
  · intro c
    simpa only [transformed, isotopeTransform, Equiv.symm_apply_apply] using
      (hnormal (χ c)).2.2

theorem group_isotope_global_minimizer_iff_unitary_collinear
    (Θ : HCParams n) (f : BinOp n) (hq : IsQuasigroup f)
    (hgroup : IsGroupIsotope f) :
    IsGlobalMinimizer Θ f ↔ UnitaryCollinear Θ f := by
  constructor
  · intro hmin
    obtain ⟨optimal, hoptimal⟩ := group_isotope_admits_unitary_collinear f hq hgroup
    apply (absolute_feasible_bound_rigidity f hq Θ hmin.1).mp
    have hlower := absolute_feasible_bound_lower f Θ hmin.1
    have hupper := hmin.2 optimal hoptimal.feasible
    rw [uc_objective_value optimal f hoptimal] at hupper
    exact le_antisymm hupper hlower
  · intro huc
    refine ⟨huc.feasible, ?_⟩
    intro other hother
    rw [uc_objective_value Θ f huc]
    exact absolute_feasible_bound_lower f other hother

theorem group_isotope_global_minimizer_classification
    (Θ : HCParams n) (f : BinOp n) (hq : IsQuasigroup f)
    (hgroup : IsGroupIsotope f) (hmin : IsGlobalMinimizer Θ f) :
    ∃ g : BinOp n, IsLoop g ∧ IsAssociative g ∧
      ∃ φ ψ χ : Equiv.Perm (Fin n), IsIsotopic f g ∧
        (∀ a b, g.op (φ a) (ψ b) = χ (f.op a b)) ∧
        ∃ L R S : Matrix (Fin n) (Fin n) ℂ,
          L ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
          R ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
          S ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
          (∀ a, Θ.A a = L * leftRegularRep g (φ a) * R.conjTranspose) ∧
          (∀ b, Θ.B b = R * leftRegularRep g (ψ b) * S.conjTranspose) ∧
          (∀ c, Θ.C c = S * (leftRegularRep g (χ c)).conjTranspose * L.conjTranspose) :=
  quasigroup_unitary_collinear_classification Θ f hq
    ((group_isotope_global_minimizer_iff_unitary_collinear Θ f hq hgroup).mp hmin)