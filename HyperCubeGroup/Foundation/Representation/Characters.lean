import HyperCubeGroup.Foundation.External.CharacterRigidity
import HyperCubeGroup.Foundation.Representation.UnitaryIntertwiner
import Mathlib.Algebra.Group.Shrink

/-! # Equal matrix characters give unitary equivalence (`prop:characters`)

The licensed character-rigidity reference supplies a linear isomorphism. We
extract an invertible matrix intertwiner and apply the proved polar-normalization
lemma. Finite groups in arbitrary universes are transported through `Shrink`.
-/
noncomputable section
open Matrix CategoryTheory
namespace HyperCubeGroup.Manuscript
open ThreeFamilySynchronization
variable {G : Type*} [Group G] {d : ℕ}

def matrixRepresentation (U : G →* UnitaryMatrix d) :
    Representation ℂ G (Fin d → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U)

private theorem matrix_character (H : Type) [Group H]
    (U : H →* UnitaryMatrix d) (g : H) :
    (FDRep.of (matrixRepresentation U)).character g =
      (U g : Matrix (Fin d) (Fin d) ℂ).trace := by
  change LinearMap.trace ℂ (Fin d → ℂ)
    (Matrix.toLin' (U g : Matrix (Fin d) (Fin d) ℂ)) = _
  exact Matrix.trace_toLin'_eq _

private theorem invertible_intertwiner_small {H : Type} [Group H] [Finite H]
    (U V : H →* UnitaryMatrix d)
    (hchar : ∀ g, (U g : Matrix (Fin d) (Fin d) ℂ).trace =
      (V g : Matrix (Fin d) (Fin d) ℂ).trace) :
    ∃ S : Matrix (Fin d) (Fin d) ℂ, IsUnit S ∧ ∀ g,
      S * (U g : Matrix (Fin d) (Fin d) ℂ) =
        (V g : Matrix (Fin d) (Fin d) ℂ) * S := by
  have hc : (FDRep.of (matrixRepresentation U)).character =
      (FDRep.of (matrixRepresentation V)).character := by
    funext g
    simpa only [matrix_character] using hchar g
  obtain ⟨i⟩ := RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq
    (FDRep.of (matrixRepresentation U)) (FDRep.of (matrixRepresentation V)) hc
  let f : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ) := FDRep.isoToLinearEquiv i
  let S : Matrix (Fin d) (Fin d) ℂ := LinearMap.toMatrix' f.toLinearMap
  have hS : IsUnit S := LinearMap.isUnit_toMatrix'_iff.2
    ((LinearMap.isUnit_iff_ker_eq_bot f.toLinearMap).2 (LinearMap.ker_eq_bot.2 f.injective))
  refine ⟨S, hS, ?_⟩
  intro g
  have hconj : matrixRepresentation V g = f.conj (matrixRepresentation U g) :=
    FDRep.Iso.conj_ρ i g
  have hf : f.toLinearMap.comp (matrixRepresentation U g) =
      (matrixRepresentation V g).comp f.toLinearMap := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hconj]
    simp [LinearEquiv.conj_apply_apply]
  have hm := congrArg LinearMap.toMatrix' hf
  change LinearMap.toMatrix' (f.toLinearMap.comp (Matrix.toLin' (U g : Matrix (Fin d) (Fin d) ℂ))) =
    LinearMap.toMatrix' ((Matrix.toLin' (V g : Matrix (Fin d) (Fin d) ℂ)).comp f.toLinearMap) at hm
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using hm

/-- Equal characters produce a genuinely invertible matrix intertwiner. -/
theorem invertible_intertwiner_of_character_eq [Finite G]
    (U V : G →* UnitaryMatrix d)
    (hchar : ∀ g, (U g : Matrix (Fin d) (Fin d) ℂ).trace =
      (V g : Matrix (Fin d) (Fin d) ℂ).trace) :
    ∃ S : Matrix (Fin d) (Fin d) ℂ, IsUnit S ∧ ∀ g,
      S * (U g : Matrix (Fin d) (Fin d) ℂ) =
        (V g : Matrix (Fin d) (Fin d) ℂ) * S := by
  let e : Shrink.{0} G ≃* G := Shrink.mulEquiv
  letI : Finite (Shrink.{0} G) := Finite.of_injective e e.injective
  obtain ⟨S, hS, hi⟩ := invertible_intertwiner_small
    (U.comp e.toMonoidHom) (V.comp e.toMonoidHom) (fun g => hchar (e g))
  refine ⟨S, hS, ?_⟩
  intro g
  obtain ⟨x, rfl⟩ := e.surjective g
  exact hi x

theorem unitary_equivalence_of_character_eq [Finite G]
    (U V : G →* UnitaryMatrix d)
    (hchar : ∀ g, (U g : Matrix (Fin d) (Fin d) ℂ).trace =
      (V g : Matrix (Fin d) (Fin d) ℂ).trace) :
    ∃ W : UnitaryMatrix d, ∀ g,
      (V g : Matrix (Fin d) (Fin d) ℂ) =
        (W : Matrix (Fin d) (Fin d) ℂ) * (U g : Matrix (Fin d) (Fin d) ℂ) *
          (W : Matrix (Fin d) (Fin d) ℂ).conjTranspose := by
  obtain ⟨S, hS, hi⟩ := invertible_intertwiner_of_character_eq U V hchar
  obtain ⟨W, hW⟩ := unitary_intertwiner_of_invertible U V S hS hi
  refine ⟨W, fun g => ?_⟩
  have hWW : (W : Matrix (Fin d) (Fin d) ℂ) *
      (W : Matrix (Fin d) (Fin d) ℂ).conjTranspose = 1 := W.property.2
  rw [hW g, mul_assoc, hWW, mul_one]

/-- The converse follows from trace invariance under unitary conjugation. -/
theorem character_eq_iff_unitary_equivalence [Finite G]
    (U V : G →* UnitaryMatrix d) :
    (∀ g, (U g : Matrix (Fin d) (Fin d) ℂ).trace =
      (V g : Matrix (Fin d) (Fin d) ℂ).trace) ↔
    ∃ W : UnitaryMatrix d, ∀ g,
      (V g : Matrix (Fin d) (Fin d) ℂ) =
        (W : Matrix (Fin d) (Fin d) ℂ) * (U g : Matrix (Fin d) (Fin d) ℂ) *
          (W : Matrix (Fin d) (Fin d) ℂ).conjTranspose := by
  refine ⟨unitary_equivalence_of_character_eq U V, ?_⟩
  rintro ⟨W, hW⟩ g
  have hw : (W : Matrix (Fin d) (Fin d) ℂ).conjTranspose * W = 1 := W.property.1
  rw [hW g, Matrix.trace_mul_cycle, hw, one_mul]

/-- Character equality also forces the dimensions to agree; no common dimension is assumed. -/
theorem dimension_eq_of_character_eq {m : ℕ}
    (U : G →* UnitaryMatrix d) (V : G →* UnitaryMatrix m)
    (hchar : ∀ g, (U g : Matrix (Fin d) (Fin d) ℂ).trace =
      (V g : Matrix (Fin m) (Fin m) ℂ).trace) : d = m := by
  have h := hchar 1
  simp only [map_one] at h
  change (1 : Matrix (Fin d) (Fin d) ℂ).trace = (1 : Matrix (Fin m) (Fin m) ℂ).trace at h
  simpa using h

/-- Arbitrary matrix dimensions: equal characters identify the dimensions and give
unitary equivalence after that identification. This includes zero-dimensional spaces. -/
theorem character_determines_unitary_representation [Finite G] {m : ℕ}
    (U : G →* UnitaryMatrix d) (V : G →* UnitaryMatrix m)
    (hchar : ∀ g, (U g : Matrix (Fin d) (Fin d) ℂ).trace =
      (V g : Matrix (Fin m) (Fin m) ℂ).trace) :
    ∃ hdim : d = m, ∃ W : UnitaryMatrix d, ∀ g,
      ((hdim.symm ▸ V) g : Matrix (Fin d) (Fin d) ℂ) =
        (W : Matrix (Fin d) (Fin d) ℂ) * (U g : Matrix (Fin d) (Fin d) ℂ) *
          (W : Matrix (Fin d) (Fin d) ℂ).conjTranspose := by
  have hd := dimension_eq_of_character_eq U V hchar
  subst m
  exact ⟨rfl, unitary_equivalence_of_character_eq U V hchar⟩

end HyperCubeGroup.Manuscript
