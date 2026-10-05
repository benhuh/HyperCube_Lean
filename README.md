# HyperCube Group Discovery — Lean 4 Formalization

Formal verification of the HyperCube tensor factorization model for finite quasigroups, accompanying our submitted manuscript.

This repository mechanizes the orthogonal decomposition of the objective, the amplitude-dependent inverse-rank and Matrix AM-GM bounds, the dynamic unconstrained bound, the unitary and general group-isotope equivalences, and the feasible landscape bounds. The precise correspondence and remaining gaps are documented below.

## Named Axiom-Free Theorems

For each named theorem below, `#print axioms <name>` uses only standard Lean background axioms (a subset of `[propext, Classical.choice, Quot.sound]`), not project-specific axioms. The scope column distinguishes the Lean statement from stronger manuscript claims.

| Manuscript | Lean name | File | Formalized scope |
| --- | --- | --- | --- |
| Lemma 1: Decomposition | `decomposition`, `objective_ge_inverseScalePenalty` | [Decomposition.lean](HyperCubeGroup/Foundation/Decomposition.lean) | Objective decomposition and lower bound for nondegenerate parameters |
| Lemma 2: Shared Gram Matrices | `shared_gram_matrices`, `shared_gram_matrices_of_nonzero` | [CollinearManifold.lean](HyperCubeGroup/Foundation/CollinearManifold.lean) | Shared normalized Gram matrix under nondegenerate collinearity and nonzero supported predictions; feasible specialization retained |
| Lemma 3: Normalized Rank | `normalized_rank_constant`, `normalized_rank_constant_of_nonzero`, `kappa_one_iff_unitary` | [CollinearManifold.lean](HyperCubeGroup/Foundation/CollinearManifold.lean) | Common positive ratio, bound `κ ≤ 1`, and identity Gram matrices at `κ = 1` in the feasible case |
| Lemma 4: Scalar AM-GM Bound and Inverse-rank Penalty | `collinear_inverse_rank_bound`, `collinear_dynamic_floor_eq_iff`, `collinear_lower_bound` | [InverseRank.lean](HyperCubeGroup/Foundation/InverseRank.lean), [CollinearManifold.lean](HyperCubeGroup/Foundation/CollinearManifold.lean) | Full amplitude-dependent inverse-rank bound under collinearity and nonzero supported predictions; nondegeneracy follows automatically; sharp equality iff all squared slice norms are equal; dynamic-floor equality additionally requires `κ = 1` |
| Lemma 5: Matrix AM-GM | `matrix_amgm_general`, `matrix_amgm`, `matrix_amgm_equality` | [MatrixAMGM.lean](HyperCubeGroup/Foundation/MatrixAMGM.lean) | Arbitrary complex normalized trace, including zero; equality rigidity at unit normalized trace |
| Theorem 6: Dynamic Unconstrained Bound | `dynamic_unconstrained_bound`, `dynamicFloor_eq_of_factorizes` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean) | Prediction-dependent floor for arbitrary parameters on any binary operation; no feasibility, nondegeneracy, or collinearity hypothesis |
| Theorem 7: Absolute Feasible Bound | `absolute_feasible_bound_lower`, `absolute_feasible_bound_rigidity` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean) | Feasible lower bound and equality iff unitary collinearity |
| Theorem 8: UC ⟺ Group Isotope | `unitary_collinearity_iff_group_isotope` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean) | Full unitary existence equivalence |
| Theorem 9: Global Optimality and Associativity Gap | `global_optimality_dichotomy`, `group_isotope_global_minimizer_classification`, `strict_gap_non_group`, `strict_gap_non_group_unconditional` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean), [RepresentationClassification.lean](HyperCubeGroup/Foundation/RepresentationClassification.lean) | Full group-isotope global minimizer classification up to isotopy and three unitary gauges of the left-regular representation; non-group targets have only a pointwise strict bound for every feasible factorization |
| Lemma 10: Synchronization | `synchronization` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean) | Unitary synchronizing gauge for loops |
| Lemma 11: Homomorphism and Injectivity | `synchronized_homomorphism`, `synchronized_injective` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean) | Homomorphism and injectivity of the synchronized map |
| Lemma 12: Uniqueness of Representation | `representation_unique`, `representation_unitary_equivalence` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean), [RepresentationClassification.lean](HyperCubeGroup/Foundation/RepresentationClassification.lean) | Regular-character trace identity and full unitary equivalence to the left-regular representation for a synchronized feasible associative loop |
| Lemma 13: Group-Isotope Sufficiency | `group_isotope_admits_unitary_collinear` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean) | Explicit left-regular construction of a unitary collinear factorization |
| Lemma 14: Spectral Trace-Frobenius Bound | `IsUpperTriangular.norm_trace_cubed_pow_four_le`, `matrix_schur_trace_bound_xyz` | [Spectral.lean](HyperCubeGroup/Foundation/Spectral.lean), [BlockCyclic.lean](HyperCubeGroup/Foundation/BlockCyclic.lean) | Upper-triangular bound, Schur reduction, and block-cyclic specialization |
| Theorem 15: General Collinearity ⟺ Group Isotope | `collinear_iff_group_isotope`, `collinear_to_unitary_collinear` | [GeneralCollinearity.lean](HyperCubeGroup/Foundation/GeneralCollinearity.lean) | Full feasible collinear existence equivalence, including rank-deficient and imbalanced factors; existence of a new unitary factorization |

Theorem 6 proves

$$\mathcal H(\Theta)\ge 3\sum_{a,b}|T_{ab,f(a,b)}(\Theta)|^{4/3}.$$

This includes vanishing supported predictions. Under exact factorization, `dynamicFloor_eq_of_factorizes` reduces the floor to `3n²`; Theorem 7 supplies its feasible equality characterization.

On the collinear set with nonzero supported predictions, Lemma 4 proves

$$\mathcal H(\Theta)=\mathcal B_\delta(\Theta)\ge 3\kappa^{-1/3}\sum_{a,b}|T_{ab,f(a,b)}(\Theta)|^{4/3}.$$

Equality in this sharper bound holds exactly when all squared slice norms are equal. Equality with the unpenalized dynamic floor additionally requires `κ = 1`.

`nonzero_supported_predictions_implies_nondegenerate` proves that nonzero supported predictions imply nonzero slice norms for a quasigroup, so Lemma 4 requires no separate nondegeneracy premise. Under feasibility, supported predictions equal 1. The common-positive-κ formula is stated on this nonzero-prediction domain; Theorem 6 also covers vanishing predictions.

## Gauge-Quotient Theorems (Axiom-Free)

The feasible landscape results are also lifted to the combined gauge quotient `Coercivity.FeasibleCombinedGaugeQuotient n f` in [Coercivity.lean](HyperCubeGroup/Foundation/Coercivity.lean). Names below are in the `Coercivity` namespace:

- `absolute_feasible_bound_lower_feasibleQuotient`: Theorem 7 lower bound `ℋ(Θ).re ≥ 3n²`.
- `case2_strict_gap_non_group_feasibleQuotient`: Theorem 9 pointwise strict bound for non-group targets.
- `isOptimal_iff_unitaryCollinear_feasibleQuotient`: Theorem 7 equality characterization.
- `exists_isOptimal_iff_group_isotope_feasibleQuotient`: Theorems 8 and 9 floor-attainment characterization.
- `global_optimality_dichotomy_feasibleQuotient`, `feasibleQuotient_optimal_or_strict`: feasible dichotomy.

## Overview

We formalize the theory of HyperCube parameters `Θ = (A, B, C)` where the structure tensor of a finite quasigroup `(Q, ∘)` of order `n` is approximated by:

$$T_{abc} = \frac{1}{n} \operatorname{Tr}(A_a B_b C_c)$$

The Jacobian-based objective is:

$$\mathcal{H}(\Theta) = \sum_{a,b,c} \delta_{abc}\left(\|B_b C_c\|^2 + \|C_c A_a\|^2 + \|A_a B_b\|^2\right)$$

The norms are normalized Frobenius norms. For a quasigroup table, `|δ| = n²`. The objective decomposes into an inverse-scale penalty `ℬ_δ` and a misalignment penalty `ℛ_δ`. Feasible parameters attaining `ℋ = 3|δ| = 3n²` are unitary and lie on the **collinear set**, where `ℛ_δ = 0`.

## Files

| File | Lines | Description |
| ------ | ------: | ------------- |
| `Basic.lean` | 260 | Core definitions: `BinOp`, `HCParams`, `Factorizes`, `objective`, `frobInner`, `frobNormSq` |
| `Decomposition.lean` | 888 | Objective decomposition `ℋ = ℬ_δ + ℛ_δ`, misalignment residuals |
| `CollinearManifold.lean` | 728 | Shared Gram matrices and common κ for nonzero supported predictions; feasible unitary and lower-bound results |
| `ScalarInverseRank.lean` | 122 | Scalar inverse-rank AM-GM inequality and sharp equality criterion |
| `InverseRank.lean` | 210 | Full collinear inverse-rank bound, global norm balancing, and dynamic-floor equality at κ = 1 |
| `GroupIsotope.lean` | 1235 | Dynamic unconstrained bound, isotopy transfer, unitary equivalence, and feasible landscape bounds |
| `GeneralCollinearity.lean` | 195 | General collinearity equivalence via associative sandwich products and feasibility |
| [RepresentationClassification.lean](HyperCubeGroup/Foundation/RepresentationClassification.lean) | 285 | Feasible loop synchronization, full unitary equivalence, and group-isotope global minimizer classification up to isotopy and three unitary gauges |
| [Representation/Characters.lean](HyperCubeGroup/Foundation/Representation/Characters.lean) | 130 | Character equality implies unitary equivalence; generic machinery in `HyperCubeGroup.Manuscript` |
| [Representation/UnitaryIntertwiner.lean](HyperCubeGroup/Foundation/Representation/UnitaryIntertwiner.lean) | 90 | Unitarization of invertible intertwiners in `HyperCubeGroup.Manuscript` |
| [Representation/UnitaryMatrix.lean](HyperCubeGroup/Foundation/Representation/UnitaryMatrix.lean) | 8 | Shared unitary matrix type in `HyperCubeGroup.ThreeFamilySynchronization` |
| [External/CharacterRigidity.lean](HyperCubeGroup/Foundation/External/CharacterRigidity.lean) | 250 | Licensed character-rigidity proof; Apache 2.0 license retained in [External/LICENSE](HyperCubeGroup/Foundation/External/LICENSE) |
| `Abelian.lean` | 312 | Diagonal rep, full U(n)³ gauge invariance, cyclic group instance |
| `MatrixAMGM.lean` | 341 | Arbitrary-amplitude Matrix AM-GM and unit-trace equality rigidity |
| `BlockCyclic.lean` | 519 | Block-cyclic 3n×3n matrix construction; structural equivalences |
| `Spectral.lean` | 1332 | Schur triangulation, trace bounds, equality cases |
| `Plancherel.lean` | 387 | Plancherel infrastructure: ℋ = mass matrix form, Fourier sums |
| `PontryaginBridge.lean` | 516 | `IsAbelianGroup.toAddCommGroup`, `characterBasis`, `abelian_admits_diagRep_optimum` |
| `ActiveSubspace.lean` | 740 | Active-subspace machinery |
| `ActiveSubspaceConstruction.lean` | 851 | Explicit norm-rescaling conversion to unitary collinearity for full-rank cases |
| `ActiveSubspaceGeneric.lean` | 559 | Generic `gramOf` machinery |
| `Tikhonov.lean` | 639 | HCParams normed/finite-dim structure; Weierstrass + regularized existence theorems |
| `Coercivity.lean` | 4053 | Full gauge group structure, invariances, gauge orbit + setoid + quotient + lifted predicates |

All files in this table live recursively under `HyperCubeGroup/Foundation`.

**Core totals:** 14,650 lines of Lean 4 across 23 files, **0 project axioms**, **0 proof `sorry`s**.

## Core Formalized Results

**Orthogonal Decomposition and Geometric Alignment (Section 4).** `decomposition` splits `ℋ = ℬ_δ + ℛ_δ`. `shared_gram_matrices_of_nonzero` and `normalized_rank_constant_of_nonzero` extend the shared-Gram and common-κ results beyond exact fitting to nonzero supported predictions. `collinear_inverse_rank_bound` proves Lemma 4's sharp inverse-rank bound and global equality criterion; `collinear_dynamic_floor_eq_iff` supplies its κ = 1 equality clause. The feasible specialization `collinear_lower_bound` remains available.

**Global Optimality and Associativity Gap (Section 5).** `matrix_amgm_general` establishes Lemma 5's arbitrary-amplitude inequality; `matrix_amgm_equality` proves rigidity at unit normalized trace. `dynamic_unconstrained_bound` proves Theorem 6. `absolute_feasible_bound_lower` and `absolute_feasible_bound_rigidity` prove Theorem 7's feasible floor and equality geometry. `unitary_collinearity_iff_group_isotope` proves Theorem 8. `global_optimality_dichotomy` combines constructive floor attainment for group isotopes with **the pointwise strict bound for non-group targets**. **Both `strict_gap_non_group` and `strict_gap_non_group_unconditional` remain available.**

**Deferred Proofs (Appendices B and C).** `synchronization`, `synchronized_homomorphism`, and `synchronized_injective` implement the unitary necessity argument. The stronger `loop_unitary_synchronization` in [RepresentationClassification.lean](HyperCubeGroup/Foundation/RepresentationClassification.lean) preserves feasibility and reconstructs all three original slice families using unitary gauges. `group_isotope_admits_unitary_collinear` supplies sufficiency via `leftRegularRep`. `representation_unique` establishes the regular-character trace identity, and `representation_unitary_equivalence` upgrades it to full unitary equivalence for synchronized feasible associative loops. `group_isotope_global_minimizer_classification` classifies every group-isotope global minimizer up to isotopy and three unitary gauges of the left-regular representation. **Generic character and intertwiner machinery retains the `HyperCubeGroup.Manuscript` namespace.** The spectral and block-cyclic modules provide the Matrix AM-GM proof infrastructure.

## Additional Repository Results

These results remain in the core library but are not active numbered statements in the manuscript:

- `Tikhonov.regularized_existence`: existence for the coercively regularized objective; no current manuscript theorem number.
- Active-subspace, abelian/Fourier, and gauge-quotient infrastructure extend the foundational results.

## General Collinearity--Associativity Equivalence (Theorem 15) 

[GeneralCollinearity.lean](HyperCubeGroup/Foundation/GeneralCollinearity.lean) proves that a finite quasigroup admits a feasible collinear factorization if and only if it is a group isotope. The proof includes rank-deficient and imbalanced factors and derives nondegeneracy from feasibility.

After isotopy to a loop with identity `e`, the cyclic collinearity identities define an associative sandwich product of output adjoints: with `D_a = C_a†` and `K = B_e† A_e†`, one has `D_a K D_b = λ_ab D_(a∘b)` with nonzero coefficients. Feasibility distinguishes nonzero scalar multiples of different output slices, forcing the loop operation to be associative. Neither the slices nor `K` need to be invertible.

The existing left-regular construction then supplies a new unitary collinear factorization. Thus `collinear_to_unitary_collinear` is a proved theorem, not an axiom; it does not assert that norm-rescaling or extending the original slices preserves feasibility. `collinear_implies_group_isotope` also remains available with a complete proof.

The separate active-subspace construction is additional geometric infrastructure, not a prerequisite for Theorem 15. In its full-rank `κ = 1` case, it explicitly proves that norm-rescaling the original slices gives a feasible unitary collinear factorization.

## Proof Assumptions

The foundational sources contain no project axioms and no proof `sorry`s. The named results use only standard Lean background axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## Scope of Formalization (What is not Mechanized)

The manuscript coverage focuses on the **algebraic and geometric** results in Sections 4 and 5, their supporting appendix proofs, and the general collinearity equivalence of Theorem 15.
The following manuscript components remain outside the scope of formalization:

- **Hessian eigenvalue analysis (Appendix F.2):** the manuscript's Hessian eigenvalue analysis is not formalized here.
<!-- - **Positive infimum gap:** the Lean non-group theorem proves `ℋ(Θ) > 3n²` for each feasible `Θ`. This alone does not prove the manuscript's stronger `inf ℋ > 3n²`, which would require a uniform gap or an appropriate attainment argument. [Do we need to keep this comment? is this crucial to have?] -->
- **Empirical results and training dynamics:** the experiments in Section 6 and Appendix D, numerical trade-offs, and optimizer convergence are not formalized by these algebraic results.

## Mathlib Upstream Candidates

The codebase contains several pieces of independent interest to the broader Lean / Mathlib community that are fully proved here and would naturally live upstream:

1. **Unitary Schur triangulation** (`matrix_unitary_schur_form`): `∃ U unitary, U†·A·U is upper triangular for any complex A`. Currently absent in Mathlib.
2. **Schur trace bound** (`IsUpperTriangular.norm_trace_cubed_pow_four_le`): `‖Tr(T³)‖⁴ ≤ N·(‖T·T‖²_F)³` for upper triangular `T`.
3. **Power-mean Hölder bound** (`Real.sum_pow_three_pow_four_le`): `(Σ f_i³)⁴ ≤ N · (Σ f_i⁴)³` for nonneg real `f`.
4. **`AddCommGroup (Fin n)` bridge**: Constructs the abelian-group typeclass directly from a finite quasigroup's cancellation laws (`IsAbelianGroup.toAddCommGroup`).

## Building

Requires [Lean 4](https://leanprover.github.io/) `v4.29.0-rc6` and the [Mathlib](https://github.com/leanprover-community/mathlib4) revision pinned in [lake-manifest.json](lake-manifest.json).

For a standalone Foundation package, copy the entire `HyperCubeGroup/Foundation` subtree, including [External/CharacterRigidity.lean](HyperCubeGroup/Foundation/External/CharacterRigidity.lean) and [External/LICENSE](HyperCubeGroup/Foundation/External/LICENSE), retaining the source attribution and Apache 2.0 license. Generic machinery retains the `HyperCubeGroup.Manuscript` namespace. Imports use only the canonical Foundation paths.

Run from the repository root:

```bash
lake build
```

To inspect a particular theorem's assumptions, import its module and use `#print axioms`, for example:

```lean
import HyperCubeGroup.Foundation.GeneralCollinearity

#print axioms collinear_iff_group_isotope
#print axioms collinear_to_unitary_collinear
#print axioms strict_gap_non_group
```

These declarations report only standard Lean background axioms. No separate test or audit package is required to check the foundational proofs.