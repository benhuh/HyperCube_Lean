# HyperCube Group Discovery — Lean 4 Formalization

Formal verification of the HyperCube tensor factorization model for finite quasigroups, accompanying the updated ICLR 2027 manuscript.

This repository mechanizes the orthogonal decomposition of the objective, the unit-normalized-trace Matrix AM-GM inequality, the unitary group-isotope equivalence, and the feasible landscape bounds. The precise correspondence and remaining gaps are documented below.

## Named Axiom-Free Theorems

For each named theorem below, `#print axioms <name>` uses only standard Lean background axioms (a subset of `[propext, Classical.choice, Quot.sound]`), not project-specific axioms. The scope column distinguishes the Lean statement from stronger manuscript claims.

| Manuscript | LaTeX label | Lean name | File | Formalized scope |
| --- | --- | --- | --- | --- |
| Lemma 1: Decomposition | `lem:decomposition` | `decomposition`, `objective_ge_inverseScalePenalty` | [Decomposition.lean](HyperCubeGroup/Decomposition.lean) | Objective decomposition and lower bound for nondegenerate parameters |
| Lemma 2: Shared Gram Matrices | `lem:index-independent-gram` | `shared_gram_matrices` | [CollinearManifold.lean](HyperCubeGroup/CollinearManifold.lean) | Shared normalized Gram matrix under feasible, nondegenerate collinearity |
| Lemma 3: Normalized Rank | `lem:proj-kappa` | `normalized_rank_constant`, `kappa_one_iff_unitary` | [CollinearManifold.lean](HyperCubeGroup/CollinearManifold.lean) | Constant positive ratio, bound `κ ≤ 1`, and identity Gram matrices at `κ = 1` |
| Lemma 4: Scalar AM-GM Bound | `lem:AMGM` | `collinear_lower_bound` | [CollinearManifold.lean](HyperCubeGroup/CollinearManifold.lean) | Feasible specialization `ℬ_δ ≥ 3n²` |
| Lemma 5: Matrix AM-GM | `lem:app_matrix_amgm` | `matrix_amgm`, `matrix_amgm_equality` | [MatrixAMGM.lean](HyperCubeGroup/MatrixAMGM.lean) | Unit normalized trace: cyclic norm sum at least 3; equality forces unitary factors and `XYZ = I` |
| Theorem 7: Absolute Feasible Bound | `thm:absolute_lower_bound` | `absolute_feasible_bound_lower`, `absolute_feasible_bound_rigidity` | [GroupIsotope.lean](HyperCubeGroup/GroupIsotope.lean) | Feasible lower bound and equality iff unitary collinearity |
| Theorem 8: UC ⟺ Group Isotope | `thm:unitary_equivalence` | `unitary_collinearity_iff_group_isotope` | [GroupIsotope.lean](HyperCubeGroup/GroupIsotope.lean) | Full unitary existence equivalence |
| Theorem 9: Global Optimality and Associativity Gap | `thm:global_optimality_dichotomy` | `global_optimality_dichotomy`, `strict_gap_non_group_unconditional` | [GroupIsotope.lean](HyperCubeGroup/GroupIsotope.lean) | Group-isotope floor attainment; pointwise strict bound for every feasible non-group factorization |
| Lemma 10: Synchronization | `lem:app_synchronization` | `synchronization` | [GroupIsotope.lean](HyperCubeGroup/GroupIsotope.lean) | Unitary synchronizing gauge for loops |
| Lemma 11: Homomorphism and Injectivity | `lem:app_homomorphism` | `synchronized_homomorphism`, `synchronized_injective` | [GroupIsotope.lean](HyperCubeGroup/GroupIsotope.lean) | Homomorphism and injectivity of the synchronized map |
| Lemma 12: Uniqueness of Representation | `lem:app_representation_uniqueness` | `representation_unique` | [GroupIsotope.lean](HyperCubeGroup/GroupIsotope.lean) | Regular-character trace identity only; **not full unitary equivalence** |
| Lemma 13: Group-Isotope Sufficiency | `lem:app_group_existence` | `group_isotope_admits_unitary_collinear` | [GroupIsotope.lean](HyperCubeGroup/GroupIsotope.lean) | Explicit left-regular construction of a unitary collinear factorization |
| Lemma 14: Spectral Trace-Frobenius Bound | `lem:spectral_trace_frob` | `IsUpperTriangular.norm_trace_cubed_pow_four_le`, `matrix_schur_trace_bound_xyz` | [Spectral.lean](HyperCubeGroup/Spectral.lean), [BlockCyclic.lean](HyperCubeGroup/BlockCyclic.lean) | Upper-triangular bound, Schur reduction, and block-cyclic specialization |

Theorem 6 (`thm:unconditional_bound`, Dynamic Unconstrained Bound) has no corresponding arbitrary-parameter theorem in the core modules listed here. Despite its name, `universal_lower_bound_general` requires `Factorizes Θ f` and proves the feasible floor, not the dynamic unconstrained bound.

## Gauge-Quotient Theorems (Axiom-Free)

The feasible landscape results are also lifted to the combined gauge quotient `Coercivity.FeasibleCombinedGaugeQuotient n f` in [Coercivity.lean](HyperCubeGroup/Coercivity.lean). Names below are in the `Coercivity` namespace:

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
| `Decomposition.lean` | 869 | Objective decomposition `ℋ = ℬ_δ + ℛ_δ`, misalignment residuals |
| `CollinearManifold.lean` | 589 | Shared Gram matrices, `kappaTriple` analysis, `κ = 1 ⟺ unitary`, AM-GM lower bound |
| `GroupIsotope.lean` | 1308 | Group isotopes, isotopy transfer, unitary collinear factorizations, `ℋ = 3n²` for group isotopes |
| `Abelian.lean` | 312 | Diagonal rep, full U(n)³ gauge invariance, cyclic group instance |
| `MatrixAMGM.lean` | 297 | Unit-normalized-trace Matrix AM-GM and equality rigidity |
| `BlockCyclic.lean` | 519 | Block-cyclic 3n×3n matrix construction; structural equivalences |
| `Spectral.lean` | 1332 | Schur triangulation, trace bounds, equality cases |
| `Plancherel.lean` | 387 | Plancherel infrastructure: ℋ = mass matrix form, Fourier sums |
| `PontryaginBridge.lean` | 516 | `IsAbelianGroup.toAddCommGroup`, `characterBasis`, `abelian_admits_diagRep_optimum` |
| `ActiveSubspace.lean` | 740 | Active-subspace machinery |
| `ActiveSubspaceConstruction.lean` | 851 | Explicit discharge of `collinear_to_unitary_collinear` for full-rank cases |
| `ActiveSubspaceGeneric.lean` | 559 | Generic `gramOf` machinery |
| `Tikhonov.lean` | 639 | HCParams normed/finite-dim structure; Weierstrass + regularized existence theorems |
| `Coercivity.lean` | 4056 | Full gauge group structure, invariances, gauge orbit + setoid + quotient + lifted predicates |

**Core totals:** approximately 13,250 lines of Lean 4, **1 project axiom** (not used in the manuscript), **0 proof `sorry`s**.

## Core Formalized Results

**Orthogonal Decomposition and Geometric Alignment (Section 4).** `decomposition` splits `ℋ = ℬ_δ + ℛ_δ`; `shared_gram_matrices`, `normalized_rank_constant`, and `kappa_one_iff_unitary` develop the feasible collinear geometry. `collinear_lower_bound` proves the feasible scalar AM-GM floor.

**Global Optimality and Associativity Gap (Section 5).** `matrix_amgm` and `matrix_amgm_equality` establish Lemma 5 at unit normalized trace using Schur triangulation. `absolute_feasible_bound_lower` and `absolute_feasible_bound_rigidity` prove Theorem 7's feasible floor and equality geometry. `unitary_collinearity_iff_group_isotope` proves Theorem 8. `global_optimality_dichotomy` combines constructive floor attainment for group isotopes with `strict_gap_non_group_unconditional` for non-group targets.

**Deferred Proofs (Appendices B and C).** `synchronization`, `synchronized_homomorphism`, and `synchronized_injective` implement the unitary necessity argument. `group_isotope_admits_unitary_collinear` supplies sufficiency via `leftRegularRep`. `representation_unique` establishes the regular-character trace identity. The spectral and block-cyclic modules provide the Matrix AM-GM proof infrastructure.

## Additional Repository Results

These results remain in the core library but are not active numbered statements in the updated manuscript:

- `collinear_iff_group_isotope`: general feasible nondegenerate collinearity iff group isotopy; depends on the remaining project axiom.
- `optimality_within_collinear_manifold`: existence of a unitary optimum from a feasible collinear factorization, plus the collinear lower bound; depends on that same axiom and does not assert uniqueness.
- `Tikhonov.regularized_existence`: existence for the coercively regularized objective; no current manuscript theorem number.
- Active-subspace, abelian/Fourier, and gauge-quotient infrastructure extend the foundational results.

## Axioms (1)

The core contains no proof `sorry`s. Its single private project axiom, `collinear_to_unitary_collinear` in [GroupIsotope.lean](HyperCubeGroup/GroupIsotope.lean), assumes that a feasible nondegenerate collinear factorization implies the existence of a unitary collinear factorization.

This only concerns the general/rank-deficient extension, which is not used in the current manuscript, not its active Theorem 8. [ActiveSubspaceConstruction.lean](HyperCubeGroup/ActiveSubspaceConstruction.lean) discharges the `κ = 1` case. <!-- [what does 'discharges the `κ = 1` case' mean??] -->
 <!-- the general case remains open.  -->
The named feasible landscape and unitary equivalence results above do not depend on this axiom.

## Scope of Formalization (What is not Mechanized)

The manuscript coverage focuses on the **algebraic and geometric** results in Sections 4 and 5 and Appendices B and C.
The following manuscript components remain outside the scope of formalization:

* **Hessian eigenvalue analysis (Appendix F.2):**
- **Arbitrary-amplitude bounds:** the full complex-amplitude version of Lemma 5, the general inverse-rank/amplitude formulation of Lemma 4, and Theorem 6's dynamic unconstrained bound are not established by the core declarations listed above.
- **Representation uniqueness:** `representation_unique` proves the character identity used in Lemma 12, *not the character-theoretic unitary equivalence to the left-regular representation or the full minimizer classification asserted in Theorem 9*.
- **General collinearity:** the rank-deficient extension remains axiom-dependent and is not an active theorem in the updated manuscript.
- **Empirical results and training dynamics:** the experiments in Section 6 and Appendix D, numerical trade-offs, and optimizer convergence are not formalized by these algebraic results.

## Mathlib Upstream Candidates

The codebase contains several pieces of independent interest to the broader Lean / Mathlib community that are fully proved here and would naturally live upstream:

1. **Unitary Schur triangulation** (`matrix_unitary_schur_form`): `∃ U unitary, U†·A·U is upper triangular for any complex A`. Currently absent in Mathlib.
2. **Schur trace bound** (`IsUpperTriangular.norm_trace_cubed_pow_four_le`): `‖Tr(T³)‖⁴ ≤ N·(‖T·T‖²_F)³` for upper triangular `T`.
3. **Power-mean Hölder bound** (`Real.sum_pow_three_pow_four_le`): `(Σ f_i³)⁴ ≤ N · (Σ f_i⁴)³` for nonneg real `f`.
4. **`AddCommGroup (Fin n)` bridge**: Constructs the abelian-group typeclass directly from a finite quasigroup's cancellation laws (`IsAbelianGroup.toAddCommGroup`).

## Building

Requires [Lean 4](https://leanprover.github.io/) `v4.29.0-rc6` and the [Mathlib](https://github.com/leanprover-community/mathlib4) revision pinned in [lake-manifest.json](lake-manifest.json).

Run from the repository root:

```bash
lake build
lake env lean CheckAxioms.lean
```