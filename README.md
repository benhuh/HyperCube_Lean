# HyperCube Group Discovery — Lean 4 Formalization

Formal verification of the canonical tensor factorization model and sensitivity objective for arbitrary finite binary operations, accompanying our submitted manuscript.

This repository mechanizes the support-local Cauchy--Schwarz bound and orthogonal decomposition, shared balancedness (normalized Gram geometry), normalized rank, collinear output-dependent inverse-rank bounds, Matrix AM--GM, and global output-dependent and feasible-set lower bounds for arbitrary binary operations. It also proves the unitary and general collinearity group-isotope equivalences for quasigroups.
Foundation results for arbitrary finite binary operations establish general floor rigidity, input-redundancy characterization at the floor, cancellation rigidity of reduced tables, exact reduced unitary factorization, feasible-set nonemptiness, and fixed-target and fixed-order uniform positive gaps for objective values and their real infimum whenever no feasible floor point exists. Theorem 8 covers all finite binary operations at each fixed positive order, not only quasigroups.
The precise correspondence and remaining limitations are documented below.

## Named Axiom-Free Theorems

For each named theorem below, `#print axioms <name>` uses only standard Lean background axioms (a subset of `[propext, Classical.choice, Quot.sound]`), not project-specific axioms. The scope column states the hypotheses and conclusions of each formalized result.

| Manuscript | Lean name | File | Formalized scope |
| --- | --- | --- | --- |
| Proposition 0: Exact Factorization Exists | `feasible_nonempty`, `PositiveGap.feasibleObjectiveValues_nonempty` | [Basic.lean](HyperCubeGroup/Foundation/Basic.lean), [PositiveGap.lean](HyperCubeGroup/Foundation/PositiveGap.lean) | Every finite binary operation of positive order admits full exact reconstruction, and its feasible objective set is nonempty; no quasigroup assumption |
| Lemma 1: Cauchy--Schwarz Bound | `support_decomposition`, `decomposition`, `objective_ge_inverseScalePenalty` | [SupportDecomposition.lean](HyperCubeGroup/Foundation/SupportDecomposition.lean), [Decomposition.lean](HyperCubeGroup/Foundation/Decomposition.lean) | Objective decomposition `ℋ = ℬ_δ + ℛ_δ` and Cauchy--Schwarz lower bound `ℋ ≥ ℬ_δ` for arbitrary operations under `SupportNondegenerate` (or global `Nondegenerate`); unused output norms are unrestricted |
| Lemma 2: Shared Balancedness (Eq. (7)) | `support_collinear_shared_gram_matrices`, `support_local_gram_identities`, `support_local_grams_posSemidef` | [SupportInverseRank.lean](HyperCubeGroup/Foundation/SupportInverseRank.lean), [SupportGeometry.lean](HyperCubeGroup/Foundation/SupportGeometry.lean), [SupportGramRigidity.lean](HyperCubeGroup/Foundation/SupportGramRigidity.lean) | Shared normalized input Gram `Z` and cyclic local normalized Gram identities under collinearity and nonzero supported predictions, without a quasigroup premise; local positive semidefiniteness requires neither hypothesis |
| Lemma 3: Normalized Rank κ | `support_collinear_rank_identification`, `support_kappa_one_iff_local_normalized_grams_identity` | [SupportInverseRank.lean](HyperCubeGroup/Foundation/SupportInverseRank.lean), [SupportGramRigidity.lean](HyperCubeGroup/Foundation/SupportGramRigidity.lean) | For arbitrary operations under collinearity and nonzero supported predictions: common `0 < κ ≤ 1`, `nκ = rank Z = rank A_a = rank B_b = rank C_{f(a,b)}`, and `κ = 1` iff all normalized supported Grams (both orientations) are `I` |
| Lemma 4: Collinear Output-Dependent Bound and Inverse-Rank Penalty | `support_collinear_inverse_rank_bound`, `support_collinear_dynamic_floor_eq_iff` | [SupportInverseRank.lean](HyperCubeGroup/Foundation/SupportInverseRank.lean) | Collinear output-dependent inverse-rank bound for arbitrary operations under collinearity and nonzero supported predictions; support nondegeneracy follows automatically; sharp equality balances input and used-output squared norms only; output-dependent bound equality additionally requires `κ = 1` |
| Lemma 5: Matrix AM--GM | `matrix_amgm_general`, `matrix_amgm_general_equality_iff`, `matrix_amgm`, `matrix_amgm_equality` | [MatrixAMGM.lean](HyperCubeGroup/Foundation/MatrixAMGM.lean) | Arbitrary complex trace and zero trace, with full equality characterization including equality rigidity at unit normalized trace |
| Theorem 6: Global Output-Dependent Bound | `dynamic_unconstrained_bound`, `dynamicFloor_eq_of_factorizes` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean) | Global output-dependent lower bound for arbitrary parameters on any binary operation; no feasibility, nondegeneracy, or collinearity hypothesis |
| Theorem 7: Feasible-Set Lower Bound | `absolute_feasible_bound_lower`, `support_absolute_feasible_bound_rigidity`, `universal_lower_bound_general`, `equality_rigidity_general` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean), [SupportUnitary.lean](HyperCubeGroup/Foundation/SupportUnitary.lean) | Arbitrary-operation universal complexity floor `3|supp(δ)| = 3n²` and equality iff `SupportUnitaryCollinearFactorization` (forcing unitary inputs, unitary used outputs, and the supported product identity); `absolute_feasible_bound_rigidity` characterizes equality by global `UnitaryCollinear` for quasigroups |
| Lemma 17 (App. C.3.1): Spectral No-Escape | `spectral_no_escape` (private proof helper), `PositiveGap.local_no_escape_bounded`, `PositiveGap.normalized_feasible_near_floor_bounded` | [PositiveGap.lean](HyperCubeGroup/Foundation/PositiveGap.lean) | Fixed-dimension cubic-trace and squared-matrix Frobenius limit imply boundedness of the matrix sequence; near-floor feasible boundedness holds for arbitrary positive-order operations after `zeroUnusedOutputs` normalization |
| Theorem 8 (Sec. 4 & App. C.3.2): Positive Infimum Gap | `PositiveGap.exists_gap_of_no_floor`, `PositiveGap.exists_infimum_gap_of_no_floor`, `PositiveGap.exists_gap_fixed_order_of_no_floor`, `PositiveGap.exists_infimum_gap_fixed_order_of_no_floor`, `PositiveGap.floor_or_infimum_gap_fixed_order` | [PositiveGap.lean](HyperCubeGroup/Foundation/PositiveGap.lean) | For all finite binary operations at each fixed positive order, one positive epsilon bounds all no-floor feasible values and real infima; every operation either attains the floor or has this infimum gap |
| Theorem 9: Unitary Collinearity ⟺ Group Isotope | `unitary_collinearity_iff_group_isotope` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean) | Full unitary existence equivalence for quasigroups |
| Theorem 10: Global Optimality for Quasigroups | `global_optimality_dichotomy`, `group_isotope_global_minimizer_classification`, `strict_gap_non_group`, `PositiveGap.exists_gap_fixed_order`, `PositiveGap.exists_infimum_gap_fixed_order` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean), [RepresentationClassification.lean](HyperCubeGroup/Foundation/RepresentationClassification.lean), [PositiveGap.lean](HyperCubeGroup/Foundation/PositiveGap.lean) | Quasigroup floor-attainment characterization and full group-isotope global minimizer classification up to isotopy and three unitary gauges of the left-regular representation; nongroup-isotope quasigroups have the fixed-order positive associativity gap for feasible values and their real infimum |
| Lemma 12 (App. B.2): Synchronization | `loop_unitary_synchronization` | [RepresentationClassification.lean](HyperCubeGroup/Foundation/RepresentationClassification.lean) | For a unitary collinear loop factorization, constructs a synchronized feasible family and reconstructs all three given factor families using unitary gauges |
| Lemma 13 (App. B.2): Homomorphism and Injectivity | `synchronized_homomorphism`, `synchronized_injective` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean) | Homomorphism and injectivity of a synchronized feasible loop map |
| Lemma 14 (App. B.2): Uniqueness of Representation | `synchronized_character_regular`, `representation_unitary_equivalence` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean), [RepresentationClassification.lean](HyperCubeGroup/Foundation/RepresentationClassification.lean) | Regular-character trace identity and full unitary equivalence to the left-regular representation for a synchronized feasible associative loop |
| Lemma 15 (App. B.2): Group-Isotope Sufficiency | `group_isotope_admits_unitary_collinear` | [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean) | Explicit left-regular construction of a unitary collinear factorization |
| Lemma 16 (App. C.1–C.2): Spectral Trace--Frobenius Bound | `IsUpperTriangular.norm_trace_cubed_pow_four_le`, `matrix_schur_trace_bound_xyz` | [Spectral.lean](HyperCubeGroup/Foundation/Spectral.lean), [BlockCyclic.lean](HyperCubeGroup/Foundation/BlockCyclic.lean) | Upper-triangular bound, Schur reduction, and block-cyclic specialization |
| Theorem 11 (Sec. 6 & App. E.2): Exact Reduced Unitary Factorization | `FloorDichotomy.floor_iff_reduced_unitary_factorization`, `FloorDichotomy.floor_factorization_descends`, `FloorDichotomy.ReducedUnitaryFactorization.params_factorizes`, `FloorDichotomy.ReducedUnitaryFactorization.params_floor` | [ExactStructure.lean](HyperCubeGroup/Foundation/ExactStructure.lean) | For every positive-order binary operation, full exact floor attainment iff the row and column quotients and used outputs admit unitary factors with the reduced product law and normalized-trace output orthonormality; both descent and lift are proved |
| Theorem 18 (App. E.1): Input Redundancy and Consistent Collisions | `FloorDichotomy.inputA_eq_iff_rows_eq`, `FloorDichotomy.inputB_eq_iff_columns_eq`, `FloorDichotomy.row_collision_iff_columns_eq`, `FloorDichotomy.column_collision_iff_rows_eq` | [FloorDichotomy.lean](HyperCubeGroup/Foundation/FloorDichotomy.lean), [ReducedTable.lean](HyperCubeGroup/Foundation/ReducedTable.lean) | At the floor, equal input slices are equivalent to identical entire rows or columns; a local collision propagates to an entire column or row |
| Theorem 19 (App. E.1): Group Isotope or Input Redundancy | `FloorDichotomy.floor_group_isotope_or_redundancy`, `FloorDichotomy.quasigroup_of_floor_no_redundancy`, `FloorDichotomy.group_isotope_of_floor_injective_inputs` | [FloorDichotomy.lean](HyperCubeGroup/Foundation/FloorDichotomy.lean) | Exact floor attainment forces a group isotope or repeated entire rows or columns; injective input families rule out redundancy |
| Corollary 20 (App. E.1): Uniform Infimum Gaps from Stray Collisions or No Redundancy | `FloorDichotomy.exists_gap_of_non_group_no_redundancy`, `FloorDichotomy.exists_gap_of_stray_row_collision`, `FloorDichotomy.exists_gap_of_stray_column_collision` | [UniformGap.lean](HyperCubeGroup/Foundation/UniformGap.lean) | Target-specific positive epsilon chosen before `Θ` and uniform over every feasible `Θ`, without a quasigroup premise: non-group target with neither repeated rows nor columns, or a collision at one input with disagreement at another |
| Theorem 21 (App. E.2): Reduced-Table Cancellation and Cardinalities | `FloorDichotomy.reducedTable_row_injective`, `FloorDichotomy.reducedTable_column_injective`, `FloorDichotomy.reducedTable_surjective`, `FloorDichotomy.reducedTable_card_bounds` | [ReducedTable.lean](HyperCubeGroup/Foundation/ReducedTable.lean) | Separate row and column quotients map onto used outputs; floor attainment gives separate injectivity and `max(r,s) ≤ t ≤ rs`; no associative quotient is asserted |
| Theorem 22 (App. E.2): Used-Output Orthonormality | `FloorDichotomy.used_output_trace_orthonormal` | [ReducedTable.lean](HyperCubeGroup/Foundation/ReducedTable.lean) | Used output slices have orthonormal normalized trace inner products at an exactly feasible floor point |

Theorem 6 proves the global output-dependent lower bound

$$\mathcal H(\Theta)\ge \mathcal H^*_\delta(T(\Theta)) := 3\sum_{\text{supp}(\delta)}|T_{abc}(\Theta)|^{4/3}.$$

This includes vanishing supported predictions. Under exact factorization ($T(\Theta)=\delta$), `dynamicFloor_eq_of_factorizes` reduces the bound to the universal complexity floor `3|supp(δ)| = 3n²`; Theorem 7 supplies its feasible equality characterization.

On the collinear set with nonzero supported predictions, Lemma 4 proves

$$\mathcal H(\Theta)=\mathcal B_\delta(\Theta)\ge \kappa^{-1/3}\,\mathcal H^*_\delta(T(\Theta)) = 3\kappa^{-1/3}\sum_{\text{supp}(\delta)}|T_{abc}(\Theta)|^{4/3}.$$

Equality in this sharper bound holds exactly when input and used-output squared norms are balanced: for every `a,b`, `frobNormSq (A_a) = frobNormSq (B_b) = frobNormSq (C_{f(a,b)})`. Unused output slices are unrestricted. Equality with the unpenalized output-dependent bound $\mathcal H^*_\delta(T(\Theta))$ additionally requires `κ = 1`.

`support_nondegenerate_of_nonzero` proves that nonzero supported predictions imply `SupportNondegenerate` for any binary operation, so Lemmas 2-4 require no separate nondegeneracy premise or quasigroup assumption. Under feasibility, supported predictions equal 1. The common-positive-κ formula is stated on this nonzero-prediction domain; Theorem 6 also covers vanishing predictions.

## Gauge-Quotient Theorems (Axiom-Free)

The feasible landscape results hold on the combined gauge quotient `Coercivity.FeasibleCombinedGaugeQuotient n f` in [Coercivity.lean](HyperCubeGroup/Foundation/Coercivity.lean). Its action combines common unitary conjugation with per-slice unit-modulus phases; feasibility-preserving phases satisfy `sA a * sB b * sC (f.op a b) = 1` on support. This is not the full `U(n)^3` action used in the representation classification. Names below are in the `Coercivity` namespace; all require feasible classes, and all except the lower-bound theorem require a quasigroup premise:

- `absolute_feasible_bound_lower_feasibleQuotient`: arbitrary-operation Theorem 7 lower bound `ℋ(Θ).re ≥ 3n²`.
- `case2_strict_gap_non_group_feasibleQuotient`: Theorem 10 pointwise strict bound for non-group targets.
- `isOptimal_iff_unitaryCollinear_feasibleQuotient`: Theorem 7 equality characterization.
- `exists_isOptimal_iff_group_isotope_feasibleQuotient`: Theorems 9 and 10 floor-attainment characterization.
- `global_optimality_dichotomy_feasibleQuotient`, `feasibleQuotient_optimal_or_strict`: feasible floor-or-strict-gap characterization.

## Overview

We formalize the theory of factorization parameters `Θ = (A, B, C)` where the structure tensor $\delta$ of a finite binary operation `(Q, ∘)` of positive order `n` is modeled (using normalized trace $\text{Tr}(X) := \frac{1}{n}\text{Trace}(X)$) by:

$$T_{abc}(\Theta) = \text{Tr}(A_a B_b C_c) = \frac{1}{n} \text{Trace}(A_a B_b C_c)$$

The sensitivity objective is:

$$\mathcal H (\Theta) = \sum_{(a,b,c)\in\text{supp}(\delta)} n \, \| \nabla_\Theta T_{abc}(\Theta)\|^2 = \sum_{\text{supp}(\delta)} \big( \|B_b C_c\|^2 + \| C_c A_a \|^2 + \| A_a B_b \|^2 \big)$$

The norms are normalized Frobenius norms ($\|X\|^2 = \text{Tr}(X^\dagger X)$). Every binary-operation table has support size `|supp(δ)| = n²`. Under support nondegeneracy, the objective decomposes into the Cauchy--Schwarz lower bound `ℬ_δ` and a nonnegative alignment gap `ℛ_δ = ℋ - ℬ_δ`. Feasible parameters attaining the universal complexity floor `ℋ = 3|supp(δ)| = 3n²` have unitary inputs and used outputs and lie on the **collinear set**, where `ℛ_δ = 0`; unused outputs need not be unitary.

`SupportNondegenerate` and `SupportUnitaryCollinearFactorization` express nondegeneracy and unitary collinearity on participating slices for arbitrary operations. `Nondegenerate` and `UnitaryCollinear` constrain every slice, including unused outputs. The bridges `Nondegenerate.toSupport`, `SupportNondegenerate.of_quasigroup`, `UnitaryCollinear.toSupport`, and `SupportUnitaryCollinearFactorization.of_quasigroup` relate these predicates; on quasigroups the support-local and all-slice predicates are equivalent.

## Files

| File | Description |
| ------ | ------------- |
| [Basic.lean](HyperCubeGroup/Foundation/Basic.lean) | Core definitions: `BinOp`, `HCParams`, `Factorizes`, `objective`, `frobInner`, `frobNormSq`, `SupportNondegenerate`; arbitrary-operation exact feasibility via `feasible_nonempty` |
| [Decomposition.lean](HyperCubeGroup/Foundation/Decomposition.lean) | Objective decomposition `ℋ = ℬ_δ + ℛ_δ`, alignment-gap residuals |
| [CollinearManifold.lean](HyperCubeGroup/Foundation/CollinearManifold.lean) | Quasigroup shared-balancedness (normalized Gram) and common-κ interfaces; feasible unitary and lower-bound results |
| [SupportGeometry.lean](HyperCubeGroup/Foundation/SupportGeometry.lean) | Arbitrary-operation support nondegeneracy, local normalized Gram identities, shared input Gram, projection identity, and slice-rank identification |
| [SupportDecomposition.lean](HyperCubeGroup/Foundation/SupportDecomposition.lean) | Support-local Cauchy--Schwarz bound and collinearity identities without global nondegeneracy |
| [SupportInverseRank.lean](HyperCubeGroup/Foundation/SupportInverseRank.lean) | Arbitrary-operation collinear Gram and rank API; inverse-rank bounds, supported norm balancing, and output-dependent bound equality |
| [SupportGramRigidity.lean](HyperCubeGroup/Foundation/SupportGramRigidity.lean) | Positive semidefinite normalized Grams and `κ = 1` iff all supported normalized Grams are identity |
| [SupportUnitary.lean](HyperCubeGroup/Foundation/SupportUnitary.lean) | Support unitary collinearity, arbitrary-operation feasible-floor equivalences and no-floor gaps, and bridges to all-slice quasigroup predicates |
| [ScalarInverseRank.lean](HyperCubeGroup/Foundation/ScalarInverseRank.lean) | Scalar inverse-rank AM--GM inequality and sharp equality criterion |
| [InverseRank.lean](HyperCubeGroup/Foundation/InverseRank.lean) | Quasigroup inverse-rank bound, global norm balancing, and output-dependent bound equality at κ = 1 |
| [GroupIsotope.lean](HyperCubeGroup/Foundation/GroupIsotope.lean) | Global output-dependent bound, isotopy transfer, unitary equivalence, and feasible-set lower bounds |
| [GroupIsotopeRegression.lean](HyperCubeGroup/Foundation/GroupIsotopeRegression.lean) | Verified regression checks for group-isotope factorizations |
| [GeneralCollinearity.lean](HyperCubeGroup/Foundation/GeneralCollinearity.lean) | Quasigroup collinearity equivalence via associative sandwich products and feasibility |
| [FloorDichotomy.lean](HyperCubeGroup/Foundation/FloorDichotomy.lean) | Arbitrary-operation input-redundancy characterization at the floor, input-slice equivalences, and collision propagation |
| [ReducedTable.lean](HyperCubeGroup/Foundation/ReducedTable.lean) | Separate row/column quotients, cancellation rigidity, cardinality bounds, and used-output trace orthonormality |
| [ExactStructure.lean](HyperCubeGroup/Foundation/ExactStructure.lean) | Exact floor iff reduced unitary data; factor-preserving descent, injectivity, gap criteria, and minimum-operation obstruction |
| [InputQuotients.lean](HyperCubeGroup/Foundation/InputQuotients.lean) | Floor-independent deterministic alphabet and fixed-length binary bounds; unique injective quotient factorizations, including order zero |
| [ExactStructureRegression.lean](HyperCubeGroup/Foundation/ExactStructureRegression.lean) | Verified examples: constant operation with an unused zero output, minimum-operation gap, duplicate rows and columns insufficient for floor attainment, and canonical quotient encodings |
| [RepresentationClassification.lean](HyperCubeGroup/Foundation/RepresentationClassification.lean) | Feasible loop synchronization, full unitary equivalence, and group-isotope global minimizer classification up to isotopy and three unitary gauges |
| [Representation/Characters.lean](HyperCubeGroup/Foundation/Representation/Characters.lean) | Character equality implies unitary equivalence; generic machinery in `HyperCubeGroup.Manuscript` |
| [Representation/UnitaryIntertwiner.lean](HyperCubeGroup/Foundation/Representation/UnitaryIntertwiner.lean) | Unitarization of invertible intertwiners in `HyperCubeGroup.Manuscript` |
| [Representation/UnitaryMatrix.lean](HyperCubeGroup/Foundation/Representation/UnitaryMatrix.lean) | Shared unitary matrix type in `HyperCubeGroup.ThreeFamilySynchronization` |
| [External/CharacterRigidity.lean](HyperCubeGroup/Foundation/External/CharacterRigidity.lean) | Licensed character-rigidity proof with its Apache 2.0 license in [External/LICENSE](HyperCubeGroup/Foundation/External/LICENSE) |
| [Abelian.lean](HyperCubeGroup/Foundation/Abelian.lean) | Diagonal rep, full U(n)³ gauge invariance, cyclic group instance |
| [MatrixAMGM.lean](HyperCubeGroup/Foundation/MatrixAMGM.lean) | General Matrix AM--GM, amplitude witness, and full equality characterization including zero trace |
| [BlockCyclic.lean](HyperCubeGroup/Foundation/BlockCyclic.lean) | Block-cyclic 3n×3n matrix construction; structural equivalences |
| [Spectral.lean](HyperCubeGroup/Foundation/Spectral.lean) | Schur triangulation, trace bounds, equality cases |
| [Plancherel.lean](HyperCubeGroup/Foundation/Plancherel.lean) | Plancherel infrastructure: ℋ = mass matrix form, Fourier sums |
| [PontryaginBridge.lean](HyperCubeGroup/Foundation/PontryaginBridge.lean) | `IsAbelianGroup.toAddCommGroup`, `characterBasis`, `abelian_admits_diagRep_optimum` |
| [ActiveSubspace.lean](HyperCubeGroup/Foundation/ActiveSubspace.lean) | Active-subspace machinery |
| [ActiveSubspaceConstruction.lean](HyperCubeGroup/Foundation/ActiveSubspaceConstruction.lean) | Explicit norm-rescaling conversion to unitary collinearity for full-rank cases |
| [ActiveSubspaceGeneric.lean](HyperCubeGroup/Foundation/ActiveSubspaceGeneric.lean) | Generic `gramOf` machinery |
| [Tikhonov.lean](HyperCubeGroup/Foundation/Tikhonov.lean) | HCParams normed/finite-dim structure; Weierstrass + regularized existence theorems |
| [PositiveGap.lean](HyperCubeGroup/Foundation/PositiveGap.lean) | Nonempty, bounded-below real objective-value set and `sInf` gaps; spectral no-escape, unused-output normalization, and arbitrary-operation fixed-target and fixed-order no-floor gaps |
| [UniformGap.lean](HyperCubeGroup/Foundation/UniformGap.lean) | General-operation uniform gaps for non-group targets without redundancy and for stray row or column collisions |
| [Coercivity.lean](HyperCubeGroup/Foundation/Coercivity.lean) | Common unitary conjugation and per-slice phase gauges; invariances, orbits, setoids, quotients, and lifted predicates |

All 36 files in this table live recursively under `HyperCubeGroup/Foundation` (18,144 lines total).

**Proof status:** **0 project axioms**, **0 proof `sorry`s**.

## Core Formalized Results

**Orthogonal Decomposition and Geometric Alignment (Section 3).** `support_decomposition` splits `ℋ = ℬ_δ + ℛ_δ` under support nondegeneracy. For arbitrary operations with collinearity and nonzero supported predictions, `support_collinear_shared_gram_matrices` and `support_local_gram_identities` give shared balancedness (`Z = supportGram Θ` and cyclic local normalized Gram identities); `support_local_grams_posSemidef` supplies positive semidefiniteness. `support_collinear_rank_identification` identifies `nκ` with the rank of `Z`, every input slice, and every used output. `support_kappa_one_iff_local_normalized_grams_identity` characterizes κ = 1 by identity normalized Grams in both orientations. `support_collinear_inverse_rank_bound` and `support_collinear_dynamic_floor_eq_iff` prove the collinear output-dependent bound and equality criteria, leaving unused outputs unrestricted. `collinear_lower_bound` is the feasible quasigroup inverse-rank bound.

**Global Lower Bounds, Complexity Floor, and Quasigroup Optimality (Sections 4–5).** `matrix_amgm_general` establishes Lemma 5's general Matrix AM--GM inequality; `matrix_amgm_general_equality_iff` proves equality at arbitrary trace. `dynamic_unconstrained_bound` proves Theorem 6's global output-dependent bound. `absolute_feasible_bound_lower` and `support_absolute_feasible_bound_rigidity` prove Theorem 7's arbitrary-operation universal complexity floor (`3|supp(δ)| = 3n²`) and equality geometry; `absolute_feasible_bound_rigidity` gives the all-slice quasigroup formulation. `unitary_collinearity_iff_group_isotope` proves Theorem 9 for quasigroups. Theorem 10's `global_optimality_dichotomy` gives constructive floor attainment for group isotopes and strictness for nongroup-isotope quasigroups via `strict_gap_non_group`. Theorem 8 gives a positive infimum gap uniform over all nonattaining targets of each fixed order.

`IsGroupIsotope f` means that `f` is isotopic to an **associative quasigroup**, hence to a finite group. `IsAssociativeIsotope f` means that `f` is isotopic to an associative operation, without a cancellation requirement. The two conditions coincide for quasigroup targets, but not for arbitrary operations.

**Unconditional Exact-Fit Positive Gaps (Lemma 17 and Theorem 8).** [PositiveGap.lean](HyperCubeGroup/Foundation/PositiveGap.lean) formalizes spectral no-escape and its block-cyclic matrix-triple specialization. For any finite binary operation of positive order, `PositiveGap.normalized_feasible_near_floor_bounded` bounds a positive-width feasible near-floor sublevel after `PositiveGap.zeroUnusedOutputs` normalization, which preserves exact feasibility and the support-weighted objective. Original unused output slices can be unbounded; this is not a global coercivity theorem.

`PositiveGap.exists_gap_fixed_order_of_no_floor` chooses a single positive constant before every target and feasible parameter:

$$\forall n\ge 1,\quad \exists\varepsilon_n>0,\quad \forall f,\quad \text{NoFloor}(f)\Longrightarrow\forall\Theta,\quad \text{Factorizes}(\Theta,f)\Longrightarrow\mathcal H_f(\Theta)\ge 3n^2+\varepsilon_n.$$

Here `f : BinOp n`, `Θ : HCParams n`, and `[NeZero n]` expresses positive order. `Factorizes` imposes all-output exact reconstruction of the fully observed table, and $\text{NoFloor}(f)$ means that every feasible $\Theta$ has $\mathcal H_f(\Theta)\ne 3n^2$. No quasigroup assumption is required. Nongroup-isotope operations can attain the floor, so failure to be a group isotope alone is not the general gap hypothesis.

`PositiveGap.exists_infimum_gap_fixed_order_of_no_floor` gives a common positive epsilon bounding `sInf (PositiveGap.feasibleObjectiveValues f)` below by $3n^2+\varepsilon_n$ for all no-floor operations of that order. `PositiveGap.floor_or_infimum_gap_fixed_order` chooses one positive epsilon before all operations and proves that each either has a feasible floor point or satisfies this infimum bound. The feasible-value and infimum bounds can use the same epsilon. The constant may depend on `n`; orders with no eligible targets have a positive constant and a vacuous no-floor conclusion. Neither attainment of a higher-energy infimum nor a gap independent of `n` is proved.

For quasigroups, nonattainment of the floor is equivalent to failure of group isotopy. `PositiveGap.exists_gap_fixed_order` and `PositiveGap.exists_infimum_gap_fixed_order` express this specialization under `IsQuasigroup f` and `¬ IsGroupIsotope f`. `PositiveGap.feasible_near_floor_bounded`, `PositiveGap.exists_gap`, and `PositiveGap.infimum_gt_floor` state the corresponding quasigroup boundedness and fixed-target gap results.

**Deferred Proofs (Appendices B and C).** `loop_unitary_synchronization` in [RepresentationClassification.lean](HyperCubeGroup/Foundation/RepresentationClassification.lean) preserves feasibility and reconstructs all three given factor families using unitary gauges; `synchronized_homomorphism` and `synchronized_injective` then establish the synchronized loop map's algebraic properties. `group_isotope_admits_unitary_collinear` supplies sufficiency via `leftRegularRep`. `synchronized_character_regular` establishes the regular-character trace identity, and `representation_unitary_equivalence` proves full unitary equivalence for synchronized feasible associative loops. `group_isotope_global_minimizer_classification` classifies every group-isotope global minimizer up to isotopy and three unitary gauges of the left-regular representation. Generic character and intertwiner machinery uses the `HyperCubeGroup.Manuscript` namespace. The spectral and block-cyclic modules provide the Matrix AM-GM proof infrastructure.

## Additional Repository Results

These library results are not numbered statements in the manuscript:

- `collinear_iff_group_isotope`, `collinear_to_unitary_collinear` ([GeneralCollinearity.lean](HyperCubeGroup/Foundation/GeneralCollinearity.lean)): full feasible collinear existence equivalence for quasigroups via associative sandwich products, including rank-deficient and imbalanced factors.
- `Tikhonov.regularized_existence` ([Tikhonov.lean](HyperCubeGroup/Foundation/Tikhonov.lean)): existence for the coercively regularized objective.
- Active-subspace ([ActiveSubspace.lean](HyperCubeGroup/Foundation/ActiveSubspace.lean), [ActiveSubspaceConstruction.lean](HyperCubeGroup/Foundation/ActiveSubspaceConstruction.lean), [ActiveSubspaceGeneric.lean](HyperCubeGroup/Foundation/ActiveSubspaceGeneric.lean)), abelian/Fourier ([Abelian.lean](HyperCubeGroup/Foundation/Abelian.lean), [Plancherel.lean](HyperCubeGroup/Foundation/Plancherel.lean), [PontryaginBridge.lean](HyperCubeGroup/Foundation/PontryaginBridge.lean)), input-quotient encoding ([InputQuotients.lean](HyperCubeGroup/Foundation/InputQuotients.lean)), and gauge-quotient ([Coercivity.lean](HyperCubeGroup/Foundation/Coercivity.lean)) infrastructure extend the foundational results.

## General Binary Operations (Beyond Quasigroups)

The support modules listed above and the results in [FloorDichotomy.lean](HyperCubeGroup/Foundation/FloorDichotomy.lean), [ReducedTable.lean](HyperCubeGroup/Foundation/ReducedTable.lean), and [UniformGap.lean](HyperCubeGroup/Foundation/UniformGap.lean), together with the general results in [PositiveGap.lean](HyperCubeGroup/Foundation/PositiveGap.lean), accept any finite total binary operation `f : BinOp n`. The support API, floor, and gap statements assume positive order, expressed by `[NeZero n]`, and exact feasibility means reconstruction at every input/output triple, not just on support. The input-redundancy, reduced-table, and uniform-gap modules use the `FloorDichotomy` namespace; the normalization and no-floor gap declarations use `PositiveGap`.

`feasible_nonempty` in [Basic.lean](HyperCubeGroup/Foundation/Basic.lean) constructs an exact factorization for every such operation, without quasigroup or output-surjectivity assumptions.
<!-- With matrix units $E_{ij}$, it takes $A_a=nE_{0a}$, $(B_b)_{ij}=\mathbb I_{\{f(i,b)=j\}}$, and $C_c=E_{c0}$, giving $\text{Tr}(A_aB_bC_c)=n^{-1}\text{Trace}(A_aB_bC_c)=\mathbb I_{\{f(a,b)=c\}}$. -->

The one-hot operation tensor has `|supp(δ)| = n²` for every binary operation. These results use the support-weighted objective; replacing it by three unweighted all-pairs sums requires quasigroup structure. Lemma 1's `support_decomposition` requires only support nondegeneracy; `decomposition` and `objective_ge_inverseScalePenalty` require global nondegeneracy. Lemmas 2–4 apply to arbitrary operations with collinearity and nonzero supported predictions, without constraints on unused outputs. Matrix and spectral bounds have no target-operation assumption, and `dynamic_unconstrained_bound` requires neither feasibility nor nondegeneracy. Theorem 7's `universal_lower_bound_general` gives `ℋ ≥ 3|supp(δ)| = 3n²` under feasibility; `equality_rigidity_general` forces unitary input slices, unitary **used** output slices, and the supported product identity, and `support_absolute_feasible_bound_rigidity` packages this as an iff with `SupportUnitaryCollinearFactorization`. Unused output slices need not be unitary.

### Floor Attainment and Input Redundancy

Theorem 19's `floor_group_isotope_or_redundancy` proves, without a quasigroup premise,

$$
\text{Factorizes}(\Theta,f)\land\mathcal H_f(\Theta)=3n^2
\Longrightarrow
\text{IsGroupIsotope}(f)\lor\text{RepeatedRows}(f)\lor\text{RepeatedColumns}(f).
$$

`RepeatedRows` and `RepeatedColumns` mean identical entire rows or columns with distinct labels, not rank deficiency. Theorem 18 identifies these repetitions exactly with equal input slices at the floor and proves that a collision at one input propagates to equality of entire columns or rows. Consequently, at a feasible floor point, absence of both repeated rows and repeated columns (or injectivity of both input slice families) forces a group isotope. The converse is not asserted for redundant tables: redundancy alone does not guarantee floor attainment.

### Reduced Tables and Cancellation Rigidity

`RowClass` and `ColumnClass` quotient labels by identical entire rows and columns separately, and `UsedOutput` contains the labels occurring in the table (`U_∘` in the manuscript). The well-defined `reducedTable` induces

$$\bar f:(Q/{\sim_R})\times(Q/{\sim_C})\longrightarrow\text{im}(f).$$

This map is always well-defined and surjective. At an exactly feasible floor point, Theorem 21 gives injectivity in each argument and, for row-class, column-class, and used-output counts `r`, `s`, and `t`,

$$\max(r,s)\le t\le rs.$$

The three cardinalities can differ, so this need not be a Latin square or a common quotient operation; no associativity or group structure is asserted. Theorem 22 additionally gives orthonormal used-output slices at the floor:

$$\text{Tr}(C_x^\dagger C_y)=\frac1n\text{Trace}(C_x^\dagger C_y)=\mathbb I_{\{x=y\}}\qquad(x,y\in\text{im}(f)).$$

Theorem 9's group-isotope equivalence requires quasigroups; Lemmas 1–4 and Theorem 7 use the general support interface.
These results concern operation tensors, not arbitrary nonnegative weighted tensors.

### General Fixed-Target Uniform Gaps (Theorem 8 and Corollary 20)

For any positive-order operation, let $V_f=\{\mathcal H_f(\Theta):\text{Factorizes}(\Theta,f)\}$. This set is nonempty and bounded below. If no exact factorization attains $3n^2$, Theorem 8's `PositiveGap.exists_gap_of_no_floor` and `PositiveGap.exists_infimum_gap_of_no_floor` prove

$$\exists\varepsilon_f>0,\quad 3n^2+\varepsilon_f\le\inf V_f\le\mathcal H_f(\Theta)\qquad\text{for every feasible }\Theta.$$

The proof zeros unused output slices, preserving feasibility and the objective, and uses `PositiveGap.normalized_feasible_near_floor_bounded` to obtain compactness near the floor. Original unused slices can be unbounded; neither global coercivity nor attainment of the higher-energy infimum is asserted. These fixed-target gaps also yield Theorem 8's common positive epsilon across all no-floor operations at each fixed positive order, via `PositiveGap.exists_gap_fixed_order_of_no_floor` and `PositiveGap.exists_infimum_gap_fixed_order_of_no_floor`.

Corollary 20 in [UniformGap.lean](HyperCubeGroup/Foundation/UniformGap.lean) supplies this uniform feasible-value gap under either obstruction:

- `FloorDichotomy.exists_gap_of_non_group_no_redundancy`: a nongroup-isotope target with neither repeated entire rows nor repeated entire columns.
- `FloorDichotomy.exists_gap_of_stray_row_collision` and `FloorDichotomy.exists_gap_of_stray_column_collision`: a pair collides at one input but disagrees at another, even if other redundancies exist.

### Exact Structure and Deterministic Coding

The exact reduced-factorization criterion is Theorem 11 (Section 6 and Appendix E.2) of the manuscript. The deterministic encoding bounds describe the separate input alphabets independently of floor attainment. All declarations named in this subsection are in `FloorDichotomy`.

For `f : BinOp n` with `[NeZero n]`, [ExactStructure.lean](HyperCubeGroup/Foundation/ExactStructure.lean) defines `ReducedUnitaryFactorization f`. Its maps `rowFactor : RowClass f → Matrix (Fin n) (Fin n) ℂ`, `columnFactor : ColumnClass f → Matrix (Fin n) (Fin n) ℂ`, and `outputFactor : UsedOutput f → Matrix (Fin n) (Fin n) ℂ` take unitary values, with

$$U_R V_S = W_{\bar f(R,S)}^\dagger,\qquad \text{Tr}(W_x^\dagger W_y)=\frac1n\text{Trace}(W_x^\dagger W_y)=\mathbb I_{\{x=y\}}.$$

`floor_iff_reduced_unitary_factorization` states exactly

```lean
(∃ Θ : HCParams n, Factorizes Θ f ∧ (objective Θ f).re = 3 * (n : ℝ) ^ 2) ↔
  Nonempty (ReducedUnitaryFactorization f)
```

`floor_factorization_descends` constructs these data from a given feasible floor point, preserving `Θ.A` on row classes, `Θ.B` on column classes, and `Θ.C` on used outputs. Conversely, `ReducedUnitaryFactorization.params` lifts the data to a full exact feasible floor point, setting unused output slices to zero. `ReducedUnitaryFactorization.rowFactor_injective`, `.columnFactor_injective`, and `.outputFactor_injective` prove injectivity of all three maps.

`reduced_unitary_factorization_iff_group_isotope` identifies `Nonempty (ReducedUnitaryFactorization f)` with `IsGroupIsotope f` under **both** `¬ RepeatedRows f` and `¬ RepeatedColumns f`. No group or Latin-square structure is assumed for the general reduced table, and redundancy alone is not sufficient for floor attainment. `no_reduced_unitary_factorization_iff_gap` equates nonexistence of the data with a positive gap uniform over feasible parameters for that target; `infimum_gap_of_no_reduced_unitary_factorization` bounds the real feasible infimum above the floor. For `minimumOperation n := ⟨min⟩` and `n ≥ 2`, `minimum_no_reduced_unitary_factorization`, `minimum_exists_gap`, and `minimum_exists_infimum_gap` give the obstruction and both gaps. These gaps are target-specific, not uniform in `n`, and do not assert higher-energy infimum attainment.

[InputQuotients.lean](HyperCubeGroup/Foundation/InputQuotients.lean) is independent of floor attainment: its results apply to arbitrary `f : BinOp n`, including `n = 0`, without `[NeZero n]`. Given separate encoders `encRow : Fin n → α`, `encCol : Fin n → β` and a decoder satisfying `decode (encRow row) (encCol column) = f.op row column` for every pair, `deterministic_encoding_card_bounds` proves, for finite alphabets,

$$r=\text{Nat.card}(\text{RowClass} f)\le\text{Nat.card}(\alpha),\qquad s=\text{Nat.card}(\text{ColumnClass} f)\le\text{Nat.card}(\beta).$$

`fixed_length_binary_encoding_card_bounds` specializes to alphabets `Fin rowBits → Bool` and `Fin columnBits → Bool`, giving `r ≤ 2^rowBits` and `s ≤ 2^columnBits`. `row_encoding_factors_uniquely` and `column_encoding_factors_uniquely` each require an encoder constant on identical entire profiles and distinguishing different profiles; they yield a unique injective map from the corresponding quotient through which that encoder factors.

`minimum_associative`, `minimum_no_repeated_rows`, and `minimum_no_repeated_columns` additionally prove that `min` is associative and has no identical distinct rows or columns. Thus its positive gap for `n ≥ 2` coexists with these properties.

**Scope:** These are simultaneous, separate deterministic encoding bounds, not general interactive communication-complexity theorems. No strict complexity hierarchy, exact Kolmogorov/MDL identity, reversible-computation theorem, or low-rank invariance is established. There is no bit-length theorem for $\mathcal H$ itself.

Direct imports for the exact-structure and input-quotient modules:

```lean
import HyperCubeGroup.Foundation.ExactStructure
import HyperCubeGroup.Foundation.InputQuotients

#check FloorDichotomy.floor_iff_reduced_unitary_factorization
#check FloorDichotomy.floor_factorization_descends
#check FloorDichotomy.reduced_unitary_factorization_iff_group_isotope
#check FloorDichotomy.no_reduced_unitary_factorization_iff_gap
#check FloorDichotomy.infimum_gap_of_no_reduced_unitary_factorization
#check FloorDichotomy.deterministic_encoding_card_bounds
#check FloorDichotomy.fixed_length_binary_encoding_card_bounds
#check FloorDichotomy.row_encoding_factors_uniquely
#check FloorDichotomy.column_encoding_factors_uniquely
```

## General Collinearity--Associativity Equivalence (Additional Result)

[GeneralCollinearity.lean](HyperCubeGroup/Foundation/GeneralCollinearity.lean) proves that a finite quasigroup admits a feasible collinear factorization if and only if it is a group isotope. The proof includes rank-deficient and imbalanced factors and derives nondegeneracy from feasibility.

After isotopy to a loop with identity `e`, the cyclic collinearity identities define an associative sandwich product of output adjoints: with `D_a = C_a†` and `K = B_e† A_e†`, one has `D_a K D_b = λ_ab D_(a∘b)` with nonzero coefficients. Feasibility distinguishes nonzero scalar multiples of different output slices, forcing the loop operation to be associative. Neither the slices nor `K` need to be invertible.

The left-regular construction supplies a unitary collinear factorization. `collinear_to_unitary_collinear` proves existence of this factorization; it does not assert that norm-rescaling or extending the given slices preserves feasibility. `collinear_implies_group_isotope` proves the implication from feasible collinearity to group isotopy.

The separate active-subspace construction is additional geometric infrastructure, not a prerequisite for this equivalence. In its full-rank `κ = 1` case, it explicitly proves that norm-rescaling the original slices gives a feasible unitary collinear factorization.

## Compilation verification
<!-- Proof Assumptions -->

Foundation modules compile without `sorryAx` or project axioms. All existing axiom checks report only standard Lean background axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## Scope of Formalization (What is not Mechanized)

The manuscript coverage includes the **algebraic and geometric** results in Sections 2–6 and Appendices B, C, and E: Proposition 0, Lemmas 1–4, and Theorems 6–7 for arbitrary binary operations through the support interface; Lemma 5 and Lemma 16 for matrix and spectral bounds; Lemma 17's analytic no-escape and Theorem 8's fixed-target and fixed-order positive infimum gaps and floor-or-infimum-gap characterization for all finite binary operations; Theorems 9–10 and Lemmas 12–15 for quasigroup unitary collinearity, global optimality, and representation classification; and Theorems 11, 18–19, 21–22, and Corollary 20 for arbitrary operation tensors.
The following manuscript components are outside the scope of formalization:

- **Empirical results and training dynamics:** empirical optimization trajectories and training-endpoint statistics (Section 5.1 & Appendix D) are not formalized by these algebraic results.
- **Finite-group subtable realizations and explicit counterexamples:** Corollary 23 (finite-group subtable realization via Malcev's residual-finiteness theorem, Appendix E.3) and the explicit concrete counterexamples in Appendices E.3–E.4 are not formalized.
- **Description-length bounds:** lossless prefix-coding and asymptotic description-length bounds via Pyber (1993) and McKay & Wanless (2005) (Appendix F) are not formalized.

## Mathlib Upstream Candidates

The codebase contains several pieces of independent interest to the broader Lean / Mathlib community that are fully proved here and would naturally live upstream:

1. **Unitary Schur triangulation** (`matrix_unitary_schur_form`): `∃ U unitary, U†·A·U is upper triangular for any complex A`. Currently absent in Mathlib.
2. **Schur trace bound** (`IsUpperTriangular.norm_trace_cubed_pow_four_le`): `‖Trace(T³)‖⁴ ≤ N·(‖T·T‖²_F)³` for upper triangular `T` (unnormalized trace/Frobenius norm).
3. **Power-mean Hölder bound** (`Real.sum_pow_three_pow_four_le`): `(Σ f_i³)⁴ ≤ N · (Σ f_i⁴)³` for nonneg real `f`.
4. **`AddCommGroup (Fin n)` bridge**: Constructs the abelian-group typeclass directly from a finite quasigroup's cancellation laws (`IsAbelianGroup.toAddCommGroup`).

## Building

Requires [Lean 4](https://leanprover.github.io/) `v4.29.0-rc6` and the [Mathlib](https://github.com/leanprover-community/mathlib4) revision pinned in [lake-manifest.json](lake-manifest.json).

For a standalone Foundation package, copy the entire `HyperCubeGroup/Foundation` subtree, including [External/CharacterRigidity.lean](HyperCubeGroup/Foundation/External/CharacterRigidity.lean), its source attribution, and [External/LICENSE](HyperCubeGroup/Foundation/External/LICENSE). The source attribution and Apache 2.0 license must accompany the copied code. Generic machinery uses the `HyperCubeGroup.Manuscript` namespace. Imports use only the canonical Foundation paths.

Run from the repository root:

```bash
lake build
```

To check axioms across all main declarations, run:

```bash
lake env lean CheckAxioms.lean
```

To inspect a particular theorem's assumptions, import its module and use `#print axioms`, for example:

```lean
import HyperCubeGroup.Foundation.UniformGap

#print axioms PositiveGap.exists_infimum_gap_of_no_floor
```

These declarations report only standard Lean background axioms. No separate test or audit package is required to check the foundational proofs.
