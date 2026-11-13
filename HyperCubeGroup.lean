/-
  HyperCubeGroup: Lean 4 Formalization

  Core results formalized:
  - Orthogonal decomposition H = B + R
  - Collinear manifold analysis: shared Gram matrices,
    normalized rank, AM-GM lower bound
  - Group isotope characterization
  - Matrix AM-GM and equality rigidity
  - Full gauge group structure and quotient lifting
-/

import HyperCubeGroup.Foundation.Basic
import HyperCubeGroup.Foundation.Decomposition
import HyperCubeGroup.Foundation.CollinearManifold
import HyperCubeGroup.Foundation.InverseRank
import HyperCubeGroup.Foundation.SupportGeometry
import HyperCubeGroup.Foundation.SupportDecomposition
import HyperCubeGroup.Foundation.SupportInverseRank
import HyperCubeGroup.Foundation.SupportGramRigidity
import HyperCubeGroup.Foundation.SupportUnitary
import HyperCubeGroup.Foundation.GroupIsotope
import HyperCubeGroup.Foundation.GeneralCollinearity
import HyperCubeGroup.Foundation.FloorDichotomy
import HyperCubeGroup.Foundation.ReducedTable
import HyperCubeGroup.Foundation.ExactStructure
import HyperCubeGroup.Foundation.InputQuotients
import HyperCubeGroup.Foundation.RepresentationClassification
import HyperCubeGroup.Foundation.Abelian
import HyperCubeGroup.Foundation.Spectral
import HyperCubeGroup.Foundation.BlockCyclic
import HyperCubeGroup.Foundation.MatrixAMGM
import HyperCubeGroup.Foundation.Plancherel
import HyperCubeGroup.Foundation.PontryaginBridge
import HyperCubeGroup.Foundation.ActiveSubspaceGeneric
import HyperCubeGroup.Foundation.ActiveSubspace
import HyperCubeGroup.Foundation.ActiveSubspaceConstruction
import HyperCubeGroup.Foundation.Tikhonov
import HyperCubeGroup.Foundation.PositiveGap
import HyperCubeGroup.Foundation.UniformGap
import HyperCubeGroup.Foundation.Coercivity

import HyperCubeGroup.Foundation.Representation.Characters
import HyperCubeGroup.Foundation.Representation.UnitaryIntertwiner
import HyperCubeGroup.Foundation.Representation.UnitaryMatrix

import HyperCubeGroup.Foundation.External.CharacterRigidity
