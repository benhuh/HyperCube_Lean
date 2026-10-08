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
import HyperCubeGroup.Foundation.GroupIsotope
import HyperCubeGroup.Foundation.GeneralCollinearity
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
import HyperCubeGroup.Foundation.Coercivity
