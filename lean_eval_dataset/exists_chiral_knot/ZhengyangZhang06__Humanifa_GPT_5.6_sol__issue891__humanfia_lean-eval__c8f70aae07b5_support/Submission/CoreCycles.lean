import Submission.CoreClassification
import Mathlib.Topology.Subpath

open scoped unitInterval

namespace Submission.CoreCycles

noncomputable section

def aVertex (i : Fin 2) : RadialCore.Core := CoreEdges.edge i 0 0

def bVertex (j : Fin 3) : RadialCore.Core := CoreEdges.edge 0 j 1

theorem edge_zero (i : Fin 2) (j : Fin 3) :
    CoreEdges.edge i j 0 = aVertex i := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change CoreEdges.edgeW j 0 = CoreEdges.edgeW 0 0
    unfold CoreEdges.edgeW CoreEdges.edgeWCoordinate CoreEdges.fromWCoordinate
    simp

theorem edge_one (i : Fin 2) (j : Fin 3) :
    CoreEdges.edge i j 1 = bVertex j := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change CoreEdges.edgeZ i 1 = CoreEdges.edgeZ 0 1
    unfold CoreEdges.edgeZ CoreEdges.edgeZCoordinate CoreEdges.fromZCoordinate
    simp
  · rfl

def edgePath (i : Fin 2) (j : Fin 3) : Path (aVertex i) (bVertex j) where
  toFun := CoreEdges.edge i j
  continuous_toFun := CoreEdges.edge_continuous i j
  source' := edge_zero i j
  target' := edge_one i j

def firstCycle : Path (aVertex 0) (aVertex 0) :=
  (edgePath 0 0).trans
    ((edgePath 1 0).symm.trans
      ((edgePath 1 1).trans (edgePath 0 1).symm))

def secondCycle : Path (aVertex 0) (aVertex 0) :=
  (edgePath 0 0).trans
    ((edgePath 1 0).symm.trans
      ((edgePath 1 2).trans (edgePath 0 2).symm))

theorem coreMonodromy_edgePath_apply (i : Fin 2) (j : Fin 3)
    (u : unitInterval) :
    CoreMonodromy.coreMonodromy (edgePath i j u) =
      edgePath (CoreMonodromy.flip i) (CoreMonodromy.next j) u :=
  CoreMonodromy.coreMonodromy_edge i j u

end

end Submission.CoreCycles
