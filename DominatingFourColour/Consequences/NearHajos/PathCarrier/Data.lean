import DominatingFourColour.Consequences.NearHajos.ModelReductions
import DominatingFourColour.Consequences.NearHajos.TreePathSupport

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

/-- The geometric data left after rooted and two-value tail carriers are discharged. -/
structure LargePathCarrier
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G) where
  Ktail : K4UnsplitSubdivisionData G
  attachTail : Fin 4 -> V
  hattachTail : forall i : Fin 4,
    attachTail i ∈ (D.model.branch (0 : Fin 5)).verts ∧
      G.Adj (attachTail i) (Ktail.model.branchVertex i)
  hKtail_branch_not_first : forall i : Fin 4,
    Ktail.model.branchVertex i ∉ (D.model.branch (0 : Fin 5)).verts
  hKtail_internal_not_first :
    forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
      z ∈ Walk.InternalVertices (Ktail.model.edgePath hij) ->
        z ∉ (D.model.branch (0 : Fin 5)).verts
  Btail : G.Subgraph
  hBtail_le : Btail ≤ D.model.branch (0 : Fin 5)
  hBtail_terminal : forall i : Fin 4, attachTail i ∈ Btail.verts
  TBtail : Btail.coe.Subgraph
  hTBtail_tree : TBtail.coe.IsTree
  hTBtail_spanning : TBtail.IsSpanning
  leftT : TBtail.verts
  rightT : TBtail.verts
  bridge : Btail.coe.Walk (leftT : Btail.verts) (rightT : Btail.verts)
  order : Fin 4 ↪ Fin 4
  leftStem : forall a : Fin 4,
    Btail.coe.Walk (leftT : Btail.verts)
      (⟨attachTail (order a), hBtail_terminal (order a)⟩ : Btail.verts)
  rightStem : forall a : Fin 4,
    Btail.coe.Walk (rightT : Btail.verts)
      (⟨attachTail (order a), hBtail_terminal (order a)⟩ : Btail.verts)
  left_ne_right : ((leftT : Btail.verts) : V) ≠ ((rightT : Btail.verts) : V)
  bridge_isPath : bridge.IsPath
  bridge_le : bridge.toSubgraph ≤ TBtail
  left_eq_zero : ((leftT : Btail.verts) : V) = attachTail (order (0 : Fin 4))
  right_eq_two : ((rightT : Btail.verts) : V) = attachTail (order (2 : Fin 4))
  one_ne_right : attachTail (order (1 : Fin 4)) ≠ ((rightT : Btail.verts) : V)
  three_ne_left : attachTail (order (3 : Fin 4)) ≠ ((leftT : Btail.verts) : V)
  leftStem_isPath : forall a : Fin 4, (leftStem a).IsPath
  leftStem_le : forall a : Fin 4, (leftStem a).toSubgraph ≤ TBtail
  rightStem_isPath : forall a : Fin 4, (rightStem a).IsPath
  rightStem_le : forall a : Fin 4, (rightStem a).toSubgraph ≤ TBtail
  leftStem_avoids_right : forall {z : Btail.verts},
    z ∈ (leftStem (1 : Fin 4)).support ->
      z ≠ (leftT : Btail.verts) -> z ≠ (rightT : Btail.verts)
  rightStem_avoids_left : forall {z : Btail.verts},
    z ∈ (rightStem (3 : Fin 4)).support ->
      z ≠ (rightT : Btail.verts) -> z ≠ (leftT : Btail.verts)

def LargePathCarrier.Clean
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    {D : ThirdBranchPathAndTailInducedCycleData G}
    (C : LargePathCarrier D) : Prop :=
  (forall {z : C.Btail.verts},
    z ∈ Walk.InternalVertices C.bridge ->
      z ∈ (C.leftStem (1 : Fin 4)).support ->
        z ≠ (C.leftT : C.Btail.verts) -> False) ∧
    (forall {z : C.Btail.verts},
      z ∈ Walk.InternalVertices C.bridge ->
        z ∈ (C.rightStem (3 : Fin 4)).support ->
          z ≠ (C.rightT : C.Btail.verts) -> False) ∧
      (forall {z : C.Btail.verts},
        z ∈ (C.leftStem (1 : Fin 4)).support ->
          z ∈ (C.rightStem (3 : Fin 4)).support ->
            z ≠ (C.leftT : C.Btail.verts) ->
              z ≠ (C.rightT : C.Btail.verts) -> False)

end PathCarrier

end Schematic.Math.GraphTheory
