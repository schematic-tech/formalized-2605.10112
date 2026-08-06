import DominatingFourColour.Consequences.NearHajos.PathCarrier.Geometry

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

/-- The four rooted paths and their first/last common-contact invariants. -/
structure NormalizedCommonObstruction
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    {D : ThirdBranchPathAndTailInducedCycleData G}
    (C : LargePathCarrier D) [DecidableEq C.Btail.verts] where
  root : C.TBtail.verts
  root_left :
    (root : C.Btail.verts) ∈ C.leftArm.support
  root_internal :
    (root : C.Btail.verts) ∈ Walk.InternalVertices C.bridge
  root_right :
    (root : C.Btail.verts) ∈ C.rightArm.support
  leftPath : C.Btail.coe.Walk (root : C.Btail.verts) C.left
  rightPath : C.Btail.coe.Walk (root : C.Btail.verts) C.right
  onePath : C.Btail.coe.Walk (root : C.Btail.verts) C.one
  threePath : C.Btail.coe.Walk (root : C.Btail.verts) C.three
  last : C.Btail.verts
  last_one : last ∈ onePath.support
  last_one_reverse : last ∈ onePath.reverse.support
  last_three : last ∈ threePath.support
  first_common : forall t : C.Btail.verts,
    t ∈ C.rightArm.support ->
      t ∈ (C.leftArm.takeUntil (root : C.Btail.verts) root_left).support ->
        t = (root : C.Btail.verts)
  leftPath_isPath : leftPath.IsPath
  rightPath_isPath : rightPath.IsPath
  onePath_isPath : onePath.IsPath
  threePath_isPath : threePath.IsPath
  leftPath_le : leftPath.toSubgraph ≤ C.TBtail
  rightPath_le : rightPath.toSubgraph ≤ C.TBtail
  onePath_le : onePath.toSubgraph ≤ C.TBtail
  threePath_le : threePath.toSubgraph ≤ C.TBtail
  right_not_leftPath : C.right ∉ leftPath.support
  left_not_rightPath : C.left ∉ rightPath.support
  right_not_onePath : C.right ∉ onePath.support
  left_not_threePath : C.left ∉ threePath.support
  onePath_support : forall {x : C.Btail.verts},
    x ∈ onePath.support -> x ∈ C.leftArm.support
  threePath_support : forall {x : C.Btail.verts},
    x ∈ threePath.support -> x ∈ C.rightArm.support
  last_common : forall t : C.Btail.verts,
    t ∈ threePath.support ->
      t ∈ (onePath.reverse.takeUntil last last_one_reverse).support ->
        t = last

namespace NormalizedCommonObstruction

variable {V : Type u} [Fintype V] {G : SimpleGraph V}
  {D : ThirdBranchPathAndTailInducedCycleData G}
  {C : LargePathCarrier D} [DecidableEq C.Btail.verts]

/-- Whether the right and one paths meet only at the normalized root. -/
def NoCross (N : NormalizedCommonObstruction C) : Prop :=
  forall {x : C.Btail.verts},
    x ∈ N.rightPath.support ->
      x ∈ N.onePath.support ->
        x = (N.root : C.Btail.verts)

/-- The common tree geometry used by all four normalized-obstruction cases. -/
theorem rootedFourPathSupports (N : NormalizedCommonObstruction C) :
    Walk.RootedFourPathSupports C.bridge C.leftArm C.rightArm
      N.leftPath N.rightPath N.onePath N.threePath
      N.root_internal.1 N.root_left N.root_right :=
  Subgraph.tree_rooted_four_path_supports
    (T := C.TBtail) (base := C.bridge)
    (leftOne := C.leftArm) (rightThree := C.rightArm)
    (pLeft := N.leftPath) (pRight := N.rightPath)
    (pOne := N.onePath) (pThree := N.threePath)
    C.hTBtail_tree C.bridge_le C.leftArm_le C.rightArm_le
    N.leftPath_le N.rightPath_le N.onePath_le N.threePath_le
    C.bridge_isPath C.leftArm_isPath C.rightArm_isPath
    N.leftPath_isPath N.rightPath_isPath N.onePath_isPath N.threePath_isPath
    N.root_internal.1 N.root_left N.root_right

/-- The last non-root contact of the one and right paths.  Packaging the
dependent membership witnesses here avoids rebuilding this selection argument
in both crossing cases. -/
structure LastCross (N : NormalizedCommonObstruction C) where
  vertex : C.Btail.verts
  mem_one : vertex ∈ N.onePath.support
  mem_one_reverse : vertex ∈ N.onePath.reverse.support
  mem_right : vertex ∈ N.rightPath.support
  eq_of_mem_right_mem_reverse_prefix : forall y : C.Btail.verts,
    y ∈ N.rightPath.support ->
      y ∈ (N.onePath.reverse.takeUntil vertex mem_one_reverse).support ->
        y = vertex
  ne_root : vertex ≠ (N.root : C.Btail.verts)

/-- A crossing has a canonical last contact away from the root. -/
theorem existsLastCross (N : NormalizedCommonObstruction C)
    (hcross : Not N.NoCross) : Nonempty N.LastCross := by
  classical
  have hcross_exists :
      Exists fun y : C.Btail.verts =>
        y ∈ N.rightPath.support ∧ y ∈ N.onePath.support ∧
          y ≠ (N.root : C.Btail.verts) := by
    by_contra hnone
    apply hcross
    intro y hyRight hyOne
    by_contra hy_ne
    exact hnone ⟨y, hyRight, hyOne, hy_ne⟩
  rcases hcross_exists with
    ⟨yCross, hyCross_right, hyCross_one, hyCross_ne_root⟩
  obtain ⟨xCross, hxCross_one, hxCross_one_rev,
      hxCross_right, hlastRightOne⟩ :=
    Walk.exists_last_common_support N.onePath N.rightPath
      ⟨yCross, hyCross_one, hyCross_right⟩
  refine ⟨⟨xCross, hxCross_one, hxCross_one_rev, hxCross_right,
    hlastRightOne, ?_⟩⟩
  intro hx_root
  have hyCross_one_rev : yCross ∈ N.onePath.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hyCross_one
  have hyCross_prefix_root :
      yCross ∈
        (N.onePath.reverse.takeUntil
          (N.root : C.Btail.verts)
          (hx_root ▸ hxCross_one_rev)).support :=
    Schematic.Math.GraphTheory.Walk.IsPath.mem_support_takeUntil_end
      N.onePath_isPath.reverse hyCross_one_rev
  have hyCross_prefix :
      yCross ∈
        (N.onePath.reverse.takeUntil xCross hxCross_one_rev).support := by
    cases hx_root
    simpa using hyCross_prefix_root
  exact hyCross_ne_root
    ((hlastRightOne yCross hyCross_right hyCross_prefix).trans hx_root)

end NormalizedCommonObstruction

end PathCarrier

end Schematic.Math.GraphTheory
