import DominatingFourColour.Consequences.NearHajos.PathCarrier.Geometry

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

/-- Resolve a large carrier whose bridge and two distinguished arms have clean interiors. -/
theorem resolveClean
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (C : LargePathCarrier D)
    (hclean : C.Clean) :
    NearHajosStrengtheningConclusion G := by
  rcases hclean with ⟨hbridgeLeft, hbridgeRight, harms⟩
  exact
    C.Ktail.carrier_bridge_two_arm_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
      C.order C.Btail
      (by
        intro i hmem
        exact C.hKtail_branch_not_first i (C.hBtail_le.left hmem))
      (by
        intro i j hij z hz hmem
        exact C.hKtail_internal_not_first hij hz (C.hBtail_le.left hmem))
      C.left_ne_right C.bridge C.bridge_isPath C.attachment
      C.attachment_adj C.attachment_zero C.attachment_two
      C.leftArm C.rightArm C.leftArm_isPath C.rightArm_isPath
      (by
        intro z hz hz_ne_left
        exact C.leftStem_avoids_right hz hz_ne_left)
      (by
        intro z hz hz_ne_right
        exact C.rightStem_avoids_left hz hz_ne_right)
      hbridgeLeft hbridgeRight harms

end PathCarrier

end Schematic.Math.GraphTheory

