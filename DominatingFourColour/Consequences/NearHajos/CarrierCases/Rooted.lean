import DominatingFourColour.Consequences.NearHajos.BridgeCarriers.SubgraphPaths

/-! Rooted attachment-pattern reductions for carrier models. -/

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_k4_avoids_subgraph
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    {B : G.Subgraph}
    (hB_le : B ≤ D.model.branch (0 : Fin 5)) :
    (forall i : Fin 4,
      (D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i ∉
        B.verts) ∧
      (forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices
          ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.edgePath hij) ->
            z ∉ B.verts) := by
  constructor
  · intro i hmem
    exact D.second_singleton_k4_branchVertex_not_first hsecond i
      (hB_le.left hmem)
  · intro i j hij z hz hmem
    exact D.second_singleton_k4_internal_not_first hsecond hij hz
      (hB_le.left hmem)

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_rooted_carrier_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (B : G.Subgraph)
    (hB_le : B ≤ D.model.branch (0 : Fin 5))
    (apexB : B.verts)
    (attachB : Fin 4 -> B.verts)
    [DecidableEq B.verts]
    (TB : B.coe.Subgraph)
    [DecidableEq TB.verts]
    (hTB_tree : TB.coe.IsTree)
    (hroot_T : apexB ∈ TB.verts)
    (hterminal_T : forall i : Fin 4, attachB i ∈ TB.verts)
    (hattach_adj :
      forall i : Fin 4,
        G.Adj (attachB i : V)
          ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i))
    (stemB :
      forall i : Fin 4,
        B.coe.Walk apexB (attachB i))
    (hstemB_path : forall i : Fin 4, (stemB i).IsPath)
    (hstemB_le : forall i : Fin 4, (stemB i).toSubgraph ≤ TB)
    (hpair_path_through_root :
      forall {i j : Fin 4}, i ≠ j ->
        Exists fun p : B.coe.Walk (attachB i) (attachB j) =>
          p.toSubgraph ≤ TB ∧ p.IsPath ∧ apexB ∈ p.support) :
    NearHajosStrengtheningConclusion G := by
  classical
  let K : K4UnsplitSubdivisionData G :=
    D.second_singleton_k4UnsplitSubdivisionData hsecond
  exact
    K.carrier_rooted_attachment_subgraph_tree_paths_through_root_near_hajos_with_two_incident_unsplit_edges
      B
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).1
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).2
      apexB attachB TB hTB_tree hroot_T hterminal_T hattach_adj
      stemB hstemB_path hstemB_le hpair_path_through_root

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_bridge_carrier_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (B : G.Subgraph)
    (hB_le : B ≤ D.model.branch (0 : Fin 5))
    {leftB rightB : B.verts}
    (hleft_ne_right : (leftB : V) ≠ (rightB : V))
    (pB : B.coe.Walk leftB rightB)
    (hpB : pB.IsPath)
    (attachB : Fin 4 -> B.verts)
    (hattach_adj :
      forall i : Fin 4,
        G.Adj (attachB i : V)
          ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i))
    (stemB :
      forall i : Fin 4,
        B.coe.Walk (k4BridgeEndpointSubgraph B leftB rightB i) (attachB i))
    (hstemB_path : forall i : Fin 4, (stemB i).IsPath)
    (hstemB_punctured_avoids_endpoints :
      forall i : Fin 4, forall {z : B.verts},
        z ∈ (stemB i).support ->
          z ≠ k4BridgeEndpointSubgraph B leftB rightB i ->
            z ≠ leftB ∧ z ≠ rightB)
    (hbridge_stem_meet_only_endpoint :
      forall i : Fin 4, forall {z : B.verts},
        z ∈ Walk.InternalVertices pB ->
          z ∈ (stemB i).support ->
            z ≠ k4BridgeEndpointSubgraph B leftB rightB i ->
              False)
    (hstem_meet_only_common_endpoint :
      forall {i j : Fin 4}, i ≠ j ->
        forall {z : B.verts},
          z ∈ (stemB i).support ->
            z ∈ (stemB j).support ->
              z ≠ k4BridgeEndpointSubgraph B leftB rightB i ->
                z ≠ k4BridgeEndpointSubgraph B leftB rightB j ->
                  False) :
    NearHajosStrengtheningConclusion G := by
  classical
  let K : K4UnsplitSubdivisionData G :=
    D.second_singleton_k4UnsplitSubdivisionData hsecond
  exact
    K.carrier_bridge_attachment_subgraph_paths_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
      B
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).1
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).2
      hleft_ne_right pB hpB attachB hattach_adj stemB
      hstemB_path hstemB_punctured_avoids_endpoints
      hbridge_stem_meet_only_endpoint hstem_meet_only_common_endpoint

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_common_attachment_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    {apex : V}
    (hapex_mem : apex ∈ (D.model.branch (0 : Fin 5)).verts)
    (hadj :
      forall i : Fin 4,
        G.Adj apex
          ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) :
    NearHajosStrengtheningConclusion G := by
  classical
  let K : K4UnsplitSubdivisionData G :=
    D.second_singleton_k4UnsplitSubdivisionData hsecond
  exact
    K.carrier_common_attachment_near_hajos_with_two_incident_unsplit_edges
      (D.model.branch (0 : Fin 5)).verts hapex_mem
      (D.second_singleton_k4_avoids_subgraph hsecond
        (B := D.model.branch (0 : Fin 5)) le_rfl).1
      (D.second_singleton_k4_avoids_subgraph hsecond
        (B := D.model.branch (0 : Fin 5)) le_rfl).2
      hadj

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_common_first_branch_attachment_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i))
    {apex : V}
    (hapex_mem : apex ∈ (D.model.branch (0 : Fin 5)).verts)
    (hvalues : forall i : Fin 4, attach i = apex) :
    NearHajosStrengtheningConclusion G := by
  exact
    D.second_singleton_core_common_attachment_near_hajos hsecond hapex_mem
      (by
        intro i
        simpa [hvalues i] using (hattach i).2)

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_rooted_attachment_spanning_tree_all_pairs_through_root_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (B : G.Subgraph)
    (hB_le : B ≤ D.model.branch (0 : Fin 5))
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    [DecidableEq B.verts]
    (TB : B.coe.Subgraph)
    [DecidableEq TB.verts]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning)
    (apexB : B.verts)
    (hpair_path_through_root :
      forall {i j : Fin 4}, i ≠ j ->
        Exists fun p :
          B.coe.Walk
            (⟨attach i, hB_terminal i⟩ : B.verts)
            (⟨attach j, hB_terminal j⟩ : B.verts) =>
          p.toSubgraph ≤ TB ∧ p.IsPath ∧ apexB ∈ p.support) :
    NearHajosStrengtheningConclusion G := by
  classical
  let attachB : Fin 4 -> B.verts := fun i => ⟨attach i, hB_terminal i⟩
  obtain ⟨stemB, hstemB_path, hstemB_le⟩ :=
    Subgraph.Connected.exists_coe_rooted_paths_in_spanning_coe_subgraph
      (B := B) (T := TB) hTB_tree.connected hTB_spanning
      apexB.2 attach hB_terminal
  exact
    D.second_singleton_core_rooted_carrier_near_hajos hsecond B hB_le
      apexB attachB TB hTB_tree (hTB_spanning apexB)
      (fun i => hTB_spanning (attachB i))
      (by
        intro i
        exact (hattach i).2)
      stemB hstemB_path hstemB_le
      (by
        intro i j hij
        exact hpair_path_through_root hij)

end Schematic.Math.GraphTheory
