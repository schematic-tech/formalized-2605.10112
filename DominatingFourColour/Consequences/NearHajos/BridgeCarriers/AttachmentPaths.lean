import DominatingFourColour.Consequences.NearHajos.BridgeCarriers.Construction

/-! Transport bridge-carrier attachment paths into the host graph. -/

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

set_option maxHeartbeats 0 in
theorem K4UnsplitSubdivisionData.bridge_paths_k5hat_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    {left right : V}
    (hleft_ne_right : left ≠ right)
    (hleft_not_branch : forall i : Fin 4, left ≠ D.model.branchVertex i)
    (hright_not_branch : forall i : Fin 4, right ≠ D.model.branchVertex i)
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        forall i : Fin 4, z ≠ D.model.branchVertex i)
    (hcore_internal_no_left :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ left)
    (hcore_internal_no_right :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ right)
    (hbridge_core_disjoint :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices p ->
          z ∈ Walk.InternalVertices (D.model.edgePath hij) -> False)
    (arm :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (D.model.branchVertex i))
    (harm_path : forall i : Fin 4, (arm i).IsPath)
    (harm_internal_no_special :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          z ≠ left ∧ z ≠ right ∧
            forall j : Fin 4, z ≠ D.model.branchVertex j)
    (hbridge_arm_disjoint :
      forall i : Fin 4,
        Disjoint (Walk.InternalVertices p) (Walk.InternalVertices (arm i)))
    (harm_internal_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (arm j)))
    (harm_core_disjoint :
      forall {i j k : Fin 4} (hjk : K4Graph.Adj j k),
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (D.model.edgePath hjk))) :
    NearHajosStrengtheningConclusion G := by
  exact
    D.bridge_paths_k5hat_relabel_near_hajos_with_two_incident_unsplit_edges
      (Function.Embedding.refl (Fin 4)) hleft_ne_right hleft_not_branch
      hright_not_branch p hp hp_internal_no_branch hcore_internal_no_left
      hcore_internal_no_right hbridge_core_disjoint arm harm_path
      harm_internal_no_special hbridge_arm_disjoint harm_internal_disjoint
      harm_core_disjoint
theorem K4UnsplitSubdivisionData.carrier_bridge_attachment_paths_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (C : Set V)
    {left right : V}
    (hleft_mem : left ∈ C)
    (hright_mem : right ∈ C)
    (hleft_ne_right : left ≠ right)
    (hbranch_not_carrier :
      forall i : Fin 4, D.model.branchVertex i ∉ C)
    (hcore_internal_not_carrier :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ C)
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_carrier :
      forall {z : V}, z ∈ Walk.InternalVertices p -> z ∈ C)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ C ∧ G.Adj (attach i) (D.model.branchVertex i))
    (stem :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_carrier :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support -> z ∈ C)
    (hstem_punctured_avoids_endpoints :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ≠ k4BridgeEndpoint left right i ->
            z ≠ left ∧ z ≠ right)
    (hbridge_stem_disjoint :
      forall i : Fin 4,
        Disjoint
          (Walk.InternalVertices p)
          {z : V | z ∈ (stem i).support ∧
            z ≠ k4BridgeEndpoint left right i})
    (hstem_punctured_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stem i).support ∧
            z ≠ k4BridgeEndpoint left right i}
          {z : V | z ∈ (stem j).support ∧
            z ≠ k4BridgeEndpoint left right j}) :
    NearHajosStrengtheningConclusion G := by
  classical
  let arm :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (D.model.branchVertex i) :=
    fun i => (stem i).concat (hattach i).2
  have hbranch_not_stem_support :
      forall i : Fin 4, D.model.branchVertex i ∉ (stem i).support := by
    intro i hsupport
    exact hbranch_not_carrier i (hstem_support_carrier i hsupport)
  refine
    D.bridge_paths_k5hat_near_hajos_with_two_incident_unsplit_edges
      hleft_ne_right ?_ ?_ p hp ?_ ?_ ?_ ?_ arm ?_ ?_ ?_ ?_ ?_
  · intro i h
    exact hbranch_not_carrier i (by simpa [h] using hleft_mem)
  · intro i h
    exact hbranch_not_carrier i (by simpa [h] using hright_mem)
  · intro z hz i h
    exact hbranch_not_carrier i (by simpa [h] using hp_internal_carrier hz)
  · intro i j hij z hz h
    exact hcore_internal_not_carrier hij hz (by simpa [h] using hleft_mem)
  · intro i j hij z hz h
    exact hcore_internal_not_carrier hij hz (by simpa [h] using hright_mem)
  · intro i j hij z hz_bridge hz_core
    exact hcore_internal_not_carrier hij hz_core (hp_internal_carrier hz_bridge)
  · intro i
    change ((stem i).concat (hattach i).2).IsPath
    exact (hstem_path i).concat (hbranch_not_stem_support i) (hattach i).2
  · intro i z hz
    have hz_stem :
        z ∈ (stem i).support ∧ z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hz
    refine ⟨(hstem_punctured_avoids_endpoints i hz_stem.1 hz_stem.2).1,
      (hstem_punctured_avoids_endpoints i hz_stem.1 hz_stem.2).2, ?_⟩
    intro j h
    exact hbranch_not_carrier j (by
      simpa [h] using hstem_support_carrier i hz_stem.1)
  · intro i
    rw [Set.disjoint_left]
    intro z hz_bridge hz_arm
    have hz_stem :
        z ∈ (stem i).support ∧ z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hz_arm
    exact Set.disjoint_left.mp (hbridge_stem_disjoint i) hz_bridge hz_stem
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzi_stem :
        z ∈ (stem i).support ∧ z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hzi
    have hzj_stem :
        z ∈ (stem j).support ∧ z ≠ k4BridgeEndpoint left right j :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem j) (hattach j).2 hzj
    exact Set.disjoint_left.mp (hstem_punctured_disjoint hij)
      hzi_stem hzj_stem
  · intro i j k hjk
    rw [Set.disjoint_left]
    intro z hz_arm hz_core
    have hz_stem :
        z ∈ (stem i).support :=
      Walk.mem_support_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hz_arm
    exact hcore_internal_not_carrier hjk hz_core
      (hstem_support_carrier i hz_stem)

set_option maxHeartbeats 0 in
theorem K4UnsplitSubdivisionData.carrier_bridge_attachment_paths_permute_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    (C : Set V)
    {left right : V}
    (hleft_mem : left ∈ C)
    (hright_mem : right ∈ C)
    (hleft_ne_right : left ≠ right)
    (hbranch_not_carrier :
      forall i : Fin 4, D.model.branchVertex i ∉ C)
    (hcore_internal_not_carrier :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ C)
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_carrier :
      forall {z : V}, z ∈ Walk.InternalVertices p -> z ∈ C)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ C ∧ G.Adj (attach i) (D.model.branchVertex (σ i)))
    (stem :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_carrier :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support -> z ∈ C)
    (hstem_punctured_avoids_endpoints :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ≠ k4BridgeEndpoint left right i ->
            z ≠ left ∧ z ≠ right)
    (hbridge_stem_disjoint :
      forall i : Fin 4,
        Disjoint
          (Walk.InternalVertices p)
          {z : V | z ∈ (stem i).support ∧
            z ≠ k4BridgeEndpoint left right i})
    (hstem_punctured_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stem i).support ∧
            z ≠ k4BridgeEndpoint left right i}
          {z : V | z ∈ (stem j).support ∧
            z ≠ k4BridgeEndpoint left right j}) :
    NearHajosStrengtheningConclusion G := by
  classical
  let arm :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (D.model.branchVertex (σ i)) :=
    fun i => (stem i).concat (hattach i).2
  have hbranch_not_stem_support :
      forall i : Fin 4, D.model.branchVertex (σ i) ∉ (stem i).support := by
    intro i hsupport
    exact hbranch_not_carrier (σ i) (hstem_support_carrier i hsupport)
  refine
    D.bridge_paths_k5hat_relabel_near_hajos_with_two_incident_unsplit_edges
      σ hleft_ne_right ?_ ?_ p hp ?_ ?_ ?_ ?_ arm ?_ ?_ ?_ ?_ ?_
  · intro i h
    exact hbranch_not_carrier (σ i) (by simpa [h] using hleft_mem)
  · intro i h
    exact hbranch_not_carrier (σ i) (by simpa [h] using hright_mem)
  · intro z hz i h
    exact hbranch_not_carrier (σ i) (by simpa [h] using hp_internal_carrier hz)
  · intro i j hij z hz h
    exact hcore_internal_not_carrier hij hz (by simpa [h] using hleft_mem)
  · intro i j hij z hz h
    exact hcore_internal_not_carrier hij hz (by simpa [h] using hright_mem)
  · intro i j hij z hz_bridge hz_core
    exact hcore_internal_not_carrier hij hz_core (hp_internal_carrier hz_bridge)
  · intro i
    change ((stem i).concat (hattach i).2).IsPath
    exact (hstem_path i).concat (hbranch_not_stem_support i) (hattach i).2
  · intro i z hz
    have hz_stem :
        z ∈ (stem i).support ∧ z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hz
    refine ⟨(hstem_punctured_avoids_endpoints i hz_stem.1 hz_stem.2).1,
      (hstem_punctured_avoids_endpoints i hz_stem.1 hz_stem.2).2, ?_⟩
    intro j h
    exact hbranch_not_carrier (σ j) (by
      simpa [h] using hstem_support_carrier i hz_stem.1)
  · intro i
    rw [Set.disjoint_left]
    intro z hz_bridge hz_arm
    have hz_stem :
        z ∈ (stem i).support ∧ z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hz_arm
    exact Set.disjoint_left.mp (hbridge_stem_disjoint i) hz_bridge hz_stem
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzi_stem :
        z ∈ (stem i).support ∧ z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hzi
    have hzj_stem :
        z ∈ (stem j).support ∧ z ≠ k4BridgeEndpoint left right j :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem j) (hattach j).2 hzj
    exact Set.disjoint_left.mp (hstem_punctured_disjoint hij)
      hzi_stem hzj_stem
  · intro i j k hjk
    rw [Set.disjoint_left]
    intro z hz_arm hz_core
    have hz_stem :
        z ∈ (stem i).support :=
      Walk.mem_support_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hz_arm
    exact hcore_internal_not_carrier hjk hz_core
      (hstem_support_carrier i hz_stem)

theorem K4UnsplitSubdivisionData.carrier_bridge_attachment_paths_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (C : Set V)
    {left right : V}
    (hleft_mem : left ∈ C)
    (hright_mem : right ∈ C)
    (hleft_ne_right : left ≠ right)
    (hbranch_not_carrier :
      forall i : Fin 4, D.model.branchVertex i ∉ C)
    (hcore_internal_not_carrier :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ C)
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_carrier :
      forall {z : V}, z ∈ Walk.InternalVertices p -> z ∈ C)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ C ∧ G.Adj (attach i) (D.model.branchVertex i))
    (stem :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_carrier :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support -> z ∈ C)
    (hstem_punctured_avoids_endpoints :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ≠ k4BridgeEndpoint left right i ->
            z ≠ left ∧ z ≠ right)
    (hbridge_stem_meet_only_endpoint :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices p ->
          z ∈ (stem i).support ->
            z ≠ k4BridgeEndpoint left right i ->
              False)
    (hstem_meet_only_common_endpoint :
      forall {i j : Fin 4}, i ≠ j ->
        forall {z : V},
          z ∈ (stem i).support ->
            z ∈ (stem j).support ->
              z ≠ k4BridgeEndpoint left right i ->
                z ≠ k4BridgeEndpoint left right j ->
                  False) :
    NearHajosStrengtheningConclusion G := by
  exact
    D.carrier_bridge_attachment_paths_near_hajos_with_two_incident_unsplit_edges
      C hleft_mem hright_mem hleft_ne_right hbranch_not_carrier
      hcore_internal_not_carrier p hp hp_internal_carrier attach hattach
      stem hstem_path hstem_support_carrier hstem_punctured_avoids_endpoints
      (walk_support_punctured_disjoint_of_forall_not_mem p
        (fun i => ⟨k4BridgeEndpoint left right i, ⟨attach i, stem i⟩⟩)
        (fun i => k4BridgeEndpoint left right i)
        hbridge_stem_meet_only_endpoint)
      (by
        intro i j hij
        rw [Set.disjoint_left]
        rintro z ⟨hzi, hzi_ne⟩ ⟨hzj, hzj_ne⟩
        exact hstem_meet_only_common_endpoint hij hzi hzj hzi_ne hzj_ne)

end Schematic.Math.GraphTheory
