import DominatingFourColour.Consequences.NearHajos.BridgeCarriers.AttachmentPaths

/-! Lift bridge-carrier paths from an induced carrier subgraph. -/

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

set_option maxHeartbeats 0 in
theorem K4UnsplitSubdivisionData.carrier_bridge_attachment_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    (B : G.Subgraph)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    {leftB rightB : B.verts}
    (hleft_ne_right : (leftB : V) ≠ (rightB : V))
    (pB : B.coe.Walk leftB rightB)
    (hpB : pB.IsPath)
    (attachB : Fin 4 -> B.verts)
    (hattach_adj :
      forall i : Fin 4,
        G.Adj (attachB i : V) (D.model.branchVertex (σ i)))
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
  let left : V := leftB
  let right : V := rightB
  let p : G.Walk left right := pB.map B.hom
  let attach : Fin 4 -> V := fun i => attachB i
  have hstart_eq :
      forall i : Fin 4,
        ((k4BridgeEndpointSubgraph B leftB rightB i : B.verts) : V) =
          k4BridgeEndpoint left right i := by
    intro i
    fin_cases i <;> rfl
  let stem :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (attach i) := fun i =>
    ((stemB i).map B.hom).copy (hstart_eq i) rfl
  have hp : p.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hpB
  have hp_internal_B :
      forall {z : V}, z ∈ Walk.InternalVertices p -> z ∈ B.verts := by
    intro z hz
    exact Walk.internalVertices_map_subgraph_hom_subset (H := B) pB
      (by simpa [p] using hz)
  have hstem_path : forall i : Fin 4, (stem i).IsPath := by
    intro i
    have hmap : ((stemB i).map B.hom).IsPath :=
      SimpleGraph.Walk.map_isPath_of_injective
        SimpleGraph.Subgraph.hom_injective (hstemB_path i)
    simpa [stem] using
      (SimpleGraph.Walk.isPath_copy ((stemB i).map B.hom)
        (hstart_eq i) rfl).mpr hmap
  have hstem_support_B :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support -> z ∈ B.verts := by
    intro i z hz
    exact Walk.support_map_subgraph_hom_subset (H := B) (stemB i)
      (by simpa [stem] using hz)
  have hstem_avoids :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ≠ k4BridgeEndpoint left right i ->
            z ≠ left ∧ z ≠ right := by
    intro i z hz hz_ne_start
    rcases (Walk.mem_support_map_subgraph_hom_iff
      (H := B) (stemB i)).mp (by simpa [stem] using hz) with
      ⟨zB, hzB_support, hzB_eq⟩
    have hzB_ne_start :
        zB ≠ k4BridgeEndpointSubgraph B leftB rightB i := by
      intro h
      exact hz_ne_start (by
        calc
          z = (zB : V) := hzB_eq.symm
          _ = ((k4BridgeEndpointSubgraph B leftB rightB i : B.verts) : V) := by
            rw [h]
          _ = k4BridgeEndpoint left right i := hstart_eq i)
    have havoid :=
      hstemB_punctured_avoids_endpoints i hzB_support hzB_ne_start
    constructor
    · intro hz_left
      exact havoid.1 (by
        apply Subtype.ext
        exact hzB_eq.trans hz_left)
    · intro hz_right
      exact havoid.2 (by
        apply Subtype.ext
        exact hzB_eq.trans hz_right)
  have hbridge_stem_meet :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices p ->
          z ∈ (stem i).support ->
            z ≠ k4BridgeEndpoint left right i ->
              False := by
    intro i z hz_p hz_stem hz_ne_start
    rcases (Walk.mem_internalVertices_map_subgraph_hom_iff
      (H := B) pB).mp (by simpa [p] using hz_p) with
      ⟨zBridgeB, hzBridgeB, hzBridgeB_eq⟩
    rcases (Walk.mem_support_map_subgraph_hom_iff
      (H := B) (stemB i)).mp (by simpa [stem] using hz_stem) with
      ⟨zStemB, hzStemB, hzStemB_eq⟩
    have hzStem_eq_bridge : zStemB = zBridgeB := by
      apply Subtype.ext
      exact hzStemB_eq.trans hzBridgeB_eq.symm
    have hzBridge_ne_start :
        zBridgeB ≠ k4BridgeEndpointSubgraph B leftB rightB i := by
      intro h
      exact hz_ne_start (by
        calc
          z = (zBridgeB : V) := hzBridgeB_eq.symm
          _ = ((k4BridgeEndpointSubgraph B leftB rightB i : B.verts) : V) := by
            rw [h]
          _ = k4BridgeEndpoint left right i := hstart_eq i)
    exact hbridge_stem_meet_only_endpoint i hzBridgeB
      (by simpa [hzStem_eq_bridge] using hzStemB) hzBridge_ne_start
  have hstem_meet :
      forall {i j : Fin 4}, i ≠ j ->
        forall {z : V},
          z ∈ (stem i).support ->
            z ∈ (stem j).support ->
              z ≠ k4BridgeEndpoint left right i ->
                z ≠ k4BridgeEndpoint left right j ->
                  False := by
    intro i j hij z hzi hzj hzi_ne hzj_ne
    rcases (Walk.mem_support_map_subgraph_hom_iff
      (H := B) (stemB i)).mp (by simpa [stem] using hzi) with
      ⟨ziB, hziB, hziB_eq⟩
    rcases (Walk.mem_support_map_subgraph_hom_iff
      (H := B) (stemB j)).mp (by simpa [stem] using hzj) with
      ⟨zjB, hzjB, hzjB_eq⟩
    have hzj_eq_zi : zjB = ziB := by
      apply Subtype.ext
      exact hzjB_eq.trans hziB_eq.symm
    have hziB_ne_start :
        ziB ≠ k4BridgeEndpointSubgraph B leftB rightB i := by
      intro h
      exact hzi_ne (by
        calc
          z = (ziB : V) := hziB_eq.symm
          _ = ((k4BridgeEndpointSubgraph B leftB rightB i : B.verts) : V) := by
            rw [h]
          _ = k4BridgeEndpoint left right i := hstart_eq i)
    have hzjB_ne_start :
        zjB ≠ k4BridgeEndpointSubgraph B leftB rightB j := by
      intro h
      exact hzj_ne (by
        calc
          z = (zjB : V) := hzjB_eq.symm
          _ = ((k4BridgeEndpointSubgraph B leftB rightB j : B.verts) : V) := by
            rw [h]
          _ = k4BridgeEndpoint left right j := hstart_eq j)
    exact hstem_meet_only_common_endpoint hij hziB
      (by simpa [hzj_eq_zi] using hzjB)
      hziB_ne_start (by simpa [hzj_eq_zi] using hzjB_ne_start)
  exact
    D.carrier_bridge_attachment_paths_permute_near_hajos_with_two_incident_unsplit_edges
      σ B.verts (by exact leftB.2) (by exact rightB.2) hleft_ne_right
      hbranch_not_B hcore_internal_not_B p hp hp_internal_B attach
      (by
        intro i
        exact ⟨(attachB i).2, hattach_adj i⟩)
      stem hstem_path hstem_support_B hstem_avoids
      (walk_support_punctured_disjoint_of_forall_not_mem p
        (fun i => ⟨k4BridgeEndpoint left right i, ⟨attach i, stem i⟩⟩)
        (fun i => k4BridgeEndpoint left right i)
        hbridge_stem_meet)
      (by
        intro i j hij
        rw [Set.disjoint_left]
        rintro z ⟨hzi, hzi_ne⟩ ⟨hzj, hzj_ne⟩
        exact hstem_meet hij hzi hzj hzi_ne hzj_ne)


theorem K4UnsplitSubdivisionData.carrier_bridge_attachment_subgraph_paths_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (B : G.Subgraph)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    {leftB rightB : B.verts}
    (hleft_ne_right : (leftB : V) ≠ (rightB : V))
    (pB : B.coe.Walk leftB rightB)
    (hpB : pB.IsPath)
    (attachB : Fin 4 -> B.verts)
    (hattach_adj :
      forall i : Fin 4, G.Adj (attachB i : V) (D.model.branchVertex i))
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
  exact
    D.carrier_bridge_attachment_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
      (Function.Embedding.refl (Fin 4)) B hbranch_not_B hcore_internal_not_B
      hleft_ne_right pB hpB attachB hattach_adj stemB hstemB_path
      hstemB_punctured_avoids_endpoints hbridge_stem_meet_only_endpoint
      hstem_meet_only_common_endpoint
theorem K4UnsplitSubdivisionData.carrier_bridge_attachment_subgraph_paths_relabel_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    (B : G.Subgraph)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    {leftB rightB : B.verts}
    (hleft_ne_right : (leftB : V) ≠ (rightB : V))
    (pB : B.coe.Walk leftB rightB)
    (hpB : pB.IsPath)
    (attachB : Fin 4 -> B.verts)
    (hattach_adj :
      forall i : Fin 4,
        G.Adj (attachB i : V) (D.model.branchVertex (σ i)))
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
  exact
    D.carrier_bridge_attachment_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
    σ B hbranch_not_B hcore_internal_not_B hleft_ne_right pB hpB attachB
    hattach_adj stemB hstemB_path hstemB_punctured_avoids_endpoints
    hbridge_stem_meet_only_endpoint hstem_meet_only_common_endpoint
theorem K4UnsplitSubdivisionData.carrier_bridge_two_arm_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    (B : G.Subgraph)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    {leftB rightB : B.verts}
    (hleft_ne_right : (leftB : V) ≠ (rightB : V))
    (pB : B.coe.Walk leftB rightB)
    (hpB : pB.IsPath)
    (attachB : Fin 4 -> B.verts)
    (hattach_adj :
      forall i : Fin 4,
        G.Adj (attachB i : V) (D.model.branchVertex (σ i)))
    (hattach0 : attachB (0 : Fin 4) = leftB)
    (hattach2 : attachB (2 : Fin 4) = rightB)
    (stemLeftB : B.coe.Walk leftB (attachB (1 : Fin 4)))
    (stemRightB : B.coe.Walk rightB (attachB (3 : Fin 4)))
    (hstemLeftB_path : stemLeftB.IsPath)
    (hstemRightB_path : stemRightB.IsPath)
    (hstemLeftB_avoids_right :
      forall {z : B.verts},
        z ∈ stemLeftB.support -> z ≠ leftB -> z ≠ rightB)
    (hstemRightB_avoids_left :
      forall {z : B.verts},
        z ∈ stemRightB.support -> z ≠ rightB -> z ≠ leftB)
    (hbridge_stemLeft_meet_only_endpoint :
      forall {z : B.verts},
        z ∈ Walk.InternalVertices pB ->
          z ∈ stemLeftB.support -> z ≠ leftB -> False)
    (hbridge_stemRight_meet_only_endpoint :
      forall {z : B.verts},
        z ∈ Walk.InternalVertices pB ->
          z ∈ stemRightB.support -> z ≠ rightB -> False)
    (hstemLeftRight_meet_only_endpoints :
      forall {z : B.verts},
        z ∈ stemLeftB.support ->
          z ∈ stemRightB.support -> z ≠ leftB -> z ≠ rightB -> False) :
    NearHajosStrengtheningConclusion G := by
  classical
  let stemB :
      forall i : Fin 4,
        B.coe.Walk (k4BridgeEndpointSubgraph B leftB rightB i) (attachB i)
    | 0 => (SimpleGraph.Walk.nil : B.coe.Walk leftB leftB).copy rfl hattach0.symm
    | 1 => stemLeftB
    | 2 => (SimpleGraph.Walk.nil : B.coe.Walk rightB rightB).copy rfl hattach2.symm
    | 3 => stemRightB
  have hstemB_path : forall i : Fin 4, (stemB i).IsPath := by
    intro i
    fin_cases i
    · simp [stemB]
    · simpa [stemB] using hstemLeftB_path
    · simp [stemB]
    · simpa [stemB] using hstemRightB_path
  have hstemB_avoids :
      forall i : Fin 4, forall {z : B.verts},
        z ∈ (stemB i).support ->
          z ≠ k4BridgeEndpointSubgraph B leftB rightB i ->
            z ≠ leftB ∧ z ≠ rightB := by
    intro i z hz hz_ne
    fin_cases i
    · have hz_left : z = leftB := by
        simpa [stemB, k4BridgeEndpointSubgraph] using hz
      exact False.elim (hz_ne (by simp [k4BridgeEndpointSubgraph, hz_left]))
    · refine ⟨by simpa [k4BridgeEndpointSubgraph] using hz_ne, ?_⟩
      exact hstemLeftB_avoids_right
        (by simpa [stemB] using hz)
        (by simpa [k4BridgeEndpointSubgraph] using hz_ne)
    · have hz_right : z = rightB := by
        simpa [stemB, k4BridgeEndpointSubgraph] using hz
      exact False.elim (hz_ne (by simp [k4BridgeEndpointSubgraph, hz_right]))
    · refine ⟨?_, by simpa [k4BridgeEndpointSubgraph] using hz_ne⟩
      exact hstemRightB_avoids_left
        (by simpa [stemB] using hz)
        (by simpa [k4BridgeEndpointSubgraph] using hz_ne)
  have hbridge_stem_meet :
      forall i : Fin 4, forall {z : B.verts},
        z ∈ Walk.InternalVertices pB ->
          z ∈ (stemB i).support ->
            z ≠ k4BridgeEndpointSubgraph B leftB rightB i ->
              False := by
    intro i z hz_p hz_stem hz_ne
    fin_cases i
    · have hz_left : z = leftB := by
        simpa [stemB, k4BridgeEndpointSubgraph] using hz_stem
      exact hz_p.2.1 hz_left
    · exact hbridge_stemLeft_meet_only_endpoint hz_p
        (by simpa [stemB] using hz_stem)
        (by simpa [k4BridgeEndpointSubgraph] using hz_ne)
    · have hz_right : z = rightB := by
        simpa [stemB, k4BridgeEndpointSubgraph] using hz_stem
      exact hz_p.2.2 hz_right
    · exact hbridge_stemRight_meet_only_endpoint hz_p
        (by simpa [stemB] using hz_stem)
        (by simpa [k4BridgeEndpointSubgraph] using hz_ne)
  have hstem_meet :
      forall {i j : Fin 4}, i ≠ j ->
        forall {z : B.verts},
          z ∈ (stemB i).support ->
            z ∈ (stemB j).support ->
              z ≠ k4BridgeEndpointSubgraph B leftB rightB i ->
                z ≠ k4BridgeEndpointSubgraph B leftB rightB j ->
                  False := by
    intro i j hij z hzi hzj hzi_ne hzj_ne
    fin_cases i <;> fin_cases j <;>
      simp [stemB, k4BridgeEndpointSubgraph] at hzi hzj hzi_ne hzj_ne hij
    · exact hzi_ne hzi
    · exact hleft_ne_right (by
        calc
          (leftB : V) = (z : V) := by simp [hzi]
          _ = (rightB : V) := by simp [hzj])
    · exact hzi_ne hzi
    · exact hzj_ne hzj
    · exact (hstemLeftB_avoids_right hzi (by simpa using hzi_ne)) hzj
    · exact hstemLeftRight_meet_only_endpoints hzi hzj
        (by simpa using hzi_ne) (by simpa using hzj_ne)
    · exact hleft_ne_right (by
        calc
          (leftB : V) = (z : V) := by simp [hzj]
          _ = (rightB : V) := by simp [hzi])
    · exact (hstemLeftB_avoids_right hzj (by simpa using hzj_ne)) hzi
    · exact hzi_ne hzi
    · exact hzj_ne hzj
    · exact hstemLeftRight_meet_only_endpoints hzj hzi
        (by simpa using hzj_ne) (by simpa using hzi_ne)
    · exact hzj_ne hzj
  exact
    D.carrier_bridge_attachment_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
      σ B hbranch_not_B hcore_internal_not_B
      hleft_ne_right pB hpB attachB hattach_adj stemB hstemB_path
      hstemB_avoids hbridge_stem_meet hstem_meet


theorem K4UnsplitSubdivisionData.carrier_bridge_two_arm_subgraph_paths_relabel_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    (B : G.Subgraph)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    {leftB rightB : B.verts}
    (hleft_ne_right : (leftB : V) ≠ (rightB : V))
    (pB : B.coe.Walk leftB rightB)
    (hpB : pB.IsPath)
    (attachB : Fin 4 -> B.verts)
    (hattach_adj :
      forall i : Fin 4,
        G.Adj (attachB i : V) (D.model.branchVertex (σ i)))
    (hattach0 : attachB (0 : Fin 4) = leftB)
    (hattach2 : attachB (2 : Fin 4) = rightB)
    (stemLeftB : B.coe.Walk leftB (attachB (1 : Fin 4)))
    (stemRightB : B.coe.Walk rightB (attachB (3 : Fin 4)))
    (hstemLeftB_path : stemLeftB.IsPath)
    (hstemRightB_path : stemRightB.IsPath)
    (hstemLeftB_avoids_right :
      forall {z : B.verts},
        z ∈ stemLeftB.support -> z ≠ leftB -> z ≠ rightB)
    (hstemRightB_avoids_left :
      forall {z : B.verts},
        z ∈ stemRightB.support -> z ≠ rightB -> z ≠ leftB)
    (hbridge_stemLeft_meet_only_endpoint :
      forall {z : B.verts},
        z ∈ Walk.InternalVertices pB ->
          z ∈ stemLeftB.support -> z ≠ leftB -> False)
    (hbridge_stemRight_meet_only_endpoint :
      forall {z : B.verts},
        z ∈ Walk.InternalVertices pB ->
          z ∈ stemRightB.support -> z ≠ rightB -> False)
    (hstemLeftRight_meet_only_endpoints :
      forall {z : B.verts},
        z ∈ stemLeftB.support ->
          z ∈ stemRightB.support -> z ≠ leftB -> z ≠ rightB -> False) :
    NearHajosStrengtheningConclusion G := by
  exact
    D.carrier_bridge_two_arm_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
    σ B hbranch_not_B hcore_internal_not_B hleft_ne_right pB hpB attachB
    hattach_adj hattach0 hattach2 stemLeftB stemRightB hstemLeftB_path
    hstemRightB_path hstemLeftB_avoids_right hstemRightB_avoids_left
    hbridge_stemLeft_meet_only_endpoint hbridge_stemRight_meet_only_endpoint
    hstemLeftRight_meet_only_endpoints

end Schematic.Math.GraphTheory
