import DominatingFourColour.Consequences.NearHajos.AllSingleton.ConePaths

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem k4_clique_with_connected_bridge_pair_split_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (e : Fin 4 ↪ V)
    (h_adj : forall x y : Fin 4, x ≠ y -> G.Adj (e x) (e y))
    (B : G.Subgraph)
    (hB_connected : B.coe.Connected)
    {left right : V}
    (hleft_mem : left ∈ B.verts)
    (hright_mem : right ∈ B.verts)
    (hcore_not_mem_B : forall i : Fin 4, e i ∉ B.verts)
    (hleft0 : G.Adj left (e (0 : Fin 4)))
    (hleft1 : G.Adj left (e (1 : Fin 4)))
    (hright2 : G.Adj right (e (2 : Fin 4)))
    (hright3 : G.Adj right (e (3 : Fin 4))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let D : K4UnsplitSubdivisionData G := K4UnsplitSubdivisionData.ofCliqueEmbedding e h_adj
  have hcore_internal_empty :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> False := by
    intro i j hij z hz
    have hunsplit : D.model.EdgeUnsplit hij := by
      simp [D, K4UnsplitSubdivisionData.ofCliqueEmbedding,
        StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit]
    exact (Walk.not_mem_internalVertices_of_length_eq_one hunsplit hz).elim
  by_cases hsame : left = right
  · subst right
    refine D.cone_apex_near_hajos_with_two_incident_unsplit_edges left ?_ ?_ ?_
    · intro i
      change left ≠ e i
      intro h
      exact hcore_not_mem_B i (by simpa [h] using hleft_mem)
    · intro i j hij z hz
      exact (hcore_internal_empty hij hz).elim
    · intro i
      fin_cases i <;>
        simp [D, K4UnsplitSubdivisionData.ofCliqueEmbedding,
          StrictSubdivisionModel.ofCompleteGraphEmbedding,
          StrictSubdivisionModel.ofGraphEmbedding]
      · exact hleft0
      · exact hleft1
      · exact hright2
      · exact hright3
  · obtain ⟨p, hp, hp_le⟩ :=
      Subgraph.Connected.exists_path_between hB_connected hleft_mem hright_mem
    refine
      D.bridge_path_k5hat_near_hajos_with_two_incident_unsplit_edges
        hsame ?_ ?_ p hp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i
      change left ≠ e i
      intro h
      exact hcore_not_mem_B i (by simpa [h] using hleft_mem)
    · intro i
      change right ≠ e i
      intro h
      exact hcore_not_mem_B i (by simpa [h] using hright_mem)
    · intro z hz i
      change z ≠ e i
      intro h
      have hzB : z ∈ B.verts :=
        hp_le.left (by
          rw [SimpleGraph.Walk.mem_verts_toSubgraph]
          exact hz.1)
      exact hcore_not_mem_B i (by simpa [h] using hzB)
    · intro i j hij z hz
      exact (hcore_internal_empty hij hz).elim
    · intro i j hij z hz
      exact (hcore_internal_empty hij hz).elim
    · intro i j hij z _hz_bridge hz_core
      exact (hcore_internal_empty hij hz_core).elim
    · simpa [D, K4UnsplitSubdivisionData.ofCliqueEmbedding,
        StrictSubdivisionModel.ofCompleteGraphEmbedding,
        StrictSubdivisionModel.ofGraphEmbedding] using hleft0
    · simpa [D, K4UnsplitSubdivisionData.ofCliqueEmbedding,
        StrictSubdivisionModel.ofCompleteGraphEmbedding,
        StrictSubdivisionModel.ofGraphEmbedding] using hleft1
    · simpa [D, K4UnsplitSubdivisionData.ofCliqueEmbedding,
        StrictSubdivisionModel.ofCompleteGraphEmbedding,
        StrictSubdivisionModel.ofGraphEmbedding] using hright2
    · simpa [D, K4UnsplitSubdivisionData.ofCliqueEmbedding,
        StrictSubdivisionModel.ofCompleteGraphEmbedding,
        StrictSubdivisionModel.ofGraphEmbedding] using hright3

theorem k4_clique_with_disjoint_bridge_paths_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (e : Fin 4 ↪ V)
    (h_adj : forall x y : Fin 4, x ≠ y -> G.Adj (e x) (e y))
    {left right : V}
    (hleft_ne_right : left ≠ right)
    (hleft_not_core : forall i : Fin 4, left ≠ e i)
    (hright_not_core : forall i : Fin 4, right ≠ e i)
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_no_core :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        forall i : Fin 4, z ≠ e i)
    (arm :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (e i))
    (harm_path : forall i : Fin 4, (arm i).IsPath)
    (harm_internal_no_special :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          z ≠ left ∧ z ≠ right ∧ forall j : Fin 4, z ≠ e j)
    (hbridge_arm_disjoint :
      forall i : Fin 4,
        Disjoint (Walk.InternalVertices p) (Walk.InternalVertices (arm i)))
    (harm_internal_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (arm j))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let D : K4UnsplitSubdivisionData G := K4UnsplitSubdivisionData.ofCliqueEmbedding e h_adj
  have hcore_internal_empty :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> False := by
    intro i j hij z hz
    have hunsplit : D.model.EdgeUnsplit hij := by
      simp [D, K4UnsplitSubdivisionData.ofCliqueEmbedding,
        StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit]
    exact (Walk.not_mem_internalVertices_of_length_eq_one hunsplit hz).elim
  refine
    D.bridge_paths_k5hat_near_hajos_with_two_incident_unsplit_edges
      hleft_ne_right ?_ ?_ p hp ?_ ?_ ?_ ?_
      arm ?_ ?_ ?_ ?_ ?_
  · intro i
    change left ≠ e i
    exact hleft_not_core i
  · intro i
    change right ≠ e i
    exact hright_not_core i
  · intro z hz i
    change z ≠ e i
    exact hp_internal_no_core hz i
  · intro i j hij z hz
    exact (hcore_internal_empty hij hz).elim
  · intro i j hij z hz
    exact (hcore_internal_empty hij hz).elim
  · intro i j hij z _hz_bridge hz_core
    exact (hcore_internal_empty hij hz_core).elim
  · intro i
    change (arm i).IsPath
    exact harm_path i
  · intro i z hz
    exact harm_internal_no_special i hz
  · exact hbridge_arm_disjoint
  · exact harm_internal_disjoint
  · intro i j k hjk
    rw [Set.disjoint_left]
    intro z _hz_arm hz_core
    exact (hcore_internal_empty hjk hz_core).elim

theorem dominating_K5_model_tail_all_singleton_first_branch_disjoint_bridge_paths_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {left right : V}
    (hleft_mem : left ∈ (T.branch (0 : Fin 5)).verts)
    (hright_mem : right ∈ (T.branch (0 : Fin 5)).verts)
    (hleft_ne_right : left ≠ right)
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_in_first_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        z ∈ (T.branch (0 : Fin 5)).verts)
    (arm :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (htail i).choose)
    (harm_path : forall i : Fin 4, (arm i).IsPath)
    (harm_internal_in_first_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          z ∈ (T.branch (0 : Fin 5)).verts)
    (harm_internal_avoids_endpoints :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          z ≠ left ∧ z ≠ right)
    (hbridge_arm_disjoint :
      forall i : Fin 4,
        Disjoint (Walk.InternalVertices p) (Walk.InternalVertices (arm i)))
    (harm_internal_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (arm j))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let e : Fin 4 ↪ V :=
    T.tailK4.singletonBranchEmbedding htail
  refine
    k4_clique_with_disjoint_bridge_paths_near_hajos
      e ?_ hleft_ne_right ?_ ?_ p hp ?_
      arm ?_ ?_ ?_ ?_
  · intro x y hxy
    change G.Adj (htail x).choose (htail y).choose
    exact dominating_K5_model_tail_all_singleton_tail_adj T htail hxy
  · intro i
    change left ≠ (htail i).choose
    intro h
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail i (by simpa [h] using hleft_mem)
  · intro i
    change right ≠ (htail i).choose
    intro h
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail i (by simpa [h] using hright_mem)
  · intro z hz i
    change z ≠ (htail i).choose
    intro h
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail i (by simpa [h] using hp_internal_in_first_branch hz)
  · intro i
    change (arm i).IsPath
    exact harm_path i
  · intro i z hz
    refine ⟨(harm_internal_avoids_endpoints i hz).1,
      (harm_internal_avoids_endpoints i hz).2, ?_⟩
    intro j hcore
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail j (by
        simpa [hcore] using harm_internal_in_first_branch i hz)
  · exact hbridge_arm_disjoint
  · exact harm_internal_disjoint

theorem dominating_K5_model_tail_all_singleton_first_branch_bridge_attachment_paths_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {left right : V}
    (hleft_mem : left ∈ (T.branch (0 : Fin 5)).verts)
    (hright_mem : right ∈ (T.branch (0 : Fin 5)).verts)
    (hleft_ne_right : left ≠ right)
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_in_first_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        z ∈ (T.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (stem :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_first_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts)
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
        G.Walk (k4BridgeEndpoint left right i) (htail i).choose :=
    fun i => (stem i).concat (hattach i).2
  have htail_not_stem_support :
      forall i : Fin 4, (htail i).choose ∉ (stem i).support := by
    intro i hsupport
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail i (hstem_support_first_branch i hsupport)
  refine
    dominating_K5_model_tail_all_singleton_first_branch_disjoint_bridge_paths_near_hajos
      T htail hleft_mem hright_mem hleft_ne_right p hp
      hp_internal_in_first_branch arm ?_ ?_ ?_ ?_ ?_
  · intro i
    change ((stem i).concat (hattach i).2).IsPath
    exact (hstem_path i).concat (htail_not_stem_support i) (hattach i).2
  · intro i z hz
    change z ∈ (T.branch (0 : Fin 5)).verts
    have hz_stem :
        z ∈ (stem i).support :=
      Walk.mem_support_of_mem_internalVertices_concat (stem i) (hattach i).2 hz
    exact hstem_support_first_branch i hz_stem
  · intro i z hz
    have hz_stem :
        z ∈ (stem i).support ∧
          z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hz
    exact hstem_punctured_avoids_endpoints i hz_stem.1 hz_stem.2
  · intro i
    rw [Set.disjoint_left]
    intro z hz_bridge hz_arm
    have hz_stem :
        z ∈ (stem i).support ∧
          z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hz_arm
    exact Set.disjoint_left.mp (hbridge_stem_disjoint i) hz_bridge hz_stem
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzi_stem :
        z ∈ (stem i).support ∧
          z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hzi
    have hzj_stem :
        z ∈ (stem j).support ∧
          z ≠ k4BridgeEndpoint left right j :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem j) (hattach j).2 hzj
    exact Set.disjoint_left.mp (hstem_punctured_disjoint hij)
      hzi_stem hzj_stem

theorem dominating_K5_model_tail_all_singleton_first_branch_bridge_attachment_paths_meet_only_endpoints_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {left right : V}
    (hleft_mem : left ∈ (T.branch (0 : Fin 5)).verts)
    (hright_mem : right ∈ (T.branch (0 : Fin 5)).verts)
    (hleft_ne_right : left ≠ right)
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_in_first_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        z ∈ (T.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (stem :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_first_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts)
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
    dominating_K5_model_tail_all_singleton_first_branch_bridge_attachment_paths_near_hajos
      T htail hleft_mem hright_mem hleft_ne_right p hp hp_internal_in_first_branch
      attach hattach stem hstem_path hstem_support_first_branch
      hstem_punctured_avoids_endpoints
      (walk_support_punctured_disjoint_of_forall_not_mem p
        (fun i => ⟨k4BridgeEndpoint left right i, ⟨attach i, stem i⟩⟩)
        (fun i => k4BridgeEndpoint left right i)
        hbridge_stem_meet_only_endpoint)
      (by
        intro i j hij
        rw [Set.disjoint_left]
        rintro z ⟨hzi, hzi_ne⟩ ⟨hzj, hzj_ne⟩
        exact hstem_meet_only_common_endpoint hij hzi hzj hzi_ne hzj_ne)

theorem dominating_K5_model_tail_all_singleton_first_branch_bridge_attachment_paths_relabel_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (σ : Fin 4 ↪ Fin 4)
    {left right : V}
    (hleft_mem : left ∈ (T.branch (0 : Fin 5)).verts)
    (hright_mem : right ∈ (T.branch (0 : Fin 5)).verts)
    (hleft_ne_right : left ≠ right)
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_in_first_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        z ∈ (T.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail (σ i)).choose)
    (stem :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_first_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts)
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
  let e : Fin 4 ↪ V :=
    σ.trans (T.tailK4.singletonBranchEmbedding htail)
  let arm :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (e i) :=
    fun i => (stem i).concat (hattach i).2
  have htail_not_stem_support :
      forall i : Fin 4, (htail (σ i)).choose ∉ (stem i).support := by
    intro i hsupport
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail (σ i) (hstem_support_first_branch i hsupport)
  refine
    k4_clique_with_disjoint_bridge_paths_near_hajos
      e ?_ hleft_ne_right ?_ ?_ p hp ?_
      arm ?_ ?_ ?_ ?_
  · intro x y hxy
    change G.Adj (htail (σ x)).choose (htail (σ y)).choose
    exact dominating_K5_model_tail_all_singleton_tail_adj_reindex
      T htail σ hxy
  · intro i
    change left ≠ (htail (σ i)).choose
    intro h
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail (σ i) (by simpa [h] using hleft_mem)
  · intro i
    change right ≠ (htail (σ i)).choose
    intro h
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail (σ i) (by simpa [h] using hright_mem)
  · intro z hz i
    change z ≠ (htail (σ i)).choose
    intro h
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail (σ i) (by
        simpa [h] using hp_internal_in_first_branch hz)
  · intro i
    change ((stem i).concat (hattach i).2).IsPath
    exact (hstem_path i).concat (htail_not_stem_support i) (hattach i).2
  · intro i z hz
    change z ≠ left ∧ z ≠ right ∧ forall j : Fin 4, z ≠ e j
    have hz_stem :
        z ∈ (stem i).support ∧
          z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hz
    refine ⟨(hstem_punctured_avoids_endpoints i hz_stem.1 hz_stem.2).1,
      (hstem_punctured_avoids_endpoints i hz_stem.1 hz_stem.2).2, ?_⟩
    intro j
    change z ≠ (htail (σ j)).choose
    intro hcore
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail (σ j) (by
        simpa [hcore] using hstem_support_first_branch i hz_stem.1)
  · intro i
    rw [Set.disjoint_left]
    intro z hz_bridge hz_arm
    have hz_stem :
        z ∈ (stem i).support ∧
          z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hz_arm
    exact Set.disjoint_left.mp (hbridge_stem_disjoint i) hz_bridge hz_stem
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzi_stem :
        z ∈ (stem i).support ∧
          z ≠ k4BridgeEndpoint left right i :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hzi
    have hzj_stem :
        z ∈ (stem j).support ∧
          z ≠ k4BridgeEndpoint left right j :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem j) (hattach j).2 hzj
    exact Set.disjoint_left.mp (hstem_punctured_disjoint hij)
      hzi_stem hzj_stem

theorem dominating_K5_model_tail_all_singleton_first_branch_bridge_attachment_paths_relabel_meet_only_endpoints_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (σ : Fin 4 ↪ Fin 4)
    {left right : V}
    (hleft_mem : left ∈ (T.branch (0 : Fin 5)).verts)
    (hright_mem : right ∈ (T.branch (0 : Fin 5)).verts)
    (hleft_ne_right : left ≠ right)
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_in_first_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        z ∈ (T.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail (σ i)).choose)
    (stem :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_first_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts)
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
    dominating_K5_model_tail_all_singleton_first_branch_bridge_attachment_paths_relabel_near_hajos
      T htail σ hleft_mem hright_mem hleft_ne_right p hp hp_internal_in_first_branch
      attach hattach stem hstem_path hstem_support_first_branch
      hstem_punctured_avoids_endpoints
      (walk_support_punctured_disjoint_of_forall_not_mem p
        (fun i => ⟨k4BridgeEndpoint left right i, ⟨attach i, stem i⟩⟩)
        (fun i => k4BridgeEndpoint left right i)
        hbridge_stem_meet_only_endpoint)
      (by
        intro i j hij
        rw [Set.disjoint_left]
        rintro z ⟨hzi, hzi_ne⟩ ⟨hzj, hzj_ne⟩
        exact hstem_meet_only_common_endpoint hij hzi hzj hzi_ne hzj_ne)

theorem dominating_K5_model_tail_all_singleton_first_branch_bridge_attachment_subgraph_paths_relabel_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (σ : Fin 4 ↪ Fin 4)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (leftB rightB : B.verts)
    (hleft_ne_right : (leftB : V) ≠ (rightB : V))
    (pB : B.coe.Walk leftB rightB)
    (hpB : pB.IsPath)
    (attachB : Fin 4 -> B.verts)
    (hattach :
      forall i : Fin 4,
        (attachB i : V) ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attachB i : V) (htail (σ i)).choose)
    (stemB :
      forall i : Fin 4,
        B.coe.Walk (k4BridgeEndpoint leftB rightB i) (attachB i))
    (hstemB_path : forall i : Fin 4, (stemB i).IsPath)
    (hstem_punctured_avoids_endpoints :
      forall i : Fin 4, forall {z : B.verts},
        z ∈ (stemB i).support ->
          z ≠ k4BridgeEndpoint leftB rightB i ->
            (z : V) ≠ (leftB : V) ∧ (z : V) ≠ (rightB : V))
    (hbridge_stem_disjoint :
      forall i : Fin 4,
        Disjoint
          (Walk.InternalVertices pB)
          {z : B.verts | z ∈ (stemB i).support ∧
            z ≠ k4BridgeEndpoint leftB rightB i})
    (hstem_punctured_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : B.verts | z ∈ (stemB i).support ∧
            z ≠ k4BridgeEndpoint leftB rightB i}
          {z : B.verts | z ∈ (stemB j).support ∧
            z ≠ k4BridgeEndpoint leftB rightB j}) :
    NearHajosStrengtheningConclusion G := by
  let left : V := leftB
  let right : V := rightB
  let attach : Fin 4 -> V := fun i => attachB i
  let p : G.Walk left right := pB.map B.hom
  have endpoint_coe :
      forall i : Fin 4,
        ((k4BridgeEndpoint leftB rightB i : B.verts) : V) =
          k4BridgeEndpoint left right i := by
    intro i
    fin_cases i <;> rfl
  have endpoint_cast :
      forall i : Fin 4,
        ((k4BridgeEndpoint leftB rightB i : B.verts) : V) =
          k4BridgeEndpoint (leftB : V) (rightB : V) i := by
    intro i
    fin_cases i <;> rfl
  have endpoint_val :
      forall i : Fin 4,
        k4BridgeEndpoint (leftB : V) (rightB : V) i =
          k4BridgeEndpoint left right i := by
    intro i
    rfl
  let stem : forall i : Fin 4,
      G.Walk (k4BridgeEndpoint left right i) (attach i) := fun i =>
    ((stemB i).map B.hom).copy
      (endpoint_coe i) rfl
  have hp : p.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hpB
  have hp_internal :
      forall {z : V},
        z ∈ Walk.InternalVertices p ->
          z ∈ (T.branch (0 : Fin 5)).verts := by
    intro z hz
    exact hB_le.left
      (Walk.internalVertices_map_subgraph_hom_subset (H := B) pB
        (by simpa [p] using hz))
  have hstem_path : forall i : Fin 4, (stem i).IsPath := by
    intro i
    simpa [stem] using
      (SimpleGraph.Walk.map_isPath_of_injective
        SimpleGraph.Subgraph.hom_injective (hstemB_path i))
  have hstem_support :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts := by
    intro i z hz
    exact hB_le.left
      (Walk.support_map_subgraph_hom_subset (H := B) (stemB i)
        (by simpa [stem] using hz))
  have hstem_avoids :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ≠ k4BridgeEndpoint left right i ->
            z ≠ left ∧ z ≠ right := by
    intro i z hz hz_ne
    rcases (Walk.mem_support_map_subgraph_hom_iff
      (H := B) (stemB i)).mp (by simpa [stem] using hz) with
      ⟨zB, hzB, hzB_eq⟩
    have hzB_ne :
        zB ≠ k4BridgeEndpoint leftB rightB i := by
      intro h
      exact hz_ne (by
        calc
          z = (zB : V) := hzB_eq.symm
          _ = ((k4BridgeEndpoint leftB rightB i : B.verts) : V) := by rw [h]
          _ = k4BridgeEndpoint (leftB : V) (rightB : V) i := endpoint_cast i
          _ = k4BridgeEndpoint left right i := endpoint_val i)
    simpa [left, right, hzB_eq] using
      (hstem_punctured_avoids_endpoints i hzB hzB_ne)
  have hbridge_stem_disjoint_G :
      forall i : Fin 4,
        Disjoint
          (Walk.InternalVertices p)
          {z : V | z ∈ (stem i).support ∧
            z ≠ k4BridgeEndpoint left right i} := by
    intro i
    have hraw :
        Disjoint
          (Walk.InternalVertices (pB.map B.hom))
          {z : V | z ∈ ((stemB i).map B.hom).support ∧
            z ≠ ((k4BridgeEndpoint leftB rightB i : B.verts) : V)} :=
      Subgraph.mapped_internalVertices_disjoint_punctured_support
        (G := G) (B := B) pB (stemB i) (hbridge_stem_disjoint i)
    simpa [p, stem, endpoint_coe i] using hraw
  have hstem_punctured_disjoint_G :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stem i).support ∧
            z ≠ k4BridgeEndpoint left right i}
          {z : V | z ∈ (stem j).support ∧
            z ≠ k4BridgeEndpoint left right j} := by
    intro i j hij
    have hraw :
        Disjoint
          {z : V | z ∈ ((stemB i).map B.hom).support ∧
            z ≠ ((k4BridgeEndpoint leftB rightB i : B.verts) : V)}
          {z : V | z ∈ ((stemB j).map B.hom).support ∧
            z ≠ ((k4BridgeEndpoint leftB rightB j : B.verts) : V)} :=
      Subgraph.mapped_punctured_supports_disjoint
        (G := G) (B := B) (stemB i) (stemB j)
        (hstem_punctured_disjoint hij)
    simpa [stem, endpoint_coe i, endpoint_coe j] using hraw
  exact
    dominating_K5_model_tail_all_singleton_first_branch_bridge_attachment_paths_relabel_near_hajos
      T htail σ (hB_le.left leftB.2) (hB_le.left rightB.2) hleft_ne_right
      p hp hp_internal attach hattach stem hstem_path hstem_support
      hstem_avoids hbridge_stem_disjoint_G hstem_punctured_disjoint_G

theorem dominating_K5_model_tail_all_singleton_first_branch_bridge_attachment_subgraph_paths_relabel_meet_only_endpoints_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (σ : Fin 4 ↪ Fin 4)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (leftB rightB : B.verts)
    (hleft_ne_right : (leftB : V) ≠ (rightB : V))
    (pB : B.coe.Walk leftB rightB)
    (hpB : pB.IsPath)
    (attachB : Fin 4 -> B.verts)
    (hattach :
      forall i : Fin 4,
        (attachB i : V) ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attachB i : V) (htail (σ i)).choose)
    (stemB :
      forall i : Fin 4,
        B.coe.Walk (k4BridgeEndpoint leftB rightB i) (attachB i))
    (hstemB_path : forall i : Fin 4, (stemB i).IsPath)
    (hstem_punctured_avoids_endpoints :
      forall i : Fin 4, forall {z : B.verts},
        z ∈ (stemB i).support ->
          z ≠ k4BridgeEndpoint leftB rightB i ->
            (z : V) ≠ (leftB : V) ∧ (z : V) ≠ (rightB : V))
    (hbridge_stem_meet_only_endpoint :
      forall i : Fin 4, forall {z : B.verts},
        z ∈ Walk.InternalVertices pB ->
          z ∈ (stemB i).support ->
            z ≠ k4BridgeEndpoint leftB rightB i ->
              False)
    (hstem_meet_only_common_endpoint :
      forall {i j : Fin 4}, i ≠ j ->
        forall {z : B.verts},
          z ∈ (stemB i).support ->
            z ∈ (stemB j).support ->
              z ≠ k4BridgeEndpoint leftB rightB i ->
                z ≠ k4BridgeEndpoint leftB rightB j ->
                  False) :
    NearHajosStrengtheningConclusion G := by
  let left : V := leftB
  let right : V := rightB
  let attach : Fin 4 -> V := fun i => attachB i
  let p : G.Walk left right := pB.map B.hom
  have endpoint_coe :
      forall i : Fin 4,
        ((k4BridgeEndpoint leftB rightB i : B.verts) : V) =
          k4BridgeEndpoint left right i := by
    intro i
    fin_cases i <;> rfl
  have endpoint_cast :
      forall i : Fin 4,
        ((k4BridgeEndpoint leftB rightB i : B.verts) : V) =
          k4BridgeEndpoint (leftB : V) (rightB : V) i := by
    intro i
    fin_cases i <;> rfl
  have endpoint_val :
      forall i : Fin 4,
        k4BridgeEndpoint (leftB : V) (rightB : V) i =
          k4BridgeEndpoint left right i := by
    intro i
    rfl
  let stem : forall i : Fin 4,
      G.Walk (k4BridgeEndpoint left right i) (attach i) := fun i =>
    ((stemB i).map B.hom).copy
      (endpoint_coe i) rfl
  have hp : p.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hpB
  have hp_internal :
      forall {z : V},
        z ∈ Walk.InternalVertices p ->
          z ∈ (T.branch (0 : Fin 5)).verts := by
    intro z hz
    exact hB_le.left
      (Walk.internalVertices_map_subgraph_hom_subset (H := B) pB
        (by simpa [p] using hz))
  have hstem_path : forall i : Fin 4, (stem i).IsPath := by
    intro i
    simpa [stem] using
      (SimpleGraph.Walk.map_isPath_of_injective
        SimpleGraph.Subgraph.hom_injective (hstemB_path i))
  have hstem_support :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts := by
    intro i z hz
    exact hB_le.left
      (Walk.support_map_subgraph_hom_subset (H := B) (stemB i)
        (by simpa [stem] using hz))
  have hstem_avoids :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ≠ k4BridgeEndpoint left right i ->
            z ≠ left ∧ z ≠ right := by
    intro i z hz hz_ne
    rcases (Walk.mem_support_map_subgraph_hom_iff
      (H := B) (stemB i)).mp (by simpa [stem] using hz) with
      ⟨zB, hzB, hzB_eq⟩
    have hzB_ne :
        zB ≠ k4BridgeEndpoint leftB rightB i := by
      intro h
      exact hz_ne (by
        calc
          z = (zB : V) := hzB_eq.symm
          _ = ((k4BridgeEndpoint leftB rightB i : B.verts) : V) := by rw [h]
          _ = k4BridgeEndpoint (leftB : V) (rightB : V) i := endpoint_cast i
          _ = k4BridgeEndpoint left right i := endpoint_val i)
    simpa [left, right, hzB_eq] using
      (hstem_punctured_avoids_endpoints i hzB hzB_ne)
  have hbridge_stem_meet :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices p ->
          z ∈ (stem i).support ->
            z ≠ k4BridgeEndpoint left right i ->
              False := by
    intro i z hz_p hz_stem hz_ne
    rcases (Walk.mem_internalVertices_map_subgraph_hom_iff
      (H := B) pB).mp (by simpa [p] using hz_p) with
      ⟨zB, hzB_p, hzB_eq⟩
    rcases (Walk.mem_support_map_subgraph_hom_iff
      (H := B) (stemB i)).mp (by simpa [stem] using hz_stem) with
      ⟨zB', hzB'_stem, hzB'_eq⟩
    have hzz : zB = zB' := by
      apply Subtype.ext
      exact hzB_eq.trans hzB'_eq.symm
    have hzB_stem : zB ∈ (stemB i).support := by
      simpa [hzz] using hzB'_stem
    have hzB_ne :
        zB ≠ k4BridgeEndpoint leftB rightB i := by
      intro h
      exact hz_ne (by
        calc
          z = (zB : V) := hzB_eq.symm
          _ = ((k4BridgeEndpoint leftB rightB i : B.verts) : V) := by rw [h]
          _ = k4BridgeEndpoint (leftB : V) (rightB : V) i := endpoint_cast i
          _ = k4BridgeEndpoint left right i := endpoint_val i)
    exact hbridge_stem_meet_only_endpoint i hzB_p hzB_stem hzB_ne
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
    have hzij : ziB = zjB := by
      apply Subtype.ext
      exact hziB_eq.trans hzjB_eq.symm
    have hziB_ne :
        ziB ≠ k4BridgeEndpoint leftB rightB i := by
      intro h
      exact hzi_ne (by
        calc
          z = (ziB : V) := hziB_eq.symm
          _ = ((k4BridgeEndpoint leftB rightB i : B.verts) : V) := by rw [h]
          _ = k4BridgeEndpoint (leftB : V) (rightB : V) i := endpoint_cast i
          _ = k4BridgeEndpoint left right i := endpoint_val i)
    have hzjB_ne :
        ziB ≠ k4BridgeEndpoint leftB rightB j := by
      intro h
      exact hzj_ne (by
        calc
          z = (ziB : V) := hziB_eq.symm
          _ = ((k4BridgeEndpoint leftB rightB j : B.verts) : V) := by rw [h]
          _ = k4BridgeEndpoint (leftB : V) (rightB : V) j := endpoint_cast j
          _ = k4BridgeEndpoint left right j := endpoint_val j)
    exact hstem_meet_only_common_endpoint hij hziB
      (by simpa [hzij] using hzjB) hziB_ne hzjB_ne
  exact
    dominating_K5_model_tail_all_singleton_first_branch_bridge_attachment_paths_relabel_meet_only_endpoints_near_hajos
      T htail σ (hB_le.left leftB.2) (hB_le.left rightB.2) hleft_ne_right
      p hp hp_internal attach hattach stem hstem_path hstem_support
      hstem_avoids hbridge_stem_meet hstem_meet

end Schematic.Math.GraphTheory
