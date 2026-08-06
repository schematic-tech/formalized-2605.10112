import DominatingFourColour.Consequences.NearHajos.AllSingleton.Attachments

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem k4_clique_with_disjoint_cone_paths_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (e : Fin 4 ↪ V)
    (h_adj : forall x y : Fin 4, x ≠ y -> G.Adj (e x) (e y))
    (apex : V)
    (hapex_not_core : forall i : Fin 4, apex ≠ e i)
    (arm : forall i : Fin 4, G.Walk apex (e i))
    (harm_path : forall i : Fin 4, (arm i).IsPath)
    (harm_internal_no_special :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          z ≠ apex ∧ forall j : Fin 4, z ≠ e j)
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
    D.cone_paths_near_hajos_with_two_incident_unsplit_edges
      apex ?_ arm ?_ ?_ ?_ ?_ ?_
  · intro i
    change apex ≠ e i
    exact hapex_not_core i
  · intro i
    change (arm i).IsPath
    exact harm_path i
  · intro i z hz w hzw
    cases w with
    | none =>
        exact (harm_internal_no_special i hz).1 hzw
    | some j =>
        exact ((harm_internal_no_special i hz).2 j) (by
          simpa [D, K4UnsplitSubdivisionData.ofCliqueEmbedding,
            StrictSubdivisionModel.ofCompleteGraphEmbedding,
            StrictSubdivisionModel.ofGraphEmbedding] using hzw)
  · intro i j hij z hz
    exact (hcore_internal_empty hij hz).elim
  · exact harm_internal_disjoint
  · intro i j k hjk
    rw [Set.disjoint_left]
    intro z _hz_arm hz_core
    exact (hcore_internal_empty hjk hz_core).elim

theorem dominating_K5_model_tail_all_singleton_first_branch_disjoint_cone_paths_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {apex : V}
    (hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts)
    (arm : forall i : Fin 4, G.Walk apex (htail i).choose)
    (harm_path : forall i : Fin 4, (arm i).IsPath)
    (harm_internal_in_first_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          z ∈ (T.branch (0 : Fin 5)).verts)
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
    k4_clique_with_disjoint_cone_paths_near_hajos
      e ?_ apex ?_ arm ?_ ?_ ?_
  · intro x y hxy
    change G.Adj (htail x).choose (htail y).choose
    exact dominating_K5_model_tail_all_singleton_tail_adj T htail hxy
  · intro i
    change apex ≠ (htail i).choose
    intro h
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail i (by simpa [h] using hapex_mem)
  · intro i
    change (arm i).IsPath
    exact harm_path i
  · intro i z hz
    refine ⟨?_, ?_⟩
    · exact hz.2.1
    · intro j hcore
      exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
        T htail j (by
          simpa [hcore] using harm_internal_in_first_branch i hz)
  · exact harm_internal_disjoint

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_paths_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {apex : V}
    (hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (stem : forall i : Fin 4, G.Walk apex (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_first_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts)
    (hstem_punctured_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stem i).support ∧ z ≠ apex}
          {z : V | z ∈ (stem j).support ∧ z ≠ apex}) :
    NearHajosStrengtheningConclusion G := by
  classical
  let arm : forall i : Fin 4, G.Walk apex (htail i).choose :=
    fun i => (stem i).concat (hattach i).2
  have htail_not_stem_support :
      forall i : Fin 4, (htail i).choose ∉ (stem i).support := by
    intro i hsupport
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail i (hstem_support_first_branch i hsupport)
  refine
    dominating_K5_model_tail_all_singleton_first_branch_disjoint_cone_paths_near_hajos
      T htail hapex_mem arm ?_ ?_ ?_
  · intro i
    change ((stem i).concat (hattach i).2).IsPath
    exact (hstem_path i).concat (htail_not_stem_support i) (hattach i).2
  · intro i z hz
    change z ∈ (T.branch (0 : Fin 5)).verts
    have hz_stem :
        z ∈ (stem i).support :=
      Walk.mem_support_of_mem_internalVertices_concat (stem i) (hattach i).2 hz
    exact hstem_support_first_branch i hz_stem
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzi_stem :
        z ∈ (stem i).support ∧ z ≠ apex :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hzi
    have hzj_stem :
        z ∈ (stem j).support ∧ z ≠ apex :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem j) (hattach j).2 hzj
    exact Set.disjoint_left.mp (hstem_punctured_disjoint hij)
      hzi_stem hzj_stem

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_paths_relabel_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (σ : Fin 4 ↪ Fin 4)
    {apex : V}
    (hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail (σ i)).choose)
    (stem : forall i : Fin 4, G.Walk apex (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_first_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts)
    (hstem_punctured_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stem i).support ∧ z ≠ apex}
          {z : V | z ∈ (stem j).support ∧ z ≠ apex}) :
    NearHajosStrengtheningConclusion G := by
  classical
  let e : Fin 4 ↪ V :=
    σ.trans (T.tailK4.singletonBranchEmbedding htail)
  let arm : forall i : Fin 4, G.Walk apex (e i) :=
    fun i => (stem i).concat (hattach i).2
  have htail_not_stem_support :
      forall i : Fin 4, (htail (σ i)).choose ∉ (stem i).support := by
    intro i hsupport
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail (σ i) (hstem_support_first_branch i hsupport)
  refine
    k4_clique_with_disjoint_cone_paths_near_hajos
      e ?_ apex ?_ arm ?_ ?_ ?_
  · intro x y hxy
    change G.Adj (htail (σ x)).choose (htail (σ y)).choose
    exact dominating_K5_model_tail_all_singleton_tail_adj_reindex
      T htail σ hxy
  · intro i
    change apex ≠ (htail (σ i)).choose
    intro h
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
      T htail (σ i) (by simpa [h] using hapex_mem)
  · intro i
    change ((stem i).concat (hattach i).2).IsPath
    exact (hstem_path i).concat (htail_not_stem_support i) (hattach i).2
  · intro i z hz
    refine ⟨?_, ?_⟩
    · exact hz.2.1
    · intro j hcore
      exact dominating_K5_model_tail_all_singleton_not_mem_first_branch
        T htail (σ j) (by
          have hz_stem :
              z ∈ (stem i).support :=
            Walk.mem_support_of_mem_internalVertices_concat
              (stem i) (hattach i).2 hz
          simpa [e, hcore] using hstem_support_first_branch i hz_stem)
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzi_stem :
        z ∈ (stem i).support ∧ z ≠ apex :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hzi
    have hzj_stem :
        z ∈ (stem j).support ∧ z ≠ apex :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem j) (hattach j).2 hzj
    exact Set.disjoint_left.mp (hstem_punctured_disjoint hij)
      hzi_stem hzj_stem

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_paths_meet_only_root_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {apex : V}
    (hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (stem : forall i : Fin 4, G.Walk apex (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_first_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts)
    (hstem_meet_only_root :
      forall {i j : Fin 4}, i ≠ j ->
        forall {z : V},
          z ∈ (stem i).support ->
            z ∈ (stem j).support ->
              z = apex) :
    NearHajosStrengtheningConclusion G := by
  exact
    dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_paths_near_hajos
      T htail hapex_mem attach hattach stem hstem_path hstem_support_first_branch
      (walk_family_punctured_supports_disjoint_of_forall_eq_root
        (terminal := attach) stem hstem_meet_only_root)

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_paths_relabel_meet_only_root_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (σ : Fin 4 ↪ Fin 4)
    {apex : V}
    (hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail (σ i)).choose)
    (stem : forall i : Fin 4, G.Walk apex (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_first_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts)
    (hstem_meet_only_root :
      forall {i j : Fin 4}, i ≠ j ->
        forall {z : V},
          z ∈ (stem i).support ->
            z ∈ (stem j).support ->
              z = apex) :
    NearHajosStrengtheningConclusion G := by
  exact
    dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_paths_relabel_near_hajos
      T htail σ hapex_mem attach hattach stem hstem_path hstem_support_first_branch
      (walk_family_punctured_supports_disjoint_of_forall_eq_root
      (terminal := attach) stem hstem_meet_only_root)

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_subgraph_paths_relabel_meet_only_root_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (σ : Fin 4 ↪ Fin 4)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (apexB : B.verts)
    (attachB : Fin 4 -> B.verts)
    (hattach :
      forall i : Fin 4,
        (attachB i : V) ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attachB i : V) (htail (σ i)).choose)
    (stemB :
      forall i : Fin 4,
        B.coe.Walk apexB (attachB i))
    (hstemB_path : forall i : Fin 4, (stemB i).IsPath)
    (hstemB_meet_only_root :
      forall {i j : Fin 4}, i ≠ j ->
        forall {z : B.verts},
          z ∈ (stemB i).support ->
            z ∈ (stemB j).support ->
              z = apexB) :
    NearHajosStrengtheningConclusion G := by
  classical
  let apex : V := apexB
  let attach : Fin 4 -> V := fun i => attachB i
  let stemG : forall i : Fin 4, G.Walk apex (attach i) :=
    fun i => (stemB i).map B.hom
  have hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts := by
    exact hB_le.left apexB.2
  have hstemG_path : forall i : Fin 4, (stemG i).IsPath := by
    intro i
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective (hstemB_path i)
  have hstemG_support :
      forall i : Fin 4, forall {z : V},
        z ∈ (stemG i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts := by
    intro i z hz
    exact hB_le.left
      (Walk.support_map_subgraph_hom_subset (H := B) (stemB i)
        (by simpa [stemG] using hz))
  have hstemG_meet_only_root :
      forall {i j : Fin 4}, i ≠ j ->
        forall {z : V},
          z ∈ (stemG i).support ->
            z ∈ (stemG j).support ->
              z = apex := by
    intro i j hij z hzi hzj
    rcases (Walk.mem_support_map_subgraph_hom_iff
      (H := B) (stemB i)).mp (by simpa [stemG] using hzi) with
      ⟨zi, hziB, hzi_eq⟩
    rcases (Walk.mem_support_map_subgraph_hom_iff
      (H := B) (stemB j)).mp (by simpa [stemG] using hzj) with
      ⟨zj, hzjB, hzj_eq⟩
    have hzij : zi = zj := by
      apply Subtype.ext
      exact hzi_eq.trans hzj_eq.symm
    have hroot : zi = apexB :=
      hstemB_meet_only_root hij hziB (by simpa [hzij] using hzjB)
    calc
      z = (zi : V) := hzi_eq.symm
      _ = (apexB : V) := by rw [hroot]
      _ = apex := rfl
  exact
    dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_paths_relabel_meet_only_root_near_hajos
      T htail σ hapex_mem attach hattach stemG hstemG_path hstemG_support
      hstemG_meet_only_root

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_paths_delete_root_unreachable_near_hajos
    {V : Type u} {G : SimpleGraph V}
    [DecidableEq V]
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {apex : V}
    (hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (stem : forall i : Fin 4, G.Walk apex (attach i))
    (hattach_ne_apex : forall i : Fin 4, attach i ≠ apex)
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_first_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts)
    (hunreachable :
      forall {i j : Fin 4}, i ≠ j ->
        ¬ (G.induce ({apex} : Set V)ᶜ).Reachable
            ⟨attach i, by exact hattach_ne_apex i⟩
            ⟨attach j, by exact hattach_ne_apex j⟩) :
    NearHajosStrengtheningConclusion G := by
  exact
    dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_paths_near_hajos
      T htail hapex_mem attach hattach stem hstem_path hstem_support_first_branch
      (walk_family_punctured_supports_disjoint_of_delete_root_unreachable
        (root := apex) (terminal := attach) stem hattach_ne_apex
        hstem_path hunreachable)

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_subgraph_paths_delete_root_unreachable_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {apex : V}
    (hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hapexB : apex ∈ B.verts)
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    [DecidableEq B.verts]
    (stemB :
      forall i : Fin 4,
        B.coe.Walk (⟨apex, hapexB⟩ : B.verts)
          (⟨attach i, hB_terminal i⟩ : B.verts))
    (hattach_ne_apex : forall i : Fin 4, attach i ≠ apex)
    (hstemB_path : forall i : Fin 4, (stemB i).IsPath)
    (hunreachable :
      forall {i j : Fin 4}, i ≠ j ->
        ¬ (B.coe.induce ({(⟨apex, hapexB⟩ : B.verts)} : Set B.verts)ᶜ).Reachable
            ⟨(⟨attach i, hB_terminal i⟩ : B.verts), by
              intro h
              exact hattach_ne_apex i (by
                have hval := congrArg (fun x : B.verts => (x : V)) h
                simpa using hval)⟩
            ⟨(⟨attach j, hB_terminal j⟩ : B.verts), by
              intro h
              exact hattach_ne_apex j (by
                have hval := congrArg (fun x : B.verts => (x : V)) h
                simpa using hval)⟩) :
    NearHajosStrengtheningConclusion G := by
  let apexB : B.verts := ⟨apex, hapexB⟩
  let attachB : Fin 4 -> B.verts := fun i => ⟨attach i, hB_terminal i⟩
  let stemG : forall i : Fin 4, G.Walk apex (attach i) :=
    fun i => (stemB i).map B.hom
  have hterminal_ne :
      forall i : Fin 4, attachB i ≠ apexB := by
    intro i h
    exact hattach_ne_apex i (by
      have hval := congrArg (fun x : B.verts => (x : V)) h
      simpa [attachB, apexB] using hval)
  have hstemG_path : forall i : Fin 4, (stemG i).IsPath := by
    intro i
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective (hstemB_path i)
  have hstemG_support :
      forall i : Fin 4, forall {z : V},
        z ∈ (stemG i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts := by
    intro i z hz
    exact hB_le.left
      (Walk.support_map_subgraph_hom_subset (H := B) (stemB i)
        (by simpa [stemG] using hz))
  have hdisjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stemG i).support ∧ z ≠ apex}
          {z : V | z ∈ (stemG j).support ∧ z ≠ apex} := by
    have hdisjoint_raw :
        forall {i j : Fin 4}, i ≠ j ->
          Disjoint
            {z : V | z ∈ ((stemB i).map B.hom).support ∧ z ≠ (apexB : V)}
            {z : V | z ∈ ((stemB j).map B.hom).support ∧ z ≠ (apexB : V)} :=
      Subgraph.walk_family_mapped_punctured_supports_disjoint_of_delete_root_unreachable
        (G := G) (B := B) (root := apexB) (terminal := attachB)
        (fun i : Fin 4 => stemB i) hterminal_ne hstemB_path
        (by
          intro i j hij
          simpa [apexB, attachB] using hunreachable hij)
    intro i j hij
    simpa [stemG, apexB, attachB] using hdisjoint_raw hij
  exact
    dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_paths_near_hajos
      T htail hapex_mem attach hattach stemG hstemG_path hstemG_support hdisjoint

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_subgraph_tree_paths_through_root_relabel_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (σ : Fin 4 ↪ Fin 4)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (apexB : B.verts)
    (attachB : Fin 4 -> B.verts)
    [DecidableEq B.verts]
    (TB : B.coe.Subgraph)
    [DecidableEq TB.verts]
    (hTB_tree : TB.coe.IsTree)
    (hroot_T : apexB ∈ TB.verts)
    (hterminal_T : forall i : Fin 4, attachB i ∈ TB.verts)
    (hattach :
      forall i : Fin 4,
        (attachB i : V) ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attachB i : V) (htail (σ i)).choose)
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
  let apex : V := apexB
  let attach : Fin 4 -> V := fun i => attachB i
  let stemG : forall i : Fin 4, G.Walk apex (attach i) :=
    fun i => (stemB i).map B.hom
  have hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts := by
    exact hB_le.left apexB.2
  have hstemG_path : forall i : Fin 4, (stemG i).IsPath := by
    intro i
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective (hstemB_path i)
  have hstemG_support :
      forall i : Fin 4, forall {z : V},
        z ∈ (stemG i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts := by
    intro i z hz
    exact hB_le.left
      (Walk.support_map_subgraph_hom_subset (H := B) (stemB i)
        (by simpa [stemG] using hz))
  let rootT : TB.verts := ⟨apexB, hroot_T⟩
  let terminalT : Fin 4 -> TB.verts := fun i => ⟨attachB i, hterminal_T i⟩
  have hpair_path_through_root_T :
      forall {i j : Fin 4}, i ≠ j ->
        Exists fun p : B.coe.Walk (terminalT i : B.verts) (terminalT j : B.verts) =>
          p.toSubgraph ≤ TB ∧ p.IsPath ∧ (rootT : B.verts) ∈ p.support := by
    intro i j hij
    obtain ⟨p, hp_le, hp, hroot⟩ := hpair_path_through_root hij
    exact ⟨p.copy (Subtype.ext rfl) (Subtype.ext rfl), by
      simpa using hp_le, by
      simpa using hp, by
      simpa [rootT] using hroot⟩
  have hdisjointB :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : B.verts | z ∈ (stemB i).support ∧ z ≠ apexB}
          {z : B.verts | z ∈ (stemB j).support ∧ z ≠ apexB} := by
    have hraw :
        forall {i j : Fin 4}, i ≠ j ->
          Disjoint
            {z : B.verts | z ∈ (stemB i).support ∧ z ≠ (rootT : B.verts)}
            {z : B.verts | z ∈ (stemB j).support ∧ z ≠ (rootT : B.verts)} :=
      Subgraph.tree_rooted_paths_punctured_supports_disjoint_of_pair_paths_through_root_allow_eq
        (G := B.coe) (T := TB) hTB_tree
        (root := rootT) (terminal := terminalT)
        stemB hstemB_le hstemB_path hpair_path_through_root_T
    intro i j hij
    simpa [rootT] using hraw hij
  have hdisjointG :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stemG i).support ∧ z ≠ apex}
          {z : V | z ∈ (stemG j).support ∧ z ≠ apex} := by
    intro i j hij
    simpa [stemG, apex] using
      (Subgraph.walk_family_mapped_punctured_supports_disjoint
        (G := G) (B := B) stemB hdisjointB hij)
  exact
    dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_paths_relabel_near_hajos
      T htail σ hapex_mem attach hattach stemG hstemG_path hstemG_support
      hdisjointG

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_subgraph_tree_paths_through_root_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (apexB : B.verts)
    (attachB : Fin 4 -> B.verts)
    [DecidableEq B.verts]
    (TB : B.coe.Subgraph)
    [DecidableEq TB.verts]
    (hTB_tree : TB.coe.IsTree)
    (hroot_T : apexB ∈ TB.verts)
    (hterminal_T : forall i : Fin 4, attachB i ∈ TB.verts)
    (hattach :
      forall i : Fin 4,
        (attachB i : V) ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attachB i : V) (htail i).choose)
    (stemB :
      forall i : Fin 4,
        B.coe.Walk apexB (attachB i))
    (hstemB_path : forall i : Fin 4, (stemB i).IsPath)
    (hstemB_le : forall i : Fin 4, (stemB i).toSubgraph ≤ TB)
    (hpair_path_through_root :
      forall {i j : Fin 4}, i ≠ j ->
        Exists fun p : B.coe.Walk (attachB i) (attachB j) =>
          p.toSubgraph ≤ TB ∧ p.IsPath ∧ apexB ∈ p.support) :
    NearHajosStrengtheningConclusion G :=
  dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_subgraph_tree_paths_through_root_relabel_near_hajos
    T htail (Function.Embedding.refl (Fin 4)) B hB_le apexB attachB TB
    hTB_tree hroot_T hterminal_T hattach stemB hstemB_path hstemB_le
    hpair_path_through_root

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_spanning_tree_all_pairs_through_root_relabel_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (σ : Fin 4 ↪ Fin 4)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (attach : Fin 4 -> V)
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    [DecidableEq B.verts]
    (TB : B.coe.Subgraph)
    [DecidableEq TB.verts]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning)
    (apexB : B.verts)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail (σ i)).choose)
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
  have hroot_T : apexB ∈ TB.verts := hTB_spanning apexB
  have hterminal_T : forall i : Fin 4, attachB i ∈ TB.verts := by
    intro i
    exact hTB_spanning (attachB i)
  obtain ⟨stemB, hstemB_path, hstemB_le⟩ :=
    Subgraph.Connected.exists_coe_rooted_paths_in_spanning_coe_subgraph
      (B := B) (T := TB) hTB_tree.connected hTB_spanning
      apexB.2 attach hB_terminal
  exact
    dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_subgraph_tree_paths_through_root_relabel_near_hajos
      T htail σ B hB_le apexB attachB TB hTB_tree hroot_T hterminal_T
      (by
        intro i
        simpa [attachB] using hattach i)
      (fun i => by
        simpa [attachB] using stemB i)
      (by
        intro i
        simpa [attachB] using hstemB_path i)
      (by
        intro i
        simpa [attachB] using hstemB_le i)
      (by
        intro i j hij
        simpa [attachB] using hpair_path_through_root hij)

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_spanning_tree_all_pairs_through_root_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (attach : Fin 4 -> V)
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    [DecidableEq B.verts]
    (TB : B.coe.Subgraph)
    [DecidableEq TB.verts]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning)
    (apexB : B.verts)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (hpair_path_through_root :
      forall {i j : Fin 4}, i ≠ j ->
        Exists fun p :
          B.coe.Walk
            (⟨attach i, hB_terminal i⟩ : B.verts)
            (⟨attach j, hB_terminal j⟩ : B.verts) =>
          p.toSubgraph ≤ TB ∧ p.IsPath ∧ apexB ∈ p.support) :
    NearHajosStrengtheningConclusion G :=
  dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_spanning_tree_all_pairs_through_root_relabel_near_hajos
    T htail (Function.Embedding.refl (Fin 4)) B hB_le attach hB_terminal TB
    hTB_tree hTB_spanning apexB hattach hpair_path_through_root

theorem dominating_K5_model_tail_all_singleton_first_branch_rooted_attachment_spanning_tree_all_pairs_through_root_witness
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (attach : Fin 4 -> V)
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    [DecidableEq B.verts]
    (TB : B.coe.Subgraph)
    [DecidableEq TB.verts]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning)
    (apexB : B.verts)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (hpair_path_through_root :
      forall {i j : Fin 4}, i ≠ j ->
        Exists fun p :
          B.coe.Walk
            (⟨attach i, hB_terminal i⟩ : B.verts)
            (⟨attach j, hB_terminal j⟩ : B.verts) =>
          p.toSubgraph ≤ TB ∧ p.IsPath ∧ apexB ∈ p.support) :
    Exists fun apex : V =>
      Exists fun attach' : Fin 4 -> V =>
        Exists fun stem : forall i : Fin 4, G.Walk apex (attach' i) =>
          apex ∈ (T.branch (0 : Fin 5)).verts ∧
            (forall i : Fin 4,
              attach' i ∈ (T.branch (0 : Fin 5)).verts ∧
                G.Adj (attach' i) (htail i).choose) ∧
              (forall i : Fin 4, (stem i).IsPath) ∧
                (forall i : Fin 4, forall {z : V},
                  z ∈ (stem i).support ->
                    z ∈ (T.branch (0 : Fin 5)).verts) ∧
                  (forall {i j : Fin 4}, i ≠ j ->
                    Disjoint
                      {z : V | z ∈ (stem i).support ∧ z ≠ apex}
                      {z : V | z ∈ (stem j).support ∧ z ≠ apex}) := by
  classical
  let attachB : Fin 4 -> B.verts := fun i => ⟨attach i, hB_terminal i⟩
  have hroot_T : apexB ∈ TB.verts := hTB_spanning apexB
  have hterminal_T : forall i : Fin 4, attachB i ∈ TB.verts := by
    intro i
    exact hTB_spanning (attachB i)
  obtain ⟨stemB, hstemB_path, hstemB_le⟩ :=
    Subgraph.Connected.exists_coe_rooted_paths_in_spanning_coe_subgraph
      (B := B) (T := TB) hTB_tree.connected hTB_spanning
      apexB.2 attach hB_terminal
  let apex : V := apexB
  let stemG : forall i : Fin 4, G.Walk apex (attach i) :=
    fun i => (stemB i).map B.hom
  have hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts := by
    exact hB_le.left apexB.2
  have hstemG_path : forall i : Fin 4, (stemG i).IsPath := by
    intro i
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective (hstemB_path i)
  have hstemG_support :
      forall i : Fin 4, forall {z : V},
        z ∈ (stemG i).support ->
          z ∈ (T.branch (0 : Fin 5)).verts := by
    intro i z hz
    exact hB_le.left
      (Walk.support_map_subgraph_hom_subset (H := B) (stemB i)
        (by simpa [stemG] using hz))
  let rootT : TB.verts := ⟨apexB, hroot_T⟩
  let terminalT : Fin 4 -> TB.verts := fun i => ⟨attachB i, hterminal_T i⟩
  have hpair_path_through_root_T :
      forall {i j : Fin 4}, i ≠ j ->
        Exists fun p : B.coe.Walk (terminalT i : B.verts) (terminalT j : B.verts) =>
          p.toSubgraph ≤ TB ∧ p.IsPath ∧ (rootT : B.verts) ∈ p.support := by
    intro i j hij
    obtain ⟨p, hp_le, hp, hroot⟩ := hpair_path_through_root hij
    exact ⟨p.copy (Subtype.ext rfl) (Subtype.ext rfl), by
      simpa using hp_le, by
      simpa using hp, by
      simpa [rootT] using hroot⟩
  have hdisjointB :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : B.verts | z ∈ (stemB i).support ∧ z ≠ apexB}
          {z : B.verts | z ∈ (stemB j).support ∧ z ≠ apexB} := by
    have hraw :
        forall {i j : Fin 4}, i ≠ j ->
          Disjoint
            {z : B.verts | z ∈ (stemB i).support ∧ z ≠ (rootT : B.verts)}
            {z : B.verts | z ∈ (stemB j).support ∧ z ≠ (rootT : B.verts)} :=
      Subgraph.tree_rooted_paths_punctured_supports_disjoint_of_pair_paths_through_root_allow_eq
        (G := B.coe) (T := TB) hTB_tree
        (root := rootT) (terminal := terminalT)
        stemB hstemB_le hstemB_path hpair_path_through_root_T
    intro i j hij
    simpa [rootT] using hraw hij
  have hdisjointG :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stemG i).support ∧ z ≠ apex}
          {z : V | z ∈ (stemG j).support ∧ z ≠ apex} := by
    intro i j hij
    simpa [stemG, apex] using
      (Subgraph.walk_family_mapped_punctured_supports_disjoint
        (G := G) (B := B) stemB hdisjointB hij)
  exact ⟨apex, attach, stemG, hapex_mem, hattach, hstemG_path,
    hstemG_support, hdisjointG⟩

end Schematic.Math.GraphTheory
