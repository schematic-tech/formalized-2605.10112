import DominatingFourColour.Consequences.NearHajos.AllSingleton.BridgePaths

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem k4_clique_with_connected_branch_three_one_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (e : Fin 4 ↪ V)
    (h_adj : forall x y : Fin 4, x ≠ y -> G.Adj (e x) (e y))
    (B : G.Subgraph)
    (hB_connected : B.coe.Connected)
    {apex tip : V}
    (hapex_mem : apex ∈ B.verts)
    (htip_mem : tip ∈ B.verts)
    (hcore_not_mem_B : forall i : Fin 4, e i ∉ B.verts)
    (hapex0 : G.Adj apex (e (0 : Fin 4)))
    (hapex1 : G.Adj apex (e (1 : Fin 4)))
    (hapex2 : G.Adj apex (e (2 : Fin 4)))
    (htip3 : G.Adj tip (e (3 : Fin 4))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let D : K4UnsplitSubdivisionData G := K4UnsplitSubdivisionData.ofCliqueEmbedding e h_adj
  have hapex_not_branch : forall i : Fin 4, apex ≠ D.model.branchVertex i := by
    intro i
    change apex ≠ e i
    intro h
    exact hcore_not_mem_B i (by simpa [h] using hapex_mem)
  have hcore_internal_empty :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> False := by
    intro i j hij z hz
    have hunsplit : D.model.EdgeUnsplit hij := by
      simp [D, K4UnsplitSubdivisionData.ofCliqueEmbedding,
        StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit]
    exact (Walk.not_mem_internalVertices_of_length_eq_one hunsplit hz).elim
  obtain ⟨q, hq_path, hq_le⟩ :=
    Subgraph.Connected.exists_path_between hB_connected hapex_mem htip_mem
  have hcore3_not_q_support : e (3 : Fin 4) ∉ q.support := by
    intro hsupport
    exact hcore_not_mem_B 3
      (hq_le.left (by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        exact hsupport))
  let arm : forall i : Fin 4, G.Walk apex (D.model.branchVertex i)
    | 0 => hapex0.toWalk
    | 1 => hapex1.toWalk
    | 2 => hapex2.toWalk
    | 3 => q.concat htip3
  have harm_path : forall i : Fin 4, (arm i).IsPath := by
    intro i
    fin_cases i <;> simp [arm]
    · exact SimpleGraph.Walk.IsPath.of_adj hapex0
    · exact SimpleGraph.Walk.IsPath.of_adj hapex1
    · exact SimpleGraph.Walk.IsPath.of_adj hapex2
    · exact hq_path.concat hcore3_not_q_support htip3
  refine
    D.cone_paths_near_hajos_with_two_incident_unsplit_edges
      apex hapex_not_branch arm harm_path ?_ ?_ ?_ ?_
  · intro i z hz w hzw
    fin_cases i <;> simp [arm] at hz
    · exact (Walk.not_mem_internalVertices_toWalk hapex0 hz).elim
    · exact (Walk.not_mem_internalVertices_toWalk hapex1 hz).elim
    · exact (Walk.not_mem_internalVertices_toWalk hapex2 hz).elim
    · cases w with
      | none =>
          exact hz.2.1 hzw
      | some j =>
          have hz_q : z ∈ q.support :=
            Walk.mem_support_of_mem_internalVertices_concat q htip3 hz
          have hzB : z ∈ B.verts :=
            hq_le.left (by
              rw [SimpleGraph.Walk.mem_verts_toSubgraph]
              exact hz_q)
          exact hcore_not_mem_B j
            (by
              simpa [D, K4UnsplitSubdivisionData.ofCliqueEmbedding,
                StrictSubdivisionModel.ofCompleteGraphEmbedding,
                StrictSubdivisionModel.ofGraphEmbedding, hzw] using hzB)
  · intro i j hij z hz
    exact (hcore_internal_empty hij hz).elim
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    fin_cases i <;> fin_cases j <;> simp [arm] at hzi hzj
    all_goals first
      | exact (Walk.not_mem_internalVertices_toWalk hapex0 hzi).elim
      | exact (Walk.not_mem_internalVertices_toWalk hapex1 hzi).elim
      | exact (Walk.not_mem_internalVertices_toWalk hapex2 hzi).elim
      | exact (Walk.not_mem_internalVertices_toWalk hapex0 hzj).elim
      | exact (Walk.not_mem_internalVertices_toWalk hapex1 hzj).elim
      | exact (Walk.not_mem_internalVertices_toWalk hapex2 hzj).elim
      | exact False.elim (hij rfl)
  · intro i j k hjk
    rw [Set.disjoint_left]
    intro z hzi hcore
    exact (hcore_internal_empty hjk hcore).elim

theorem dominating_K5_model_tail_all_singleton_first_branch_three_one_relabel_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (σ : Fin 4 ↪ Fin 4)
    {apex tip : V}
    (hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts)
    (htip_mem : tip ∈ (T.branch (0 : Fin 5)).verts)
    (hapex0 : G.Adj apex (htail (σ (0 : Fin 4))).choose)
    (hapex1 : G.Adj apex (htail (σ (1 : Fin 4))).choose)
    (hapex2 : G.Adj apex (htail (σ (2 : Fin 4))).choose)
    (htip3 : G.Adj tip (htail (σ (3 : Fin 4))).choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  let e : Fin 4 ↪ V :=
    σ.trans (T.tailK4.singletonBranchEmbedding htail)
  refine
    k4_clique_with_connected_branch_three_one_near_hajos
      e ?_ (T.branch (0 : Fin 5)) (T.connected (0 : Fin 5))
      hapex_mem htip_mem ?_ ?_ ?_ ?_ ?_
  · intro x y hxy
    change G.Adj (htail (σ x)).choose (htail (σ y)).choose
    exact dominating_K5_model_tail_all_singleton_tail_adj_reindex
      T htail σ hxy
  · intro i
    change (htail (σ i)).choose ∉ (T.branch (0 : Fin 5)).verts
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch T htail (σ i)
  · change G.Adj apex (htail (σ (0 : Fin 4))).choose
    simpa [e] using hapex0
  · change G.Adj apex (htail (σ (1 : Fin 4))).choose
    simpa [e] using hapex1
  · change G.Adj apex (htail (σ (2 : Fin 4))).choose
    simpa [e] using hapex2
  · change G.Adj tip (htail (σ (3 : Fin 4))).choose
    simpa [e] using htip3

theorem dominating_K5_model_tail_all_singleton_first_branch_pair_split_relabel_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (σ : Fin 4 ↪ Fin 4)
    {left right : V}
    (hleft_mem : left ∈ (T.branch (0 : Fin 5)).verts)
    (hright_mem : right ∈ (T.branch (0 : Fin 5)).verts)
    (hleft0 : G.Adj left (htail (σ (0 : Fin 4))).choose)
    (hleft1 : G.Adj left (htail (σ (1 : Fin 4))).choose)
    (hright2 : G.Adj right (htail (σ (2 : Fin 4))).choose)
    (hright3 : G.Adj right (htail (σ (3 : Fin 4))).choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  let e : Fin 4 ↪ V :=
    σ.trans (T.tailK4.singletonBranchEmbedding htail)
  refine
    k4_clique_with_connected_bridge_pair_split_near_hajos
      e ?_ (T.branch (0 : Fin 5)) (T.connected (0 : Fin 5))
      hleft_mem hright_mem ?_ ?_ ?_ ?_ ?_
  · intro x y hxy
    change G.Adj (htail (σ x)).choose (htail (σ y)).choose
    exact dominating_K5_model_tail_all_singleton_tail_adj_reindex
      T htail σ hxy
  · intro i
    change (htail (σ i)).choose ∉ (T.branch (0 : Fin 5)).verts
    exact dominating_K5_model_tail_all_singleton_not_mem_first_branch T htail (σ i)
  · change G.Adj left (htail (σ (0 : Fin 4))).choose
    simpa [e] using hleft0
  · change G.Adj left (htail (σ (1 : Fin 4))).choose
    simpa [e] using hleft1
  · change G.Adj right (htail (σ (2 : Fin 4))).choose
    simpa [e] using hright2
  · change G.Adj right (htail (σ (3 : Fin 4))).choose
    simpa [e] using hright3

theorem dominating_K5_model_tail_all_singleton_first_branch_pair_split_02_13_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {left right : V}
    (hleft_mem : left ∈ (T.branch (0 : Fin 5)).verts)
    (hright_mem : right ∈ (T.branch (0 : Fin 5)).verts)
    (hleft0 : G.Adj left (htail (0 : Fin 4)).choose)
    (hleft2 : G.Adj left (htail (2 : Fin 4)).choose)
    (hright1 : G.Adj right (htail (1 : Fin 4)).choose)
    (hright3 : G.Adj right (htail (3 : Fin 4)).choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  let σ : Fin 4 ↪ Fin 4 := {
    toFun
      | 0 => 0
      | 1 => 2
      | 2 => 1
      | 3 => 3
    inj' := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp at h ⊢ }
  exact
    dominating_K5_model_tail_all_singleton_first_branch_pair_split_relabel_near_hajos
      T htail σ hleft_mem hright_mem
      (by simpa [σ] using hleft0)
      (by simpa [σ] using hleft2)
      (by simpa [σ] using hright1)
      (by simpa [σ] using hright3)

theorem dominating_K5_model_tail_all_singleton_first_branch_pair_split_03_12_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {left right : V}
    (hleft_mem : left ∈ (T.branch (0 : Fin 5)).verts)
    (hright_mem : right ∈ (T.branch (0 : Fin 5)).verts)
    (hleft0 : G.Adj left (htail (0 : Fin 4)).choose)
    (hleft3 : G.Adj left (htail (3 : Fin 4)).choose)
    (hright1 : G.Adj right (htail (1 : Fin 4)).choose)
    (hright2 : G.Adj right (htail (2 : Fin 4)).choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  let σ : Fin 4 ↪ Fin 4 := {
    toFun
      | 0 => 0
      | 1 => 3
      | 2 => 1
      | 3 => 2
    inj' := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp at h ⊢ }
  exact
    dominating_K5_model_tail_all_singleton_first_branch_pair_split_relabel_near_hajos
      T htail σ hleft_mem hright_mem
      (by simpa [σ] using hleft0)
      (by simpa [σ] using hleft3)
      (by simpa [σ] using hright1)
      (by simpa [σ] using hright2)

private def fin4PermTip0 : Fin 4 ↪ Fin 4 where
  toFun
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | 3 => 0
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢

private def fin4PermTip1 : Fin 4 ↪ Fin 4 where
  toFun
    | 0 => 0
    | 1 => 2
    | 2 => 3
    | 3 => 1
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢

private def fin4PermTip2 : Fin 4 ↪ Fin 4 where
  toFun
    | 0 => 0
    | 1 => 1
    | 2 => 3
    | 3 => 2
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢

private def fin4PermTip3 : Fin 4 ↪ Fin 4 where
  toFun := id
  inj' := by
    intro i j h
    exact h

theorem dominating_K5_model_tail_all_singleton_first_branch_two_value_attachments_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {u v : V}
    (hu_mem : u ∈ (T.branch (0 : Fin 5)).verts)
    (hv_mem : v ∈ (T.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (hvalues : forall i : Fin 4, attach i = u ∨ attach i = v) :
    NearHajosStrengtheningConclusion G := by
  classical
  have hu_adj : forall i : Fin 4, attach i = u -> G.Adj u (htail i).choose := by
    intro i hi
    simpa [hi] using (hattach i).2
  have hv_adj : forall i : Fin 4, attach i = v -> G.Adj v (htail i).choose := by
    intro i hi
    simpa [hi] using (hattach i).2
  rcases hvalues 0 with h0u | h0v
  · rcases hvalues 1 with h1u | h1v
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact
            dominating_K5_model_tail_all_singleton_common_first_branch_apex_near_hajos
              T htail hu_mem (by
                intro i
                fin_cases i
                · exact hu_adj 0 h0u
                · exact hu_adj 1 h1u
                · exact hu_adj 2 h2u
                · exact hu_adj 3 h3u)
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_three_one_relabel_near_hajos
              T htail fin4PermTip3 hu_mem hv_mem
              (by simpa [fin4PermTip3] using hu_adj 0 h0u)
              (by simpa [fin4PermTip3] using hu_adj 1 h1u)
              (by simpa [fin4PermTip3] using hu_adj 2 h2u)
              (by simpa [fin4PermTip3] using hv_adj 3 h3v)
      · rcases hvalues 3 with h3u | h3v
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_three_one_relabel_near_hajos
              T htail fin4PermTip2 hu_mem hv_mem
              (by simpa [fin4PermTip2] using hu_adj 0 h0u)
              (by simpa [fin4PermTip2] using hu_adj 1 h1u)
              (by simpa [fin4PermTip2] using hu_adj 3 h3u)
              (by simpa [fin4PermTip2] using hv_adj 2 h2v)
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_pair_split_near_hajos
              T htail hu_mem hv_mem
              (hu_adj 0 h0u) (hu_adj 1 h1u)
              (hv_adj 2 h2v) (hv_adj 3 h3v)
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_three_one_relabel_near_hajos
              T htail fin4PermTip1 hu_mem hv_mem
              (by simpa [fin4PermTip1] using hu_adj 0 h0u)
              (by simpa [fin4PermTip1] using hu_adj 2 h2u)
              (by simpa [fin4PermTip1] using hu_adj 3 h3u)
              (by simpa [fin4PermTip1] using hv_adj 1 h1v)
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_pair_split_02_13_near_hajos
              T htail hu_mem hv_mem
              (hu_adj 0 h0u) (hu_adj 2 h2u)
              (hv_adj 1 h1v) (hv_adj 3 h3v)
      · rcases hvalues 3 with h3u | h3v
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_pair_split_03_12_near_hajos
              T htail hu_mem hv_mem
              (hu_adj 0 h0u) (hu_adj 3 h3u)
              (hv_adj 1 h1v) (hv_adj 2 h2v)
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_three_one_relabel_near_hajos
              T htail fin4PermTip0 hv_mem hu_mem
              (by simpa [fin4PermTip0] using hv_adj 1 h1v)
              (by simpa [fin4PermTip0] using hv_adj 2 h2v)
              (by simpa [fin4PermTip0] using hv_adj 3 h3v)
              (by simpa [fin4PermTip0] using hu_adj 0 h0u)
  · rcases hvalues 1 with h1u | h1v
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_three_one_relabel_near_hajos
              T htail fin4PermTip0 hu_mem hv_mem
              (by simpa [fin4PermTip0] using hu_adj 1 h1u)
              (by simpa [fin4PermTip0] using hu_adj 2 h2u)
              (by simpa [fin4PermTip0] using hu_adj 3 h3u)
              (by simpa [fin4PermTip0] using hv_adj 0 h0v)
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_pair_split_03_12_near_hajos
              T htail hv_mem hu_mem
              (hv_adj 0 h0v) (hv_adj 3 h3v)
              (hu_adj 1 h1u) (hu_adj 2 h2u)
      · rcases hvalues 3 with h3u | h3v
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_pair_split_02_13_near_hajos
              T htail hv_mem hu_mem
              (hv_adj 0 h0v) (hv_adj 2 h2v)
              (hu_adj 1 h1u) (hu_adj 3 h3u)
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_three_one_relabel_near_hajos
              T htail fin4PermTip1 hv_mem hu_mem
              (by simpa [fin4PermTip1] using hv_adj 0 h0v)
              (by simpa [fin4PermTip1] using hv_adj 2 h2v)
              (by simpa [fin4PermTip1] using hv_adj 3 h3v)
              (by simpa [fin4PermTip1] using hu_adj 1 h1u)
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_pair_split_near_hajos
              T htail hv_mem hu_mem
              (hv_adj 0 h0v) (hv_adj 1 h1v)
              (hu_adj 2 h2u) (hu_adj 3 h3u)
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_three_one_relabel_near_hajos
              T htail fin4PermTip2 hv_mem hu_mem
              (by simpa [fin4PermTip2] using hv_adj 0 h0v)
              (by simpa [fin4PermTip2] using hv_adj 1 h1v)
              (by simpa [fin4PermTip2] using hv_adj 3 h3v)
              (by simpa [fin4PermTip2] using hu_adj 2 h2u)
      · rcases hvalues 3 with h3u | h3v
        · exact
            dominating_K5_model_tail_all_singleton_first_branch_three_one_relabel_near_hajos
              T htail fin4PermTip3 hv_mem hu_mem
              (by simpa [fin4PermTip3] using hv_adj 0 h0v)
              (by simpa [fin4PermTip3] using hv_adj 1 h1v)
              (by simpa [fin4PermTip3] using hv_adj 2 h2v)
              (by simpa [fin4PermTip3] using hu_adj 3 h3u)
        · exact
            dominating_K5_model_tail_all_singleton_common_first_branch_apex_near_hajos
              T htail hv_mem (by
                intro i
                fin_cases i
                · exact hv_adj 0 h0v
                · exact hv_adj 1 h1v
                · exact hv_adj 2 h2v
                · exact hv_adj 3 h3v)

end Schematic.Math.GraphTheory
