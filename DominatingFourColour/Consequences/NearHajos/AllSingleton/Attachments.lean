import DominatingFourColour.Consequences.NearHajos.CarrierCases.Connected

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem dominating_K5_model_tail_all_singleton_first_branch_bridge_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {left right : V}
    (hleft_mem : left ∈ (T.branch (0 : Fin 5)).verts)
    (hright_mem : right ∈ (T.branch (0 : Fin 5)).verts)
    (hleft_ne_right : left ≠ right)
    (hleft0 : G.Adj left (htail (0 : Fin 4)).choose)
    (hleft1 : G.Adj left (htail (1 : Fin 4)).choose)
    (hright2 : G.Adj right (htail (2 : Fin 4)).choose)
    (hright3 : G.Adj right (htail (3 : Fin 4)).choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  let D : K4UnsplitSubdivisionData G :=
    dominating_K5_model_tail_all_singleton_k4UnsplitSubdivisionData T htail
  have htail_mem : forall i : Fin 4, (htail i).choose ∈ (T.tailK4.branch i).verts := by
    intro i
    exact (htail i).choose_mem
  let left₀ : (T.branch (0 : Fin 5)).verts := ⟨left, hleft_mem⟩
  let right₀ : (T.branch (0 : Fin 5)).verts := ⟨right, hright_mem⟩
  obtain ⟨p₀, hp₀⟩ := (T.connected (0 : Fin 5)).exists_isPath left₀ right₀
  let p : G.Walk left right := p₀.map (T.branch (0 : Fin 5)).hom
  have hp : p.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hp₀
  have hp_le : p.toSubgraph ≤ T.branch (0 : Fin 5) := by
    simpa [p] using Walk.map_subgraph_toSubgraph_le p₀
  have hp_support_le {x : V} (hx : x ∈ p.support) :
      x ∈ (T.branch (0 : Fin 5)).verts := by
    exact hp_le.left (by rwa [SimpleGraph.Walk.mem_verts_toSubgraph])
  have hnot_tail_of_branch0 {x : V}
      (hx : x ∈ (T.branch (0 : Fin 5)).verts) :
      forall i : Fin 4, x ≠ (htail i).choose := by
    intro i h
    exact (Set.disjoint_left.mp (T.tailK4_branch_disjoint_first i)
      (htail_mem i)) (by simpa [h] using hx)
  refine
    D.bridge_path_k5hat_near_hajos_with_two_incident_unsplit_edges
      hleft_ne_right ?_ ?_ p hp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    change left ≠ (htail i).choose
    exact hnot_tail_of_branch0 hleft_mem i
  · intro i
    change right ≠ (htail i).choose
    exact hnot_tail_of_branch0 hright_mem i
  · intro z hz i
    change z ≠ (htail i).choose
    exact hnot_tail_of_branch0 (hp_support_le hz.1) i
  · intro i j hij z hz
    have hunsplit : D.model.EdgeUnsplit hij := by
      simp [D, dominating_K5_model_tail_all_singleton_k4UnsplitSubdivisionData,
        dominating_K4_model_all_singleton_k4UnsplitSubdivisionData,
        K4UnsplitSubdivisionData.ofCliqueEmbedding,
        StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit]
    exact (Walk.not_mem_internalVertices_of_length_eq_one hunsplit hz).elim
  · intro i j hij z hz
    have hunsplit : D.model.EdgeUnsplit hij := by
      simp [D, dominating_K5_model_tail_all_singleton_k4UnsplitSubdivisionData,
        dominating_K4_model_all_singleton_k4UnsplitSubdivisionData,
        K4UnsplitSubdivisionData.ofCliqueEmbedding,
        StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit]
    exact (Walk.not_mem_internalVertices_of_length_eq_one hunsplit hz).elim
  · intro i j hij z _hz_bridge hz_core
    have hunsplit : D.model.EdgeUnsplit hij := by
      simp [D, dominating_K5_model_tail_all_singleton_k4UnsplitSubdivisionData,
        dominating_K4_model_all_singleton_k4UnsplitSubdivisionData,
        K4UnsplitSubdivisionData.ofCliqueEmbedding,
        StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit]
    exact (Walk.not_mem_internalVertices_of_length_eq_one hunsplit hz_core).elim
  · change G.Adj left (htail (0 : Fin 4)).choose
    exact hleft0
  · change G.Adj left (htail (1 : Fin 4)).choose
    exact hleft1
  · change G.Adj right (htail (2 : Fin 4)).choose
    exact hright2
  · change G.Adj right (htail (3 : Fin 4)).choose
    exact hright3

theorem dominating_K5_model_tail_all_singleton_first_branch_pair_split_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {left right : V}
    (hleft_mem : left ∈ (T.branch (0 : Fin 5)).verts)
    (hright_mem : right ∈ (T.branch (0 : Fin 5)).verts)
    (hleft0 : G.Adj left (htail (0 : Fin 4)).choose)
    (hleft1 : G.Adj left (htail (1 : Fin 4)).choose)
    (hright2 : G.Adj right (htail (2 : Fin 4)).choose)
    (hright3 : G.Adj right (htail (3 : Fin 4)).choose) :
    NearHajosStrengtheningConclusion G := by
  by_cases hsame : left = right
  · subst right
    refine
      dominating_K5_model_tail_all_singleton_common_first_branch_apex_near_hajos
        T htail hleft_mem ?_
    intro i
    fin_cases i
    · exact hleft0
    · exact hleft1
    · exact hright2
    · exact hright3
  · exact
      dominating_K5_model_tail_all_singleton_first_branch_bridge_near_hajos
        T htail hleft_mem hright_mem hsame hleft0 hleft1 hright2 hright3

theorem dominating_K5_model_tail_all_singleton_first_branch_attachments
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i) :
    Exists fun x0 : V =>
      Exists fun x1 : V =>
        Exists fun x2 : V =>
          Exists fun x3 : V =>
            x0 ∈ (T.branch (0 : Fin 5)).verts ∧
              x1 ∈ (T.branch (0 : Fin 5)).verts ∧
                x2 ∈ (T.branch (0 : Fin 5)).verts ∧
                  x3 ∈ (T.branch (0 : Fin 5)).verts ∧
                    G.Adj x0 (htail (0 : Fin 4)).choose ∧
                      G.Adj x1 (htail (1 : Fin 4)).choose ∧
                        G.Adj x2 (htail (2 : Fin 4)).choose ∧
                          G.Adj x3 (htail (3 : Fin 4)).choose := by
  classical
  have htail_mem : forall i : Fin 4, (htail i).choose ∈ (T.tailK4.branch i).verts := by
    intro i
    exact (htail i).choose_mem
  obtain ⟨x0, hx0, hx0_adj⟩ :=
    T.dominates (0 : Fin 5) (1 : Fin 5) (by decide)
      (htail (0 : Fin 4)).choose
      (by simpa [DominatingK5Model.tailK4] using htail_mem 0)
  obtain ⟨x1, hx1, hx1_adj⟩ :=
    T.dominates (0 : Fin 5) (2 : Fin 5) (by decide)
      (htail (1 : Fin 4)).choose
      (by simpa [DominatingK5Model.tailK4] using htail_mem 1)
  obtain ⟨x2, hx2, hx2_adj⟩ :=
    T.dominates (0 : Fin 5) (3 : Fin 5) (by decide)
      (htail (2 : Fin 4)).choose
      (by simpa [DominatingK5Model.tailK4] using htail_mem 2)
  obtain ⟨x3, hx3, hx3_adj⟩ :=
    T.dominates (0 : Fin 5) (4 : Fin 5) (by decide)
      (htail (3 : Fin 4)).choose
      (by simpa [DominatingK5Model.tailK4] using htail_mem 3)
  exact ⟨x0, x1, x2, x3,
    hx0, hx1, hx2, hx3, hx0_adj, hx1_adj, hx2_adj, hx3_adj⟩

theorem dominating_K5_model_tail_all_singleton_first_branch_minimal_attachment_carrier
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i) :
    Exists fun attach : Fin 4 -> V =>
      (forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose) ∧
        Exists fun B : G.Subgraph =>
          B ≤ T.branch (0 : Fin 5) ∧
            B.coe.Connected ∧
              (forall i : Fin 4, attach i ∈ B.verts) ∧
                forall B' : G.Subgraph,
                  B' ≤ T.branch (0 : Fin 5) ->
                    B'.coe.Connected ->
                      (forall i : Fin 4, attach i ∈ B'.verts) ->
                        B'.verts ⊆ B.verts ->
                          B.verts ⊆ B'.verts := by
  classical
  obtain ⟨x0, x1, x2, x3,
    hx0, hx1, hx2, hx3, hx0_adj, hx1_adj, hx2_adj, hx3_adj⟩ :=
    dominating_K5_model_tail_all_singleton_first_branch_attachments T htail
  let attach : Fin 4 -> V
    | 0 => x0
    | 1 => x1
    | 2 => x2
    | 3 => x3
  have hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose := by
    intro i
    fin_cases i <;> simp [attach]
    · exact ⟨hx0, hx0_adj⟩
    · exact ⟨hx1, hx1_adj⟩
    · exact ⟨hx2, hx2_adj⟩
    · exact ⟨hx3, hx3_adj⟩
  obtain ⟨B, hB_le, hB_connected, hB_terminal, hB_minimal⟩ :=
    Subgraph.Connected.exists_minimal_connected_subgraph_containing
      (G := G) (T.connected (0 : Fin 5)) attach (fun i => (hattach i).1)
  exact ⟨attach, hattach, B, hB_le, hB_connected, hB_terminal, hB_minimal⟩

theorem dominating_K5_model_tail_all_singleton_choose_mem
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (i : Fin 4) :
    (htail i).choose ∈ (T.tailK4.branch i).verts := by
  exact (htail i).choose_mem

theorem dominating_K5_model_tail_all_singleton_tail_adj
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {i j : Fin 4}
    (hij : i ≠ j) :
    G.Adj (htail i).choose (htail j).choose :=
  T.tailK4.singletonBranchEmbedding_adj htail hij

theorem dominating_K5_model_tail_all_singleton_tail_adj_reindex
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {t : Nat}
    (σ : Fin t ↪ Fin 4)
    {i j : Fin t}
    (hij : i ≠ j) :
    G.Adj (htail (σ i)).choose (htail (σ j)).choose :=
  dominating_K5_model_tail_all_singleton_tail_adj T htail
    (fun hσ => hij (σ.injective hσ))

theorem dominating_K5_model_tail_all_singleton_not_mem_first_branch
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (i : Fin 4) :
    (htail i).choose ∉ (T.branch (0 : Fin 5)).verts := by
  intro hfirst
  have htail_mem := dominating_K5_model_tail_all_singleton_choose_mem T htail i
  exact (Set.disjoint_left.mp (T.tailK4_branch_disjoint_first i)
    htail_mem) hfirst

end Schematic.Math.GraphTheory
