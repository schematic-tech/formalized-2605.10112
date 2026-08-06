import DominatingFourColour.Consequences.NearHajos.AllSingleton.IncidentEdges

/-! Model-level reductions used by the Near-Hajos carrier argument. -/

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

private structure BranchExtensionPathData
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G) (i : Fin 5) (a c : V) where
  path : G.Walk a c
  path_isPath : path.IsPath
  internal_mem_branch :
    forall {x : V}, x ∈ Walk.InternalVertices path -> x ∈ (T.branch i).verts

/-- A path inside one branch, extended by one edge into a disjoint branch.
The package records exactly the path and internal-vertex facts used by the
model reductions below. -/
private noncomputable def DominatingK5Model.branchExtensionPathData
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    {i j : Fin 5} (hij : i ≠ j)
    {a b c : V}
    (ha : a ∈ (T.branch i).verts)
    (hb : b ∈ (T.branch i).verts)
    (hc : c ∈ (T.branch j).verts)
    (hbc : G.Adj b c) :
    BranchExtensionPathData T i a c := by
  classical
  let aᵢ : (T.branch i).verts := ⟨a, ha⟩
  let bᵢ : (T.branch i).verts := ⟨b, hb⟩
  let q := Classical.choose ((T.connected i).exists_isPath aᵢ bᵢ)
  have hq : q.IsPath :=
    Classical.choose_spec ((T.connected i).exists_isPath aᵢ bᵢ)
  let mid : G.Walk a b := q.map (T.branch i).hom
  have hmid : mid.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hq
  have hmid_le : mid.toSubgraph ≤ T.branch i := by
    simpa [mid] using Walk.map_subgraph_toSubgraph_le q
  have hmid_support {x : V} (hx : x ∈ mid.support) :
      x ∈ (T.branch i).verts := by
    exact hmid_le.left (by rwa [SimpleGraph.Walk.mem_verts_toSubgraph])
  have hc_not_mid : c ∉ mid.support := by
    intro hc_mid
    exact Set.disjoint_left.mp (T.vertex_disjoint i j hij)
      (hmid_support hc_mid) hc
  let p : G.Walk a c := mid.concat hbc
  refine {
    path := p
    path_isPath := hmid.concat hc_not_mid hbc
    internal_mem_branch := ?_
  }
  intro x hx
  exact hmid_support
    (Walk.mem_support_of_mem_internalVertices_concat mid hbc hx)

theorem dominating_K5_model_all_singleton_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (hsingle : forall i : Fin 5, BranchIsSingleton T i) :
    NearHajosStrengtheningConclusion G :=
  clique_near_hajos_with_two_incident_unsplit_edges
    (T.singletonBranchEmbedding hsingle)
    (fun _ _ hne => T.singletonBranchEmbedding_adj hsingle hne)

theorem dominating_K5_model_middle_common_attachment_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (h0 : BranchIsSingleton T (0 : Fin 5))
    (h1 : BranchIsSingleton T (1 : Fin 5))
    (h3 : BranchIsSingleton T (3 : Fin 5))
    (h4 : BranchIsSingleton T (4 : Fin 5))
    {z : V}
    (hz : z ∈ (T.branch (2 : Fin 5)).verts)
    (hz0 : G.Adj z h0.choose)
    (hz1 : G.Adj z h1.choose)
    (hz3 : G.Adj z h3.choose)
    (hz4 : G.Adj z h4.choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  let eFun : Fin 5 -> V
    | 0 => h0.choose
    | 1 => h1.choose
    | 2 => z
    | 3 => h3.choose
    | 4 => h4.choose
  have he_mem : forall i : Fin 5, eFun i ∈ (T.branch i).verts := by
    intro i
    fin_cases i
    · change h0.choose ∈ (T.branch (0 : Fin 5)).verts
      exact h0.choose_mem
    · change h1.choose ∈ (T.branch (1 : Fin 5)).verts
      exact h1.choose_mem
    · simpa [eFun] using hz
    · change h3.choose ∈ (T.branch (3 : Fin 5)).verts
      exact h3.choose_mem
    · change h4.choose ∈ (T.branch (4 : Fin 5)).verts
      exact h4.choose_mem
  let e : Fin 5 ↪ V := T.branchVertexEmbedding eFun he_mem
  have h01 : G.Adj (e (0 : Fin 5)) (e (1 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) (he_mem 1)
  have h03 : G.Adj (e (0 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) (he_mem 3)
  have h04 : G.Adj (e (0 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) (he_mem 4)
  have h13 : G.Adj (e (1 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using
      h1.choose_adj_of_lt (by decide) (he_mem 3)
  have h14 : G.Adj (e (1 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h1.choose_adj_of_lt (by decide) (he_mem 4)
  have h34 : G.Adj (e (3 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h3.choose_adj_of_lt (by decide) (he_mem 4)
  refine clique_near_hajos_with_two_incident_unsplit_edges e ?_
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp at hxy
  · exact h01
  · simpa [e, eFun] using hz0.symm
  · exact h03
  · exact h04
  · exact h01.symm
  · simpa [e, eFun] using hz1.symm
  · exact h13
  · exact h14
  · simpa [e, eFun] using hz0
  · simpa [e, eFun] using hz1
  · simpa [e, eFun] using hz3
  · simpa [e, eFun] using hz4
  · exact h03.symm
  · exact h13.symm
  · simpa [e, eFun] using hz3.symm
  · exact h34
  · exact h04.symm
  · exact h14.symm
  · simpa [e, eFun] using hz4.symm
  · exact h34.symm

theorem dominating_K5_model_middle_common_tail_attachment_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (h0 : BranchIsSingleton T (0 : Fin 5))
    (h1 : BranchIsSingleton T (1 : Fin 5))
    (h3 : BranchIsSingleton T (3 : Fin 5))
    (h4 : BranchIsSingleton T (4 : Fin 5))
    {z : V}
    (hz : z ∈ (T.branch (2 : Fin 5)).verts)
    (hz3 : G.Adj z h3.choose)
    (hz4 : G.Adj z h4.choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  have hz0 : G.Adj z h0.choose := by
    exact (h0.choose_adj_of_lt (by decide) hz).symm
  have hz1 : G.Adj z h1.choose := by
    exact (h1.choose_adj_of_lt (by decide) hz).symm
  exact
    dominating_K5_model_middle_common_attachment_near_hajos_with_two_incident_unsplit_edges
      T h0 h1 h3 h4 hz hz0 hz1 hz3 hz4

theorem dominating_K5_model_first_second_fourth_fifth_singleton_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (h0 : BranchIsSingleton T (0 : Fin 5))
    (h1 : BranchIsSingleton T (1 : Fin 5))
    (h3 : BranchIsSingleton T (3 : Fin 5))
    (h4 : BranchIsSingleton T (4 : Fin 5)) :
    NearHajosStrengtheningConclusion G := by
  classical
  have h0_mem : h0.choose ∈ (T.branch (0 : Fin 5)).verts := by
    exact h0.choose_mem
  have h1_mem : h1.choose ∈ (T.branch (1 : Fin 5)).verts := by
    exact h1.choose_mem
  have h3_mem : h3.choose ∈ (T.branch (3 : Fin 5)).verts := by
    exact h3.choose_mem
  have h4_mem : h4.choose ∈ (T.branch (4 : Fin 5)).verts := by
    exact h4.choose_mem
  obtain ⟨a, ha, ha3⟩ :=
    T.dominates (2 : Fin 5) (3 : Fin 5) (by decide) h3.choose h3_mem
  obtain ⟨b, hb, hb4⟩ :=
    T.dominates (2 : Fin 5) (4 : Fin 5) (by decide) h4.choose h4_mem
  let pData := T.branchExtensionPathData
    (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
    ha hb h4_mem hb4
  let p : G.Walk a h4.choose := pData.path
  have hp : p.IsPath := pData.path_isPath
  let eFun : Fin 5 -> V
    | 0 => h0.choose
    | 1 => h1.choose
    | 2 => a
    | 3 => h3.choose
    | 4 => h4.choose
  have he_mem : forall i : Fin 5, eFun i ∈ (T.branch i).verts := by
    intro i
    fin_cases i
    · simpa [eFun] using h0_mem
    · simpa [eFun] using h1_mem
    · simpa [eFun] using ha
    · simpa [eFun] using h3_mem
    · simpa [eFun] using h4_mem
  let e : Fin 5 ↪ V := T.branchVertexEmbedding eFun he_mem
  have h01 : G.Adj (e (0 : Fin 5)) (e (1 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) h1_mem
  have h02 : G.Adj (e (0 : Fin 5)) (e (2 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) ha
  have h03 : G.Adj (e (0 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) h3_mem
  have h04 : G.Adj (e (0 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) h4_mem
  have h12 : G.Adj (e (1 : Fin 5)) (e (2 : Fin 5)) := by
    simpa [e, eFun] using
      h1.choose_adj_of_lt (by decide) ha
  have h13 : G.Adj (e (1 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using
      h1.choose_adj_of_lt (by decide) h3_mem
  have h14 : G.Adj (e (1 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h1.choose_adj_of_lt (by decide) h4_mem
  have h23 : G.Adj (e (2 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using ha3
  have h34 : G.Adj (e (3 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h3.choose_adj_of_lt (by decide) h4_mem
  refine
    k5_one_edge_subdivided_near_hajos_with_two_incident_unsplit_edges
      e ?_ p hp ?_
  · intro x y hxy hnot
    fin_cases x <;> fin_cases y <;> simp at hxy
    · exact h01
    · exact h02
    · exact h03
    · exact h04
    · exact h01.symm
    · exact h12
    · exact h13
    · exact h14
    · exact h02.symm
    · exact h12.symm
    · exact h23
    · exact False.elim (hnot (Or.inl ⟨rfl, rfl⟩))
    · exact h03.symm
    · exact h13.symm
    · exact h23.symm
    · exact h34
    · exact h04.symm
    · exact h14.symm
    · exact False.elim (hnot (Or.inr ⟨rfl, rfl⟩))
    · exact h34.symm
  · intro z hz i
    have hz_branch2 : z ∈ (T.branch (2 : Fin 5)).verts := by
      exact pData.internal_mem_branch (by simpa [p] using hz)
    rcases hz with ⟨_hz_support, hz_ne_a, hz_ne_h4⟩
    fin_cases i
    · intro hz0
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (0 : Fin 5) (by decide))
        hz_branch2) (by simpa [e, eFun, hz0] using h0_mem)
    · intro hz1
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (1 : Fin 5) (by decide))
        hz_branch2) (by simpa [e, eFun, hz1] using h1_mem)
    · simpa [e, eFun] using hz_ne_a
    · intro hz3
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (3 : Fin 5) (by decide))
        hz_branch2) (by simpa [e, eFun, hz3] using h3_mem)
    · simpa [e, eFun] using hz_ne_h4

theorem dominating_K5_model_first_fourth_fifth_singleton_second_common_tail_attachment_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (h0 : BranchIsSingleton T (0 : Fin 5))
    (h3 : BranchIsSingleton T (3 : Fin 5))
    (h4 : BranchIsSingleton T (4 : Fin 5))
    {y z : V}
    (hy : y ∈ (T.branch (1 : Fin 5)).verts)
    (hz : z ∈ (T.branch (2 : Fin 5)).verts)
    (hyz : G.Adj y z)
    (hy3 : G.Adj y h3.choose)
    (hy4 : G.Adj y h4.choose)
    (hz3 : G.Adj z h3.choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  have h0_mem : h0.choose ∈ (T.branch (0 : Fin 5)).verts := by
    exact h0.choose_mem
  have h3_mem : h3.choose ∈ (T.branch (3 : Fin 5)).verts := by
    exact h3.choose_mem
  have h4_mem : h4.choose ∈ (T.branch (4 : Fin 5)).verts := by
    exact h4.choose_mem
  obtain ⟨b, hb, hb4⟩ :=
    T.dominates (2 : Fin 5) (4 : Fin 5) (by decide) h4.choose h4_mem
  let pData := T.branchExtensionPathData
    (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
    hz hb h4_mem hb4
  let p : G.Walk z h4.choose := pData.path
  have hp : p.IsPath := pData.path_isPath
  let eFun : Fin 5 -> V
    | 0 => h0.choose
    | 1 => y
    | 2 => z
    | 3 => h3.choose
    | 4 => h4.choose
  have he_mem : forall i : Fin 5, eFun i ∈ (T.branch i).verts := by
    intro i
    fin_cases i
    · simpa [eFun] using h0_mem
    · simpa [eFun] using hy
    · simpa [eFun] using hz
    · simpa [eFun] using h3_mem
    · simpa [eFun] using h4_mem
  let e : Fin 5 ↪ V := T.branchVertexEmbedding eFun he_mem
  have h01 : G.Adj (e (0 : Fin 5)) (e (1 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) hy
  have h02 : G.Adj (e (0 : Fin 5)) (e (2 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) hz
  have h03 : G.Adj (e (0 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) h3_mem
  have h04 : G.Adj (e (0 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) h4_mem
  have h12 : G.Adj (e (1 : Fin 5)) (e (2 : Fin 5)) := by
    simpa [e, eFun] using hyz
  have h13 : G.Adj (e (1 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using hy3
  have h14 : G.Adj (e (1 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using hy4
  have h23 : G.Adj (e (2 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using hz3
  have h34 : G.Adj (e (3 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h3.choose_adj_of_lt (by decide) h4_mem
  refine
    k5_one_edge_subdivided_near_hajos_with_two_incident_unsplit_edges
      e ?_ p hp ?_
  · intro x x' hxx' hnot
    fin_cases x <;> fin_cases x' <;> simp at hxx'
    · exact h01
    · exact h02
    · exact h03
    · exact h04
    · exact h01.symm
    · exact h12
    · exact h13
    · exact h14
    · exact h02.symm
    · exact h12.symm
    · exact h23
    · exact False.elim (hnot (Or.inl ⟨rfl, rfl⟩))
    · exact h03.symm
    · exact h13.symm
    · exact h23.symm
    · exact h34
    · exact h04.symm
    · exact h14.symm
    · exact False.elim (hnot (Or.inr ⟨rfl, rfl⟩))
    · exact h34.symm
  · intro x hx i
    have hx_branch2 : x ∈ (T.branch (2 : Fin 5)).verts := by
      exact pData.internal_mem_branch (by simpa [p] using hx)
    rcases hx with ⟨_hx_support, hx_ne_z, hx_ne_h4⟩
    fin_cases i
    · intro hx0
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (0 : Fin 5) (by decide))
        hx_branch2) (by simpa [e, eFun, hx0] using h0_mem)
    · intro hx1
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (1 : Fin 5) (by decide))
        hx_branch2) (by simpa [e, eFun, hx1] using hy)
    · simpa [e, eFun] using hx_ne_z
    · intro hx3
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (3 : Fin 5) (by decide))
        hx_branch2) (by simpa [e, eFun, hx3] using h3_mem)
    · simpa [e, eFun] using hx_ne_h4

theorem dominating_K5_model_first_fourth_fifth_singleton_second_common_other_tail_attachment_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (h0 : BranchIsSingleton T (0 : Fin 5))
    (h3 : BranchIsSingleton T (3 : Fin 5))
    (h4 : BranchIsSingleton T (4 : Fin 5))
    {y z : V}
    (hy : y ∈ (T.branch (1 : Fin 5)).verts)
    (hz : z ∈ (T.branch (2 : Fin 5)).verts)
    (hyz : G.Adj y z)
    (hy3 : G.Adj y h3.choose)
    (hy4 : G.Adj y h4.choose)
    (hz4 : G.Adj z h4.choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  have h0_mem : h0.choose ∈ (T.branch (0 : Fin 5)).verts := by
    exact h0.choose_mem
  have h3_mem : h3.choose ∈ (T.branch (3 : Fin 5)).verts := by
    exact h3.choose_mem
  have h4_mem : h4.choose ∈ (T.branch (4 : Fin 5)).verts := by
    exact h4.choose_mem
  obtain ⟨b, hb, hb3⟩ :=
    T.dominates (2 : Fin 5) (3 : Fin 5) (by decide) h3.choose h3_mem
  let pData := T.branchExtensionPathData
    (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
    hz hb h3_mem hb3
  let p : G.Walk z h3.choose := pData.path
  have hp : p.IsPath := pData.path_isPath
  let eFun : Fin 5 -> V
    | 0 => h0.choose
    | 1 => y
    | 2 => z
    | 3 => h3.choose
    | 4 => h4.choose
  have he_mem : forall i : Fin 5, eFun i ∈ (T.branch i).verts := by
    intro i
    fin_cases i
    · simpa [eFun] using h0_mem
    · simpa [eFun] using hy
    · simpa [eFun] using hz
    · simpa [eFun] using h3_mem
    · simpa [eFun] using h4_mem
  let e : Fin 5 ↪ V := T.branchVertexEmbedding eFun he_mem
  have h01 : G.Adj (e (0 : Fin 5)) (e (1 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) hy
  have h02 : G.Adj (e (0 : Fin 5)) (e (2 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) hz
  have h03 : G.Adj (e (0 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) h3_mem
  have h04 : G.Adj (e (0 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h0.choose_adj_of_lt (by decide) h4_mem
  have h12 : G.Adj (e (1 : Fin 5)) (e (2 : Fin 5)) := by
    simpa [e, eFun] using hyz
  have h13 : G.Adj (e (1 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using hy3
  have h14 : G.Adj (e (1 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using hy4
  have h24 : G.Adj (e (2 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using hz4
  have h34 : G.Adj (e (3 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h3.choose_adj_of_lt (by decide) h4_mem
  refine
    k5_one_edge_23_subdivided_near_hajos_with_two_incident_unsplit_edges
      e ?_ p hp ?_
  · intro x x' hxx' hnot
    fin_cases x <;> fin_cases x' <;> simp at hxx'
    · exact h01
    · exact h02
    · exact h03
    · exact h04
    · exact h01.symm
    · exact h12
    · exact h13
    · exact h14
    · exact h02.symm
    · exact h12.symm
    · exact False.elim (hnot (Or.inl ⟨rfl, rfl⟩))
    · exact h24
    · exact h03.symm
    · exact h13.symm
    · exact False.elim (hnot (Or.inr ⟨rfl, rfl⟩))
    · exact h34
    · exact h04.symm
    · exact h14.symm
    · exact h24.symm
    · exact h34.symm
  · intro x hx i
    have hx_branch2 : x ∈ (T.branch (2 : Fin 5)).verts := by
      exact pData.internal_mem_branch (by simpa [p] using hx)
    rcases hx with ⟨_hx_support, hx_ne_z, hx_ne_h3⟩
    fin_cases i
    · intro hx0
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (0 : Fin 5) (by decide))
        hx_branch2) (by simpa [e, eFun, hx0] using h0_mem)
    · intro hx1
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (1 : Fin 5) (by decide))
        hx_branch2) (by simpa [e, eFun, hx1] using hy)
    · simpa [e, eFun] using hx_ne_z
    · simpa [e, eFun] using hx_ne_h3
    · intro hx4
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (4 : Fin 5) (by decide))
        hx_branch2) (by simpa [e, eFun, hx4] using h4_mem)

theorem dominating_K5_model_second_fourth_fifth_singleton_first_common_tail_attachment_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (h1 : BranchIsSingleton T (1 : Fin 5))
    (h3 : BranchIsSingleton T (3 : Fin 5))
    (h4 : BranchIsSingleton T (4 : Fin 5))
    {x z : V}
    (hx : x ∈ (T.branch (0 : Fin 5)).verts)
    (hz : z ∈ (T.branch (2 : Fin 5)).verts)
    (hx1 : G.Adj x h1.choose)
    (hxz : G.Adj x z)
    (hx3 : G.Adj x h3.choose)
    (hx4 : G.Adj x h4.choose)
    (hz3 : G.Adj z h3.choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  have h1_mem : h1.choose ∈ (T.branch (1 : Fin 5)).verts := by
    exact h1.choose_mem
  have h3_mem : h3.choose ∈ (T.branch (3 : Fin 5)).verts := by
    exact h3.choose_mem
  have h4_mem : h4.choose ∈ (T.branch (4 : Fin 5)).verts := by
    exact h4.choose_mem
  obtain ⟨b, hb, hb4⟩ :=
    T.dominates (2 : Fin 5) (4 : Fin 5) (by decide) h4.choose h4_mem
  let pData := T.branchExtensionPathData
    (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
    hz hb h4_mem hb4
  let p : G.Walk z h4.choose := pData.path
  have hp : p.IsPath := pData.path_isPath
  let eFun : Fin 5 -> V
    | 0 => x
    | 1 => h1.choose
    | 2 => z
    | 3 => h3.choose
    | 4 => h4.choose
  have he_mem : forall i : Fin 5, eFun i ∈ (T.branch i).verts := by
    intro i
    fin_cases i
    · simpa [eFun] using hx
    · simpa [eFun] using h1_mem
    · simpa [eFun] using hz
    · simpa [eFun] using h3_mem
    · simpa [eFun] using h4_mem
  let e : Fin 5 ↪ V := T.branchVertexEmbedding eFun he_mem
  have h01 : G.Adj (e (0 : Fin 5)) (e (1 : Fin 5)) := by
    simpa [e, eFun] using hx1
  have h02 : G.Adj (e (0 : Fin 5)) (e (2 : Fin 5)) := by
    simpa [e, eFun] using hxz
  have h03 : G.Adj (e (0 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using hx3
  have h04 : G.Adj (e (0 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using hx4
  have h12 : G.Adj (e (1 : Fin 5)) (e (2 : Fin 5)) := by
    simpa [e, eFun] using
      h1.choose_adj_of_lt (by decide) hz
  have h13 : G.Adj (e (1 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using
      h1.choose_adj_of_lt (by decide) h3_mem
  have h14 : G.Adj (e (1 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h1.choose_adj_of_lt (by decide) h4_mem
  have h23 : G.Adj (e (2 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using hz3
  have h34 : G.Adj (e (3 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h3.choose_adj_of_lt (by decide) h4_mem
  refine
    k5_one_edge_subdivided_near_hajos_with_two_incident_unsplit_edges
      e ?_ p hp ?_
  · intro a b' hab hnot
    fin_cases a <;> fin_cases b' <;> simp at hab
    · exact h01
    · exact h02
    · exact h03
    · exact h04
    · exact h01.symm
    · exact h12
    · exact h13
    · exact h14
    · exact h02.symm
    · exact h12.symm
    · exact h23
    · exact False.elim (hnot (Or.inl ⟨rfl, rfl⟩))
    · exact h03.symm
    · exact h13.symm
    · exact h23.symm
    · exact h34
    · exact h04.symm
    · exact h14.symm
    · exact False.elim (hnot (Or.inr ⟨rfl, rfl⟩))
    · exact h34.symm
  · intro a ha i
    have ha_branch2 : a ∈ (T.branch (2 : Fin 5)).verts := by
      exact pData.internal_mem_branch (by simpa [p] using ha)
    rcases ha with ⟨_ha_support, ha_ne_z, ha_ne_h4⟩
    fin_cases i
    · intro ha0
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (0 : Fin 5) (by decide))
        ha_branch2) (by simpa [e, eFun, ha0] using hx)
    · intro ha1
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (1 : Fin 5) (by decide))
        ha_branch2) (by simpa [e, eFun, ha1] using h1_mem)
    · simpa [e, eFun] using ha_ne_z
    · intro ha3
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (3 : Fin 5) (by decide))
        ha_branch2) (by simpa [e, eFun, ha3] using h3_mem)
    · simpa [e, eFun] using ha_ne_h4

theorem dominating_K5_model_second_fourth_fifth_singleton_first_common_other_tail_attachment_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (h1 : BranchIsSingleton T (1 : Fin 5))
    (h3 : BranchIsSingleton T (3 : Fin 5))
    (h4 : BranchIsSingleton T (4 : Fin 5))
    {x z : V}
    (hx : x ∈ (T.branch (0 : Fin 5)).verts)
    (hz : z ∈ (T.branch (2 : Fin 5)).verts)
    (hx1 : G.Adj x h1.choose)
    (hxz : G.Adj x z)
    (hx3 : G.Adj x h3.choose)
    (hx4 : G.Adj x h4.choose)
    (hz4 : G.Adj z h4.choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  have h1_mem : h1.choose ∈ (T.branch (1 : Fin 5)).verts := by
    exact h1.choose_mem
  have h3_mem : h3.choose ∈ (T.branch (3 : Fin 5)).verts := by
    exact h3.choose_mem
  have h4_mem : h4.choose ∈ (T.branch (4 : Fin 5)).verts := by
    exact h4.choose_mem
  obtain ⟨b, hb, hb3⟩ :=
    T.dominates (2 : Fin 5) (3 : Fin 5) (by decide) h3.choose h3_mem
  let pData := T.branchExtensionPathData
    (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
    hz hb h3_mem hb3
  let p : G.Walk z h3.choose := pData.path
  have hp : p.IsPath := pData.path_isPath
  let eFun : Fin 5 -> V
    | 0 => x
    | 1 => h1.choose
    | 2 => z
    | 3 => h3.choose
    | 4 => h4.choose
  have he_mem : forall i : Fin 5, eFun i ∈ (T.branch i).verts := by
    intro i
    fin_cases i
    · simpa [eFun] using hx
    · simpa [eFun] using h1_mem
    · simpa [eFun] using hz
    · simpa [eFun] using h3_mem
    · simpa [eFun] using h4_mem
  let e : Fin 5 ↪ V := T.branchVertexEmbedding eFun he_mem
  have h01 : G.Adj (e (0 : Fin 5)) (e (1 : Fin 5)) := by
    simpa [e, eFun] using hx1
  have h02 : G.Adj (e (0 : Fin 5)) (e (2 : Fin 5)) := by
    simpa [e, eFun] using hxz
  have h03 : G.Adj (e (0 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using hx3
  have h04 : G.Adj (e (0 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using hx4
  have h12 : G.Adj (e (1 : Fin 5)) (e (2 : Fin 5)) := by
    simpa [e, eFun] using
      h1.choose_adj_of_lt (by decide) hz
  have h13 : G.Adj (e (1 : Fin 5)) (e (3 : Fin 5)) := by
    simpa [e, eFun] using
      h1.choose_adj_of_lt (by decide) h3_mem
  have h14 : G.Adj (e (1 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h1.choose_adj_of_lt (by decide) h4_mem
  have h24 : G.Adj (e (2 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using hz4
  have h34 : G.Adj (e (3 : Fin 5)) (e (4 : Fin 5)) := by
    simpa [e, eFun] using
      h3.choose_adj_of_lt (by decide) h4_mem
  refine
    k5_one_edge_23_subdivided_near_hajos_with_two_incident_unsplit_edges
      e ?_ p hp ?_
  · intro a b' hab hnot
    fin_cases a <;> fin_cases b' <;> simp at hab
    · exact h01
    · exact h02
    · exact h03
    · exact h04
    · exact h01.symm
    · exact h12
    · exact h13
    · exact h14
    · exact h02.symm
    · exact h12.symm
    · exact False.elim (hnot (Or.inl ⟨rfl, rfl⟩))
    · exact h24
    · exact h03.symm
    · exact h13.symm
    · exact False.elim (hnot (Or.inr ⟨rfl, rfl⟩))
    · exact h34
    · exact h04.symm
    · exact h14.symm
    · exact h24.symm
    · exact h34.symm
  · intro a ha i
    have ha_branch2 : a ∈ (T.branch (2 : Fin 5)).verts := by
      exact pData.internal_mem_branch (by simpa [p] using ha)
    rcases ha with ⟨_ha_support, ha_ne_z, ha_ne_h3⟩
    fin_cases i
    · intro ha0
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (0 : Fin 5) (by decide))
        ha_branch2) (by simpa [e, eFun, ha0] using hx)
    · intro ha1
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (1 : Fin 5) (by decide))
        ha_branch2) (by simpa [e, eFun, ha1] using h1_mem)
    · simpa [e, eFun] using ha_ne_z
    · simpa [e, eFun] using ha_ne_h3
    · intro ha4
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (2 : Fin 5) (4 : Fin 5) (by decide))
        ha_branch2) (by simpa [e, eFun, ha4] using h4_mem)

theorem k5hat_embedding_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (e : Fin 6 ↪ V)
    (h_adj : forall {x y : Fin 6}, K5Hat.Adj x y -> G.Adj (e x) (e y)) :
    NearHajosStrengtheningConclusion G := by
  let M : StrictSubdivisionModel K5Hat G :=
    StrictSubdivisionModel.ofGraphEmbedding e h_adj
  exact Or.inr ⟨{
    model := M
    edge₁_unsplit :=
      StrictSubdivisionModel.ofGraphEmbedding_edgeUnsplit e h_adj
        (show K5Hat.Adj (2 : Fin 6) (3 : Fin 6) from by simp [K5Hat])
    edge₂_unsplit :=
      StrictSubdivisionModel.ofGraphEmbedding_edgeUnsplit e h_adj
        (show K5Hat.Adj (2 : Fin 6) (4 : Fin 6) from by simp [K5Hat])
  }⟩

theorem k5hat_one_edge_subdivided_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (e : Fin 6 ↪ V)
    (h_adj :
      forall {x y : Fin 6},
        K5Hat.Adj x y ->
          ¬ ((x = (0 : Fin 6) ∧ y = (1 : Fin 6)) ∨
              (x = (1 : Fin 6) ∧ y = (0 : Fin 6))) ->
            G.Adj (e x) (e y))
    (p : G.Walk (e (0 : Fin 6)) (e (1 : Fin 6)))
    (hp : p.IsPath)
    (hp_internal_no_branch :
      forall {z : V},
        z ∈ Walk.InternalVertices p -> forall i : Fin 6, z ≠ e i) :
    NearHajosStrengtheningConclusion G := by
  classical
  let M : StrictSubdivisionModel K5Hat G :=
    StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath
      e p hp h_adj hp_internal_no_branch
  exact Or.inr ⟨{
    model := M
    edge₁_unsplit := by
      let h23 : K5Hat.Adj (2 : Fin 6) (3 : Fin 6) := by simp [K5Hat]
      have hnot23 :
          ¬ (((2 : Fin 6) = (0 : Fin 6) ∧ (3 : Fin 6) = (1 : Fin 6)) ∨
              ((2 : Fin 6) = (1 : Fin 6) ∧ (3 : Fin 6) = (0 : Fin 6))) := by
        decide
      exact
        StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath_edgeUnsplit_of_not_special
          e p hp h_adj hp_internal_no_branch h23 hnot23
    edge₂_unsplit := by
      let h24 : K5Hat.Adj (2 : Fin 6) (4 : Fin 6) := by simp [K5Hat]
      have hnot24 :
          ¬ (((2 : Fin 6) = (0 : Fin 6) ∧ (4 : Fin 6) = (1 : Fin 6)) ∨
              ((2 : Fin 6) = (1 : Fin 6) ∧ (4 : Fin 6) = (0 : Fin 6))) := by
        decide
      exact
        StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath_edgeUnsplit_of_not_special
          e p hp h_adj hp_internal_no_branch h24 hnot24
  }⟩

theorem K5Graph_near_hajos_with_two_incident_unsplit_edges :
    NearHajosStrengtheningConclusion K5Graph := by
  exact clique_near_hajos_with_two_incident_unsplit_edges
    (Function.Embedding.refl (Fin 5))
    (by
      intro x y hxy
      simpa [K5Graph, CompleteGraphOn] using hxy)

theorem K5Hat_near_hajos_with_two_incident_unsplit_edges :
    NearHajosStrengtheningConclusion K5Hat := by
  exact k5hat_embedding_near_hajos_with_two_incident_unsplit_edges
    (Function.Embedding.refl (Fin 6))
    (by
      intro x y hxy
      simpa using hxy)

theorem completeGraph_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} [Fintype V]
    (h_card : 5 <= Fintype.card V) :
    NearHajosStrengtheningConclusion (SimpleGraph.completeGraph V) := by
  classical
  obtain ⟨e⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin 5) (β := V) (by simpa using h_card)
  exact clique_near_hajos_with_two_incident_unsplit_edges e
    (by
      intro x y hxy
      exact show (SimpleGraph.completeGraph V).Adj (e x) (e y) from by
        simpa using hxy)

theorem completeGraph_near_hajos_with_two_incident_unsplit_edges_of_five_chromatic
    {V : Type u} [Fintype V]
    (h_five_chromatic_or_more :
      FiveChromaticOrMore (SimpleGraph.completeGraph V)) :
    NearHajosStrengtheningConclusion (SimpleGraph.completeGraph V) := by
  have h_card_gt : 4 < Fintype.card V :=
    card_gt_four_of_not_colorable_four
      (G := SimpleGraph.completeGraph V) h_five_chromatic_or_more
  exact completeGraph_near_hajos_with_two_incident_unsplit_edges
    (V := V) (by omega)

end Schematic.Math.GraphTheory
