import DominatingFourColour.Consequences.SingletonModels
import DominatingFourColour.Statements

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

private def replaceThirdAndLastTwoBranches
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G) (P : G.Subgraph) (w v : V) : Fin 5 -> G.Subgraph
  | 0 => T.branch 0
  | 1 => T.branch 1
  | 2 => P
  | 3 => G.singletonSubgraph w
  | 4 => G.singletonSubgraph v

theorem five_chromatic_has_dominating_K5_with_two_singletons
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    Exists fun T : DominatingK5Model G =>
      BranchIsSingleton T (3 : Fin 5) ∧ BranchIsSingleton T (4 : Fin 5) := by
  obtain ⟨T⟩ := five_chromatic_has_dominating_K5_model G h_five_chromatic_or_more
  exact dominating_K5_model_with_last_two_singletons T

theorem dominating_K5_can_choose_third_branch_path_and_tail_induced_cycle
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    ThirdBranchPathAndTailInducedCycleConclusion G := by
  classical
  obtain ⟨T, hT3, hT4⟩ :=
    five_chromatic_has_dominating_K5_with_two_singletons G h_five_chromatic_or_more
  obtain ⟨w, hw_single⟩ := hT3
  obtain ⟨v, hv_single⟩ := hT4
  have hw_mem : w ∈ (T.branch (3 : Fin 5)).verts := by
    simp [hw_single]
  have hv_mem : v ∈ (T.branch (4 : Fin 5)).verts := by
    simp [hv_single]
  obtain ⟨a, ha, haw⟩ := T.dominates (2 : Fin 5) (3 : Fin 5) (by decide) w hw_mem
  obtain ⟨b, hb, hbv⟩ := T.dominates (2 : Fin 5) (4 : Fin 5) (by decide) v hv_mem
  obtain ⟨w', hw', hw'v⟩ := T.dominates (3 : Fin 5) (4 : Fin 5) (by decide) v hv_mem
  have hw'_eq : w' = w := by
    simpa [hw_single] using hw'
  have hwv : G.Adj w v := by
    simpa [hw'_eq] using hw'v
  let a₂ : (T.branch (2 : Fin 5)).verts := ⟨a, ha⟩
  let b₂ : (T.branch (2 : Fin 5)).verts := ⟨b, hb⟩
  obtain ⟨p₂, hp₂⟩ := (T.connected (2 : Fin 5)).exists_isPath a₂ b₂
  let p : G.Walk a b := p₂.map (T.branch (2 : Fin 5)).hom
  have hp : p.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hp₂
  have hP_path : IsPathSubgraph p.toSubgraph :=
    Walk.isPathSubgraph_toSubgraph p hp
  have hP_le : p.toSubgraph ≤ T.branch (2 : Fin 5) := by
    simpa [p] using Walk.map_subgraph_toSubgraph_le p₂
  have hP_support_le {x : V} (hx : x ∈ p.support) :
      x ∈ (T.branch (2 : Fin 5)).verts := by
    exact hP_le.left (by rwa [SimpleGraph.Walk.mem_verts_toSubgraph])
  have haP : a ∈ p.toSubgraph.verts := by
    rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    exact p.start_mem_support
  have hbP : b ∈ p.toSubgraph.verts := by
    rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    exact p.end_mem_support
  have hv_not_p_support : v ∉ p.support := by
    intro hvp
    have hvP : v ∈ p.toSubgraph.verts := by
      rwa [SimpleGraph.Walk.mem_verts_toSubgraph]
    exact (Set.disjoint_left.mp
      (T.vertex_disjoint (2 : Fin 5) (4 : Fin 5) (by decide))
      (hP_le.left hvP)) hv_mem
  have hw_not_p_support : w ∉ p.support := by
    intro hwp
    have hwP : w ∈ p.toSubgraph.verts := by
      rwa [SimpleGraph.Walk.mem_verts_toSubgraph]
    exact (Set.disjoint_left.mp
      (T.vertex_disjoint (2 : Fin 5) (3 : Fin 5) (by decide))
      (hP_le.left hwP)) hw_mem
  have hv_ne_w : v ≠ w := hwv.ne.symm
  have hpath_to_v : (p.concat hbv).IsPath := by
    exact hp.concat hv_not_p_support hbv
  have hw_not_path_to_v_support : w ∉ (p.concat hbv).support := by
    intro hw_support
    rw [SimpleGraph.Walk.support_concat] at hw_support
    simp only [List.mem_append, List.mem_singleton] at hw_support
    rcases hw_support with hwp | hwv_eq
    · exact hw_not_p_support hwp
    · exact hwv.ne hwv_eq
  let q : G.Walk a w := (p.concat hbv).concat hwv.symm
  have hq_path : q.IsPath := by
    exact hpath_to_v.concat hw_not_path_to_v_support hwv.symm
  have hwa_not_q_edges : s(w, a) ∉ q.edges := by
    intro he
    simp only [q, SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append,
      List.mem_singleton, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at he
    rcases he with (he | he | he) | he | he
    · exact hw_not_p_support (p.fst_mem_support_of_mem_edges he)
    · rcases he with ⟨hwb, _hav⟩
      exact hw_not_p_support (by simp [hwb])
    · rcases he with ⟨hwv_eq, _hab⟩
      exact hwv.ne hwv_eq
    · rcases he with ⟨hwv_eq, _haw_eq⟩
      exact hwv.ne hwv_eq
    · rcases he with ⟨_h, hav⟩
      exact hv_not_p_support (by simpa [hav] using p.start_mem_support)
  let c : G.Walk w w := SimpleGraph.Walk.cons haw.symm q
  have hc : c.IsCycle := by
    simpa [c] using (SimpleGraph.Walk.cons_isCycle_iff q haw.symm).2
      ⟨hq_path, by simpa [Sym2.eq_swap] using hwa_not_q_edges⟩
  have hw_c_support : w ∈ c.support := by
    exact c.start_mem_support
  have hv_c_support : v ∈ c.support := by
    simp [c, q, SimpleGraph.Walk.support_concat]
  have hp_le_c : p.toSubgraph ≤ c.toSubgraph := by
    constructor
    · intro x hx
      have hx_support : x ∈ p.support := by
        rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hx
      rw [SimpleGraph.Walk.mem_verts_toSubgraph]
      simp [c, q, SimpleGraph.Walk.support_concat, hx_support]
    · intro x y hxy
      have hxy_edge : s(x, y) ∈ p.edges :=
        (SimpleGraph.Walk.mem_edges_toSubgraph p).mp
          ((SimpleGraph.Subgraph.mem_edgeSet).2 hxy)
      have hxy_c_edge : s(x, y) ∈ c.edges := by
        simp [c, q, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_concat,
          hxy_edge]
      exact (SimpleGraph.Subgraph.mem_edgeSet).1
        ((SimpleGraph.Walk.mem_edges_toSubgraph c).mpr hxy_c_edge)
  let T' : DominatingK5Model G := {
    branch := replaceThirdAndLastTwoBranches T p.toSubgraph w v
    connected := by
      intro i
      fin_cases i <;> simp [replaceThirdAndLastTwoBranches]
      · exact T.connected 0
      · exact T.connected 1
      · exact p.toSubgraph_connected.coe
      · exact SimpleGraph.Connected.of_subsingleton
      · exact SimpleGraph.Connected.of_subsingleton
    vertex_disjoint := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [replaceThirdAndLastTwoBranches] at hij ⊢
      · simpa using T.vertex_disjoint (0 : Fin 5) (1 : Fin 5) (by decide)
      · exact Set.disjoint_left.mpr (by
          intro x hx hy
          exact (Set.disjoint_left.mp
            (T.vertex_disjoint (0 : Fin 5) (2 : Fin 5) (by decide))
            hx) (hP_support_le hy))
      · exact fun hx => (Set.disjoint_left.mp
          (T.vertex_disjoint (0 : Fin 5) (3 : Fin 5) (by decide))
          hx) hw_mem
      · exact fun hx => (Set.disjoint_left.mp
          (T.vertex_disjoint (0 : Fin 5) (4 : Fin 5) (by decide))
          hx) hv_mem
      · simpa using T.vertex_disjoint (1 : Fin 5) (0 : Fin 5) (by decide)
      · exact Set.disjoint_left.mpr (by
          intro x hx hy
          exact (Set.disjoint_left.mp
            (T.vertex_disjoint (1 : Fin 5) (2 : Fin 5) (by decide))
            hx) (hP_support_le hy))
      · exact fun hx => (Set.disjoint_left.mp
          (T.vertex_disjoint (1 : Fin 5) (3 : Fin 5) (by decide))
          hx) hw_mem
      · exact fun hx => (Set.disjoint_left.mp
          (T.vertex_disjoint (1 : Fin 5) (4 : Fin 5) (by decide))
          hx) hv_mem
      · exact Set.disjoint_left.mpr (by
          intro x hx hy
          exact (Set.disjoint_left.mp
            (T.vertex_disjoint (2 : Fin 5) (0 : Fin 5) (by decide))
            (hP_support_le hx)) hy)
      · exact Set.disjoint_left.mpr (by
          intro x hx hy
          exact (Set.disjoint_left.mp
            (T.vertex_disjoint (2 : Fin 5) (1 : Fin 5) (by decide))
            (hP_support_le hx)) hy)
      · exact hw_not_p_support
      · exact hv_not_p_support
      · exact (Set.disjoint_left.mp
          (T.vertex_disjoint (3 : Fin 5) (0 : Fin 5) (by decide))
          hw_mem)
      · exact (Set.disjoint_left.mp
          (T.vertex_disjoint (3 : Fin 5) (1 : Fin 5) (by decide))
          hw_mem)
      · exact fun hx => (Set.disjoint_left.mp
          (T.vertex_disjoint (3 : Fin 5) (2 : Fin 5) (by decide))
          hw_mem) (hP_support_le hx)
      · exact hwv.ne
      · exact (Set.disjoint_left.mp
          (T.vertex_disjoint (4 : Fin 5) (0 : Fin 5) (by decide))
          hv_mem)
      · exact (Set.disjoint_left.mp
          (T.vertex_disjoint (4 : Fin 5) (1 : Fin 5) (by decide))
          hv_mem)
      · exact fun hx => (Set.disjoint_left.mp
          (T.vertex_disjoint (4 : Fin 5) (2 : Fin 5) (by decide))
          hv_mem) (hP_support_le hx)
      · exact hwv.ne.symm
    dominates := by
      intro i j hij x hx
      fin_cases i <;> fin_cases j <;>
        simp [replaceThirdAndLastTwoBranches] at hij hx ⊢
      · exact T.dominates (0 : Fin 5) (1 : Fin 5) (by decide) x hx
      · exact T.dominates (0 : Fin 5) (2 : Fin 5) (by decide) x (hP_support_le hx)
      · rw [hx]
        exact T.dominates (0 : Fin 5) (3 : Fin 5) (by decide) w hw_mem
      · rw [hx]
        exact T.dominates (0 : Fin 5) (4 : Fin 5) (by decide) v hv_mem
      · exact T.dominates (1 : Fin 5) (2 : Fin 5) (by decide) x (hP_support_le hx)
      · rw [hx]
        exact T.dominates (1 : Fin 5) (3 : Fin 5) (by decide) w hw_mem
      · rw [hx]
        exact T.dominates (1 : Fin 5) (4 : Fin 5) (by decide) v hv_mem
      · rw [hx]
        exact ⟨a, p.start_mem_support, haw⟩
      · rw [hx]
        exact ⟨b, p.end_mem_support, hbv⟩
      · rw [hx]
        exact hwv
  }
  exact ⟨{
    model := T'
    fourth_singleton := ⟨w, by simp [T', replaceThirdAndLastTwoBranches]⟩
    fifth_singleton := ⟨v, by simp [T', replaceThirdAndLastTwoBranches]⟩
    third_branch_path := by simpa [T', replaceThirdAndLastTwoBranches] using hP_path
    tail_cycle := c.toSubgraph
    tail_induced_cycle := Walk.isCycleSubgraph_toSubgraph c hc
    tail_contains_third_branch_subgraph := by
      simpa [T', replaceThirdAndLastTwoBranches] using hp_le_c
    tail_contains_third_branch := by
      simpa [T', replaceThirdAndLastTwoBranches] using hp_le_c.left
    tail_contains_last_branches := by
      constructor
      · intro x hx
        simp [T', replaceThirdAndLastTwoBranches, SimpleGraph.singletonSubgraph_verts] at hx
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        simp [hx, hw_c_support]
      · intro x hx
        simp [T', replaceThirdAndLastTwoBranches, SimpleGraph.singletonSubgraph_verts] at hx
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        simpa [hx] using hv_c_support
  }⟩

theorem five_chromatic_has_two_distinct_incident_graph_edges_from_tail_data
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_five_chromatic_or_more : FiveChromaticOrMore G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        edge₁ ≠ edge₂ ∧
          (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
            edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  obtain ⟨D⟩ :=
    dominating_K5_can_choose_third_branch_path_and_tail_induced_cycle
      G h_five_chromatic_or_more
  exact D.distinct_incidentGraphEdges

end Schematic.Math.GraphTheory
