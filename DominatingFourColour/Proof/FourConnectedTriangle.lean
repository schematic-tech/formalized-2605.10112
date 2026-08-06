import DominatingFourColour.Prerequisites.FinalAlternative

/-!
Formalization of Lemma `4-connected-triangle`.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

private def triangleTailBranches
    (B0 B1 : G.Subgraph) (feet : Fin 3 -> V) : Fin 5 -> G.Subgraph
  | 0 => B0
  | 1 => B1
  | 2 => G.singletonSubgraph (feet 0)
  | 3 => G.singletonSubgraph (feet 1)
  | 4 => G.singletonSubgraph (feet 2)

theorem HasTriangleDisjointFromPair.exists_fin3_triangle
    {v1 v2 : V}
    (h_triangle : HasTriangleDisjointFromPair G v1 v2) :
    Exists fun feet : Fin 3 -> V =>
      IsTriangle G (feet 0) (feet 1) (feet 2) ∧
        (forall i : Fin 3, feet i ≠ v1 ∧ feet i ≠ v2) := by
  rcases h_triangle with
    ⟨a, b, c, htri, hav1, hav2, hbv1, hbv2, hcv1, hcv2⟩
  let feet : Fin 3 -> V
    | 0 => a
    | 1 => b
    | 2 => c
  refine ⟨feet, ?_, ?_⟩
  · simpa using htri
  · intro i
    fin_cases i <;> simp [feet, hav1, hav2, hbv1, hbv2, hcv1, hcv2]

theorem IsFourConnected.delete_triangle_connected
    [Fintype V]
    (h_four_connected : IsFourConnected G)
    {a b c : V} :
    (G.induce ({a, b, c} : Set V)ᶜ).Connected :=
  isFourConnected_delete_triple_connected h_four_connected a b c

theorem IsFourConnected.delete_triangle_top_connected
    [Fintype V]
    (h_four_connected : IsFourConnected G)
    {a b c : V} :
    (((⊤ : G.Subgraph).deleteVerts ({a, b, c} : Set V)).coe).Connected :=
  isFourConnected_delete_triple_top_connected h_four_connected a b c

theorem compatible_model_of_two_branches_and_tail_triangle
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (B0 B1 : G.Subgraph)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (hB0_connected : B0.coe.Connected)
    (hB1_connected : B1.coe.Connected)
    (hB0B1_disjoint : Disjoint B0.verts B1.verts)
    (hB0_feet : forall i : Fin 3, feet i ∉ B0.verts)
    (hB1_feet : forall i : Fin 3, feet i ∉ B1.verts)
    (hv1_B0 : v1 ∈ B0.verts)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i)
    (hdom01 : forall v : V, v ∈ B1.verts ->
      Exists fun u : V => u ∈ B0.verts ∧ G.Adj u v)
    (hdom0feet : forall i : Fin 3,
      Exists fun u : V => u ∈ B0.verts ∧ G.Adj u (feet i))
    (hdom1feet : forall i : Fin 3,
      Exists fun u : V => u ∈ B1.verts ∧ G.Adj u (feet i)) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) := by
  classical
  rcases h_triangle with ⟨h01, h12, h20, h01adj, h12adj, h20adj⟩
  let T : DominatingK5Model G := {
    branch := triangleTailBranches B0 B1 feet
    connected := by
      intro i
      fin_cases i <;> simp [triangleTailBranches]
      · exact hB0_connected
      · exact hB1_connected
      · exact SimpleGraph.Connected.of_subsingleton
      · exact SimpleGraph.Connected.of_subsingleton
      · exact SimpleGraph.Connected.of_subsingleton
    vertex_disjoint := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [triangleTailBranches] at hij ⊢
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp hB0B1_disjoint
      · exact hB0_feet 0
      · exact hB0_feet 1
      · exact hB0_feet 2
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp hB0B1_disjoint.symm
      · exact hB1_feet 0
      · exact hB1_feet 1
      · exact hB1_feet 2
      · exact hB0_feet 0
      · exact hB1_feet 0
      · exact h01
      · exact h20.symm
      · exact hB0_feet 1
      · exact hB1_feet 1
      · exact h01.symm
      · exact h12
      · exact hB0_feet 2
      · exact hB1_feet 2
      · exact h20
      · exact h12.symm
    dominates := by
      intro i j hij v hv
      fin_cases i <;> fin_cases j <;>
        simp [triangleTailBranches] at hij hv ⊢
      · exact hdom01 v hv
      · rw [hv]
        exact hdom0feet 0
      · rw [hv]
        exact hdom0feet 1
      · rw [hv]
        exact hdom0feet 2
      · rw [hv]
        exact hdom1feet 0
      · rw [hv]
        exact hdom1feet 1
      · rw [hv]
        exact hdom1feet 2
      · rw [hv]
        exact h01adj
      · rw [hv]
        exact h20adj.symm
      · rw [hv]
        exact h12adj
  }
  refine ⟨T, ?_⟩
  have hv1_index : T.branchIndex v1 = 1 := by
    simpa [T, triangleTailBranches] using
      T.branchIndex_eq_add_one_of_mem (i := (0 : Fin 5)) hv1_B0
  have hv2_index_le_two : T.branchIndex v2 <= 2 := by
    by_cases hv20 : v2 ∈ B0.verts
    · rw [T.branchIndex_eq_add_one_of_mem (i := (0 : Fin 5)) (by
        simpa [T, triangleTailBranches] using hv20)]
      simp
    · by_cases hv21 : v2 ∈ B1.verts
      · rw [T.branchIndex_eq_add_one_of_mem (i := (1 : Fin 5)) (by
          simpa [T, triangleTailBranches] using hv21)]
        simp
      · have hzero : T.branchIndex v2 = 0 := by
          exact T.branchIndex_eq_zero_of_forall_not_mem (by
            intro i hi
            fin_cases i <;> simp [T, triangleTailBranches] at hi
            · exact hv20 hi
            · exact hv21 hi
            · exact (hv2_not_feet 0) hi
            · exact (hv2_not_feet 1) hi
            · exact (hv2_not_feet 2) hi)
        rw [hzero]
        simp
  exact ⟨hv1_index ▸ by simp, hv2_index_le_two, fun _ => hv1_index⟩

theorem compatible_model_of_complete_pair_and_disjoint_triangle
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (hfeet_disjoint : forall i : Fin 3, feet i ≠ v1 ∧ feet i ≠ v2) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) := by
  classical
  let B0 : G.Subgraph := G.singletonSubgraph v1
  let B1 : G.Subgraph := G.singletonSubgraph v2
  refine compatible_model_of_two_branches_and_tail_triangle
    (G := G) edge B0 B1 feet h_triangle
    SimpleGraph.Connected.of_subsingleton
    SimpleGraph.Connected.of_subsingleton
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Set.disjoint_left]
    intro x hx0 hx1
    rw [SimpleGraph.singletonSubgraph_verts] at hx0 hx1
    exact edge.ne (hx0.symm.trans hx1)
  · intro i
    simpa [B0, SimpleGraph.singletonSubgraph_verts] using (hfeet_disjoint i).1
  · intro i
    simpa [B1, SimpleGraph.singletonSubgraph_verts] using (hfeet_disjoint i).2
  · simp [B0, SimpleGraph.singletonSubgraph_verts]
  · intro i h
    exact (hfeet_disjoint i).2 h.symm
  · intro v hv
    simp [B1, SimpleGraph.singletonSubgraph_verts] at hv
    refine ⟨v1, ?_, by simpa [hv] using edge⟩
    simp [B0, SimpleGraph.singletonSubgraph_verts]
  · intro i
    refine ⟨v1, ?_, h_complete v1 (feet i) ?_⟩
    · simp [B0, SimpleGraph.singletonSubgraph_verts]
    · exact (hfeet_disjoint i).1.symm
  · intro i
    refine ⟨v2, ?_, h_complete v2 (feet i) ?_⟩
    · simp [B1, SimpleGraph.singletonSubgraph_verts]
    · exact (hfeet_disjoint i).2.symm

theorem compatible_model_of_common_neighbor_pair_and_disjoint_triangle
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (hfeet_disjoint : forall i : Fin 3, feet i ≠ v1 ∧ feet i ≠ v2)
    (hv1_feet : forall i : Fin 3, G.Adj v1 (feet i))
    (hv2_feet : forall i : Fin 3, G.Adj v2 (feet i)) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) := by
  classical
  let B0 : G.Subgraph := G.singletonSubgraph v1
  let B1 : G.Subgraph := G.singletonSubgraph v2
  refine compatible_model_of_two_branches_and_tail_triangle
    (G := G) edge B0 B1 feet h_triangle
    SimpleGraph.Connected.of_subsingleton
    SimpleGraph.Connected.of_subsingleton
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Set.disjoint_left]
    intro x hx0 hx1
    rw [SimpleGraph.singletonSubgraph_verts] at hx0 hx1
    exact edge.ne (hx0.symm.trans hx1)
  · intro i
    simpa [B0, SimpleGraph.singletonSubgraph_verts] using (hfeet_disjoint i).1
  · intro i
    simpa [B1, SimpleGraph.singletonSubgraph_verts] using (hfeet_disjoint i).2
  · simp [B0, SimpleGraph.singletonSubgraph_verts]
  · intro i h
    exact (hfeet_disjoint i).2 h.symm
  · intro v hv
    simp [B1, SimpleGraph.singletonSubgraph_verts] at hv
    refine ⟨v1, ?_, by simpa [hv] using edge⟩
    simp [B0, SimpleGraph.singletonSubgraph_verts]
  · intro i
    refine ⟨v1, ?_, hv1_feet i⟩
    simp [B0, SimpleGraph.singletonSubgraph_verts]
  · intro i
    refine ⟨v2, ?_, hv2_feet i⟩
    simp [B1, SimpleGraph.singletonSubgraph_verts]

theorem compatible_model_of_outside_and_punctured_triad
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (houtside_connected :
      (((⊤ : G.Subgraph).deleteVerts T.vertexSet).coe).Connected)
    (hpunctured_connected :
      ((T.carrier.deleteVerts (Set.range feet)).coe).Connected)
    (hv1_outside : v1 ∉ T.vertexSet)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i)
    (hdom_outside_punctured : forall v : V,
      v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧ G.Adj u v)
    (hdom_outside_feet : forall i : Fin 3,
      Exists fun u : V =>
        u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧ G.Adj u (feet i)) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) := by
  classical
  let B0 : G.Subgraph := (⊤ : G.Subgraph).deleteVerts T.vertexSet
  let B1 : G.Subgraph := T.carrier.deleteVerts (Set.range feet)
  refine compatible_model_of_two_branches_and_tail_triangle
    (G := G) edge B0 B1 feet h_triangle houtside_connected hpunctured_connected
    ?_ ?_ ?_ ?_ hv2_not_feet ?_ ?_ ?_
  · rw [Set.disjoint_left]
    intro x hx0 hx1
    simp only [B0, B1, SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
      Set.mem_diff, Set.mem_univ, true_and] at hx0 hx1
    exact hx0 (T.mem_carrier_verts_iff.mp hx1.1)
  · intro i
    simp only [B0, SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
      Set.mem_diff, Set.mem_univ, true_and, not_not]
    exact T.foot_mem_vertexSet i
  · intro i
    simp only [B1, SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff, not_and]
    intro _hcarrier hnot
    exact hnot ⟨i, rfl⟩
  · simp only [B0, SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
      Set.mem_diff, Set.mem_univ, true_and]
    exact hv1_outside
  · intro v hv
    exact hdom_outside_punctured v (by simpa [B1] using hv)
  · intro i
    exact hdom_outside_feet i
  · intro i
    exact T.foot_has_neighbor_in_punctured_carrier hfeet_injective i

theorem compatible_model_of_outside_and_triad
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (houtside_connected :
      (((⊤ : G.Subgraph).deleteVerts T.vertexSet).coe).Connected)
    (hv1_outside : v1 ∉ T.vertexSet)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i)
    (hdom_outside_punctured : forall v : V,
      v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧ G.Adj u v)
    (hdom_outside_feet : forall i : Fin 3,
      Exists fun u : V =>
        u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧ G.Adj u (feet i)) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) :=
  compatible_model_of_outside_and_punctured_triad
    (G := G) edge feet h_triangle T hfeet_injective houtside_connected
    (T.punctured_carrier_connected hfeet_injective)
    hv1_outside hv2_not_feet hdom_outside_punctured hdom_outside_feet

theorem compatible_model_of_induced_outside_and_triad
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (houtside_connected : (G.induce T.vertexSetᶜ).Connected)
    (hv1_outside : v1 ∉ T.vertexSet)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i)
    (hdom_outside_punctured : forall v : V,
      v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧ G.Adj u v)
    (hdom_outside_feet : forall i : Fin 3,
      Exists fun u : V =>
        u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧ G.Adj u (feet i)) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) :=
  compatible_model_of_outside_and_triad
    (G := G) edge feet h_triangle T hfeet_injective
    ((connected_deleteVerts_top_iff_induce_compl (G := G) T.vertexSet).mpr
      houtside_connected)
    hv1_outside hv2_not_feet hdom_outside_punctured hdom_outside_feet

theorem triad_punctured_vertices_have_outside_neighbors_of_inside_neighbor_bound
    [Fintype V] [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hmin_degree : forall v : V, 4 <= G.degree v)
    (hinside_neighbors : forall v : V,
      v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ T.vertexSet).ncard <= 3) :
    forall v : V,
      v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧ G.Adj u v := by
  intro v hv
  exact exists_neighbor_outside_set_of_degree_atLeast_four_of_inside_neighbors_atMost_three
    (G := G) T.vertexSet (hmin_degree v) (hinside_neighbors v hv)

theorem compatible_model_of_induced_outside_and_triad_with_inside_neighbor_bound
    [Fintype V] [DecidableRel G.Adj]
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (hmin_degree : forall v : V, 4 <= G.degree v)
    (houtside_connected : (G.induce T.vertexSetᶜ).Connected)
    (hv1_outside : v1 ∉ T.vertexSet)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i)
    (hinside_neighbors : forall v : V,
      v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ T.vertexSet).ncard <= 3)
    (hdom_outside_feet : forall i : Fin 3,
      Exists fun u : V =>
        u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧ G.Adj u (feet i)) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) :=
  compatible_model_of_induced_outside_and_triad
    (G := G) edge feet h_triangle T hfeet_injective houtside_connected
    hv1_outside hv2_not_feet
    (triad_punctured_vertices_have_outside_neighbors_of_inside_neighbor_bound
      (G := G) T hmin_degree hinside_neighbors)
    hdom_outside_feet

theorem compatible_model_of_induced_outside_and_triad_with_four_connected_inside_neighbor_bound
    [Fintype V] [DecidableRel G.Adj]
    (h_four_connected : IsFourConnected G)
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (houtside_connected : (G.induce T.vertexSetᶜ).Connected)
    (hv1_outside : v1 ∉ T.vertexSet)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i)
    (hinside_neighbors : forall v : V,
      v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ T.vertexSet).ncard <= 3)
    (hdom_outside_feet : forall i : Fin 3,
      Exists fun u : V =>
        u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧ G.Adj u (feet i)) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) :=
  compatible_model_of_induced_outside_and_triad_with_inside_neighbor_bound
    (G := G) edge feet h_triangle T hfeet_injective
    (fun v => four_connected_minDegree_atLeast_four (G := G) h_four_connected v)
    houtside_connected hv1_outside hv2_not_feet hinside_neighbors hdom_outside_feet

theorem compatible_model_of_rst_lean_triad_data
    [Fintype V] [DecidableRel G.Adj]
    (h_four_connected : IsFourConnected G)
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (D : RSTLeanTriadData G feet v1)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) :=
  compatible_model_of_induced_outside_and_triad_with_four_connected_inside_neighbor_bound
    (G := G) h_four_connected edge feet h_triangle D.triad
    (IsTriangle.injective_fin3 h_triangle)
    D.complement_connected D.root_outside hv2_not_feet
    D.inside_neighbors_at_most_three D.foot_has_neighbor_outside

theorem compatible_model_of_legless_tripod_second
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (Tripod : LeglessTripod G feet)
    (houtside_connected :
      (((⊤ : G.Subgraph).deleteVerts Tripod.second.vertexSet).coe).Connected)
    (hv1_outside : v1 ∉ Tripod.second.vertexSet)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i)
    (hdom_outside_punctured : forall v : V,
      v ∈ (Tripod.second.carrier.deleteVerts (Set.range feet)).verts ->
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts Tripod.second.vertexSet).verts ∧
            G.Adj u v) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) := by
  exact compatible_model_of_outside_and_triad
    (G := G) edge feet h_triangle Tripod.second
    (IsTriangle.injective_fin3 h_triangle)
    houtside_connected hv1_outside hv2_not_feet
    hdom_outside_punctured
    (Tripod.foot_has_neighbor_outside_second (IsTriangle.injective_fin3 h_triangle))

theorem compatible_model_of_legless_tripod_first
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (Tripod : LeglessTripod G feet)
    (houtside_connected :
      (((⊤ : G.Subgraph).deleteVerts Tripod.first.vertexSet).coe).Connected)
    (hv1_outside : v1 ∉ Tripod.first.vertexSet)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i)
    (hdom_outside_punctured : forall v : V,
      v ∈ (Tripod.first.carrier.deleteVerts (Set.range feet)).verts ->
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts Tripod.first.vertexSet).verts ∧
            G.Adj u v) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) := by
  exact compatible_model_of_outside_and_triad
    (G := G) edge feet h_triangle Tripod.first
    (IsTriangle.injective_fin3 h_triangle)
    houtside_connected hv1_outside hv2_not_feet
    hdom_outside_punctured
    (Tripod.foot_has_neighbor_outside_first (IsTriangle.injective_fin3 h_triangle))

theorem compatible_model_of_legless_tripod_second_induced_with_four_connected_inside_neighbor_bound
    [Fintype V] [DecidableRel G.Adj]
    (h_four_connected : IsFourConnected G)
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (Tripod : LeglessTripod G feet)
    (houtside_connected : (G.induce Tripod.second.vertexSetᶜ).Connected)
    (hv1_outside : v1 ∉ Tripod.second.vertexSet)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i)
    (hinside_neighbors : forall v : V,
      v ∈ (Tripod.second.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ Tripod.second.vertexSet).ncard <= 3) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) := by
  exact compatible_model_of_induced_outside_and_triad_with_four_connected_inside_neighbor_bound
    (G := G) h_four_connected edge feet h_triangle Tripod.second
    (IsTriangle.injective_fin3 h_triangle)
    houtside_connected hv1_outside hv2_not_feet hinside_neighbors
    (Tripod.foot_has_neighbor_outside_second (IsTriangle.injective_fin3 h_triangle))

theorem compatible_model_of_legless_tripod_first_induced_with_four_connected_inside_neighbor_bound
    [Fintype V] [DecidableRel G.Adj]
    (h_four_connected : IsFourConnected G)
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (Tripod : LeglessTripod G feet)
    (houtside_connected : (G.induce Tripod.first.vertexSetᶜ).Connected)
    (hv1_outside : v1 ∉ Tripod.first.vertexSet)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i)
    (hinside_neighbors : forall v : V,
      v ∈ (Tripod.first.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ Tripod.first.vertexSet).ncard <= 3) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) := by
  exact compatible_model_of_induced_outside_and_triad_with_four_connected_inside_neighbor_bound
    (G := G) h_four_connected edge feet h_triangle Tripod.first
    (IsTriangle.injective_fin3 h_triangle)
    houtside_connected hv1_outside hv2_not_feet hinside_neighbors
    (Tripod.foot_has_neighbor_outside_first (IsTriangle.injective_fin3 h_triangle))

theorem compatible_model_of_legless_tripod_either_induced_with_four_connected_inside_neighbor_bound
    [Fintype V] [DecidableRel G.Adj]
    (h_four_connected : IsFourConnected G)
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (Tripod : LeglessTripod G feet)
    (hv1_avoids_one :
      v1 ∉ Tripod.first.vertexSet ∨ v1 ∉ Tripod.second.vertexSet)
    (hv2_not_feet : forall i : Fin 3, v2 ≠ feet i)
    (hfirst_outside_connected : (G.induce Tripod.first.vertexSetᶜ).Connected)
    (hsecond_outside_connected : (G.induce Tripod.second.vertexSetᶜ).Connected)
    (hfirst_inside_neighbors : forall v : V,
      v ∈ (Tripod.first.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ Tripod.first.vertexSet).ncard <= 3)
    (hsecond_inside_neighbors : forall v : V,
      v ∈ (Tripod.second.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ Tripod.second.vertexSet).ncard <= 3) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) := by
  rcases hv1_avoids_one with hv1_first | hv1_second
  · exact compatible_model_of_legless_tripod_first_induced_with_four_connected_inside_neighbor_bound
      (G := G) h_four_connected edge feet h_triangle Tripod
      hfirst_outside_connected hv1_first hv2_not_feet hfirst_inside_neighbors
  · exact compatible_model_of_legless_tripod_second_induced_with_four_connected_inside_neighbor_bound
      (G := G) h_four_connected edge feet h_triangle Tripod
      hsecond_outside_connected hv1_second hv2_not_feet hsecond_inside_neighbors

theorem lemma_four_connected_triangle
    [Fintype V]
    (h_four_connected : IsFourConnected G)
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (h_triangle : HasTriangleDisjointFromPair G v1 v2) :
    IsPlanar G ∨ CompatibleDominatingK5Model (.pair v1 v2 edge) := by
  classical
  obtain ⟨feet, hfeet_triangle, _hfeet_disjoint⟩ :=
    h_triangle.exists_fin3_triangle
  have hv1_not_feet : v1 ∉ Set.range feet := by
    rintro ⟨i, hi⟩
    exact (_hfeet_disjoint i).1 hi
  have hv2_not_feet : forall i : Fin 3, v2 ≠ feet i := by
    intro i h
    exact (_hfeet_disjoint i).2 h.symm
  by_cases h_complete : forall u v : V, u ≠ v -> G.Adj u v
  · exact Or.inr
      (compatible_model_of_complete_pair_and_disjoint_triangle
        (G := G) edge h_complete feet hfeet_triangle _hfeet_disjoint)
  by_cases h_common_pair :
      (forall i : Fin 3, G.Adj v1 (feet i)) ∧
        (forall i : Fin 3, G.Adj v2 (feet i))
  · exact Or.inr
      (compatible_model_of_common_neighbor_pair_and_disjoint_triangle
        (G := G) edge feet hfeet_triangle _hfeet_disjoint
        h_common_pair.1 h_common_pair.2)
  letI : DecidableRel G.Adj := Classical.decRel _
  by_cases hv1_common : forall i : Fin 3, G.Adj v1 (feet i)
  · rcases rst_lean_triad_data_of_four_connected_triangle_root_common_neighbor
        (G := G) h_four_connected hfeet_triangle hv1_not_feet hv1_common with
      ⟨D⟩
    exact Or.inr
      (compatible_model_of_rst_lean_triad_data
        (G := G) h_four_connected edge feet hfeet_triangle D hv2_not_feet)
  rcases rst_planar_or_rst_lean_triad_data
      h_four_connected feet hfeet_triangle v1 hv1_not_feet with
    hplanar | htriad_data
  ·
      exact Or.inl hplanar
  ·
      rcases htriad_data with ⟨D⟩
      exact Or.inr
        (compatible_model_of_rst_lean_triad_data
          (G := G) h_four_connected edge feet hfeet_triangle D hv2_not_feet)

end Schematic.Math.GraphTheory
