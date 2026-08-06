import DominatingFourColour.Proof.DominatingK4.CycleComponents

/-!
Constructing a dominating K4 model from a cycle and its connected complement.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace DominatingK4

theorem exists_dominating_K4_model_of_connected_subgraph_dominating_cycle
    (L : Finset V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hL_subset_H : forall v : V, v ∈ L -> v ∈ H.verts)
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (hH_disjoint_cycle : Disjoint H.verts {v : V | v ∈ c.support})
    (hH_dominates_cycle :
      forall v : V, v ∈ c.support ->
        Exists fun u : V => u ∈ H.verts ∧ G.Adj u v) :
    Exists fun T : DominatingK4Model G =>
      forall v : V, v ∈ L -> v ∈ (T.branch (0 : Fin 4)).verts := by
  classical
  let P : G.Walk c.tail.snd c.tail.tail.penultimate := c.tail.tail.dropLast
  let y : V := c.snd
  let branches : Fin 4 -> G.Subgraph
    | 0 => H
    | 1 => P.toSubgraph
    | 2 => G.singletonSubgraph y
    | 3 => G.singletonSubgraph x
  have hc_not_nil : Not c.Nil := hc.not_nil
  have htail_len_add : c.tail.length + 1 = c.length :=
    c.length_tail_add_one hc_not_nil
  have htail_len_ge_two : 2 <= c.tail.length := by
    have hcycle_len : 3 <= c.length := hc.three_le_length
    omega
  have htail_not_nil : Not c.tail.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    omega
  have htailtail_len_add : c.tail.tail.length + 1 = c.tail.length :=
    c.tail.length_tail_add_one htail_not_nil
  have htailtail_not_nil : Not c.tail.tail.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    omega
  have hP_sub_cycle : P.support ⊆ c.support := by
    intro v hv
    exact (Walk.cycle_middle_subwalk c).support_subset hv
  have hy_mem_cycle : y ∈ c.support := by
    exact List.mem_of_mem_tail (c.snd_mem_tail_support hc_not_nil)
  have hx_mem_cycle : x ∈ c.support := c.start_mem_support
  have hy_not_P : y ∉ P.support := by
    intro hyP
    have hy_tailtail : y ∈ c.tail.tail.support := by
      have hsub : P.support ⊆ c.tail.tail.support :=
        ((SimpleGraph.Walk.isSubwalk_rfl c.tail.tail).dropLast).support_subset
      exact hsub hyP
    have hy_tail : y ∈ c.tail.support.tail := by
      simpa [SimpleGraph.Walk.support_tail_of_not_nil c.tail htail_not_nil] using
        hy_tailtail
    exact (Walk.IsPath.start_notMem_tail_support hc.isPath_tail) hy_tail
  have hx_not_P : x ∉ P.support := by
    exact Walk.IsPath.end_notMem_walk_dropLast_support
      (SimpleGraph.Walk.IsPath.tail hc.isPath_tail) htailtail_not_nil
  have hxy_adj : G.Adj x y := c.adj_snd hc_not_nil
  have hP_y_adj : G.Adj c.tail.snd y := by
    exact (c.tail.adj_snd htail_not_nil).symm
  have hP_x_adj : G.Adj c.tail.tail.penultimate x := by
    exact c.tail.tail.adj_penultimate htailtail_not_nil
  have hH_disjoint_P : Disjoint H.verts {v : V | v ∈ P.support} := by
    rw [Set.disjoint_left]
    intro v hvH hvP
    exact Set.disjoint_left.mp hH_disjoint_cycle hvH (hP_sub_cycle hvP)
  have hH_not_y : y ∉ H.verts := by
    intro hyH
    exact Set.disjoint_left.mp hH_disjoint_cycle hyH hy_mem_cycle
  have hH_not_x : x ∉ H.verts := by
    intro hxH
    exact Set.disjoint_left.mp hH_disjoint_cycle hxH hx_mem_cycle
  let T : DominatingK4Model G := {
    branch := branches
    connected := by
      intro i
      fin_cases i <;> simp [branches]
      · exact hH_connected
      · exact P.toSubgraph_connected.coe
      · exact SimpleGraph.Connected.of_subsingleton
      · exact SimpleGraph.Connected.of_subsingleton
    vertex_disjoint := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [branches] at hij ⊢
      · rw [Set.disjoint_left]
        intro v hvH hvP
        exact Set.disjoint_left.mp hH_disjoint_P hvH hvP
      · exact hH_not_y
      · exact hH_not_x
      · rw [Set.disjoint_left]
        intro v hvP hvH
        exact Set.disjoint_left.mp hH_disjoint_P hvH hvP
      · exact hy_not_P
      · exact hx_not_P
      · exact hH_not_y
      · exact hy_not_P
      · exact hxy_adj.ne'
      · exact hH_not_x
      · exact hx_not_P
      · exact hxy_adj.ne
    dominates := by
      intro i j hij v hv
      fin_cases i <;> fin_cases j <;> simp [branches] at hij hv ⊢
      · exact hH_dominates_cycle v (hP_sub_cycle hv)
      · rw [hv]
        exact hH_dominates_cycle y hy_mem_cycle
      · rw [hv]
        exact hH_dominates_cycle x hx_mem_cycle
      · rw [hv]
        exact ⟨c.tail.snd, P.start_mem_support, hP_y_adj⟩
      · rw [hv]
        exact ⟨c.tail.tail.penultimate, P.end_mem_support, hP_x_adj⟩
      · rw [hv]
        exact hxy_adj.symm
  }
  refine ⟨T, ?_⟩
  intro v hvL
  exact hL_subset_H v hvL

theorem exists_dominating_K4_model_of_connected_set_dominating_cycle
    (L : Finset V)
    (A : Set V)
    (hA_connected : (G.induce A).Connected)
    (hL_subset_A : forall v : V, v ∈ L -> v ∈ A)
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (hA_disjoint_cycle : Disjoint A {v : V | v ∈ c.support})
    (hA_dominates_cycle :
      forall v : V, v ∈ c.support ->
        Exists fun u : V => u ∈ A ∧ G.Adj u v) :
    Exists fun T : DominatingK4Model G =>
      forall v : V, v ∈ L -> v ∈ (T.branch (0 : Fin 4)).verts := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce A
  refine exists_dominating_K4_model_of_connected_subgraph_dominating_cycle
    (G := G) L H ?_ ?_ c hc ?_ ?_
  · change (((⊤ : G.Subgraph).induce A).coe).Connected
    exact ((SimpleGraph.connected_induce_iff (G := G) (s := A)).mp hA_connected).coe
  · intro v hvL
    exact hL_subset_A v hvL
  · simpa [H, SimpleGraph.Subgraph.induce_verts] using hA_disjoint_cycle
  · intro v hv_cycle
    obtain ⟨u, huA, huv⟩ := hA_dominates_cycle v hv_cycle
    exact ⟨u, by simpa [H, SimpleGraph.Subgraph.induce_verts] using huA, huv⟩

theorem cycle_complement_dominates_of_inside_neighbors_atMost_two
    [Fintype V] [DecidableRel G.Adj]
    (L : Finset V)
    {x : V}
    (c : G.Walk x x)
    (hcycle_avoids_L : forall v : V, v ∈ c.support -> v ∉ L)
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L)
    (hinside :
      forall v : V, v ∈ c.support ->
        (G.neighborSet v ∩ {w : V | w ∈ c.support}).ncard <= 2) :
    forall v : V, v ∈ c.support ->
      Exists fun u : V => u ∈ ({w : V | w ∈ c.support}ᶜ) ∧ G.Adj u v := by
  intro v hv_cycle
  have hv_not_low : ¬ G.degree v <= 2 := by
    intro hv_low
    exact hcycle_avoids_L v hv_cycle (h_low_degree_in_L v hv_low)
  have hdeg_ge : 3 <= G.degree v := by omega
  have hinside_lt :
      (G.neighborSet v ∩ {w : V | w ∈ c.support}).ncard < G.degree v := by
    have hinside_le := hinside v hv_cycle
    omega
  obtain ⟨u, hu, huv⟩ :=
    exists_neighbor_outside_set_of_inside_neighbors_lt_degree
      (G := G) {w : V | w ∈ c.support} hinside_lt
  refine ⟨u, ?_, huv⟩
  rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hu
  exact hu.2

theorem cycle_inside_neighbors_atMost_two_of_chordless
    [Fintype V]
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (hchordless :
      forall {u v : V}, u ∈ c.support -> v ∈ c.support ->
        G.Adj u v -> c.toSubgraph.Adj u v) :
    forall v : V, v ∈ c.support ->
      (G.neighborSet v ∩ {w : V | w ∈ c.support}).ncard <= 2 := by
  intro v hv_cycle
  have hsubset :
      G.neighborSet v ∩ {w : V | w ∈ c.support} ⊆
        c.toSubgraph.neighborSet v := by
    intro w hw
    exact hchordless hv_cycle hw.2 hw.1
  have hle :
      (G.neighborSet v ∩ {w : V | w ∈ c.support}).ncard <=
        (c.toSubgraph.neighborSet v).ncard :=
    Set.ncard_le_ncard hsubset
  have hcard : (c.toSubgraph.neighborSet v).ncard = 2 :=
    hc.ncard_neighborSet_toSubgraph_eq_two hv_cycle
  omega

/-- Every vertex of a chordless cycle has a neighbor outside it under the low-degree hypothesis. -/
theorem cycle_complement_dominates_of_chordless
    [Fintype V] [DecidableRel G.Adj]
    (L : Finset V)
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (hcycle_avoids_L : forall v : V, v ∈ c.support -> v ∉ L)
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L)
    (hchordless : c.IsChordless) :
    forall v : V, v ∈ c.support ->
      Exists fun u : V => u ∈ ({w : V | w ∈ c.support}ᶜ) ∧ G.Adj u v :=
  cycle_complement_dominates_of_inside_neighbors_atMost_two
    (G := G) L c hcycle_avoids_L h_low_degree_in_L
    (cycle_inside_neighbors_atMost_two_of_chordless
      (G := G) c hc fun hu hv hadj =>
        Schematic.Math.GraphTheory.Walk.IsChordless.toSubgraph_adj_of_adj
          hchordless hu hv hadj)

theorem cycle_support_ncard_gt_one
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle) :
    1 < ({v : V | v ∈ c.support}).ncard := by
  classical
  letI : Fintype ({v : V | v ∈ c.support} : Set V) :=
    (List.finite_toSet c.support).fintype
  have hnot_nil : ¬ c.Nil := hc.not_nil
  have hsnd_mem : c.snd ∈ c.support :=
    List.mem_of_mem_tail (c.snd_mem_tail_support hnot_nil)
  have hxsnd_ne : x ≠ c.snd :=
    (c.adj_snd hnot_nil).ne
  exact (Set.one_lt_ncard (s := {v : V | v ∈ c.support})).mpr
    ⟨x, c.start_mem_support, c.snd, hsnd_mem, hxsnd_ne⟩

theorem two_connected_component_boundary_cycle_atLeast_two
    [Fintype V]
    (h_two_connected : IsTwoConnected G)
    {A : Set V}
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (hA_nonempty : A.Nonempty)
    (hA_disjoint_cycle : Disjoint A {v : V | v ∈ c.support})
    (hclosed :
      forall a : V, a ∈ A -> forall b : V, G.Adj a b ->
        b ∈ A ∨ b ∈ {v : V | v ∈ c.support}) :
    2 <=
      ({v : V | v ∈ {w : V | w ∈ c.support} ∧
        Exists fun a : V => a ∈ A ∧ G.Adj a v}).ncard := by
  exact h_two_connected.boundary_ncard_ge_two
    hA_nonempty hA_disjoint_cycle (cycle_support_ncard_gt_one c hc) hclosed

theorem two_connected_complement_component_has_two_cycle_attachments
    [Fintype V]
    (h_two_connected : IsTwoConnected G)
    {A : Set V}
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (hA_nonempty : A.Nonempty)
    (hA_subset_cycle_compl : A ⊆ {v : V | v ∈ c.support}ᶜ)
    (hcomponent_closed :
      forall a : V, a ∈ A -> forall b : V,
        b ∈ {v : V | v ∈ c.support}ᶜ -> G.Adj a b -> b ∈ A) :
    2 <=
      ({v : V | v ∈ {w : V | w ∈ c.support} ∧
        Exists fun a : V => a ∈ A ∧ G.Adj a v}).ncard := by
  refine two_connected_component_boundary_cycle_atLeast_two
    (G := G) h_two_connected c hc hA_nonempty ?_ ?_
  · rw [Set.disjoint_left]
    intro a haA ha_cycle
    exact hA_subset_cycle_compl haA ha_cycle
  · intro a haA b hab
    by_cases hb_cycle : b ∈ {v : V | v ∈ c.support}
    · exact Or.inr hb_cycle
    · exact Or.inl (hcomponent_closed a haA b hb_cycle hab)

theorem exists_dominating_K4_model_of_cycle_complement_connected
    (L : Finset V)
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (hcycle_avoids_L : forall v : V, v ∈ c.support -> v ∉ L)
    (hcompl_connected : (G.induce ({v : V | v ∈ c.support}ᶜ)).Connected)
    (hcompl_dominates_cycle :
      forall v : V, v ∈ c.support ->
        Exists fun u : V => u ∈ ({w : V | w ∈ c.support}ᶜ) ∧ G.Adj u v) :
    Exists fun T : DominatingK4Model G =>
      forall v : V, v ∈ L -> v ∈ (T.branch (0 : Fin 4)).verts := by
  refine exists_dominating_K4_model_of_connected_set_dominating_cycle
    (G := G) L ({v : V | v ∈ c.support}ᶜ) hcompl_connected ?_ c hc ?_
    hcompl_dominates_cycle
  · intro v hvL hv_cycle
    exact hcycle_avoids_L v (by simpa using hv_cycle) hvL
  · rw [Set.disjoint_left]
    intro v hv_compl hv_cycle
    exact hv_compl hv_cycle

theorem exists_dominating_K4_model_of_induced_cycle_complement_connected
    [Fintype V] [DecidableRel G.Adj]
    (L : Finset V)
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (hcycle_avoids_L : forall v : V, v ∈ c.support -> v ∉ L)
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L)
    (hcompl_connected : (G.induce ({v : V | v ∈ c.support}ᶜ)).Connected)
    (hinside :
      forall v : V, v ∈ c.support ->
        (G.neighborSet v ∩ {w : V | w ∈ c.support}).ncard <= 2) :
    Exists fun T : DominatingK4Model G =>
      forall v : V, v ∈ L -> v ∈ (T.branch (0 : Fin 4)).verts := by
  exact exists_dominating_K4_model_of_cycle_complement_connected
    (G := G) L c hc hcycle_avoids_L hcompl_connected
    (cycle_complement_dominates_of_inside_neighbors_atMost_two
      (G := G) L c hcycle_avoids_L h_low_degree_in_L hinside)

theorem exists_dominating_K4_model_of_chordless_cycle_complement_connected
    [Fintype V] [DecidableRel G.Adj]
    (L : Finset V)
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (hcycle_avoids_L : forall v : V, v ∈ c.support -> v ∉ L)
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L)
    (hcompl_connected : (G.induce ({v : V | v ∈ c.support}ᶜ)).Connected)
    (hchordless :
      forall {u v : V}, u ∈ c.support -> v ∈ c.support ->
        G.Adj u v -> c.toSubgraph.Adj u v) :
    Exists fun T : DominatingK4Model G =>
      forall v : V, v ∈ L -> v ∈ (T.branch (0 : Fin 4)).verts := by
  exact exists_dominating_K4_model_of_induced_cycle_complement_connected
    (G := G) L c hc hcycle_avoids_L h_low_degree_in_L hcompl_connected
    (cycle_inside_neighbors_atMost_two_of_chordless
      (G := G) c hc hchordless)

theorem exists_dominating_K4_model_of_walk_chordless_cycle_complement_connected
    [Fintype V] [DecidableRel G.Adj]
    (L : Finset V)
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (hcycle_avoids_L : forall v : V, v ∈ c.support -> v ∉ L)
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L)
    (hcompl_connected : (G.induce ({v : V | v ∈ c.support}ᶜ)).Connected)
    (hchordless : c.IsChordless) :
    Exists fun T : DominatingK4Model G =>
      forall v : V, v ∈ L -> v ∈ (T.branch (0 : Fin 4)).verts := by
  exact exists_dominating_K4_model_of_chordless_cycle_complement_connected
    (G := G) L c hc hcycle_avoids_L h_low_degree_in_L hcompl_connected
    (fun hu hv hadj =>
      Schematic.Math.GraphTheory.Walk.IsChordless.toSubgraph_adj_of_adj hchordless hu hv hadj)

end DominatingK4

end Schematic.Math.GraphTheory
