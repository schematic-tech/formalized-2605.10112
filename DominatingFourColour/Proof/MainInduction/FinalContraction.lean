import DominatingFourColour.Proof.MainInduction.Counterexample

/-! The final neighborhood contraction and its coloring lift. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def finalFarNeighbors
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) : Set V :=
  {m : V | G.Adj (u : V) m ∧ m ∉ ({v1} : Set V) ∪ G.neighborSet v1}

def finalFiberSet
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) : Set V :=
  ({v1} : Set V) ∪ finalFarNeighbors G v1 u

def finalCollapsedSet
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) : Set V :=
  insert (u : V) (finalFiberSet G v1 u)

def finalContractionSubgraph
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) : G.Subgraph :=
  (⊤ : G.Subgraph).induce (finalCollapsedSet G v1 u)

@[simp]
theorem finalContractionSubgraph_verts
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) :
    (finalContractionSubgraph G v1 u).verts = finalCollapsedSet G v1 u := rfl

theorem final_v1_mem_collapsed
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) :
    v1 ∈ finalCollapsedSet G v1 u := by
  simp [finalCollapsedSet, finalFiberSet]

theorem final_u_mem_collapsed
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) :
    (u : V) ∈ finalCollapsedSet G v1 u := by
  simp [finalCollapsedSet]

theorem final_second_not_mem_collapsed
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (u : G.neighborSet v1)
    (hu_ne_v2 : (u : V) ≠ v2) :
    v2 ∉ finalCollapsedSet G v1 u := by
  classical
  intro hv
  simp [finalCollapsedSet, finalFiberSet, finalFarNeighbors] at hv
  rcases hv with hv_u | hv_v1 | hv_far
  · exact hu_ne_v2 hv_u.symm
  · exact edge.ne' hv_v1
  · exact hv_far.2.2 edge

theorem finalContractionSubgraph_connected
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) :
    (finalContractionSubgraph G v1 u).coe.Connected := by
  classical
  let H : G.Subgraph := finalContractionSubgraph G v1 u
  have huH : (u : V) ∈ H.verts := by
    simp [H, finalContractionSubgraph, finalCollapsedSet]
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨(u : V), huH⟩, ?_⟩
  intro x
  rcases x with ⟨x, hxH⟩
  have hx : x ∈ finalCollapsedSet G v1 u := by
    simpa [H, finalContractionSubgraph] using hxH
  simp [finalCollapsedSet, finalFiberSet, finalFarNeighbors] at hx
  rcases hx with hx_u | hx_v1 | hx_far
  · subst x
    exact SimpleGraph.Reachable.rfl
  · subst x
    apply SimpleGraph.Adj.reachable
    change H.Adj (u : V) v1
    simpa [H, finalContractionSubgraph, finalCollapsedSet, finalFiberSet] using u.2.symm
  · apply SimpleGraph.Adj.reachable
    change H.Adj (u : V) x
    simp [H, finalContractionSubgraph, finalCollapsedSet, finalFiberSet,
      finalFarNeighbors, hx_far]

noncomputable def finalCollapse
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) : GraphContraction G :=
  GraphContraction.collapseSubgraph G
    (finalContractionSubgraph G v1 u)
    (finalContractionSubgraph_connected G v1 u)

theorem finalCollapse_map_v1
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) :
    (finalCollapse G v1 u).map v1 =
      (none : (finalCollapse G v1 u).Target) := by
  classical
  exact GraphContraction.collapseSubgraph_map_eq_none_of_mem G
    (finalContractionSubgraph G v1 u)
    (finalContractionSubgraph_connected G v1 u)
    (by simp [finalContractionSubgraph, final_v1_mem_collapsed])

theorem finalCollapse_map_v2
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (u : G.neighborSet v1)
    (hu_ne_v2 : (u : V) ≠ v2) :
    (finalCollapse G v1 u).map v2 =
      some (⟨v2, by
        simpa [finalContractionSubgraph] using
          final_second_not_mem_collapsed (G := G) edge u hu_ne_v2⟩ :
        {v : V // v ∉ (finalContractionSubgraph G v1 u).verts}) := by
  classical
  exact GraphContraction.collapseSubgraph_map_eq_some_of_not_mem G
    (finalContractionSubgraph G v1 u)
    (finalContractionSubgraph_connected G v1 u)
    (by
      simpa [finalContractionSubgraph] using
        final_second_not_mem_collapsed (G := G) edge u hu_ne_v2)

theorem finalCollapse_pair_adj
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (u : G.neighborSet v1)
    (hu_ne_v2 : (u : V) ≠ v2) :
    (finalCollapse G v1 u).graph.Adj
      ((finalCollapse G v1 u).map v1)
      ((finalCollapse G v1 u).map v2) := by
  classical
  let Cq : GraphContraction G := finalCollapse G v1 u
  have hv1_map :
      Cq.map v1 = (none : Cq.Target) := by
    simpa [Cq] using finalCollapse_map_v1 G v1 u
  have hv2_map :
      Cq.map v2 =
        some (⟨v2, by
          simpa [finalContractionSubgraph] using
            final_second_not_mem_collapsed (G := G) edge u hu_ne_v2⟩ :
          {v : V // v ∉ (finalContractionSubgraph G v1 u).verts}) := by
    simpa [Cq] using finalCollapse_map_v2 (G := G) edge u hu_ne_v2
  have hmap_ne : Cq.map v1 ≠ Cq.map v2 := by
    rw [hv1_map, hv2_map]
    simp
  rcases Cq.map_adj edge with hsame | hadj
  · exact False.elim (hmap_ne hsame)
  · exact hadj

theorem counterexample_final_collapse_pair_no_compatible_model
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge))
    (u : G.neighborSet v1)
    (hu_ne_v2 : (u : V) ≠ v2) :
    let Cq : GraphContraction G := finalCollapse G v1 u
    let edgeq : Cq.graph.Adj (Cq.map v1) (Cq.map v2) :=
      finalCollapse_pair_adj (G := G) edge u hu_ne_v2
    Not (CompatibleDominatingK5Model (.pair (Cq.map v1) (Cq.map v2) edgeq)) := by
  classical
  intro Cq edgeq hmodel
  have hfirst :
      (OrderedClique.pair (Cq.map v1) (Cq.map v2) edgeq).first? =
        some (none : Cq.Target) := by
    change some (Cq.map v1) = some (none : Cq.Target)
    rw [show Cq.map v1 = (none : Cq.Target) by
      simpa [Cq] using finalCollapse_map_v1 G v1 u]
    rfl
  exact C.no_compatible_model
    (contraction_lifts_first_branch_of_collapse
      (G := G)
      (L := OrderedClique.pair v1 v2 edge)
      (H1 := finalContractionSubgraph G v1 u)
      (hH1_connected := finalContractionSubgraph_connected G v1 u)
      (Lq := OrderedClique.pair (Cq.map v1) (Cq.map v2) edgeq)
      (himage := OrderedCliqueContractionImage.pair_uncollapsed edge edgeq)
      hfirst hmodel)

noncomputable instance finalCollapseTargetFintype
    [Fintype V]
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) :
    Fintype (finalCollapse G v1 u).Target := by
  classical
  dsimp [finalCollapse, GraphContraction.collapseSubgraph, GraphContraction.ofMap]
  infer_instance

theorem finalCollapse_target_card_lt
    [Fintype V]
    (G : SimpleGraph V) (v1 : V) (u : G.neighborSet v1) :
    Fintype.card (finalCollapse G v1 u).Target < Fintype.card V := by
  simpa [finalCollapse] using
    GraphContraction.collapseSubgraph_target_card_lt G
      (finalContractionSubgraph G v1 u)
      (finalContractionSubgraph_connected G v1 u)
      (final_v1_mem_collapsed G v1 u)
      (final_u_mem_collapsed G v1 u) u.2.ne

theorem counterexample_far_neighbors_independent
    [Fintype V]
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge))
    (u : G.neighborSet v1)
    (hu_ne_v2 : (u : V) ≠ v2) :
    let M : Set V :=
      {m : V | G.Adj (u : V) m ∧ m ∉ ({v1} : Set V) ∪ G.neighborSet v1}
    forall a : V, a ∈ M ->
      forall b : V, b ∈ M -> a ≠ b -> Not (G.Adj a b) := by
  classical
  intro M a ha b hb hab_ne hab
  have htriangle_free : Not (HasTriangleDisjointFromPair G v1 v2) :=
    counterexample_triangle_free_off_L C
  have hu_ne_v1 : (u : V) ≠ v1 := u.2.ne'
  have ha_ne_v1 : a ≠ v1 := by
    intro h
    exact ha.2 (Or.inl (by simp [h]))
  have hb_ne_v1 : b ≠ v1 := by
    intro h
    exact hb.2 (Or.inl (by simp [h]))
  have ha_ne_v2 : a ≠ v2 := by
    intro h
    exact ha.2 (Or.inr (by simpa [h] using edge))
  have hb_ne_v2 : b ≠ v2 := by
    intro h
    exact hb.2 (Or.inr (by simpa [h] using edge))
  exact htriangle_free
    ⟨(u : V), a, b,
      ⟨ha.1.ne, hab_ne, hb.1.ne', ha.1, hab, hb.1.symm⟩,
      hu_ne_v1, hu_ne_v2, ha_ne_v1, ha_ne_v2, hb_ne_v1, hb_ne_v2⟩

theorem counterexample_far_neighbors_union_first_independent
    [Fintype V]
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge))
    (u : G.neighborSet v1)
    (hu_ne_v2 : (u : V) ≠ v2) :
    let M : Set V :=
      {m : V | G.Adj (u : V) m ∧ m ∉ ({v1} : Set V) ∪ G.neighborSet v1}
    let S : Set V := ({v1} : Set V) ∪ M
    forall a : V, a ∈ S ->
      forall b : V, b ∈ S -> a ≠ b -> Not (G.Adj a b) := by
  classical
  intro M S a ha b hb hab_ne hab
  rcases ha with ha_v1 | ha_M
  · rcases hb with hb_v1 | hb_M
    · exact hab_ne (ha_v1.trans hb_v1.symm)
    · subst a
      exact hb_M.2 (Or.inr hab)
  · rcases hb with hb_v1 | hb_M
    · subst b
      exact ha_M.2 (Or.inr hab.symm)
    · exact counterexample_far_neighbors_independent C u hu_ne_v2
        a ha_M b hb_M hab_ne hab

theorem final_outside_neighbors_card_le_of_neighbor_subgraph_degree
    [Fintype V] [DecidableRel G.Adj]
    {v1 : V}
    (u : G.neighborSet v1)
    (hdeg : (G.induce (G.neighborSet v1)).degree u <= 2) :
    let M : Set V :=
      {m : V | G.Adj (u : V) m ∧ m ∉ ({v1} : Set V) ∪ G.neighborSet v1}
    let S : Set V := ({v1} : Set V) ∪ M
    (G.neighborSet (u : V) \ S).ncard <= 2 := by
  classical
  intro M S
  let Nset : Set V := G.neighborSet v1
  let Ngraph : SimpleGraph Nset := G.induce Nset
  let imageN : Set V := Subtype.val '' (Ngraph.neighborSet u)
  have hsubset : G.neighborSet (u : V) \ S ⊆ imageN := by
    intro x hx
    have hxu : G.Adj (u : V) x := hx.1
    have hx_not_S : x ∉ S := hx.2
    have hx_ne_v1 : x ≠ v1 := by
      intro hxv1
      exact hx_not_S (Or.inl (by simp [hxv1]))
    have hxN : x ∈ G.neighborSet v1 := by
      by_contra hxN
      have hxM : x ∈ M := by
        refine ⟨hxu, ?_⟩
        intro hx_union
        rcases hx_union with hxv1_mem | hxN_mem
        · exact hx_ne_v1 (by simpa using hxv1_mem)
        · exact hxN hxN_mem
      exact hx_not_S (Or.inr hxM)
    refine ⟨(⟨x, hxN⟩ : Nset), ?_, rfl⟩
    exact hxu
  have himage_card : imageN.ncard = (Ngraph.neighborSet u).ncard := by
    simpa [imageN] using
      (Set.ncard_image_of_injective (Ngraph.neighborSet u) Subtype.val_injective)
  have hdegree_card : (Ngraph.neighborSet u).ncard = Ngraph.degree u := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  calc
    (G.neighborSet (u : V) \ S).ncard <= imageN.ncard :=
      Set.ncard_le_ncard hsubset
    _ = (Ngraph.neighborSet u).ncard := himage_card
    _ = Ngraph.degree u := hdegree_card
    _ <= 2 := hdeg

theorem counterexample_final_coloring_lift
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge))
    (u : G.neighborSet v1)
    (hu_ne_v2 : (u : V) ≠ v2) :
    let M : Set V :=
      {m : V | G.Adj (u : V) m ∧ m ∉ ({v1} : Set V) ∪ G.neighborSet v1}
    let S : Set V := ({v1} : Set V) ∪ M
    let Collapsed : Set V := insert (u : V) S
    let f : V -> Option {v : V // v ∉ Collapsed} := fun v =>
      if hv : v ∈ Collapsed then none else some ⟨v, hv⟩
    (G.neighborSet (u : V) \ S).ncard <= 2 ->
      (contractionTargetGraph G f).Colorable 4 -> G.Colorable 4 := by
  classical
  intro M S Collapsed f hneighbor_card hquot_color
  have hS_independent :
      forall a : V, a ∈ S ->
        forall b : V, b ∈ S -> a ≠ b -> Not (G.Adj a b) := by
    simpa [M, S] using
      counterexample_far_neighbors_union_first_independent C u hu_ne_v2
  refine colorable_of_contractionTarget_colorable_with_independent_fiber
    (G := G) f (none : Option {v : V // v ∉ Collapsed})
    (S := S) (u := (u : V)) hS_independent ?_ ?_ ?_
    hneighbor_card hquot_color
  · intro v hvS
    simp [f, Collapsed, hvS]
  · intro v hvS hvu hmap
    have hvCollapsed : v ∉ Collapsed := by
      simp [Collapsed, hvu, hvS]
    simp [f, hvCollapsed] at hmap
  · intro a b haS hau hbS hbu hmap
    have haCollapsed : a ∉ Collapsed := by
      simp [Collapsed, hau, haS]
    have hbCollapsed : b ∉ Collapsed := by
      simp [Collapsed, hbu, hbS]
    simp [f, haCollapsed, hbCollapsed] at hmap
    exact hmap

theorem counterexample_final_quotient_not_four_colorable
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge))
    (u : G.neighborSet v1)
    (hu_ne_v2 : (u : V) ≠ v2)
    (hdeg : (G.induce (G.neighborSet v1)).degree u <= 2) :
    let M : Set V :=
      {m : V | G.Adj (u : V) m ∧ m ∉ ({v1} : Set V) ∪ G.neighborSet v1}
    let S : Set V := ({v1} : Set V) ∪ M
    let Collapsed : Set V := insert (u : V) S
    let f : V -> Option {v : V // v ∉ Collapsed} := fun v =>
      if hv : v ∈ Collapsed then none else some ⟨v, hv⟩
    Not ((contractionTargetGraph G f).Colorable 4) := by
  classical
  intro M S Collapsed f hquot_color
  have hneighbor_card : (G.neighborSet (u : V) \ S).ncard <= 2 := by
    simpa [M, S] using
      final_outside_neighbors_card_le_of_neighbor_subgraph_degree
        (G := G) (v1 := v1) u hdeg
  exact C.not_four_colorable
    (counterexample_final_coloring_lift C u hu_ne_v2 hneighbor_card hquot_color)

theorem counterexample_final_collapse_not_four_colorable
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge))
    (u : G.neighborSet v1)
    (hu_ne_v2 : (u : V) ≠ v2)
    (hdeg : (G.induce (G.neighborSet v1)).degree u <= 2) :
    Not ((finalCollapse G v1 u).graph.Colorable 4) := by
  classical
  simpa [finalCollapse, GraphContraction.collapseSubgraph, GraphContraction.ofMap,
    finalContractionSubgraph, finalCollapsedSet, finalFiberSet, finalFarNeighbors] using
      counterexample_final_quotient_not_four_colorable C u hu_ne_v2 hdeg

theorem counterexample_exists_final_quotient_obstruction
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge)) :
    Exists fun u : G.neighborSet v1 =>
      (u : V) ≠ v2 ∧
        (G.induce (G.neighborSet v1)).degree u <= 2 ∧
          let M : Set V :=
            {m : V | G.Adj (u : V) m ∧ m ∉ ({v1} : Set V) ∪ G.neighborSet v1}
          let S : Set V := ({v1} : Set V) ∪ M
          let Collapsed : Set V := insert (u : V) S
          let f : V -> Option {v : V // v ∉ Collapsed} := fun v =>
            if hv : v ∈ Collapsed then none else some ⟨v, hv⟩
          Not ((contractionTargetGraph G f).Colorable 4) := by
  obtain ⟨u, hu_ne_v2, hdeg⟩ :=
    counterexample_neighbor_subgraph_has_low_degree_vertex C
  exact ⟨u, hu_ne_v2, hdeg,
    counterexample_final_quotient_not_four_colorable C u hu_ne_v2 hdeg⟩

theorem counterexample_exists_final_collapse_obstruction
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge)) :
    Exists fun u : G.neighborSet v1 =>
      (u : V) ≠ v2 ∧
        (G.induce (G.neighborSet v1)).degree u <= 2 ∧
          Fintype.card (finalCollapse G v1 u).Target < Fintype.card V ∧
            Not ((finalCollapse G v1 u).graph.Colorable 4) ∧
              forall hu_ne_v2' : (u : V) ≠ v2,
                let Cq : GraphContraction G := finalCollapse G v1 u
                let edgeq : Cq.graph.Adj (Cq.map v1) (Cq.map v2) :=
                  finalCollapse_pair_adj (G := G) edge u hu_ne_v2'
                Not (CompatibleDominatingK5Model
                  (.pair (Cq.map v1) (Cq.map v2) edgeq)) := by
  obtain ⟨u, hu_ne_v2, hdeg⟩ :=
    counterexample_neighbor_subgraph_has_low_degree_vertex C
  refine ⟨u, hu_ne_v2, hdeg, finalCollapse_target_card_lt G v1 u,
    counterexample_final_collapse_not_four_colorable C u hu_ne_v2 hdeg, ?_⟩
  intro hu_ne_v2'
  exact counterexample_final_collapse_pair_no_compatible_model C u hu_ne_v2'

theorem counterexample_absurd_of_final_collapse_minimality
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge))
    (hminimal_final :
      forall u : G.neighborSet v1,
        (u : V) ≠ v2 ->
          (G.induce (G.neighborSet v1)).degree u <= 2 ->
            Fintype.card (finalCollapse G v1 u).Target < Fintype.card V ->
              (forall hu_ne_v2' : (u : V) ≠ v2,
                let Cq : GraphContraction G := finalCollapse G v1 u
                let edgeq : Cq.graph.Adj (Cq.map v1) (Cq.map v2) :=
                  finalCollapse_pair_adj (G := G) edge u hu_ne_v2'
                Not (CompatibleDominatingK5Model
                  (.pair (Cq.map v1) (Cq.map v2) edgeq))) ->
                (finalCollapse G v1 u).graph.Colorable 4) :
    False := by
  obtain ⟨u, hu_ne_v2, hdeg, hcard_lt, hnot_colorable, hno_model⟩ :=
    counterexample_exists_final_collapse_obstruction C
  exact hnot_colorable
    (hminimal_final u hu_ne_v2 hdeg hcard_lt hno_model)

theorem final_collapse_colorable_of_smaller_induction
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (u : G.neighborSet v1)
    (hu_ne_v2 : (u : V) ≠ v2)
    (hcard_lt : Fintype.card (finalCollapse G v1 u).Target < Fintype.card V)
    (hno_model :
      forall hu_ne_v2' : (u : V) ≠ v2,
        let Cq : GraphContraction G := finalCollapse G v1 u
        let edgeq : Cq.graph.Adj (Cq.map v1) (Cq.map v2) :=
          finalCollapse_pair_adj (G := G) edge u hu_ne_v2'
        Not (CompatibleDominatingK5Model
          (.pair (Cq.map v1) (Cq.map v2) edgeq))) :
    (finalCollapse G v1 u).graph.Colorable 4 := by
  classical
  let Cq : GraphContraction G := finalCollapse G v1 u
  let edgeq : Cq.graph.Adj (Cq.map v1) (Cq.map v2) :=
    finalCollapse_pair_adj (G := G) edge u hu_ne_v2
  rcases hIH Cq.graph hcard_lt
      (OrderedClique.pair (Cq.map v1) (Cq.map v2) edgeq) with hcolor | hmodel
  · exact hcolor
  · exact False.elim ((hno_model hu_ne_v2) hmodel)

theorem delete_vertex_colorable_of_smaller_induction
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hno_model : Not (CompatibleDominatingK5Model L))
    (v : V) :
    (G.induce ({v} : Set V)ᶜ).Colorable 4 := by
  classical
  let A : Set V := ({v} : Set V)ᶜ
  have hcard_lt : Fintype.card A < Fintype.card V := by
    have hv_not_A : v ∉ A := by simp [A]
    exact
      (Fintype.card_subtype_lt (p := fun x : V => x ∈ A) (x := v) hv_not_A)
  rcases hIH (G.induce A) hcard_lt (L.restrictToSet A) with hcolor | hmodel
  · simpa [A] using hcolor
  · exact False.elim
      (hno_model
          (deletion_lifts_compatible_model
            (G := G) L A (L.restrictToSet A)
            (OrderedCliqueDeletionRestriction.restrictToSet A L) hmodel))

theorem induce_colorable_of_smaller_induction_global_no_model
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (A : Set V)
    (hA_card_lt : Nat.card A < Nat.card V)
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    (G.induce A).Colorable 4 := by
  classical
  letI : Fintype A := A.toFinite.fintype
  have hcard_lt : Fintype.card A < Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using hA_card_lt
  rcases hIH (G.induce A) hcard_lt (L.restrictToSet A) with hcolor | hmodel
  · exact hcolor
  · exact False.elim
      (hno_model
        (deletion_lifts_compatible_model
          (G := G) L A (L.restrictToSet A)
          (OrderedCliqueDeletionRestriction.restrictToSet A L) hmodel))

theorem exists_pair_extension_no_compatible_of_smaller_induction
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    Exists fun L' : OrderedClique G =>
      L.InitialSegment L' ∧ L'.length = 2 ∧
        Not (CompatibleDominatingK5Model L') ∧
          forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4 := by
  classical
  have hvertex_minimal_L :
      forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4 :=
    delete_vertex_colorable_of_smaller_induction
      (G := G) hIH hno_model
  obtain ⟨L', hinit, hlen, hno_model_L'⟩ :=
    exists_pair_extension_no_compatible
      (G := G) hnot_four_colorable hvertex_minimal_L hno_model
  have hvertex_minimal_L' :
      forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4 :=
    delete_vertex_colorable_of_smaller_induction
      (G := G) hIH hno_model_L'
  exact ⟨L', hinit, hlen, hno_model_L', hvertex_minimal_L'⟩


end Schematic.Math.GraphTheory
