import DominatingFourColour.Proof.DominatingK4.Complete

/-!
Producing a shortest chordless cycle outside the distinguished low-degree clique.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace DominatingK4

theorem no_outside_vertex_with_small_induced_degree
    [Fintype V] [DecidableRel G.Adj]
    (L : Finset V)
    [Fintype ((L : Set V)ᶜ : Set V)]
    [DecidableRel (G.induce ((L : Set V)ᶜ)).Adj]
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L)
    {v : V}
    (hv : v ∈ ((L : Set V)ᶜ : Set V))
    (hdegree_bound :
      (G.induce ((L : Set V)ᶜ)).degree ⟨v, hv⟩ + L.card <= 2) :
    False := by
  have hdegree_le :
      G.degree v <=
        (G.induce ((L : Set V)ᶜ)).degree ⟨v, hv⟩ + L.card := by
    have h :=
      degree_le_induce_compl_degree_add_ncard
        (G := G) (A := (L : Set V)) hv
    simpa [Set.ncard_coe_finset] using h
  have hv_low : G.degree v <= 2 := le_trans hdegree_le hdegree_bound
  exact hv (by simpa using h_low_degree_in_L v hv_low)

theorem leaf_neighborSet_inter_L_card_ge_two
    [Fintype V] [DecidableRel G.Adj]
    (L : Finset V)
    [Fintype (((L : Set V)ᶜ) : Set V)]
    [DecidableRel (G.induce ((L : Set V)ᶜ)).Adj]
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L)
    {v : ((L : Set V)ᶜ : Set V)}
    (hv_degree : (G.induce ((L : Set V)ᶜ)).degree v = 1) :
    2 <= (G.neighborSet (v : V) ∩ (L : Set V)).ncard := by
  classical
  have hv_not_low : ¬ G.degree (v : V) <= 2 := by
    intro hv_low
    exact v.2 (by simpa using h_low_degree_in_L v hv_low)
  have hv_degree_ge : 3 <= G.degree (v : V) := by omega
  have hdegree_bound :
      G.degree (v : V) <=
        (G.induce ((L : Set V)ᶜ)).degree v +
          (G.neighborSet (v : V) ∩ (L : Set V)).ncard := by
    simpa using
      degree_le_induce_compl_degree_add_neighbor_inter_ncard
        (G := G) (A := (L : Set V)) (v := (v : V)) v.2
  omega

theorem all_L_adjacent_to_leaf
    [Fintype V] [DecidableRel G.Adj]
    (L : Finset V)
    (h_card_L : L.card <= 2)
    [Fintype (((L : Set V)ᶜ) : Set V)]
    [DecidableRel (G.induce ((L : Set V)ᶜ)).Adj]
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L)
    {v : ((L : Set V)ᶜ : Set V)}
    (hv_degree : (G.induce ((L : Set V)ᶜ)).degree v = 1) :
    forall a : V, a ∈ L -> G.Adj (v : V) a := by
  classical
  intro a haL
  let N : Set V := G.neighborSet (v : V) ∩ (L : Set V)
  have hN_sub_L : N ⊆ (L : Set V) := by
    intro x hx
    exact hx.2
  have hN_card_ge : 2 <= N.ncard :=
    leaf_neighborSet_inter_L_card_ge_two
      (G := G) L h_low_degree_in_L hv_degree
  have hL_card_le : (L : Set V).ncard <= 2 := by
    rw [Set.ncard_coe_finset]
    exact h_card_L
  have hL_subset_N : (L : Set V) ⊆ N := by
    have hL_le_N : (L : Set V).ncard <= N.ncard := by omega
    have hN_eq_L : N = (L : Set V) :=
      Set.eq_of_subset_of_ncard_le hN_sub_L hL_le_N
    intro x hx
    rw [hN_eq_L]
    exact hx
  exact (hL_subset_N haL).1

theorem induce_compl_not_acyclic
    [Fintype V] [DecidableRel G.Adj]
    (h_card : 4 <= Fintype.card V)
    (L : Finset V)
    (h_clique : G.IsClique (L : Set V))
    (h_card_L : L.card <= 2)
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L)
    (h_high_degree_L_singleton :
      (Exists fun v : V => v ∈ L ∧ 3 <= G.degree v) -> L.card = 1) :
    Not ((G.induce ((L : Set V)ᶜ)).IsAcyclic) := by
  classical
  let A : Set V := (L : Set V)
  letI : Fintype (Aᶜ : Set V) := (Aᶜ).toFinite.fintype
  haveI : DecidableRel (G.induce Aᶜ).Adj := Classical.decRel _
  intro hacyclic
  have hlt_univ : L.card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨x, _hx_univ, hxL⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt_univ
  have hxA : x ∈ Aᶜ := by
    simpa [A] using hxL
  haveI : Nonempty (Aᶜ : Set V) := ⟨⟨x, hxA⟩⟩
  have hno_isolated :
      forall v : (Aᶜ : Set V), (G.induce Aᶜ).degree v ≠ 0 := by
    intro v hv0
    have hbound : (G.induce Aᶜ).degree v + L.card <= 2 := by
      rw [hv0]
      omega
    exact no_outside_vertex_with_small_induced_degree
      (G := G) L h_low_degree_in_L (v := (v : V)) (by
        simp [A, v.2]) (by
        simpa [A] using hbound)
  obtain ⟨u, v, huv, hu_degree, hv_degree⟩ :=
    exists_two_distinct_degree_one_of_finite_acyclic_no_isolated
      (G := G.induce Aᶜ) hacyclic hno_isolated
  have hL_card_ge_two : 2 <= L.card := by
    have hN_ge :
        2 <= (G.neighborSet (u : V) ∩ (L : Set V)).ncard :=
      leaf_neighborSet_inter_L_card_ge_two
        (G := G) L h_low_degree_in_L (by
          simpa [A] using hu_degree)
    have hN_le :
        (G.neighborSet (u : V) ∩ (L : Set V)).ncard <= L.card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard (by
        intro y hy
        exact hy.2)
    omega
  have hL_card_eq_two : L.card = 2 := le_antisymm h_card_L hL_card_ge_two
  obtain ⟨a, b, hab, hL_eq⟩ := Finset.card_eq_two.mp hL_card_eq_two
  have haL : a ∈ L := by
    rw [hL_eq]
    simp
  have hbL : b ∈ L := by
    rw [hL_eq]
    simp
  have hua : G.Adj (u : V) a :=
    all_L_adjacent_to_leaf
      (G := G) L h_card_L h_low_degree_in_L (by
        simpa [A] using hu_degree) a haL
  have hva : G.Adj (v : V) a :=
    all_L_adjacent_to_leaf
      (G := G) L h_card_L h_low_degree_in_L (by
        simpa [A] using hv_degree) a haL
  have hba : G.Adj b a := (h_clique hbL haL hab.symm)
  have hu_ne_v : (u : V) ≠ (v : V) := by
    intro huv_val
    exact huv (Subtype.ext huv_val)
  have hb_ne_u : b ≠ (u : V) := by
    intro h
    exact u.2 (by simpa [h] using hbL)
  have hb_ne_v : b ≠ (v : V) := by
    intro h
    exact v.2 (by simpa [h] using hbL)
  have hdeg_a : 3 <= G.degree a :=
    degree_atLeast_three_of_three_neighbors
      (G := G) hua.symm hva.symm hba.symm
      hu_ne_v (by exact hb_ne_u.symm) (by exact hb_ne_v.symm)
  have hL_card_one : L.card = 1 :=
    h_high_degree_L_singleton ⟨a, haL, hdeg_a⟩
  omega

theorem exists_cycle_of_not_acyclic
    {H : SimpleGraph V}
    (h_not_acyclic : Not H.IsAcyclic) :
    Exists fun x : V => Exists fun c : H.Walk x x => c.IsCycle := by
  rw [SimpleGraph.IsAcyclic] at h_not_acyclic
  push Not at h_not_acyclic
  exact h_not_acyclic

theorem exists_cycle_disjoint_from_finset_of_not_induce_compl_acyclic
    (L : Finset V)
    (h_not_acyclic : Not ((G.induce ((L : Set V)ᶜ)).IsAcyclic)) :
    Exists fun x : V =>
      Exists fun c : G.Walk x x =>
        c.IsCycle ∧ forall v : V, v ∈ c.support -> v ∉ L := by
  classical
  obtain ⟨x, c, hc⟩ :=
    exists_cycle_of_not_acyclic
      (H := G.induce ((L : Set V)ᶜ)) h_not_acyclic
  let f : G.induce ((L : Set V)ᶜ) →g G :=
    inducedSubgraphHom ((L : Set V)ᶜ)
  refine ⟨x, c.map f, ?_, ?_⟩
  · exact hc.map Subtype.val_injective
  · intro v hv hvL
    change v ∈ (c.map f).support at hv
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hv
    rcases hv with ⟨w, _hw, rfl⟩
    exact w.2 (by simpa using hvL)

theorem exists_shortest_cycle_disjoint_from_finset_of_not_induce_compl_acyclic
    (L : Finset V)
    (h_not_acyclic : Not ((G.induce ((L : Set V)ᶜ)).IsAcyclic)) :
    Exists fun x : V =>
      Exists fun c : G.Walk x x =>
        c.IsCycle ∧
          (forall v : V, v ∈ c.support -> v ∉ L) ∧
            forall {y : V} (d : G.Walk y y),
              d.IsCycle ->
                (forall v : V, v ∈ d.support -> v ∉ L) ->
                  c.length <= d.length := by
  classical
  let P : Nat -> Prop := fun n =>
    Exists fun x : V =>
      Exists fun c : G.Walk x x =>
        c.IsCycle ∧
          (forall v : V, v ∈ c.support -> v ∉ L) ∧
            c.length = n
  have hP : Exists P := by
    obtain ⟨x, c, hc, havoid⟩ :=
      exists_cycle_disjoint_from_finset_of_not_induce_compl_acyclic
        (G := G) L h_not_acyclic
    exact ⟨c.length, x, c, hc, havoid, rfl⟩
  obtain ⟨x, c, hc, havoid, hlength⟩ := Nat.find_spec hP
  refine ⟨x, c, hc, havoid, ?_⟩
  intro y d hd havoid_d
  have hdP : P d.length := ⟨y, d, hd, havoid_d, rfl⟩
  have hmin := Nat.find_min' hP hdP
  simpa [hlength] using hmin

theorem shortest_cycle_disjoint_from_finset_isChordless
    [DecidableEq V]
    (L : Finset V)
    {x : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (hcycle_avoids_L : forall v : V, v ∈ c.support -> v ∉ L)
    (hminimal :
      forall {y : V} (d : G.Walk y y),
        d.IsCycle ->
          (forall v : V, v ∈ d.support -> v ∉ L) ->
            c.length <= d.length) :
    c.IsChordless := by
  classical
  by_contra hnot_chordless
  obtain ⟨a, ha_cycle, b, hb_cycle, hab, hab_not_cycle⟩ :=
    (Walk.not_isChordless_iff_exists_adj_not_toSubgraph_adj
      (G := G) c).mp hnot_chordless
  obtain ⟨c', hc', hc'_shorter, hc'_support_subset⟩ :=
    Walk.exists_isCycle_of_cycle_chord
      (G := G) c hc ha_cycle hb_cycle hab hab_not_cycle
  have hc'_avoids_L :
      forall v : V, v ∈ c'.support -> v ∉ L := by
    intro v hv
    exact hcycle_avoids_L v (hc'_support_subset v hv)
  have hle := hminimal c' hc' hc'_avoids_L
  omega

end DominatingK4

end Schematic.Math.GraphTheory
