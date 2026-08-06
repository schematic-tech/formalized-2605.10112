import DominatingFourColour.Proof.DominatingK4.CycleModels

/-!
The two-connected cycle-rerouting branch of the dominating-K4 lemma.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace DominatingK4

/-- The cycle-rerouting case of the article's dominating-K4 lemma. -/
theorem lemma_dominating_K4_of_two_connected
    [Fintype V] [DecidableRel G.Adj]
    (h_two_connected : IsTwoConnected G)
    (h_card : 4 <= Fintype.card V)
    (L : Finset V)
    (h_clique : G.IsClique (L : Set V))
    (h_card_L : L.card <= 2)
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L)
    (h_high_degree_L_singleton :
      (Exists fun v : V => v ∈ L ∧ 3 <= G.degree v) -> L.card = 1) :
    Exists fun T : DominatingK4Model G =>
      forall v : V, v ∈ L -> v ∈ (T.branch (0 : Fin 4)).verts := by
  classical
  have h_not_forest :
      Not ((G.induce ((L : Set V)ᶜ)).IsAcyclic) :=
    induce_compl_not_acyclic
      (G := G) h_card L h_clique h_card_L
      h_low_degree_in_L h_high_degree_L_singleton
  obtain ⟨cycleBase0, cycle0, cycle0_isCycle, cycle0_avoids_L,
      cycle0_minimal⟩ :=
    exists_shortest_cycle_disjoint_from_finset_of_not_induce_compl_acyclic
      (G := G) L h_not_forest
  have cycle0_chordless : cycle0.IsChordless :=
    shortest_cycle_disjoint_from_finset_isChordless
      (G := G) L cycle0 cycle0_isCycle cycle0_avoids_L cycle0_minimal
  have cycle0_complement_dominates :
      forall v : V, v ∈ cycle0.support ->
        Exists fun u : V =>
          u ∈ ({w : V | w ∈ cycle0.support}ᶜ) ∧ G.Adj u v :=
    cycle_complement_dominates_of_chordless
      (G := G) L cycle0 cycle0_isCycle cycle0_avoids_L
      h_low_degree_in_L cycle0_chordless
  have hcompl0_nonempty :
      ({v : V | v ∈ cycle0.support}ᶜ : Set V).Nonempty := by
    obtain ⟨u, hu_compl, _huv⟩ :=
      cycle0_complement_dominates cycleBase0 cycle0.start_mem_support
    exact ⟨u, hu_compl⟩
  obtain ⟨Hcomp0, hL_Hcomp0⟩ :=
    exists_cycle_complement_component_containing_clique
      (G := G) L cycle0 cycle0_avoids_L h_clique hcompl0_nonempty
  let initialPair : CycleComponentPair G L := {
    root := cycleBase0
    cycle := cycle0
    isCycle := cycle0_isCycle
    avoids_L := cycle0_avoids_L
    component := Hcomp0
    L_in_component := hL_Hcomp0
  }
  obtain ⟨Best, hBest_max, hBest_min⟩ :=
    exists_maximal_minimal_cycle_component_pair
      (G := G) L ⟨initialPair⟩
  let cycleBase : V := Best.root
  let cycle : G.Walk cycleBase cycleBase := Best.cycle
  have cycle_isCycle : cycle.IsCycle := Best.isCycle
  have cycle_avoids_L : forall v : V, v ∈ cycle.support -> v ∉ L :=
    Best.avoids_L
  have cycle_chordless : cycle.IsChordless := by
    simpa [cycle] using
      maximal_minimal_cycle_component_pair_isChordless
        (G := G) Best hBest_max hBest_min
  by_cases hcompl_connected :
      (G.induce ({v : V | v ∈ cycle.support}ᶜ)).Connected
  · exact exists_dominating_K4_model_of_walk_chordless_cycle_complement_connected
      (G := G) L cycle cycle_isCycle cycle_avoids_L
      h_low_degree_in_L hcompl_connected cycle_chordless
  · -- Remaining: choose the maximal component of the cycle complement
    -- and run the paper's rerouting argument.
    have cycle_complement_dominates :
        forall v : V, v ∈ cycle.support ->
          Exists fun u : V =>
            u ∈ ({w : V | w ∈ cycle.support}ᶜ) ∧ G.Adj u v :=
      cycle_complement_dominates_of_chordless
        (G := G) L cycle cycle_isCycle cycle_avoids_L
        h_low_degree_in_L cycle_chordless
    let CycleCompl : Set V := {v : V | v ∈ cycle.support}ᶜ
    let Hcomp : (G.induce CycleCompl).ConnectedComponent := Best.component
    have hL_Hcomp :
        forall v : V, forall hvL : v ∈ L,
          (⟨v, by
            intro hv_cycle
            exact cycle_avoids_L v hv_cycle hvL⟩ : CycleCompl) ∈
            Hcomp.supp := by
      intro v hvL
      simpa [Hcomp, CycleCompl, cycle] using Best.L_in_component v hvL
    let Hset : Set V :=
      {v : V | Exists fun hv : v ∈ CycleCompl =>
        (⟨v, hv⟩ : CycleCompl) ∈ Hcomp.supp}
    have hH_connected : (G.induce Hset).Connected := by
      simpa [Hset, CycleCompl] using
        connectedComponent_support_as_base_connected (G := G) Hcomp
    have hL_subset_H : forall v : V, v ∈ L -> v ∈ Hset := by
      intro v hvL
      have hv_compl : v ∈ CycleCompl := by
        intro hv_cycle
        exact cycle_avoids_L v hv_cycle hvL
      refine ⟨hv_compl, ?_⟩
      simpa [CycleCompl] using hL_Hcomp v hvL
    have hH_nonempty : Hset.Nonempty := by
      obtain ⟨u, huH⟩ := Hcomp.nonempty_supp
      exact ⟨u, u.2, huH⟩
    have hH_subset_compl : Hset ⊆ CycleCompl := by
      intro v hv
      exact hv.choose
    have hH_component_closed :
        forall a : V, a ∈ Hset -> forall b : V,
          b ∈ CycleCompl -> G.Adj a b -> b ∈ Hset := by
      intro a ha b hb hab
      rcases ha with ⟨ha_compl, haH⟩
      refine ⟨hb, ?_⟩
      have hab_ind :
          (G.induce CycleCompl).Adj
            (⟨a, ha_compl⟩ : CycleCompl) ⟨b, hb⟩ := by
        exact hab
      exact Hcomp.mem_supp_of_adj_mem_supp haH hab_ind
    have hH_two_attachments :
        2 <=
          ({v : V | v ∈ {w : V | w ∈ cycle.support} ∧
            Exists fun a : V => a ∈ Hset ∧ G.Adj a v}).ncard :=
      two_connected_complement_component_has_two_cycle_attachments
        (G := G) h_two_connected cycle cycle_isCycle hH_nonempty
        hH_subset_compl hH_component_closed
    obtain ⟨y, hy_attach, z, hz_attach, hyz_ne⟩ :=
      (Set.one_lt_ncard
        (s := {v : V | v ∈ {w : V | w ∈ cycle.support} ∧
          Exists fun a : V => a ∈ Hset ∧ G.Adj a v})).mp
        (by omega : 1 <
          ({v : V | v ∈ {w : V | w ∈ cycle.support} ∧
            Exists fun a : V => a ∈ Hset ∧ G.Adj a v}).ncard)
    have hy_cycle : y ∈ cycle.support := hy_attach.1
    have hz_cycle : z ∈ cycle.support := hz_attach.1
    obtain ⟨hy_neighbor, hhyH, hhy_adj⟩ := hy_attach.2
    obtain ⟨hz_neighbor, hhzH, hhz_adj⟩ := hz_attach.2
    by_cases hH_dominates_cycle :
        forall v : V, v ∈ cycle.support ->
          Exists fun u : V => u ∈ Hset ∧ G.Adj u v
    · exact exists_dominating_K4_model_of_connected_set_dominating_cycle
        (G := G) L Hset hH_connected hL_subset_H
        cycle cycle_isCycle
        (by
          rw [Set.disjoint_left]
          intro v hvH hv_cycle
          exact hH_subset_compl hvH hv_cycle)
        hH_dominates_cycle
    ·
      push Not at hH_dominates_cycle
      obtain ⟨v, hv_cycle, hv_not_dominated_by_H⟩ :=
        hH_dominates_cycle
      obtain ⟨u, hu_compl, huv⟩ :=
        cycle_complement_dominates v hv_cycle
      let uCompl : CycleCompl := ⟨u, hu_compl⟩
      let Jcomp : (G.induce CycleCompl).ConnectedComponent :=
        (G.induce CycleCompl).connectedComponentMk uCompl
      have huJ : uCompl ∈ Jcomp.supp :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      have hJ_ne_H : Jcomp ≠ Hcomp := by
        intro hJH
        have huH : u ∈ Hset := by
          refine ⟨hu_compl, ?_⟩
          simpa [hJH] using huJ
        exact hv_not_dominated_by_H u huH huv
      let Jset : Set V :=
        {v : V | Exists fun hv : v ∈ CycleCompl =>
          (⟨v, hv⟩ : CycleCompl) ∈ Jcomp.supp}
      have hJ_connected : (G.induce Jset).Connected := by
        simpa [Jset] using
          connectedComponent_support_as_base_connected (G := G) Jcomp
      have hJ_nonempty : Jset.Nonempty := by
        exact ⟨u, hu_compl, huJ⟩
      have hJ_subset_compl : Jset ⊆ CycleCompl := by
        intro w hw
        exact hw.choose
      have hJ_component_closed :
          forall a : V, a ∈ Jset -> forall b : V,
            b ∈ CycleCompl -> G.Adj a b -> b ∈ Jset := by
        intro a ha b hb hab
        rcases ha with ⟨ha_compl, haJ⟩
        refine ⟨hb, ?_⟩
        have hab_ind :
            (G.induce CycleCompl).Adj
              (⟨a, ha_compl⟩ : CycleCompl) ⟨b, hb⟩ := by
          exact hab
        exact Jcomp.mem_supp_of_adj_mem_supp haJ hab_ind
      have hJ_two_attachments :
          2 <=
            ({w : V | w ∈ {q : V | q ∈ cycle.support} ∧
              Exists fun a : V => a ∈ Jset ∧ G.Adj a w}).ncard :=
        two_connected_complement_component_has_two_cycle_attachments
          (G := G) h_two_connected cycle cycle_isCycle hJ_nonempty
          hJ_subset_compl hJ_component_closed
      have hv_J_attach :
          v ∈ {w : V | w ∈ {q : V | q ∈ cycle.support} ∧
            Exists fun a : V => a ∈ Jset ∧ G.Adj a w} := by
        exact ⟨hv_cycle, u, ⟨hu_compl, huJ⟩, huv⟩
      obtain ⟨w, hw_attach, hw_ne_v⟩ :
          Exists fun w : V =>
            w ∈ {q : V | q ∈ {r : V | r ∈ cycle.support} ∧
              Exists fun a : V => a ∈ Jset ∧ G.Adj a q} ∧
              w ≠ v := by
        by_contra hno_other
        push Not at hno_other
        have hsub :
            {q : V | q ∈ {r : V | r ∈ cycle.support} ∧
              Exists fun a : V => a ∈ Jset ∧ G.Adj a q} ⊆ {v} := by
          intro q hq
          exact Set.mem_singleton_iff.mpr (hno_other q hq)
        have hcard_le :
            ({q : V | q ∈ {r : V | r ∈ cycle.support} ∧
              Exists fun a : V => a ∈ Jset ∧ G.Adj a q}).ncard <= 1 := by
          calc
            ({q : V | q ∈ {r : V | r ∈ cycle.support} ∧
              Exists fun a : V => a ∈ Jset ∧ G.Adj a q}).ncard <=
                ({v} : Set V).ncard := Set.ncard_le_ncard hsub
            _ = 1 := by simp
        omega
      have hw_cycle : w ∈ cycle.support := hw_attach.1
      obtain ⟨w_neighbor, hwJ, hw_adj⟩ := hw_attach.2
      obtain ⟨Jcore, hJcore_path, hJcore_support⟩ :=
        connected_induce_exists_path_support_subset
          (G := G) hJ_connected
          (show u ∈ Jset from ⟨hu_compl, huJ⟩) hwJ
      let Jwalk : G.Walk v w :=
        (SimpleGraph.Walk.cons huv.symm Jcore).concat hw_adj
      have Jwalk_support_subset :
          forall q : V, q ∈ Jwalk.support -> q = v ∨ q = w ∨ q ∈ Jset := by
        intro q hq
        simp [Jwalk, SimpleGraph.Walk.concat] at hq
        rcases hq with rfl | hq
        · exact Or.inl rfl
        · rcases hq with hqJ | hq_end
          · exact Or.inr (Or.inr (hJcore_support q hqJ))
          · rcases hq_end with rfl | rfl
            · exact Or.inr (Or.inr hwJ)
            · exact Or.inr (Or.inl rfl)
      have hy_ne_v : y ≠ v := by
        intro hyv
        exact hv_not_dominated_by_H hy_neighbor hhyH
          (by simpa [hyv] using hhy_adj)
      have hz_ne_v : z ≠ v := by
        intro hzv
        exact hv_not_dominated_by_H hz_neighbor hhzH
          (by simpa [hzv] using hhz_adj)
      obtain ⟨anchor, hanchor_cycle, hanchor_attach,
          hanchor_ne_v, hanchor_ne_w⟩ :
          Exists fun anchor : V =>
            anchor ∈ cycle.support ∧
              (Exists fun a : V => a ∈ Hset ∧ G.Adj a anchor) ∧
                anchor ≠ v ∧ anchor ≠ w := by
        by_cases hyw : y = w
        · refine ⟨z, hz_cycle, ⟨hz_neighbor, hhzH, hhz_adj⟩,
            hz_ne_v, ?_⟩
          intro hzw
          exact hyz_ne (hyw.trans hzw.symm)
        · exact ⟨y, hy_cycle, ⟨hy_neighbor, hhyH, hhy_adj⟩,
            hy_ne_v, hyw⟩
      obtain ⟨anchor_neighbor, hanchorH, hanchor_adj⟩ := hanchor_attach
      obtain ⟨Ppath, hPpath_path, hPpath_support_cycle,
          hanchor_not_Ppath⟩ :=
        Walk.IsCycle.exists_path_between_avoiding
          (G := G) cycle cycle_isCycle hv_cycle hw_cycle hanchor_cycle
          (by exact hw_ne_v.symm) hanchor_ne_v hanchor_ne_w
      have hv_not_Jset : v ∉ Jset := by
        intro hvJ
        exact hJ_subset_compl hvJ hv_cycle
      have hw_not_Jset : w ∉ Jset := by
        intro hwJset
        exact hJ_subset_compl hwJset hw_cycle
      have hv_not_Jcore : v ∉ Jcore.support := by
        intro hvJcore
        exact hv_not_Jset (hJcore_support v hvJcore)
      have hcons_Jcore_path :
          (SimpleGraph.Walk.cons huv.symm Jcore).IsPath := by
        rw [SimpleGraph.Walk.cons_isPath_iff]
        exact ⟨hJcore_path, hv_not_Jcore⟩
      have hw_not_cons_Jcore :
          w ∉ (SimpleGraph.Walk.cons huv.symm Jcore).support := by
        intro hw_support
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw_support
        rcases hw_support with hwv | hwcore
        · exact hw_ne_v hwv
        · exact hw_not_Jset (hJcore_support w hwcore)
      have hJwalk_path : Jwalk.IsPath := by
        dsimp [Jwalk]
        exact hcons_Jcore_path.concat hw_not_cons_Jcore hw_adj
      let Jtail : G.Walk u w := Jcore.concat hw_adj
      have hw_not_Jcore : w ∉ Jcore.support := by
        intro hwcore
        exact hw_not_Jset (hJcore_support w hwcore)
      have hJtail_path : Jtail.IsPath := by
        dsimp [Jtail]
        exact hJcore_path.concat hw_not_Jcore hw_adj
      have hJtail_support_cases :
          forall q : V, q ∈ Jtail.support -> q = w ∨ q ∈ Jset := by
        intro q hq
        dsimp [Jtail] at hq
        rw [SimpleGraph.Walk.support_concat] at hq
        have hq' : q ∈ Jcore.support ∨ q = w := by
          simpa using hq
        rcases hq' with hqcore | rfl
        · exact Or.inr (hJcore_support q hqcore)
        · exact Or.inl rfl
      let Rtail : G.Walk u v := Jtail.append Ppath.reverse
      have hRtail_path : Rtail.IsPath := by
        change (Jtail.append Ppath.reverse).IsPath
        rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
          List.nodup_append]
        refine ⟨hJtail_path.support_nodup,
          hPpath_path.reverse.support_nodup.tail, ?_⟩
        intro q hqJ q' hqPtail hqq'
        subst q'
        have hqP_rev : q ∈ Ppath.reverse.support :=
          List.mem_of_mem_tail hqPtail
        have hqP : q ∈ Ppath.support := by
          rw [SimpleGraph.Walk.support_reverse] at hqP_rev
          exact List.mem_reverse.mp hqP_rev
        have hq_cycle : q ∈ cycle.support :=
          hPpath_support_cycle q hqP
        have hq_ne_w : q ≠ w := by
          intro hqw
          exact Walk.IsPath.start_notMem_tail_support hPpath_path.reverse
            (by simpa [hqw] using hqPtail)
        rcases hJtail_support_cases q hqJ with rfl | hqJset
        · exact hq_ne_w rfl
        · exact hJ_subset_compl hqJset hq_cycle
      have hfirst_edge_not_Rtail : s(v, u) ∉ Rtail.edges := by
        intro he
        change s(v, u) ∈ (Jtail.append Ppath.reverse).edges at he
        rw [SimpleGraph.Walk.edges_append] at he
        rcases List.mem_append.mp he with heJ | heP
        · have hvJtail : v ∈ Jtail.support :=
            Jtail.fst_mem_support_of_mem_edges heJ
          rcases hJtail_support_cases v hvJtail with hvw | hvJset
          · exact hw_ne_v hvw.symm
          · exact hv_not_Jset hvJset
        · have huP_rev : u ∈ Ppath.reverse.support :=
            Ppath.reverse.snd_mem_support_of_mem_edges heP
          have huP : u ∈ Ppath.support := by
            rw [SimpleGraph.Walk.support_reverse] at huP_rev
            exact List.mem_reverse.mp huP_rev
          exact hu_compl (hPpath_support_cycle u huP)
      let newCycle : G.Walk v v := SimpleGraph.Walk.cons huv.symm Rtail
      have newCycle_isCycle : newCycle.IsCycle := by
        change (SimpleGraph.Walk.cons huv.symm Rtail).IsCycle
        rw [SimpleGraph.Walk.cons_isCycle_iff]
        exact ⟨hRtail_path, hfirst_edge_not_Rtail⟩
      have hJ_H_disjoint : Disjoint Jset Hset := by
        rw [Set.disjoint_left]
        intro q hqJ hqH
        rcases hqJ with ⟨hqComplJ, hqJsupp⟩
        rcases hqH with ⟨hqComplH, hqHsupp⟩
        have hqHsupp' :
            (⟨q, hqComplJ⟩ : CycleCompl) ∈ Hcomp.supp := by
          convert hqHsupp using 1
        exact hJ_ne_H
          (SimpleGraph.ConnectedComponent.eq_of_common_vertex
            hqJsupp hqHsupp')
      have hRtail_support_cases :
          forall q : V, q ∈ Rtail.support ->
            q ∈ cycle.support ∨ q ∈ Jset := by
        intro q hq
        change q ∈ (Jtail.append Ppath.reverse).support at hq
        rw [SimpleGraph.Walk.support_append] at hq
        rcases List.mem_append.mp hq with hqJtail | hqPtail
        · rcases hJtail_support_cases q hqJtail with rfl | hqJ
          · exact Or.inl hw_cycle
          · exact Or.inr hqJ
        · have hqP_rev : q ∈ Ppath.reverse.support :=
            List.mem_of_mem_tail hqPtail
          have hqP : q ∈ Ppath.support := by
            rw [SimpleGraph.Walk.support_reverse] at hqP_rev
            exact List.mem_reverse.mp hqP_rev
          exact Or.inl (hPpath_support_cycle q hqP)
      have newCycle_support_cases :
          forall q : V, q ∈ newCycle.support ->
            q ∈ cycle.support ∨ q ∈ Jset := by
        intro q hq
        change q ∈ (SimpleGraph.Walk.cons huv.symm Rtail).support at hq
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hq
        rcases hq with rfl | hqR
        · exact Or.inl hv_cycle
        · exact hRtail_support_cases q hqR
      have newCycle_avoids_L :
          forall q : V, q ∈ newCycle.support -> q ∉ L := by
        intro q hq hqL
        rcases newCycle_support_cases q hq with hq_cycle | hqJ
        · exact cycle_avoids_L q hq_cycle hqL
        · exact Set.disjoint_left.mp hJ_H_disjoint hqJ
            (hL_subset_H q hqL)
      let NewCompl : Set V := {q : V | q ∈ newCycle.support}ᶜ
      have hH_subset_newCompl : Hset ⊆ NewCompl := by
        intro q hqH hqNew
        rcases newCycle_support_cases q hqNew with hq_cycle | hqJ
        · exact hH_subset_compl hqH hq_cycle
        · exact Set.disjoint_left.mp hJ_H_disjoint hqJ hqH
      have hanchor_not_H : anchor ∉ Hset := by
        intro hanchorHset
        exact hH_subset_compl hanchorHset hanchor_cycle
      have hanchor_not_Jset : anchor ∉ Jset := by
        intro hanchorJ
        exact hJ_subset_compl hanchorJ hanchor_cycle
      have hanchor_newCompl : anchor ∈ NewCompl := by
        intro hanchor_new
        change anchor ∈
          (SimpleGraph.Walk.cons huv.symm Rtail).support at hanchor_new
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hanchor_new
        rcases hanchor_new with hanchor_v | hanchor_R
        · exact hanchor_ne_v hanchor_v
        · change anchor ∈ (Jtail.append Ppath.reverse).support at hanchor_R
          rw [SimpleGraph.Walk.support_append] at hanchor_R
          rcases List.mem_append.mp hanchor_R with hanchor_Jtail | hanchor_Ptail
          · rcases hJtail_support_cases anchor hanchor_Jtail with hanchor_w | hanchorJ
            · exact hanchor_ne_w hanchor_w
            · exact hanchor_not_Jset hanchorJ
          · have hanchor_P_rev : anchor ∈ Ppath.reverse.support :=
              List.mem_of_mem_tail hanchor_Ptail
            have hanchor_P : anchor ∈ Ppath.support := by
              rw [SimpleGraph.Walk.support_reverse] at hanchor_P_rev
              exact List.mem_reverse.mp hanchor_P_rev
            exact hanchor_not_Ppath hanchor_P
      have hanchor_neighbor_newCompl : anchor_neighbor ∈ NewCompl :=
        hH_subset_newCompl hanchorH
      let Cnew : (G.induce NewCompl).ConnectedComponent :=
        (G.induce NewCompl).connectedComponentMk
          ⟨anchor_neighbor, hanchor_neighbor_newCompl⟩
      have hH_subset_Cnew :
          forall q : V, forall hqH : q ∈ Hset,
            (⟨q, hH_subset_newCompl hqH⟩ : NewCompl) ∈
              Cnew.supp := by
        intro q hqH
        have hreachH :
            (G.induce Hset).Reachable
              ⟨anchor_neighbor, hanchorH⟩ ⟨q, hqH⟩ :=
          hH_connected ⟨anchor_neighbor, hanchorH⟩ ⟨q, hqH⟩
        have hreachNew :
            (G.induce NewCompl).Reachable
              ⟨anchor_neighbor, hanchor_neighbor_newCompl⟩
              ⟨q, hH_subset_newCompl hqH⟩ :=
          hreachH.map (G.induceHomOfLE hH_subset_newCompl).toHom
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        simpa [Cnew] using
          (SimpleGraph.ConnectedComponent.sound hreachNew).symm
      have hanchor_Cnew :
          (⟨anchor, hanchor_newCompl⟩ : NewCompl) ∈ Cnew.supp := by
        have hanchor_adj_ind :
            (G.induce NewCompl).Adj
              (⟨anchor_neighbor, hanchor_neighbor_newCompl⟩ : NewCompl)
              ⟨anchor, hanchor_newCompl⟩ := by
          exact hanchor_adj
        have hbase :
            (⟨anchor_neighbor, hanchor_neighbor_newCompl⟩ :
              NewCompl) ∈ Cnew.supp :=
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        exact Cnew.mem_supp_of_adj_mem_supp hbase hanchor_adj_ind
      have hL_in_Cnew :
          forall q : V, forall hqL : q ∈ L,
            (⟨q, by
              intro hq_new
              exact newCycle_avoids_L q hq_new hqL⟩ :
                NewCompl) ∈ Cnew.supp := by
        intro q hqL
        have hqH : q ∈ Hset := hL_subset_H q hqL
        convert hH_subset_Cnew q hqH using 1
      let Q : CycleComponentPair G L := {
        root := v
        cycle := newCycle
        isCycle := newCycle_isCycle
        avoids_L := newCycle_avoids_L
        component := Cnew
        L_in_component := hL_in_Cnew
      }
      have hBest_componentSize :
          Best.componentSize = Hset.ncard := by
        simp [CycleComponentPair.componentSize,
          CycleComponentPair.componentSet, Hset, Hcomp, CycleCompl, cycle]
      have hInsert_subset_Q :
          insert anchor Hset ⊆ Q.componentSet := by
        intro q hq
        rcases hq with rfl | hqH
        · exact ⟨hanchor_newCompl, hanchor_Cnew⟩
        · exact ⟨hH_subset_newCompl hqH, hH_subset_Cnew q hqH⟩
      have hH_lt_insert : Hset.ncard < (insert anchor Hset).ncard := by
        rw [Set.ncard_insert_of_notMem hanchor_not_H]
        exact Nat.lt_succ_self _
      have hQ_ge_insert : (insert anchor Hset).ncard <= Q.componentSize := by
        have hbase :
            (insert anchor Hset).ncard <= Q.componentSet.ncard :=
          Set.ncard_le_ncard hInsert_subset_Q
        simpa [CycleComponentPair.componentSize] using hbase
      have hBest_lt_Q : Best.componentSize < Q.componentSize := by
        calc
          Best.componentSize = Hset.ncard := hBest_componentSize
          _ < (insert anchor Hset).ncard := hH_lt_insert
          _ <= Q.componentSize := hQ_ge_insert
      have hQ_le_Best : Q.componentSize <= Best.componentSize := hBest_max Q
      omega

end DominatingK4

end Schematic.Math.GraphTheory
