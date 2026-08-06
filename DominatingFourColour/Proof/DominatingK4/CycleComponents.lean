import DominatingFourColour.Proof.DominatingK4.ComplementCycles

/-!
Maximal complement components and minimal cycles used in the rerouting argument.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace DominatingK4

theorem exists_cycle_complement_component_containing_clique
    (L : Finset V)
    {x : V}
    (c : G.Walk x x)
    (hcycle_avoids_L : forall v : V, v ∈ c.support -> v ∉ L)
    (h_clique : G.IsClique (L : Set V))
    (hcompl_nonempty : ({v : V | v ∈ c.support}ᶜ : Set V).Nonempty) :
    Exists fun C : (G.induce ({v : V | v ∈ c.support}ᶜ)).ConnectedComponent =>
      forall v : V, forall hvL : v ∈ L,
        (⟨v, by
          intro hv_cycle
          exact hcycle_avoids_L v hv_cycle hvL⟩ :
            ({v : V | v ∈ c.support}ᶜ : Set V)) ∈ C.supp := by
  classical
  by_cases hL_empty : L = ∅
  · obtain ⟨u, hu⟩ := hcompl_nonempty
    refine ⟨(G.induce ({v : V | v ∈ c.support}ᶜ)).connectedComponentMk
      ⟨u, hu⟩, ?_⟩
    intro v hvL
    simp [hL_empty] at hvL
  · obtain ⟨l, hlL⟩ := Finset.nonempty_iff_ne_empty.mpr hL_empty
    have hlA : l ∈ ({v : V | v ∈ c.support}ᶜ : Set V) := by
      intro hl_cycle
      exact hcycle_avoids_L l hl_cycle hlL
    let lA : ({v : V | v ∈ c.support}ᶜ : Set V) := ⟨l, hlA⟩
    let C : (G.induce ({v : V | v ∈ c.support}ᶜ)).ConnectedComponent :=
      (G.induce ({v : V | v ∈ c.support}ᶜ)).connectedComponentMk lA
    refine ⟨C, ?_⟩
    intro v hvL
    have hvA : v ∈ ({v : V | v ∈ c.support}ᶜ : Set V) := by
      intro hv_cycle
      exact hcycle_avoids_L v hv_cycle hvL
    let vA : ({v : V | v ∈ c.support}ᶜ : Set V) := ⟨v, hvA⟩
    by_cases hvl : v = l
    · subst v
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    · have hvl_adj : G.Adj v l := h_clique hvL hlL hvl
      have hvl_adj_ind :
          (G.induce ({v : V | v ∈ c.support}ᶜ)).Adj vA lA := by
        exact hvl_adj
      have hC_l : lA ∈ C.supp :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      exact C.mem_supp_of_adj_mem_supp hC_l hvl_adj_ind.symm

theorem connectedComponent_support_as_base_connected
    {A : Set V}
    (C : (G.induce A).ConnectedComponent) :
    (G.induce {v : V | Exists fun hv : v ∈ A =>
      (⟨v, hv⟩ : A) ∈ C.supp}).Connected := by
  simpa [induceComponentSupport] using
    induceComponentSupport_connected (G := G) C

structure CycleComponentPair (G : SimpleGraph V) (L : Finset V) where
  root : V
  cycle : G.Walk root root
  isCycle : cycle.IsCycle
  avoids_L : forall v : V, v ∈ cycle.support -> v ∉ L
  component :
    (G.induce ({v : V | v ∈ cycle.support}ᶜ)).ConnectedComponent
  L_in_component :
    forall v : V, forall hvL : v ∈ L,
      (⟨v, by
        intro hv_cycle
        exact avoids_L v hv_cycle hvL⟩ :
          ({v : V | v ∈ cycle.support}ᶜ : Set V)) ∈ component.supp

def CycleComponentPair.componentSet
    {L : Finset V}
    (P : CycleComponentPair G L) : Set V :=
  {v : V | Exists fun hv : v ∈ ({w : V | w ∈ P.cycle.support}ᶜ : Set V) =>
    (⟨v, hv⟩ : ({w : V | w ∈ P.cycle.support}ᶜ : Set V)) ∈ P.component.supp}

theorem CycleComponentPair.componentSet_subset_complement
    {L : Finset V}
    (P : CycleComponentPair G L) :
    P.componentSet ⊆ ({v : V | v ∈ P.cycle.support}ᶜ : Set V) := by
  intro v hv
  exact hv.choose

theorem CycleComponentPair.componentSet_nonempty
    {L : Finset V}
    (P : CycleComponentPair G L) :
    P.componentSet.Nonempty := by
  obtain ⟨u, hu⟩ := P.component.nonempty_supp
  exact ⟨u, u.2, hu⟩

theorem CycleComponentPair.L_subset_componentSet
    {L : Finset V}
    (P : CycleComponentPair G L) :
    forall v : V, v ∈ L -> v ∈ P.componentSet := by
  intro v hvL
  refine ⟨?_, ?_⟩
  · intro hv_cycle
    exact P.avoids_L v hv_cycle hvL
  · exact P.L_in_component v hvL

theorem CycleComponentPair.componentSet_connected
    {L : Finset V}
    (P : CycleComponentPair G L) :
    (G.induce P.componentSet).Connected := by
  simpa [CycleComponentPair.componentSet] using
    connectedComponent_support_as_base_connected (G := G) P.component

noncomputable def CycleComponentPair.componentSize
    {L : Finset V}
    (P : CycleComponentPair G L) : Nat :=
  P.componentSet.ncard

theorem CycleComponentPair.componentSize_le_card
    [Fintype V]
    {L : Finset V}
    (P : CycleComponentPair G L) :
    P.componentSize <= Fintype.card V := by
  classical
  rw [CycleComponentPair.componentSize]
  simpa [Nat.card_eq_fintype_card] using
    (Set.ncard_le_card P.componentSet)

theorem exists_maximal_minimal_cycle_component_pair
    [Fintype V]
    (L : Finset V)
    (h_exists : Nonempty (CycleComponentPair G L)) :
    Exists fun P : CycleComponentPair G L =>
      (forall Q : CycleComponentPair G L, Q.componentSize <= P.componentSize) ∧
        forall Q : CycleComponentPair G L,
          Q.componentSize = P.componentSize -> P.cycle.length <= Q.cycle.length := by
  classical
  let HasSize : Nat -> Prop := fun n =>
    Exists fun P : CycleComponentPair G L => P.componentSize = n
  obtain ⟨P₀⟩ := h_exists
  have hP₀_bound : P₀.componentSize <= Fintype.card V :=
    P₀.componentSize_le_card
  let maxSize : Nat := Nat.findGreatest HasSize (Fintype.card V)
  have hmax_spec : HasSize maxSize := by
    exact Nat.findGreatest_spec (P := HasSize) hP₀_bound ⟨P₀, rfl⟩
  have hmax_ge :
      forall Q : CycleComponentPair G L, Q.componentSize <= maxSize := by
    intro Q
    exact Nat.le_findGreatest (P := HasSize)
      Q.componentSize_le_card ⟨Q, rfl⟩
  let HasMaxSizeLength : Nat -> Prop := fun n =>
    Exists fun P : CycleComponentPair G L =>
      P.componentSize = maxSize ∧ P.cycle.length = n
  have hlength_exists : Exists HasMaxSizeLength := by
    rcases hmax_spec with ⟨P, hPsize⟩
    exact ⟨P.cycle.length, P, hPsize, rfl⟩
  obtain ⟨P, hPsize, hPlength⟩ := Nat.find_spec hlength_exists
  refine ⟨P, ?_, ?_⟩
  · intro Q
    calc
      Q.componentSize <= maxSize := hmax_ge Q
      _ = P.componentSize := hPsize.symm
  · intro Q hQsize
    have hQmax : Q.componentSize = maxSize := hQsize.trans hPsize
    have hmin :=
      Nat.find_min' hlength_exists
        (show HasMaxSizeLength Q.cycle.length from ⟨Q, hQmax, rfl⟩)
    simpa [hPlength] using hmin

theorem maximal_minimal_cycle_component_pair_isChordless
    [Fintype V] [DecidableEq V]
    {L : Finset V}
    (P : CycleComponentPair G L)
    (hmax :
      forall Q : CycleComponentPair G L, Q.componentSize <= P.componentSize)
    (hmin :
      forall Q : CycleComponentPair G L,
        Q.componentSize = P.componentSize -> P.cycle.length <= Q.cycle.length) :
    P.cycle.IsChordless := by
  classical
  by_contra hnot_chordless
  obtain ⟨a, ha_cycle, b, hb_cycle, hab, hab_not_cycle⟩ :=
    (Walk.not_isChordless_iff_exists_adj_not_toSubgraph_adj
      (G := G) P.cycle).mp hnot_chordless
  obtain ⟨c', hc', hc'_shorter, hc'_support_subset⟩ :=
    Walk.exists_isCycle_of_cycle_chord
      (G := G) P.cycle P.isCycle ha_cycle hb_cycle hab hab_not_cycle
  let NewCompl : Set V := {v : V | v ∈ c'.support}ᶜ
  have hPset_subset_new : P.componentSet ⊆ NewCompl := by
    intro v hvP hv_new_cycle
    exact P.componentSet_subset_complement hvP
      (hc'_support_subset v hv_new_cycle)
  obtain ⟨u₀, hu₀P⟩ := P.componentSet_nonempty
  have hu₀New : u₀ ∈ NewCompl := hPset_subset_new hu₀P
  let Cnew : (G.induce NewCompl).ConnectedComponent :=
    (G.induce NewCompl).connectedComponentMk ⟨u₀, hu₀New⟩
  have hPset_subset_Cnew :
      P.componentSet ⊆
        {v : V | Exists fun hv : v ∈ NewCompl =>
          (⟨v, hv⟩ : NewCompl) ∈ Cnew.supp} := by
    intro v hvP
    have hvNew : v ∈ NewCompl := hPset_subset_new hvP
    have hreachP :
        (G.induce P.componentSet).Reachable
          ⟨u₀, hu₀P⟩ ⟨v, hvP⟩ :=
      P.componentSet_connected ⟨u₀, hu₀P⟩ ⟨v, hvP⟩
    have hreachNew :
        (G.induce NewCompl).Reachable
          ⟨u₀, hu₀New⟩ ⟨v, hvNew⟩ :=
      hreachP.map (G.induceHomOfLE hPset_subset_new).toHom
    refine ⟨hvNew, ?_⟩
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [Cnew] using
      (SimpleGraph.ConnectedComponent.sound hreachNew).symm
  have hL_in_Cnew :
      forall v : V, forall hvL : v ∈ L,
        (⟨v, by
          intro hv_cycle
          exact P.avoids_L v (hc'_support_subset v hv_cycle) hvL⟩ :
            NewCompl) ∈ Cnew.supp := by
    intro v hvL
    exact (hPset_subset_Cnew (P.L_subset_componentSet v hvL)).choose_spec
  let Q : CycleComponentPair G L := {
    root := a
    cycle := c'
    isCycle := hc'
    avoids_L := by
      intro v hv hvL
      exact P.avoids_L v (hc'_support_subset v hv) hvL
    component := Cnew
    L_in_component := hL_in_Cnew
  }
  have hP_le_Q : P.componentSize <= Q.componentSize := by
    have hbase :
        P.componentSet.ncard <=
          ({v : V | Exists fun hv : v ∈ NewCompl =>
            (⟨v, hv⟩ : NewCompl) ∈ Cnew.supp}).ncard :=
      Set.ncard_le_ncard hPset_subset_Cnew
    simpa [Q, CycleComponentPair.componentSize,
      CycleComponentPair.componentSet, NewCompl] using hbase
  have hQ_le_P : Q.componentSize <= P.componentSize := hmax Q
  have hQ_size : Q.componentSize = P.componentSize :=
    le_antisymm hQ_le_P hP_le_Q
  have hlength_le : P.cycle.length <= Q.cycle.length := hmin Q hQ_size
  simpa [Q] using (not_le_of_gt hc'_shorter hlength_le)

end DominatingK4

end Schematic.Math.GraphTheory
