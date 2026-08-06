import DominatingFourColour.Proof.Contraction
import DominatingFourColour.Proof.Colouring.SeparatorCases
import DominatingFourColour.Proof.DominatingK4.LowDegree
import DominatingFourColour.Proof.FourConnectedTriangle
import FourColorTheorem.Statement

/-! Connectivity and local structure of a minimal counterexample. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The colour-or-compatible-model conclusion for every graph with fewer than `n` vertices. -/
def ColorOrCompatibleModelBelow (n : Nat) : Prop :=
  forall {W : Type u} [Fintype W],
    forall H : SimpleGraph W,
      Fintype.card W < n ->
        forall L : OrderedClique H,
          H.Colorable 4 ∨ CompatibleDominatingK5Model L

structure MainInductionCounterexample (G : SimpleGraph V) (L : OrderedClique G) where
  not_four_colorable : Not (G.Colorable 4)
  no_compatible_model : Not (CompatibleDominatingK5Model L)
  vertex_minimal : forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4
  clique_maximal :
    forall L' : OrderedClique G,
      L.InitialSegment L' ->
        Not (CompatibleDominatingK5Model L') ->
          L'.length <= L.length
  no_proper_separation_orderAtMost_three :
    forall S : Separation G, S.Proper -> S.OrderAtMost 3 -> False

theorem exists_pair_extension_no_compatible
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {L : OrderedClique G}
    (hnot_four_colorable : Not (G.Colorable 4))
    (hvertex_minimal : forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    Exists fun L' : OrderedClique G =>
      L.InitialSegment L' ∧ L'.length = 2 ∧
        Not (CompatibleDominatingK5Model L') := by
  classical
  cases L with
  | nil =>
      have h_nonempty : Nonempty V := by
        have hgt := card_gt_four_of_not_colorable_four (G := G) hnot_four_colorable
        exact Fintype.card_pos_iff.mp (by omega)
      obtain ⟨v1⟩ := h_nonempty
      have h_no_single : Not (CompatibleDominatingK5Model (G := G) (.single v1)) := by
        intro hsingle
        exact hno_model
          (CompatibleDominatingK5Model.of_initialSegment
            (L := (OrderedClique.nil : OrderedClique G))
            (L' := .single v1)
            (by simp [OrderedClique.InitialSegment]) hsingle)
      have h_degree : 4 <= G.degree v1 :=
        degree_atLeast_four_of_not_colorable_four_of_delete_vertex_colorable
          (G := G) v1 hnot_four_colorable (hvertex_minimal v1)
      have h_neighbor_card_pos : 0 < (G.neighborFinset v1).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        omega
      obtain ⟨v2, hv2_mem⟩ := Finset.card_pos.mp h_neighbor_card_pos
      have edge : G.Adj v1 v2 := by
        rw [SimpleGraph.mem_neighborFinset] at hv2_mem
        exact hv2_mem
      have h_no_pair : Not (CompatibleDominatingK5Model (G := G) (.pair v1 v2 edge)) := by
        intro hpair
        exact h_no_single
          (CompatibleDominatingK5Model.of_initialSegment
            (L := (OrderedClique.single v1 : OrderedClique G))
            (L' := .pair v1 v2 edge)
            (by simp [OrderedClique.InitialSegment]) hpair)
      exact ⟨.pair v1 v2 edge,
        by simp [OrderedClique.InitialSegment],
        by simp [OrderedClique.length],
        h_no_pair⟩
  | single v1 =>
      have h_degree : 4 <= G.degree v1 :=
        degree_atLeast_four_of_not_colorable_four_of_delete_vertex_colorable
          (G := G) v1 hnot_four_colorable (hvertex_minimal v1)
      have h_neighbor_card_pos : 0 < (G.neighborFinset v1).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        omega
      obtain ⟨v2, hv2_mem⟩ := Finset.card_pos.mp h_neighbor_card_pos
      have edge : G.Adj v1 v2 := by
        rw [SimpleGraph.mem_neighborFinset] at hv2_mem
        exact hv2_mem
      have h_no_pair : Not (CompatibleDominatingK5Model (G := G) (.pair v1 v2 edge)) := by
        intro hpair
        exact hno_model
          (CompatibleDominatingK5Model.of_initialSegment
            (L := (OrderedClique.single v1 : OrderedClique G))
            (L' := .pair v1 v2 edge)
            (by simp [OrderedClique.InitialSegment]) hpair)
      exact ⟨.pair v1 v2 edge,
        by simp [OrderedClique.InitialSegment],
        by simp [OrderedClique.length],
        h_no_pair⟩
  | pair v1 v2 edge =>
      exact ⟨.pair v1 v2 edge,
        by simp [OrderedClique.InitialSegment], rfl, hno_model⟩

theorem counterexample_ordered_clique_has_length_two
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {L : OrderedClique G}
    (C : MainInductionCounterexample G L) :
    L.length = 2 := by
  classical
  obtain ⟨L', hinit, hlength, hno_model⟩ :=
    exists_pair_extension_no_compatible
      C.not_four_colorable C.vertex_minimal C.no_compatible_model
  have hle := C.clique_maximal L' hinit hno_model
  rw [hlength] at hle
  cases L <;> simp [OrderedClique.length] at hle ⊢

theorem induce_colorable_of_delete_vertex_colorable
    (hvertex_minimal : forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    {A : Set V}
    (hA : A ≠ Set.univ) :
    (G.induce A).Colorable 4 := by
  classical
  have hnot_all : ¬ forall v : V, v ∈ A := by
    intro hall
    exact hA (Set.eq_univ_iff_forall.mpr hall)
  obtain ⟨v, hvA⟩ := not_forall.mp hnot_all
  have hA_subset : A ⊆ ({v} : Set V)ᶜ := by
    intro x hxA hxv
    exact hvA (by simpa [Set.mem_singleton_iff.mp hxv] using hxA)
  exact SimpleGraph.Colorable.of_hom
    (G.induceHomOfLE hA_subset).toHom
    (hvertex_minimal v)

theorem MainInductionCounterexample.induce_colorable_of_ne_univ
    [Fintype V]
    {L : OrderedClique G}
    (C : MainInductionCounterexample G L)
    {A : Set V}
    (hA : A ≠ Set.univ) :
    (G.induce A).Colorable 4 := by
  classical
  exact induce_colorable_of_delete_vertex_colorable
    (G := G) C.vertex_minimal hA

theorem colorable_of_proper_clique_separation_of_delete_vertex_colorable
    [Fintype V]
    (hvertex_minimal : forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    (S : Separation G)
    (hproper : S.Proper)
    (hseparator_clique : G.IsClique S.separator) :
    G.Colorable 4 := by
  classical
  have hleft_ne_univ : S.left ≠ Set.univ := by
    intro hleft
    obtain ⟨y, _hy_right, hy_not_left⟩ := hproper.2
    exact hy_not_left (by rw [hleft]; exact Set.mem_univ y)
  have hright_ne_univ : S.right ≠ Set.univ := by
    intro hright
    obtain ⟨y, _hy_left, hy_not_right⟩ := hproper.1
    exact hy_not_right (by rw [hright]; exact Set.mem_univ y)
  exact colorable_of_separation_clique S hseparator_clique
    (induce_colorable_of_delete_vertex_colorable
      (G := G) hvertex_minimal hleft_ne_univ)
    (induce_colorable_of_delete_vertex_colorable
      (G := G) hvertex_minimal hright_ne_univ)

theorem connected_of_not_colorable_of_delete_vertex_colorable
    [Fintype V]
    (hnot_four_colorable : Not (G.Colorable 4))
    (hvertex_minimal : forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4) :
    G.Connected := by
  classical
  by_contra hnot_connected
  have hcard_pos : 0 < Fintype.card V := by
    have hgt := card_gt_four_of_not_colorable_four (G := G) hnot_four_colorable
    omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp hcard_pos
  have hnot_preconnected : Not G.Preconnected := by
    intro hpre
    exact hnot_connected { preconnected := hpre }
  obtain ⟨x, hx⟩ := not_forall.mp hnot_preconnected
  obtain ⟨y, hxy_not_reachable⟩ := not_forall.mp hx
  let A : Set V := (G.connectedComponentMk x).supp
  have hxA : x ∈ A := by
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hy_not_A : y ∉ A := by
    intro hyA
    exact hxy_not_reachable
      (SimpleGraph.ConnectedComponent.exact (by simpa [A] using hyA.symm))
  have hA_ne_univ : A ≠ Set.univ := by
    intro hA
    exact hy_not_A (by rw [hA]; exact Set.mem_univ y)
  have hAc_ne_univ : Aᶜ ≠ Set.univ := by
    intro hAc
    have hx_not_A : x ∉ A := by
      have hxAc : x ∈ Aᶜ := by rw [hAc]; exact Set.mem_univ x
      exact hxAc
    exact hx_not_A hxA
  obtain ⟨colA⟩ :=
    induce_colorable_of_delete_vertex_colorable
      (G := G) hvertex_minimal hA_ne_univ
  obtain ⟨colB⟩ :=
    induce_colorable_of_delete_vertex_colorable
      (G := G) hvertex_minimal hAc_ne_univ
  let color : V -> Fin 4 := fun v =>
    if hv : v ∈ A then colA ⟨v, hv⟩ else colB ⟨v, hv⟩
  exact hnot_four_colorable ⟨SimpleGraph.Coloring.mk color (by
    intro u v huv hsame
    by_cases huA : u ∈ A
    · by_cases hvA : v ∈ A
      · have huvA : (G.induce A).Adj ⟨u, huA⟩ ⟨v, hvA⟩ := by
          simpa using huv
        exact colA.valid huvA (by simpa [color, huA, hvA] using hsame)
      · have hvA_from_adj : v ∈ A :=
          (G.connectedComponentMk x).mem_supp_of_adj_mem_supp (by simpa [A] using huA) huv
        exact hvA hvA_from_adj
    · by_cases hvA : v ∈ A
      · have huA_from_adj : u ∈ A :=
          (G.connectedComponentMk x).mem_supp_of_adj_mem_supp (by simpa [A] using hvA) huv.symm
        exact huA huA_from_adj
      · have huAc : u ∈ Aᶜ := huA
        have hvAc : v ∈ Aᶜ := hvA
        have huvB : (G.induce Aᶜ).Adj ⟨u, huAc⟩ ⟨v, hvAc⟩ := by
          simpa using huv
        exact colB.valid huvB (by simpa [color, huA, hvA] using hsame)
  )⟩

theorem colorable_of_orderAtMost_one_separation_of_connected_of_delete_vertex_colorable
    [Fintype V]
    (hconnected : G.Connected)
    (hvertex_minimal : forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    (S : Separation G)
    (hproper : S.Proper)
    (horder : S.OrderAtMost 1) :
    G.Colorable 4 := by
  classical
  obtain ⟨sep, hsep_left, hsep_right, hseparator_unique⟩ :=
    Separation.exists_unique_separator_of_connected_orderAtMost_one
      (G := G) S hconnected hproper horder
  have hleft_ne_univ : S.left ≠ Set.univ := by
    intro hleft
    obtain ⟨y, _hy_right, hy_not_left⟩ := hproper.2
    exact hy_not_left (by rw [hleft]; exact Set.mem_univ y)
  have hright_ne_univ : S.right ≠ Set.univ := by
    intro hright
    obtain ⟨y, _hy_left, hy_not_right⟩ := hproper.1
    exact hy_not_right (by rw [hright]; exact Set.mem_univ y)
  exact colorable_of_separation_singleton S sep hsep_left hsep_right hseparator_unique
    (induce_colorable_of_delete_vertex_colorable
      (G := G) hvertex_minimal hleft_ne_univ)
    (induce_colorable_of_delete_vertex_colorable
      (G := G) hvertex_minimal hright_ne_univ)

theorem MainInductionCounterexample.connected
    [Fintype V]
    {L : OrderedClique G}
    (C : MainInductionCounterexample G L) :
    G.Connected := by
  exact connected_of_not_colorable_of_delete_vertex_colorable
    (G := G) C.not_four_colorable C.vertex_minimal

theorem delete_singleton_connected_of_not_colorable_of_delete_vertex_colorable
    [Fintype V]
    (hnot_four_colorable : Not (G.Colorable 4))
    (hvertex_minimal : forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    (hconnected : G.Connected)
    (x : V) :
    (G.induce ({x} : Set V)ᶜ).Connected := by
  classical
  by_contra hdisc
  have hcard_gt : 4 < Nat.card V := by
    rw [Nat.card_eq_fintype_card]
    exact card_gt_four_of_not_colorable_four (G := G) hnot_four_colorable
  have h_compl_large : 1 < (({x} : Set V)ᶜ).ncard := by
    have hsum :
        ({x} : Set V).ncard + (({x} : Set V)ᶜ).ncard = Nat.card V := by
      simpa [Set.ncard_univ] using Set.ncard_add_ncard_compl ({x} : Set V)
    have hsingleton : ({x} : Set V).ncard = 1 := by
      simp
    omega
  obtain ⟨S, hproper, horder_raw⟩ :=
    disconnected_deletion_has_proper_separation
      (G := G) ({x} : Set V) h_compl_large hdisc
  have horder : S.OrderAtMost 1 := by
    simpa using horder_raw
  exact hnot_four_colorable
    (colorable_of_orderAtMost_one_separation_of_connected_of_delete_vertex_colorable
      (G := G) hconnected hvertex_minimal S hproper horder)

theorem MainInductionCounterexample.delete_singleton_connected
    [Fintype V]
    {L : OrderedClique G}
    (C : MainInductionCounterexample G L)
    (x : V) :
    (G.induce ({x} : Set V)ᶜ).Connected := by
  exact delete_singleton_connected_of_not_colorable_of_delete_vertex_colorable
    (G := G) C.not_four_colorable C.vertex_minimal C.connected x

theorem MainInductionCounterexample.no_proper_clique_separation
    [Fintype V]
    {L : OrderedClique G}
    (C : MainInductionCounterexample G L)
    (S : Separation G)
    (hproper : S.Proper)
    (hseparator_clique : G.IsClique S.separator) :
    False := by
  classical
  have hleft_ne_univ : S.left ≠ Set.univ := by
    intro hleft
    obtain ⟨y, _hy_right, hy_not_left⟩ := hproper.2
    exact hy_not_left (by rw [hleft]; exact Set.mem_univ y)
  have hright_ne_univ : S.right ≠ Set.univ := by
    intro hright
    obtain ⟨y, _hy_left, hy_not_right⟩ := hproper.1
    exact hy_not_right (by rw [hright]; exact Set.mem_univ y)
  exact C.not_four_colorable
    (colorable_of_separation_clique S hseparator_clique
      (C.induce_colorable_of_ne_univ hleft_ne_univ)
      (C.induce_colorable_of_ne_univ hright_ne_univ))

theorem MainInductionCounterexample.delete_clique_connected
    [Fintype V]
    {L : OrderedClique G}
    (C : MainInductionCounterexample G L)
    {S : Set V}
    (hS_card : S.ncard < 4)
    (hS_clique : G.IsClique S) :
    (G.induce Sᶜ).Connected := by
  classical
  by_contra hdisc
  have hcard_gt : 4 < Nat.card V := by
    rw [Nat.card_eq_fintype_card]
    exact card_gt_four_of_not_colorable_four (G := G) C.not_four_colorable
  have h_compl_large : 1 < Sᶜ.ncard := by
    have hsum : S.ncard + Sᶜ.ncard = Nat.card V := by
      simpa [Set.ncard_univ] using Set.ncard_add_ncard_compl S
    omega
  obtain ⟨T, hproper, hsubset, _horder⟩ :=
    disconnected_deletion_has_proper_separation_subset
      (G := G) S h_compl_large hdisc
  have hseparator_clique : G.IsClique T.separator := by
    intro a ha b hb hne
    exact hS_clique (hsubset ha) (hsubset hb) hne
  exact C.no_proper_clique_separation T hproper hseparator_clique

theorem counterexample_four_connected
    [Fintype V]
    {L : OrderedClique G}
    (C : MainInductionCounterexample G L) :
    IsFourConnected G := by
  refine ⟨?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    exact card_gt_four_of_not_colorable_four (G := G) C.not_four_colorable
  · intro S hS
    by_cases hS_empty : S = ∅
    · have h_univ : (G.induce (Set.univ : Set V)).Connected :=
        (SimpleGraph.induceUnivIso G).connected_iff.mpr C.connected
      rw [hS_empty]
      convert h_univ using 2
      · ext x
        simp
      · ext x
        simp
    · by_cases hS_clique : G.IsClique S
      · exact C.delete_clique_connected hS hS_clique
      · by_contra hdisc
        have hcard_gt : 4 < Nat.card V := by
          rw [Nat.card_eq_fintype_card]
          exact card_gt_four_of_not_colorable_four (G := G) C.not_four_colorable
        have h_compl_large : 1 < Sᶜ.ncard := by
          have hsum : S.ncard + Sᶜ.ncard = Nat.card V := by
            simpa [Set.ncard_univ] using Set.ncard_add_ncard_compl S
          omega
        obtain ⟨T, hproper, _horder⟩ :=
          disconnected_deletion_has_proper_separation (G := G) S h_compl_large hdisc
        exact C.no_proper_separation_orderAtMost_three T hproper
          (Separation.orderAtMost_mono _horder (by omega))

theorem counterexample_three_connected
    [Fintype V]
    {L : OrderedClique G}
    (C : MainInductionCounterexample G L) :
    IsThreeConnected G := by
  exact IsKConnected.mono (by decide : 3 <= 4) (counterexample_four_connected C)

theorem two_connected_of_not_colorable_of_delete_vertex_colorable
    [Fintype V]
    (hnot_four_colorable : Not (G.Colorable 4))
    (hvertex_minimal : forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4) :
    IsTwoConnected G := by
  classical
  have hconnected : G.Connected :=
    connected_of_not_colorable_of_delete_vertex_colorable
      (G := G) hnot_four_colorable hvertex_minimal
  refine ⟨?_, ?_⟩
  · have hgt := card_gt_four_of_not_colorable_four (G := G) hnot_four_colorable
    rw [Nat.card_eq_fintype_card]
    omega
  · intro S hS
    by_cases hS_empty : S = ∅
    · have h_univ : (G.induce (Set.univ : Set V)).Connected :=
        (SimpleGraph.induceUnivIso G).connected_iff.mpr hconnected
      rw [hS_empty]
      convert h_univ using 2
      · ext x
        simp
      · ext x
        simp
    · have hS_one : S.ncard = 1 := by
        have hS_pos : 0 < S.ncard := by
          by_contra hpos
          have hzero : S.ncard = 0 := by omega
          have hS_eq_empty : S = ∅ := by
            exact (Set.ncard_eq_zero (s := S) S.toFinite).mp hzero
          exact hS_empty hS_eq_empty
        omega
      obtain ⟨x, hS_eq⟩ := Set.ncard_eq_one.mp hS_one
      rw [hS_eq]
      exact delete_singleton_connected_of_not_colorable_of_delete_vertex_colorable
        (G := G) hnot_four_colorable hvertex_minimal hconnected x

theorem counterexample_two_connected
    [Fintype V]
    {L : OrderedClique G}
    (C : MainInductionCounterexample G L) :
    IsTwoConnected G := by
  exact two_connected_of_not_colorable_of_delete_vertex_colorable
    (G := G) C.not_four_colorable C.vertex_minimal

def PairLeftSmallNoncliqueSeparation
    (G : SimpleGraph V)
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (S : Separation G) : Prop :=
  S.Proper ∧ S.OrderAtMost 3 ∧ Not (S.OrderAtMost 1) ∧
    Not (G.IsClique S.separator) ∧
      (OrderedClique.pair v1 v2 edge).vertexSet ⊆ S.left

theorem exists_minimal_pair_left_small_nonclique_separation
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    {S0 : Separation G}
    (hS0 : PairLeftSmallNoncliqueSeparation G edge S0) :
    Exists fun S : Separation G =>
      PairLeftSmallNoncliqueSeparation G edge S ∧
        forall T : Separation G,
          PairLeftSmallNoncliqueSeparation G edge T ->
            S.left.ncard <= T.left.ncard := by
  classical
  let P : Nat -> Prop := fun n =>
    Exists fun S : Separation G =>
      PairLeftSmallNoncliqueSeparation G edge S ∧ S.left.ncard = n
  have hP : Exists fun n : Nat => P n := by
    exact ⟨S0.left.ncard, S0, hS0, rfl⟩
  obtain ⟨S, hS, hS_card⟩ := Nat.find_spec hP
  refine ⟨S, hS, ?_⟩
  intro T hT
  have hmin : Nat.find hP <= T.left.ncard :=
    Nat.find_min' hP ⟨T, hT, rfl⟩
  omega

theorem Separation.pair_collapse_separator_adj
    {x y : V}
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hxH : x ∈ H.verts)
    (hy_not_H : y ∉ H.verts)
    (hH_adj_y : Exists fun z : V => z ∈ H.verts ∧ G.Adj z y) :
    let C : GraphContraction G := GraphContraction.collapseSubgraph G H hH_connected
    C.graph.Adj (C.map x) (C.map y) := by
  classical
  intro C
  obtain ⟨z, hzH, hzy⟩ := hH_adj_y
  have hz_map : C.map z = (none : C.Target) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_none_of_mem
        G H hH_connected hzH
  have hx_map : C.map x = (none : C.Target) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_none_of_mem
        G H hH_connected hxH
  have hy_map_ne_none : C.map y ≠ (none : C.Target) := by
    intro hy_map
    have hy_cases :
        (y ∈ H.verts ∧ z ∈ H.verts) ∨
          (y = z ∧ y ∉ H.verts ∧ z ∉ H.verts) := by
      have hsame : C.map y = C.map z := hy_map.trans hz_map.symm
      simpa [C] using
        (GraphContraction.collapseSubgraph_map_eq_iff
          G H hH_connected (v := y) (w := z)).mp hsame
    rcases hy_cases with hboth | hout
    · exact hy_not_H hboth.1
    · exact hout.2.2 hzH
  rcases C.map_adj hzy with hsame | hadj
  · have hy_none : C.map y = (none : C.Target) := by
      exact hsame ▸ hz_map
    exact False.elim (hy_map_ne_none hy_none)
  · simpa [hz_map, hx_map] using hadj

noncomputable def Separation.rightWithSeparatorCliqueCollapseHomOfPair
    (S : Separation G)
    {x y : V}
    (hseparator : S.separator = ({x, y} : Set V))
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hxH : x ∈ H.verts)
    (hy_not_H : y ∉ H.verts)
    (hright_intersection :
      forall r : V, r ∈ S.right -> r ∈ H.verts -> r = x)
    (hH_adj_y : Exists fun z : V => z ∈ H.verts ∧ G.Adj z y) :
    S.rightWithSeparatorClique →g
      (GraphContraction.collapseSubgraph G H hH_connected).graph where
  toFun r := (GraphContraction.collapseSubgraph G H hH_connected).map (r : V)
  map_rel' := by
    classical
    intro a b hab
    let C : GraphContraction G :=
      GraphContraction.collapseSubgraph G H hH_connected
    change C.graph.Adj (C.map (a : V)) (C.map (b : V))
    have hval_ne : (a : V) ≠ (b : V) := by
      rcases hab with hab_true | hsep
      · intro h
        exact hab_true.ne (Subtype.ext h)
      · intro h
        exact hsep.2.2 (Subtype.ext h)
    have hmap_ne : C.map (a : V) ≠ C.map (b : V) := by
      intro hsame
      have hcases :
          ((a : V) ∈ H.verts ∧ (b : V) ∈ H.verts) ∨
            ((a : V) = (b : V) ∧
              (a : V) ∉ H.verts ∧ (b : V) ∉ H.verts) := by
        simpa [C] using
          (GraphContraction.collapseSubgraph_map_eq_iff
            G H hH_connected (v := (a : V)) (w := (b : V))).mp hsame
      rcases hcases with hboth | hout
      · have ha_x : (a : V) = x :=
          hright_intersection (a : V) a.2 hboth.1
        have hb_x : (b : V) = x :=
          hright_intersection (b : V) b.2 hboth.2
        exact hval_ne (ha_x.trans hb_x.symm)
      · exact hval_ne hout.1
    rcases hab with hab_true | hsep_adj
    · rcases C.map_adj (by simpa using hab_true) with hsame | hadj
      · exact False.elim (hmap_ne hsame)
      · exact hadj
    · have ha_sep : (a : V) ∈ S.separator := ⟨hsep_adj.1, a.2⟩
      have hb_sep : (b : V) ∈ S.separator := ⟨hsep_adj.2.1, b.2⟩
      have ha_pair : (a : V) = x ∨ (a : V) = y := by
        have : (a : V) ∈ ({x, y} : Set V) := by
          simpa [hseparator] using ha_sep
        simpa using this
      have hb_pair : (b : V) = x ∨ (b : V) = y := by
        have : (b : V) ∈ ({x, y} : Set V) := by
          simpa [hseparator] using hb_sep
        simpa using this
      obtain ⟨z, hzH, hzy⟩ := hH_adj_y
      have hz_map : C.map z = (none : C.Target) := by
        simpa [C] using
          GraphContraction.collapseSubgraph_map_eq_none_of_mem
            G H hH_connected hzH
      have hx_map : C.map x = (none : C.Target) := by
        simpa [C] using
          GraphContraction.collapseSubgraph_map_eq_none_of_mem
            G H hH_connected hxH
      have hy_map_ne_none : C.map y ≠ (none : C.Target) := by
        intro hy_map
        have hy_cases :
            (y ∈ H.verts ∧ z ∈ H.verts) ∨
              (y = z ∧ y ∉ H.verts ∧ z ∉ H.verts) := by
          have hsame : C.map y = C.map z := hy_map.trans hz_map.symm
          simpa [C] using
            (GraphContraction.collapseSubgraph_map_eq_iff
              G H hH_connected (v := y) (w := z)).mp hsame
        rcases hy_cases with hboth | hout
        · exact hy_not_H hboth.1
        · exact hout.2.2 hzH
      have hxy_collapse_adj : C.graph.Adj (C.map x) (C.map y) := by
        rcases C.map_adj hzy with hsame | hadj
        · have hy_none : C.map y = (none : C.Target) := by
            exact hsame ▸ hz_map
          exact False.elim (hy_map_ne_none hy_none)
        · simpa [hz_map, hx_map] using hadj
      rcases ha_pair with ha_x | ha_y <;> rcases hb_pair with hb_x | hb_y
      · exact False.elim (hval_ne (ha_x.trans hb_x.symm))
      · simpa [ha_x, hb_y] using hxy_collapse_adj
      · simpa [ha_y, hb_x] using hxy_collapse_adj.symm
      · exact False.elim (hval_ne (ha_y.trans hb_y.symm))

theorem Separation.rightWithSeparatorClique_colorable_of_pair_collapse_colorable
    (S : Separation G)
    {x y : V}
    (hseparator : S.separator = ({x, y} : Set V))
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hxH : x ∈ H.verts)
    (hy_not_H : y ∉ H.verts)
    (hright_intersection :
      forall r : V, r ∈ S.right -> r ∈ H.verts -> r = x)
    (hH_adj_y : Exists fun z : V => z ∈ H.verts ∧ G.Adj z y)
    {c : Nat}
    (hcollapse_colorable :
      (GraphContraction.collapseSubgraph G H hH_connected).graph.Colorable c) :
    S.rightWithSeparatorClique.Colorable c :=
  SimpleGraph.Colorable.of_hom
    (S.rightWithSeparatorCliqueCollapseHomOfPair
      hseparator H hH_connected hxH hy_not_H
      hright_intersection hH_adj_y)
    hcollapse_colorable

theorem counterexample_min_degree_atLeast_four
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {L : OrderedClique G}
    (C : MainInductionCounterexample G L)
    (v : V) :
    4 <= G.degree v := by
  exact degree_atLeast_four_of_not_colorable_four_of_delete_vertex_colorable
    (G := G) v C.not_four_colorable (C.vertex_minimal v)

private theorem mem_ofInduce_branch_subset
    {A : Set V} {t : Nat}
    (T : DominatingModel (G.induce A) t)
    (i : Fin t)
    {v : V}
    (hv : v ∈ (T.ofInduce.branch i).verts) :
    v ∈ A := by
  simp only [DominatingModel.ofInduce, DominatingModel.map,
    SimpleGraph.Subgraph.map_verts,
    Set.mem_image] at hv
  rcases hv with ⟨x, _hx, rfl⟩
  exact x.2

private theorem not_mem_ofInduce_branch_of_forall_not_mem
    {A : Set V} {t : Nat}
    (T : DominatingModel (G.induce A) t)
    (i : Fin t)
    {v : V}
    (hnot : forall hvA : v ∈ A, (⟨v, hvA⟩ : A) ∉ (T.branch i).verts) :
    v ∉ (T.ofInduce.branch i).verts := by
  intro hv
  simp only [DominatingModel.ofInduce, DominatingModel.map,
    SimpleGraph.Subgraph.map_verts,
    Set.mem_image] at hv
  rcases hv with ⟨x, hx, hxv⟩
  have hvA : v ∈ A := by
    rw [← hxv]
    exact x.2
  have hx_eq : x = ⟨v, hvA⟩ := Subtype.ext hxv
  exact hnot hvA (by simpa [hx_eq] using hx)

private theorem compatible_model_of_neighbor_induced_dominating_K4
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    {A : Set V}
    (hA_subset_neighbors : A ⊆ G.neighborSet v1)
    (hv1_not_A : v1 ∉ A)
    (T : DominatingK4Model (G.induce A))
    (hv2_late :
      forall i : Fin 4, 0 < (i : Nat) ->
      forall hv2A : v2 ∈ A,
        (⟨v2, hv2A⟩ : A) ∉ (T.branch i).verts) :
    CompatibleDominatingK5Model (.pair v1 v2 edge) := by
  classical
  let Tg : DominatingK4Model G := T.ofInduce
  let branches : Fin 5 -> G.Subgraph
    | 0 => G.singletonSubgraph v1
    | 1 => Tg.branch (0 : Fin 4)
    | 2 => Tg.branch (1 : Fin 4)
    | 3 => Tg.branch (2 : Fin 4)
    | 4 => Tg.branch (3 : Fin 4)
  let K : DominatingK5Model G := {
    branch := branches
    connected := by
      intro i
      fin_cases i <;> simp [branches, Tg]
      · exact SimpleGraph.Connected.of_subsingleton
      · exact Tg.connected (0 : Fin 4)
      · exact Tg.connected (1 : Fin 4)
      · exact Tg.connected (2 : Fin 4)
      · exact Tg.connected (3 : Fin 4)
    vertex_disjoint := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [branches, Tg] at hij ⊢
      · intro hx_branch
        exact hv1_not_A (mem_ofInduce_branch_subset (G := G) T (0 : Fin 4)
          hx_branch)
      · intro hx_branch
        exact hv1_not_A (mem_ofInduce_branch_subset (G := G) T (1 : Fin 4)
          hx_branch)
      · intro hx_branch
        exact hv1_not_A (mem_ofInduce_branch_subset (G := G) T (2 : Fin 4)
          hx_branch)
      · intro hx_branch
        exact hv1_not_A (mem_ofInduce_branch_subset (G := G) T (3 : Fin 4)
          hx_branch)
      · intro hx_branch
        exact hv1_not_A (mem_ofInduce_branch_subset (G := G) T (0 : Fin 4)
          hx_branch)
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (0 : Fin 4) (1 : Fin 4) (by decide))
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (0 : Fin 4) (2 : Fin 4) (by decide))
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (0 : Fin 4) (3 : Fin 4) (by decide))
      · intro hx_branch
        exact hv1_not_A (mem_ofInduce_branch_subset (G := G) T (1 : Fin 4)
          hx_branch)
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (1 : Fin 4) (0 : Fin 4) (by decide))
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (1 : Fin 4) (2 : Fin 4) (by decide))
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (1 : Fin 4) (3 : Fin 4) (by decide))
      · intro hx_branch
        exact hv1_not_A (mem_ofInduce_branch_subset (G := G) T (2 : Fin 4)
          hx_branch)
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (2 : Fin 4) (0 : Fin 4) (by decide))
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (2 : Fin 4) (1 : Fin 4) (by decide))
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (2 : Fin 4) (3 : Fin 4) (by decide))
      · intro hx_branch
        exact hv1_not_A (mem_ofInduce_branch_subset (G := G) T (3 : Fin 4)
          hx_branch)
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (3 : Fin 4) (0 : Fin 4) (by decide))
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (3 : Fin 4) (1 : Fin 4) (by decide))
      · exact SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp
          (Tg.vertex_disjoint (3 : Fin 4) (2 : Fin 4) (by decide))
    dominates := by
      intro i j hij v hv
      fin_cases i <;> fin_cases j <;> simp [branches, Tg] at hij hv ⊢
      · exact hA_subset_neighbors
          (mem_ofInduce_branch_subset (G := G) T (0 : Fin 4) hv)
      · exact hA_subset_neighbors
          (mem_ofInduce_branch_subset (G := G) T (1 : Fin 4) hv)
      · exact hA_subset_neighbors
          (mem_ofInduce_branch_subset (G := G) T (2 : Fin 4) hv)
      · exact hA_subset_neighbors
          (mem_ofInduce_branch_subset (G := G) T (3 : Fin 4) hv)
      · exact Tg.dominates (0 : Fin 4) (1 : Fin 4) (by decide) v hv
      · exact Tg.dominates (0 : Fin 4) (2 : Fin 4) (by decide) v hv
      · exact Tg.dominates (0 : Fin 4) (3 : Fin 4) (by decide) v hv
      · exact Tg.dominates (1 : Fin 4) (2 : Fin 4) (by decide) v hv
      · exact Tg.dominates (1 : Fin 4) (3 : Fin 4) (by decide) v hv
      · exact Tg.dominates (2 : Fin 4) (3 : Fin 4) (by decide) v hv
  }
  refine ⟨K, ?_⟩
  have hv1_mem : v1 ∈ (K.branch (0 : Fin 5)).verts := by
    simp [K, branches, SimpleGraph.singletonSubgraph_verts]
  have hv1_index : K.branchIndex v1 = 1 := by
    simpa using
      K.branchIndex_eq_add_one_of_mem (i := (0 : Fin 5)) hv1_mem
  have hv2_index_le_two : K.branchIndex v2 <= 2 := by
    by_cases hv2_branch0 : v2 ∈ (K.branch (1 : Fin 5)).verts
    · rw [K.branchIndex_eq_add_one_of_mem (i := (1 : Fin 5)) hv2_branch0]
      omega
    · have hv2_not_mem : forall i : Fin 5, v2 ∉ (K.branch i).verts := by
        intro i hi
        fin_cases i <;> simp [K, branches, Tg, SimpleGraph.singletonSubgraph_verts] at hi
        · exact edge.ne' hi
        · exact hv2_branch0 hi
        · exact not_mem_ofInduce_branch_of_forall_not_mem
            (G := G) T (1 : Fin 4) (hv2_late (1 : Fin 4) (by decide)) hi
        · exact not_mem_ofInduce_branch_of_forall_not_mem
            (G := G) T (2 : Fin 4) (hv2_late (2 : Fin 4) (by decide)) hi
        · exact not_mem_ofInduce_branch_of_forall_not_mem
            (G := G) T (3 : Fin 4) (hv2_late (3 : Fin 4) (by decide)) hi
      rw [K.branchIndex_eq_zero_of_forall_not_mem hv2_not_mem]
      omega
  change K.branchIndex v1 <= 1 ∧ K.branchIndex v2 <= 2 ∧
    (K.branchIndex v2 = 2 -> K.branchIndex v1 = 1)
  exact ⟨by omega, hv2_index_le_two, fun _ => hv1_index⟩

theorem counterexample_triangle_free_off_L
    [Fintype V]
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge)) :
    Not (HasTriangleDisjointFromPair G v1 v2) := by
  intro htriangle
  have hfour : IsFourConnected G := counterexample_four_connected C
  rcases lemma_four_connected_triangle hfour edge htriangle with hplanar | hmodel
  · exact C.not_four_colorable (FourColorTheorem.four_color_theorem G hplanar)
  · exact C.no_compatible_model hmodel

theorem counterexample_neighborhood_low_degree_vertex
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge)) :
    Exists fun u : V => G.Adj v1 u ∧ u ≠ v2 := by
  by_contra hno
  have hall : forall u : V, G.Adj v1 u -> u = v2 := by
    intro u hu
    by_contra hne
    exact hno ⟨u, hu, hne⟩
  have hcard_le : Fintype.card (G.neighborSet v1) <= 1 := by
    rw [Fintype.card_le_one_iff]
    intro x y
    apply Subtype.ext
    exact (hall x x.2).trans (hall y y.2).symm
  have hdeg_le : G.degree v1 <= 1 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    exact hcard_le
  have hdeg_ge : 4 <= G.degree v1 :=
    counterexample_min_degree_atLeast_four C v1
  omega

theorem counterexample_neighbor_subgraph_has_low_degree_vertex
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v1 v2 : V}
    {edge : G.Adj v1 v2}
    (C : MainInductionCounterexample G (.pair v1 v2 edge)) :
    Exists fun u : G.neighborSet v1 =>
      (u : V) ≠ v2 ∧ (G.induce (G.neighborSet v1)).degree u <= 2 := by
  classical
  let Nset : Set V := G.neighborSet v1
  let Ngraph : SimpleGraph Nset := G.induce Nset
  by_contra hno
  push Not at hno
  obtain ⟨x, hx_adj, hx_ne_v2⟩ :=
    counterexample_neighborhood_low_degree_vertex C
  let xN : Nset := ⟨x, hx_adj⟩
  have hxN_ne_v2 : (xN : V) ≠ v2 := hx_ne_v2
  have hhigh :
      forall u : Nset, (u : V) ≠ v2 -> 3 <= Ngraph.degree u := by
    intro u hu_ne
    have hgt := hno u hu_ne
    have hge := Nat.succ_le_of_lt hgt
    simpa [Ngraph, Nset] using hge
  let Comp : Ngraph.ConnectedComponent := Ngraph.connectedComponentMk xN
  letI : Fintype Comp := Comp.supp.toFinite.fintype
  haveI : DecidableRel Comp.toSimpleGraph.Adj := Classical.decRel _
  let xC : Comp :=
    ⟨xN, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hdeg_xN : 3 <= Ngraph.degree xN := hhigh xN hxN_ne_v2
  have hdeg_eq_x : Ngraph.degree xN = Comp.toSimpleGraph.degree xC := by
    simpa [Comp, xC] using
      (connectedComponent_degree_eq (G := Ngraph) Comp xC)
  have hdeg_xC : 3 <= Comp.toSimpleGraph.degree xC := by
    simpa [hdeg_eq_x] using hdeg_xN
  have hcard_comp : 4 <= Fintype.card Comp := by
    have hlt :
        Comp.toSimpleGraph.degree xC < Fintype.card Comp :=
      SimpleGraph.degree_lt_card_verts (G := Comp.toSimpleGraph) xC
    omega
  let v2N : Nset := ⟨v2, edge⟩
  let Lcomp : Finset Comp :=
    if hv2C : v2N ∈ Comp.supp then {⟨v2N, hv2C⟩} else ∅
  have hclique_Lcomp : Comp.toSimpleGraph.IsClique (Lcomp : Set Comp) := by
    intro a ha b hb hab
    by_cases hv2C : v2N ∈ Comp.supp
    · simp [Lcomp, hv2C] at ha hb
      exact False.elim (hab (ha.trans hb.symm))
    · simp [Lcomp, hv2C] at ha
  have hcard_Lcomp : Lcomp.card <= 2 := by
    by_cases hv2C : v2N ∈ Comp.supp <;> simp [Lcomp, hv2C]
  have hlow_Lcomp :
      forall y : Comp, Comp.toSimpleGraph.degree y <= 2 -> y ∈ Lcomp := by
    intro y hydeg
    by_cases hy_v2 : ((y : Nset) : V) = v2
    · have hyN_eq : (y : Nset) = v2N := Subtype.ext hy_v2
      have hv2C : v2N ∈ Comp.supp := by
        simpa [hyN_eq] using y.2
      have hy_eq : y = ⟨v2N, hv2C⟩ := Subtype.ext hyN_eq
      simp [Lcomp, hv2C, hy_eq]
    · have hdeg_eq_y :
          Ngraph.degree (y : Nset) = Comp.toSimpleGraph.degree y := by
        simpa [Comp] using
          (connectedComponent_degree_eq (G := Ngraph) Comp y)
      have hdegN_y : Ngraph.degree (y : Nset) <= 2 := by
        omega
      have hhigh_y : 3 <= Ngraph.degree (y : Nset) :=
        hhigh (y : Nset) hy_v2
      omega
  have hhigh_Lcomp :
      (Exists fun y : Comp =>
        y ∈ Lcomp ∧ 3 <= Comp.toSimpleGraph.degree y) ->
          Lcomp.card = 1 := by
    intro h
    by_cases hv2C : v2N ∈ Comp.supp
    · simp [Lcomp, hv2C]
    · rcases h with ⟨y, hyL, _⟩
      simp [Lcomp, hv2C] at hyL
  obtain ⟨Tcomp, hTcomp⟩ :=
    lemma_dominating_K4
      (G := Comp.toSimpleGraph)
      (SimpleGraph.ConnectedComponent.connected_toSimpleGraph Comp)
      hcard_comp Lcomp hclique_Lcomp hcard_Lcomp hlow_Lcomp hhigh_Lcomp
  let Tn : DominatingK4Model Ngraph := Tcomp.ofConnectedComponent Comp
  have hv2_late :
      forall i : Fin 4, 0 < (i : Nat) ->
        forall hv2A : v2 ∈ Nset,
          (⟨v2, hv2A⟩ : Nset) ∉ (Tn.branch i).verts := by
    intro i hi hv2A hv2_mem
    simp only [Tn, DominatingModel.ofConnectedComponent, DominatingModel.map,
      SimpleGraph.Subgraph.map_verts, Set.mem_image] at hv2_mem
    rcases hv2_mem with ⟨y, hy_branch, hyv2⟩
    have hyN_eq : (y : Nset) = ⟨v2, hv2A⟩ := hyv2
    by_cases hv2C : v2N ∈ Comp.supp
    · let v2C : Comp := ⟨v2N, hv2C⟩
      have hy_eq : y = v2C := by
        apply Subtype.ext
        exact hyN_eq.trans (Subtype.ext rfl)
      have hv2_branch0 : v2C ∈ (Tcomp.branch (0 : Fin 4)).verts := by
        have hv2C_mem_L : v2C ∈ Lcomp := by
          simp [Lcomp, hv2C, v2C]
        exact hTcomp v2C hv2C_mem_L
      have h0i : (0 : Fin 4) ≠ i := by
        intro h
        subst i
        simp at hi
      exact (Set.disjoint_left.mp (Tcomp.vertex_disjoint (0 : Fin 4) i h0i)
        hv2_branch0) (by simpa [hy_eq] using hy_branch)
    · have hy_supp : (⟨v2, hv2A⟩ : Nset) ∈ Comp.supp := by
        simpa [hyN_eq] using y.2
      exact hv2C (by simpa [v2N] using hy_supp)
  have hcompat : CompatibleDominatingK5Model (.pair v1 v2 edge) :=
    compatible_model_of_neighbor_induced_dominating_K4
      (G := G) edge (A := Nset) (by intro u hu; exact hu) ?_ Tn hv2_late
  · exact C.no_compatible_model hcompat
  · intro hv
    exact hv.ne rfl


end Schematic.Math.GraphTheory
