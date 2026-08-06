import DominatingFourColour.Prerequisites.RSTFlaps.EssentialWitnesses

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

theorem isPlanar_of_nonfeet_degree_bounds
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hnonfeet_degree_le_three :
      forall v : V, v ∉ Set.range feet -> G.degree v <= 3)
    (hhigh_three_nonfeet :
      {v : V | v ∉ Set.range feet ∧ 3 <= G.degree v}.ncard <= 2) :
    IsPlanar G := by
  classical
  have hdegree_four : {v : V | 4 <= G.degree v}.ncard <= 4 := by
    have hsubset : {v : V | 4 <= G.degree v} ⊆ Set.range feet := by
      intro v hv
      by_contra hvfeet
      have hle := hnonfeet_degree_le_three v hvfeet
      have hvdeg : 4 <= G.degree v := by
        simpa using hv
      omega
    have hle : {v : V | 4 <= G.degree v}.ncard <= 3 :=
      ncard_le_three_of_subset_range_feet hfeet_injective hsubset
    omega
  have hdegree_three : {v : V | 3 <= G.degree v}.ncard <= 5 := by
    let A : Set V := {v : V | 3 <= G.degree v}
    let B : Set V := Set.range feet
    let C : Set V := {v : V | v ∉ Set.range feet ∧ 3 <= G.degree v}
    have hsubset : A ⊆ B ∪ C := by
      intro v hv
      by_cases hvfeet : v ∈ Set.range feet
      · exact Or.inl hvfeet
      · exact Or.inr ⟨hvfeet, hv⟩
    have hB_card : B.ncard <= 3 := by
      have hB_subset : B ⊆ Set.range feet := by
        intro v hv
        exact hv
      simpa [B] using
        ncard_le_three_of_subset_range_feet hfeet_injective hB_subset
    have hC_card : C.ncard <= 2 := by
      simpa [C] using hhigh_three_nonfeet
    calc
      A.ncard <= (B ∪ C).ncard :=
        Set.ncard_le_ncard hsubset
      _ <= B.ncard + C.ncard :=
        Set.ncard_union_le B C
      _ <= 5 := by omega
  exact isPlanar_of_highDegree_bounds hdegree_four hdegree_three

theorem delete_feet_component_ncard_ge_two_of_mem_degree_atLeast_four
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (C : (G.induce (Set.range feet)ᶜ).ConnectedComponent)
    {v : V}
    (hvC : v ∈ induceComponentSupport (G := G) C)
    (hdegree : 4 <= G.degree v) :
    2 <= (induceComponentSupport (G := G) C).ncard := by
  classical
  have hinside :
      (G.neighborSet v ∩ Set.range feet).ncard <= 3 := by
    have hsubset :
        G.neighborSet v ∩ Set.range feet ⊆ Set.range feet :=
      Set.inter_subset_right
    have hcard_le :
        (G.neighborSet v ∩ Set.range feet).ncard <=
          (Set.range feet).ncard :=
      Set.ncard_le_ncard hsubset
    have hrange_card : (Set.range feet).ncard = 3 :=
      ncard_range_fin3_of_injective hfeet_injective
    omega
  obtain ⟨u, hu_delete, huv⟩ :=
    exists_neighbor_outside_set_of_degree_atLeast_four_of_inside_neighbors_atMost_three
      (G := G) (S := Set.range feet) (v := v) hdegree hinside
  have hu_not_feet : u ∉ Set.range feet := by
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hu_delete
    exact hu_delete.2
  have huC : u ∈ induceComponentSupport (G := G) C :=
    induceComponentSupport_mem_of_adj (G := G) C hvC hu_not_feet huv.symm
  have hpair_subset :
      ({v, u} : Set V) ⊆ induceComponentSupport (G := G) C := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hvC
    · exact huC
  have hpair_card : ({v, u} : Set V).ncard = 2 :=
    Set.ncard_pair huv.ne.symm
  have hle :=
    Set.ncard_le_ncard hpair_subset
  omega

theorem delete_feet_component_ncard_ge_two_of_degree_atLeast_four
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    {v : V}
    (hv_not_feet : v ∉ Set.range feet)
    (hdegree : 4 <= G.degree v) :
    let C : (G.induce (Set.range feet)ᶜ).ConnectedComponent :=
      (G.induce (Set.range feet)ᶜ).connectedComponentMk
        (⟨v, hv_not_feet⟩ : ((Set.range feet)ᶜ : Set V))
    2 <= (induceComponentSupport (G := G) C).ncard := by
  classical
  intro C
  exact delete_feet_component_ncard_ge_two_of_mem_degree_atLeast_four
    (G := G) hfeet_injective C
    (by
      exact ⟨hv_not_feet,
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩)
    hdegree

theorem delete_feet_component_ncard_ge_two_of_four_connected
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    (hG : IsFourConnected G)
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    {v : V}
    (hv_not_feet : v ∉ Set.range feet) :
    let C : (G.induce (Set.range feet)ᶜ).ConnectedComponent :=
      (G.induce (Set.range feet)ᶜ).connectedComponentMk
        (⟨v, hv_not_feet⟩ : ((Set.range feet)ᶜ : Set V))
    2 <= (induceComponentSupport (G := G) C).ncard :=
  delete_feet_component_ncard_ge_two_of_degree_atLeast_four
    (G := G) hfeet_injective hv_not_feet
    (four_connected_minDegree_atLeast_four hG v)

theorem neighborSet_subset_feet_of_delete_feet_components_subsingleton
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hcomponents_small :
      forall C : (G.induce (Set.range feet)ᶜ).ConnectedComponent,
        (induceComponentSupport (G := G) C).ncard <= 1)
    {v : V}
    (hv_not_feet : v ∉ Set.range feet) :
    G.neighborSet v ⊆ Set.range feet := by
  intro w hw
  by_contra hw_not_feet
  let vA : ((Set.range feet)ᶜ : Set V) := ⟨v, hv_not_feet⟩
  let C : (G.induce (Set.range feet)ᶜ).ConnectedComponent :=
    (G.induce (Set.range feet)ᶜ).connectedComponentMk vA
  let K : Set V := induceComponentSupport (G := G) C
  have hvK : v ∈ K := by
    exact ⟨hv_not_feet,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hwK : w ∈ K := by
    have hw_compl : w ∈ (Set.range feet)ᶜ := by
      simpa using hw_not_feet
    exact induceComponentSupport_mem_of_adj (G := G) C hvK hw_compl hw
  have hpair_subset : ({v, w} : Set V) ⊆ K := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hvK
    · exact hwK
  have hpair_card : ({v, w} : Set V).ncard = 2 :=
    Set.ncard_pair hw.ne
  have hK_two : 2 <= K.ncard := by
    have hle := Set.ncard_le_ncard hpair_subset
    omega
  have hK_small : K.ncard <= 1 := by
    simpa [K] using hcomponents_small C
  omega

theorem nonfeet_degree_le_three_of_delete_feet_components_subsingleton
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hcomponents_small :
      forall C : (G.induce (Set.range feet)ᶜ).ConnectedComponent,
        (induceComponentSupport (G := G) C).ncard <= 1) :
    forall v : V, v ∉ Set.range feet -> G.degree v <= 3 := by
  intro v hv_not_feet
  have hsubset : G.neighborSet v ⊆ Set.range feet :=
    neighborSet_subset_feet_of_delete_feet_components_subsingleton
      (G := G) hcomponents_small hv_not_feet
  have hneigh_card : (G.neighborSet v).ncard <= 3 :=
    ncard_le_three_of_subset_range_feet hfeet_injective hsubset
  have hdegree : (G.neighborSet v).ncard = G.degree v := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  omega

theorem common_neighbor_adjacency_of_nonfoot_degree_three_component_subsingleton
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hcomponents_small :
      forall C : (G.induce (Set.range feet)ᶜ).ConnectedComponent,
        (induceComponentSupport (G := G) C).ncard <= 1)
    {v : V}
    (hv_not_feet : v ∉ Set.range feet)
    (hdegree : 3 <= G.degree v) :
    forall i : Fin 3, G.Adj v (feet i) := by
  intro i
  have hsubset : G.neighborSet v ⊆ Set.range feet :=
    neighborSet_subset_feet_of_delete_feet_components_subsingleton
      (G := G) hcomponents_small hv_not_feet
  have hneigh_degree : (G.neighborSet v).ncard = G.degree v := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  have hrange_card : (Set.range feet).ncard = 3 :=
    ncard_range_fin3_of_injective hfeet_injective
  have hrange_le_neigh : (Set.range feet).ncard <= (G.neighborSet v).ncard := by
    rw [hneigh_degree, hrange_card]
    exact hdegree
  have hneigh_eq : G.neighborSet v = Set.range feet :=
    Set.eq_of_subset_of_ncard_le hsubset hrange_le_neigh
  have hfoot_mem : feet i ∈ G.neighborSet v := by
    rw [hneigh_eq]
    exact ⟨i, rfl⟩
  exact hfoot_mem

theorem high_three_nonfeet_ncard_le_one_of_components_subsingleton_no_legless
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hcomponents_small :
      forall C : (G.induce (Set.range feet)ᶜ).ConnectedComponent,
        (induceComponentSupport (G := G) C).ncard <= 1)
    (hno_legless : Not (Nonempty (LeglessTripod G feet))) :
    {v : V | v ∉ Set.range feet ∧ 3 <= G.degree v}.ncard <= 1 := by
  classical
  by_contra hnot
  have htwo : 1 < {v : V | v ∉ Set.range feet ∧ 3 <= G.degree v}.ncard := by
    omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Set.one_lt_ncard
      (s := {v : V | v ∉ Set.range feet ∧ 3 <= G.degree v})).mp htwo
  have ha_not_feet : a ∉ Set.range feet := ha.1
  have hb_not_feet : b ∉ Set.range feet := hb.1
  have hadj_a : forall i : Fin 3, G.Adj a (feet i) :=
    common_neighbor_adjacency_of_nonfoot_degree_three_component_subsingleton
      (G := G) hfeet_injective hcomponents_small ha_not_feet ha.2
  have hadj_b : forall i : Fin 3, G.Adj b (feet i) :=
    common_neighbor_adjacency_of_nonfoot_degree_three_component_subsingleton
      (G := G) hfeet_injective hcomponents_small hb_not_feet hb.2
  have hapex_a : forall i : Fin 3, a ≠ feet i := by
    intro i h
    exact ha_not_feet ⟨i, h.symm⟩
  have hapex_b : forall i : Fin 3, b ≠ feet i := by
    intro i h
    exact hb_not_feet ⟨i, h.symm⟩
  exact hno_legless ⟨
    LeglessTripod.of_two_common_neighbors
      (G := G) hapex_a hadj_a hapex_b hadj_b hab⟩

theorem common_neighbors_all_feet_ncard_le_one_of_no_legless
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno_legless : Not (Nonempty (LeglessTripod G feet))) :
    {v : V | forall i : Fin 3, G.Adj v (feet i)}.ncard <= 1 := by
  classical
  by_contra hnot
  have htwo :
      1 < {v : V | forall i : Fin 3, G.Adj v (feet i)}.ncard := by
    omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Set.one_lt_ncard
      (s := {v : V | forall i : Fin 3, G.Adj v (feet i)})).mp htwo
  have hapex_a : forall i : Fin 3, a ≠ feet i := by
    intro i h
    exact (ha i).ne h
  have hapex_b : forall i : Fin 3, b ≠ feet i := by
    intro i h
    exact (hb i).ne h
  exact hno_legless ⟨
    LeglessTripod.of_two_common_neighbors
      (G := G) hapex_a ha hapex_b hb hab⟩

theorem common_neighbors_all_feet_in_set_ncard_le_one_of_no_legless
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno_legless : Not (Nonempty (LeglessTripod G feet)))
    (S : Set V) :
    {v : V | v ∈ S ∧ forall i : Fin 3, G.Adj v (feet i)}.ncard <= 1 := by
  classical
  have hsubset :
      {v : V | v ∈ S ∧ forall i : Fin 3, G.Adj v (feet i)} ⊆
        {v : V | forall i : Fin 3, G.Adj v (feet i)} := by
    intro v hv
    exact hv.2
  exact le_trans (Set.ncard_le_ncard hsubset)
    (common_neighbors_all_feet_ncard_le_one_of_no_legless
      (G := G) hno_legless)

theorem exists_non_common_neighbor_in_large_set_of_no_legless
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno_legless : Not (Nonempty (LeglessTripod G feet)))
    {S : Set V}
    (hS_large : 2 <= S.ncard) :
    Exists fun v : V =>
      v ∈ S ∧ Not (forall i : Fin 3, G.Adj v (feet i)) := by
  classical
  by_contra hnone
  have hsubset :
      S ⊆ {v : V | v ∈ S ∧ forall i : Fin 3, G.Adj v (feet i)} := by
    intro v hvS
    refine ⟨hvS, ?_⟩
    by_contra hnot_common
    exact hnone ⟨v, hvS, hnot_common⟩
  have hS_le :
      S.ncard <=
        {v : V | v ∈ S ∧ forall i : Fin 3, G.Adj v (feet i)}.ncard :=
    Set.ncard_le_ncard hsubset
  have hcommon_le :
      {v : V | v ∈ S ∧ forall i : Fin 3, G.Adj v (feet i)}.ncard <= 1 :=
    common_neighbors_all_feet_in_set_ncard_le_one_of_no_legless
      (G := G) hno_legless S
  omega

theorem large_delete_feet_component_has_noncommon_vertex_of_no_legless
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno_legless : Not (Nonempty (LeglessTripod G feet)))
    (C : (G.induce (Set.range feet)ᶜ).ConnectedComponent)
    (hC_large : 2 <= (induceComponentSupport (G := G) C).ncard) :
    Exists fun v : V =>
      v ∈ induceComponentSupport (G := G) C ∧
        Not (forall i : Fin 3, G.Adj v (feet i)) :=
  exists_non_common_neighbor_in_large_set_of_no_legless
    (G := G) hno_legless hC_large

theorem isPlanar_of_delete_feet_components_subsingleton_no_legless
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hcomponents_small :
      forall C : (G.induce (Set.range feet)ᶜ).ConnectedComponent,
        (induceComponentSupport (G := G) C).ncard <= 1)
    (hno_legless : Not (Nonempty (LeglessTripod G feet))) :
    IsPlanar G := by
  exact isPlanar_of_nonfeet_degree_bounds
    (G := G) hfeet_injective
    (nonfeet_degree_le_three_of_delete_feet_components_subsingleton
      (G := G) hfeet_injective hcomponents_small)
    (by
      have hle :
          {v : V | v ∉ Set.range feet ∧ 3 <= G.degree v}.ncard <= 1 :=
        high_three_nonfeet_ncard_le_one_of_components_subsingleton_no_legless
          (G := G) hfeet_injective hcomponents_small hno_legless
      omega)

theorem Triad.complement_flapVertexSet_ncard_ge_four_of_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {B C : T.Flap}
    (hBC : B ≠ C) :
    4 <= (T.flapVertexSet B)ᶜ.ncard := by
  obtain ⟨x, hxC⟩ := T.flapVertexSet_nonempty C
  have hfeet : forall i : Fin 3, feet i ∉ T.flapVertexSet B := by
    intro i hfootB
    exact (T.flapVertexSet_subset_complement B hfootB) (T.foot_mem_vertexSet i)
  have hxB : x ∉ T.flapVertexSet B := by
    intro hxB
    exact Set.disjoint_left.mp (T.disjoint_flapVertexSet_of_ne hBC) hxB hxC
  have hx_not_feet : x ∉ Set.range feet := by
    rintro ⟨i, rfl⟩
    exact (T.flapVertexSet_subset_complement C hxC) (T.foot_mem_vertexSet i)
  exact ncard_complement_ge_four_of_feet_and_extra
    hfeet_injective hfeet hxB hx_not_feet

theorem RST31NoSeparation.no_blocked_core
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST31NoSeparation G feet)
    {K B : Set V}
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b))
    (hfeet : forall i : Fin 3, feet i ∉ K)
    (hleft_card : 4 <= Kᶜ.ncard)
    (hK : K.Nonempty)
    (hB : B.ncard <= 3) :
    False := by
  classical
  let S : Separation G := Separation.ofCoreAndBoundary K B hclosed
  have hfeet_left : forall i : Fin 3, feet i ∈ S.left := by
    intro i
    exact hfeet i
  have hright_only : (S.right \ S.left).Nonempty := by
    simpa [S] using
      Separation.ofCoreAndBoundary_right_only_nonempty
        (G := G) K B hclosed hK
  have horder : S.OrderAtMost 3 := by
    simpa [S] using
      Separation.ofCoreAndBoundary_orderAtMost_of_boundary_ncard_le
        (G := G) K B hclosed hB
  exact hno S hfeet_left (by simpa [S, Separation.ofCoreAndBoundary] using hleft_card)
    hright_only horder

theorem RST31NoSeparation.complement_ncard_le_three_of_blocked_core
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST31NoSeparation G feet)
    {K B : Set V}
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b))
    (hfeet : forall i : Fin 3, feet i ∉ K)
    (hK : K.Nonempty)
    (hB : B.ncard <= 3) :
    Kᶜ.ncard <= 3 := by
  by_contra hlarge_not
  have hlarge : 4 <= Kᶜ.ncard := by omega
  exact hno.no_blocked_core hclosed hfeet hlarge hK hB

theorem RST31NoSeparation.core_complement_subset_feet_of_boundary_le_three
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {K B : Set V}
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b))
    (hfeet : forall i : Fin 3, feet i ∉ K)
    (hK : K.Nonempty)
    (hB : B.ncard <= 3) :
    Kᶜ ⊆ Set.range feet := by
  intro x hxK
  by_contra hx_not_feet
  have hle : Kᶜ.ncard <= 3 :=
    hno.complement_ncard_le_three_of_blocked_core
      hclosed hfeet hK hB
  have hge : 4 <= Kᶜ.ncard :=
    ncard_complement_ge_four_of_feet_and_extra
      hfeet_injective hfeet hxK hx_not_feet
  omega

theorem RST31NoSeparation.component_boundary_complement_ncard_le_three
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST31NoSeparation G feet)
    {S : Set V}
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hfeet :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C)
    (hboundary :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S).ncard <= 3) :
    (induceComponentSupport (G := G) C)ᶜ.ncard <= 3 := by
  exact hno.complement_ncard_le_three_of_blocked_core
    (induceComponentSupport_closed_with_relativeBoundary (G := G) C)
    hfeet
    (induceComponentSupport_nonempty (G := G) C)
    hboundary

theorem RST31NoSeparation.component_complement_subset_feet_of_boundary_le_three
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {S : Set V}
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hfeet :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C)
    (hboundary :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S).ncard <= 3) :
    (induceComponentSupport (G := G) C)ᶜ ⊆ Set.range feet := by
  exact hno.core_complement_subset_feet_of_boundary_le_three hfeet_injective
    (induceComponentSupport_closed_with_relativeBoundary (G := G) C)
    hfeet (induceComponentSupport_nonempty (G := G) C) hboundary

theorem RST31NoSeparation.component_complement_subset_feet_of_essential_boundary_witness
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {S X : Set V}
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hfeet :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C)
    (T : Triad G feet)
    (hboundary_essential :
      relativeVertexBoundary G (induceComponentSupport (G := G) C) S ⊆
        {v : V | T.EssentialWithin X v})
    (T' : Triad G feet)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ X)
    (hboundary_inter_T' :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S ∩
        T'.vertexSet).ncard <= 3) :
    (induceComponentSupport (G := G) C)ᶜ ⊆ Set.range feet := by
  have hboundary :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S).ncard <= 3 :=
    T.ncard_le_of_essentialWithin_witness_triad
      hboundary_essential T' hT'_subset hboundary_inter_T'
  exact hno.component_complement_subset_feet_of_boundary_le_three
    hfeet_injective C hfeet hboundary

theorem RST31NoSeparation.component_complement_subset_feet_of_essential_boundary_tree_root_pair_paths
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {S X : Set V}
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hfeet :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C)
    (T : Triad G feet)
    (hboundary_essential :
      relativeVertexBoundary G (induceComponentSupport (G := G) C) S ⊆
        {v : V | T.EssentialWithin X v})
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hH_feet : forall i : Fin 3, feet i ∈ H.verts)
    (hapex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i)
    (hpair_path_through_apex :
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (feet i) (feet j) =>
          p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ X)
    (hboundary_inter_H :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S ∩
        H.verts).ncard <= 3) :
    (induceComponentSupport (G := G) C)ᶜ ⊆ Set.range feet := by
  have hboundary :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S).ncard <= 3 :=
    T.ncard_le_of_essentialWithin_tree_root_pair_paths
      hboundary_essential hH_tree hH_feet hapex_not_foot
      hpair_path_through_apex hH_subset hboundary_inter_H
  exact hno.component_complement_subset_feet_of_boundary_le_three
    hfeet_injective C hfeet hboundary

theorem RST31NoSeparation.component_complement_subset_feet_of_essential_boundary_tree_root_delete_unreachable
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {S X : Set V}
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hfeet :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C)
    (T : Triad G feet)
    (hboundary_essential :
      relativeVertexBoundary G (induceComponentSupport (G := G) C) S ⊆
        {v : V | T.EssentialWithin X v})
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hH_feet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hH_feet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hH_feet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hH_feet j⟩ : H.verts), by exact hfoot_ne_apex j⟩)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ X)
    (hboundary_inter_H :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S ∩
        H.verts).ncard <= 3) :
    (induceComponentSupport (G := G) C)ᶜ ⊆ Set.range feet := by
  have hboundary :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S).ncard <= 3 :=
    T.ncard_le_of_essentialWithin_tree_root_delete_unreachable
      hboundary_essential hH_tree hH_feet hfoot_ne_apex
      hunreachable hH_subset hboundary_inter_H
  exact hno.component_complement_subset_feet_of_boundary_le_three
    hfeet_injective C hfeet hboundary

theorem Triad.exists_lean_subtriad_subset_avoids_set
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {W : Set V}
    (havoid : T.AvoidsSet W) :
    Exists fun T' : Triad G feet =>
      T'.Lean ∧ T'.vertexSet ⊆ T.vertexSet ∧ T'.AvoidsSet W := by
  obtain ⟨T', hlean, hsubset⟩ := T.exists_lean_subtriad_subset
  refine ⟨T', hlean, hsubset, ?_⟩
  rw [Triad.AvoidsSet, Set.disjoint_left] at havoid ⊢
  intro v hvT' hvW
  exact havoid (hsubset hvT') hvW

structure RST31LeanTriadData
    (G : SimpleGraph V) (feet : Fin 3 -> V) (W : Set V) where
  triad : Triad G feet
  lean : triad.Lean
  avoids_W : triad.AvoidsSet W
  complement_connected : (G.induce triad.vertexSetᶜ).Connected

structure RST31OneFlapTriadData
    (G : SimpleGraph V) (feet : Fin 3 -> V) (W : Set V) where
  triad : Triad G feet
  lean : triad.Lean
  avoids_W : triad.AvoidsSet W
  one_flap : Subsingleton triad.Flap

def RST31OneFlapTriadData.to_rst31LeanTriadData
    {feet : Fin 3 -> V}
    {W : Set V}
    (D : RST31OneFlapTriadData G feet W)
    (hW_nonempty : W.Nonempty) :
    RST31LeanTriadData G feet W where
  triad := D.triad
  lean := D.lean
  avoids_W := D.avoids_W
  complement_connected := by
    obtain ⟨w, hwW⟩ := hW_nonempty
    have hw_compl : w ∈ D.triad.vertexSetᶜ := by
      intro hwT
      exact Set.disjoint_left.mp D.avoids_W hwT hwW
    exact D.triad.complement_connected_of_subsingleton_flaps
      ⟨w, hw_compl⟩ D.one_flap

def RST31LeanTriadData.to_rst31OneFlapTriadData
    {feet : Fin 3 -> V}
    {W : Set V}
    (D : RST31LeanTriadData G feet W) :
    RST31OneFlapTriadData G feet W where
  triad := D.triad
  lean := D.lean
  avoids_W := D.avoids_W
  one_flap := D.triad.subsingleton_flaps_of_complement_connected
    D.complement_connected

def RST31LeanTriadData.mono
    {feet : Fin 3 -> V}
    {W W' : Set V}
    (D : RST31LeanTriadData G feet W)
    (hW' : W' ⊆ W) :
    RST31LeanTriadData G feet W' where
  triad := D.triad
  lean := D.lean
  avoids_W := by
    have havoid : Disjoint D.triad.vertexSet W := D.avoids_W
    rw [Set.disjoint_left] at havoid
    rw [Triad.AvoidsSet, Set.disjoint_left]
    intro v hvT hvW'
    exact havoid hvT (hW' hvW')
  complement_connected := D.complement_connected

def RST31Statement (G : SimpleGraph V) (feet : Fin 3 -> V) : Prop :=
  forall T₀ : Triad G feet,
    forall B₀ : T₀.Flap,
      RST31NoSeparation G feet ->
        Nonempty (RST31LeanTriadData G feet (T₀.flapVertexSet B₀))

def RST31OneFlapStatement (G : SimpleGraph V) (feet : Fin 3 -> V) : Prop :=
  forall T₀ : Triad G feet,
    forall B₀ : T₀.Flap,
      RST31NoSeparation G feet ->
        Nonempty (RST31OneFlapTriadData G feet (T₀.flapVertexSet B₀))

theorem RST31OneFlapStatement.to_rst31Statement
    {feet : Fin 3 -> V}
    (h31 : RST31OneFlapStatement G feet) :
    RST31Statement G feet := by
  intro T₀ B₀ hno
  rcases h31 T₀ B₀ hno with ⟨D⟩
  exact ⟨D.to_rst31LeanTriadData (T₀.flapVertexSet_nonempty B₀)⟩

theorem RST31Statement.to_rst31OneFlapStatement
    {feet : Fin 3 -> V}
    (h31 : RST31Statement G feet) :
    RST31OneFlapStatement G feet := by
  intro T₀ B₀ hno
  rcases h31 T₀ B₀ hno with ⟨D⟩
  exact ⟨D.to_rst31OneFlapTriadData⟩

theorem RST31Statement.root_singleton
    {feet : Fin 3 -> V}
    (h31 : RST31Statement G feet)
    (hno : RST31NoSeparation G feet)
    (T₀ : Triad G feet)
    {root : V}
    (hroot : root ∉ T₀.vertexSet) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  obtain ⟨B₀, hrootB₀⟩ := T₀.exists_flap_containing_vertex_outside hroot
  rcases h31 T₀ B₀ hno with ⟨D⟩
  exact ⟨D.mono (by
    intro v hv
    have hvroot : v = root := by simpa using hv
    simpa [hvroot] using hrootB₀)⟩

theorem RST31Statement.root_singleton_of_fourConnected
    [Fintype V]
    {feet : Fin 3 -> V}
    (h31 : RST31Statement G feet)
    (hG : IsFourConnected G)
    (T₀ : Triad G feet)
    {root : V}
    (hroot : root ∉ T₀.vertexSet) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) :=
  h31.root_singleton (hG.rst31_noSeparation feet) T₀ hroot

theorem RST31OneFlapStatement.root_singleton_of_rst34_rst35_fourConnected_nonplanar
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31OneFlapStatement G feet)
    (h34 : RST34LeglessTripodStatement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet)
    (hnonplanar : Not (IsPlanar G)) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  obtain ⟨T⟩ :=
    h34.legless_tripod_of_rst35_fourConnected_nonplanar
      h35 hG hfeet_injective hnonplanar
  rcases T.vertex_avoids_first_or_second hroot_not_feet with hroot_first | hroot_second
  · exact h31.to_rst31Statement.root_singleton_of_fourConnected hG T.first hroot_first
  · exact h31.to_rst31Statement.root_singleton_of_fourConnected hG T.second hroot_second

theorem rst_planar_or_rst31_lean_triad_data_of_literal_rst_inputs
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (h31 : RST31OneFlapStatement G feet)
    (h34 : RST34LeglessTripodStatement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet) :
    IsPlanar G ∨ Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  by_cases hplanar : IsPlanar G
  · exact Or.inl hplanar
  · exact Or.inr
      (h31.root_singleton_of_rst34_rst35_fourConnected_nonplanar
        h34 h35 hG hfeet_injective hroot_not_feet hplanar)

def RST31LeanTriadData.to_rstLeanTriadData
    {feet : Fin 3 -> V}
    {W : Set V}
    {root : V}
    (D : RST31LeanTriadData G feet W)
    (hrootW : root ∈ W)
    (hinside :
      forall v : V,
        v ∈ (D.triad.carrier.deleteVerts (Set.range feet)).verts ->
          (G.neighborSet v ∩ D.triad.vertexSet).ncard <= 3)
    (hfoot_outside :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts D.triad.vertexSet).verts ∧
            G.Adj u (feet i)) :
    RSTLeanTriadData G feet root where
  triad := D.triad
  lean := D.lean
  complement_connected := D.complement_connected
  root_outside := by
    have hdisjoint : Disjoint D.triad.vertexSet W := D.avoids_W
    exact fun hroot => Set.disjoint_left.mp hdisjoint hroot hrootW
  inside_neighbors_at_most_three := hinside
  foot_has_neighbor_outside := hfoot_outside

def RST31LeanTriadData.to_rstLeanTriadData_of_min_degree_four
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {W : Set V}
    {root : V}
    (D : RST31LeanTriadData G feet W)
    (hrootW : root ∈ W)
    (hmin_degree : forall v : V, 4 <= G.degree v)
    (hinside :
      forall v : V,
        v ∈ (D.triad.carrier.deleteVerts (Set.range feet)).verts ->
          (G.neighborSet v ∩ D.triad.vertexSet).ncard <= 3)
    (hfoot_inside :
      forall i : Fin 3,
        (G.neighborSet (feet i) ∩ D.triad.vertexSet).ncard <= 3) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData hrootW hinside (by
    intro i
    exact exists_neighbor_outside_set_of_degree_atLeast_four_of_inside_neighbors_atMost_three
      (G := G) (S := D.triad.vertexSet) (v := feet i)
      (hmin_degree (feet i)) (hfoot_inside i))

def RST31LeanTriadData.to_rstLeanTriadData_of_lean_and_foot_outside
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {root : V}
    (D : RST31LeanTriadData G feet W)
    (hrootW : root ∈ W)
    (hfeet_injective : Function.Injective feet)
    (hfoot_outside :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts D.triad.vertexSet).verts ∧
            G.Adj u (feet i)) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData hrootW
    (D.triad.inside_neighbors_at_most_three_of_lean D.lean hfeet_injective)
    hfoot_outside

def RST31LeanTriadData.to_rstLeanTriadData_of_lean_and_foot_outside_singleton
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {root : V}
    (D : RST31LeanTriadData G feet ({root} : Set V))
    (hfeet_injective : Function.Injective feet)
    (hfoot_outside :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts D.triad.vertexSet).verts ∧
            G.Adj u (feet i)) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_lean_and_foot_outside
    (by simp) hfeet_injective hfoot_outside

def RST31LeanTriadData.to_rstLeanTriadData_of_foot_witnesses_in_W
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {root : V}
    (D : RST31LeanTriadData G feet W)
    (hrootW : root ∈ W)
    (hfeet_injective : Function.Injective feet)
    (hfootW :
      forall i : Fin 3,
        Exists fun u : V => u ∈ W ∧ G.Adj u (feet i)) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_lean_and_foot_outside hrootW hfeet_injective
    (by
      intro i
      obtain ⟨u, huW, hui⟩ := hfootW i
      refine ⟨u, ?_, hui⟩
      rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
      exact ⟨by simp, fun huD => Set.disjoint_left.mp D.avoids_W huD huW⟩)


end Schematic.Math.GraphTheory
