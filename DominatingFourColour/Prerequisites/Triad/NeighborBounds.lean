import DominatingFourColour.Prerequisites.Triad.SameLegRerouting

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

theorem Triad.leg_length_pos
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (i : Fin 3) :
    0 < (T.leg i).length :=
  SimpleGraph.Walk.not_nil_iff_lt_length.mp
    (SimpleGraph.Walk.not_nil_of_ne (p := T.leg i) (T.apex_not_foot i))

theorem Triad.not_lean_of_foot_adj_internal_other_leg_of_long_own_leg
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j : Fin 3}
    (hij : i ≠ j)
    {y : V}
    (hyj : y ∈ Walk.InternalVertices (T.leg j))
    (hlen_i : 1 < (T.leg i).length)
    (hiy : G.Adj (feet i) y) :
    ¬ T.Lean := by
  obtain ⟨k, hik, hjk⟩ := fin3_exists_ne_ne hij
  let x : V := (T.leg i).penultimate
  have hnot_nil : ¬ (T.leg i).Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := T.leg i) (T.apex_not_foot i)
  have hx_support : x ∈ (T.leg i).support := by
    exact List.mem_of_mem_dropLast
      ((T.leg i).penultimate_mem_dropLast_support hnot_nil)
  have hx_ne_apex : x ≠ T.apex := by
    simpa [x] using
      Schematic.Math.GraphTheory.Walk.IsPath.penultimate_ne_start_of_length_gt_one
        (G := G) (p := T.leg i) (T.leg_isPath i) hlen_i
  have hx_ne_foot : x ≠ feet i := by
    simpa [x] using (T.leg i).adj_penultimate hnot_nil |>.ne
  have hfoot_ne_apex : feet i ≠ T.apex :=
    (T.apex_not_foot i).symm
  have hidx :
      (T.leg i).support.idxOf x <
        (T.leg i).support.idxOf (feet i) := by
    exact Schematic.Math.GraphTheory.Walk.IsPath.idxOf_lt_end_of_mem_support_ne_end
      (T.leg_isPath i) hx_support hx_ne_foot
  exact T.not_lean_of_internal_adj_same_leg_ordered
    hfeet_injective
    (i := j) (j := i) (k := k)
    (fun h => hij h.symm) hjk hik
    (v := y) (x := x) (y := feet i)
    hyj hx_support (T.leg i).end_mem_support
    hx_ne_apex hfoot_ne_apex hidx hiy.symm

theorem Triad.foot_cross_neighbors_subset_of_no_internal_cross
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3)
    (hno_cross :
      forall {j : Fin 3} {y : V}, i ≠ j ->
        y ∈ Walk.InternalVertices (T.leg j) -> ¬ G.Adj (feet i) y) :
    G.neighborSet (feet i) ∩ T.vertexSet ⊆
      (G.neighborSet (feet i) ∩
        {v : V | v ∈ (T.leg i).support}) ∪
          (Set.range feet \ {feet i}) := by
  intro y hy
  by_cases hy_own : y ∈ (T.leg i).support
  · exact Or.inl ⟨hy.1, hy_own⟩
  · rcases hy.2 with ⟨j, hyj_support⟩
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hy_own hyj_support
    by_cases hy_foot_j : y = feet j
    · exact Or.inr ⟨⟨j, hy_foot_j.symm⟩, by
        intro hy_single
        have hy_eq_i : y = feet i := Set.mem_singleton_iff.mp hy_single
        have hfeet_eq : feet j = feet i := by
          rw [← hy_foot_j, hy_eq_i]
        exact hji (hfeet_injective hfeet_eq)⟩
    · have hy_ne_apex : y ≠ T.apex := by
        intro hy_apex
        exact hy_own (by simp [hy_apex])
      have hy_internal : y ∈ Walk.InternalVertices (T.leg j) :=
        ⟨hyj_support, hy_ne_apex, hy_foot_j⟩
      exact False.elim (hno_cross (fun hij => hji hij.symm) hy_internal hy.1)

theorem Triad.foot_cross_neighbors_subset_of_lean_long_legs
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3) :
    1 < (T.leg i).length ->
    G.neighborSet (feet i) ∩ T.vertexSet ⊆
      (G.neighborSet (feet i) ∩
        {v : V | v ∈ (T.leg i).support}) ∪
          (Set.range feet \ {feet i}) := by
  intro hlong_i
  apply T.foot_cross_neighbors_subset_of_no_internal_cross hfeet_injective i
  intro j y hij hy_internal hadj
  exact (T.not_lean_of_foot_adj_internal_other_leg_of_long_own_leg
    hfeet_injective hij hy_internal hlong_i hadj) hlean

theorem Triad.foot_cross_neighbors_subset_of_lean_all_long_legs
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    (hlong : forall i : Fin 3, 1 < (T.leg i).length)
    (i : Fin 3) :
    G.neighborSet (feet i) ∩ T.vertexSet ⊆
      (G.neighborSet (feet i) ∩
        {v : V | v ∈ (T.leg i).support}) ∪
          (Set.range feet \ {feet i}) :=
  T.foot_cross_neighbors_subset_of_lean_long_legs
    hlean hfeet_injective i (hlong i)

theorem Triad.foot_has_neighbor_in_punctured_carrier
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3) :
    Exists fun u : V =>
      u ∈ (T.carrier.deleteVerts (Set.range feet)).verts ∧ G.Adj u (feet i) := by
  classical
  let p := T.leg i
  have hp_not_nil : ¬ p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p) (T.apex_not_foot i)
  have hpen_support : p.penultimate ∈ p.support :=
    List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hp_not_nil)
  have hpen_not_feet : p.penultimate ∉ Set.range feet := by
    rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      exact (p.adj_penultimate hp_not_nil).ne hj.symm
    · have hinternal : feet j ∈ Walk.InternalVertices p := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hj]
          exact hpen_support
        · exact (T.apex_not_foot j).symm
        · intro h_eq
          exact hji (hfeet_injective h_eq)
      exact T.internal_vertices_avoid_feet j i hinternal
  refine ⟨p.penultimate, ?_, p.adj_penultimate hp_not_nil⟩
  rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
  constructor
  · rw [← T.vertexSet_eq_carrier_verts]
    exact ⟨i, hpen_support⟩
  · exact hpen_not_feet

theorem Triad.takeUntil_support_avoids_feet
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i : Fin 3}
    {u : V}
    (hu : u ∈ (T.leg i).support)
    (hu_not_feet : u ∉ Set.range feet)
    {x : V}
    (hx : x ∈ ((T.leg i).takeUntil u hu).support) :
    x ∉ Set.range feet := by
  rintro ⟨k, rfl⟩
  by_cases hki : k = i
  · subst k
    have hendpoint :
        feet i ∉ ((T.leg i).takeUntil u hu).support := by
      exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil
        (T.leg_isPath i) hu (by
          intro h
          exact hu_not_feet ⟨i, h⟩)
    exact hendpoint hx
  · have hx_leg : feet k ∈ (T.leg i).support :=
      SimpleGraph.Walk.support_takeUntil_subset (T.leg i) hu hx
    have h_internal : feet k ∈ Walk.InternalVertices (T.leg i) := by
      refine ⟨hx_leg, ?_, ?_⟩
      · exact (T.apex_not_foot k).symm
      · intro hki_feet
        exact hki (hfeet_injective hki_feet)
    exact T.internal_vertices_avoid_feet k i h_internal

theorem Triad.exists_walk_to_apex_in_punctured_carrier
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {u : V}
    (hu : u ∈ (T.carrier.deleteVerts (Set.range feet)).verts) :
    Exists fun p : G.Walk u T.apex =>
      p.toSubgraph ≤ T.carrier.deleteVerts (Set.range feet) := by
  classical
  rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hu
  rw [T.mem_carrier_verts_iff] at hu
  rcases hu.1 with ⟨i, hui⟩
  let pref : G.Walk (T.apex) u := (T.leg i).takeUntil u hui
  have hpref_le_leg : pref.toSubgraph ≤ (T.leg i).toSubgraph :=
    Walk.toSubgraph_le_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil (T.leg i) hui)
  refine ⟨pref.reverse, ?_⟩
  rw [SimpleGraph.Walk.toSubgraph_reverse]
  constructor
  · intro x hx
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
    constructor
    · exact (T.leg_toSubgraph_le_carrier i).1 (hpref_le_leg.1 hx)
    · exact T.takeUntil_support_avoids_feet hfeet_injective hui hu.2
        (pref.mem_verts_toSubgraph.mp hx)
  · intro x y hxy
    rw [SimpleGraph.Subgraph.deleteVerts_adj]
    have hx_pref : x ∈ pref.toSubgraph.verts :=
      pref.toSubgraph.edge_vert hxy
    have hy_pref : y ∈ pref.toSubgraph.verts :=
      pref.toSubgraph.edge_vert hxy.symm
    exact ⟨
      (T.leg_toSubgraph_le_carrier i).1 (hpref_le_leg.1 hx_pref),
      T.takeUntil_support_avoids_feet hfeet_injective hui hu.2
        (pref.mem_verts_toSubgraph.mp hx_pref),
      (T.leg_toSubgraph_le_carrier i).1 (hpref_le_leg.1 hy_pref),
      T.takeUntil_support_avoids_feet hfeet_injective hui hu.2
        (pref.mem_verts_toSubgraph.mp hy_pref),
      (T.leg_toSubgraph_le_carrier i).2 (hpref_le_leg.2 hxy)⟩

theorem Triad.punctured_carrier_connected
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet) :
    ((T.carrier.deleteVerts (Set.range feet)).coe).Connected := by
  classical
  refine SimpleGraph.Subgraph.connected_iff'.mp ?_
  rw [SimpleGraph.Subgraph.connected_iff_forall_exists_walk_subgraph]
  constructor
  · refine ⟨T.apex, ?_⟩
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
    constructor
    · rw [← T.vertexSet_eq_carrier_verts]
      exact T.apex_mem_vertexSet
    · rintro ⟨i, hi⟩
      exact T.apex_not_foot i hi.symm
  · intro u v hu hv
    obtain ⟨p, hp⟩ :=
      T.exists_walk_to_apex_in_punctured_carrier hfeet_injective hu
    obtain ⟨q, hq⟩ :=
      T.exists_walk_to_apex_in_punctured_carrier hfeet_injective hv
    refine ⟨p.append q.reverse, ?_⟩
    rw [SimpleGraph.Walk.toSubgraph_append, SimpleGraph.Walk.toSubgraph_reverse]
    exact sup_le hp hq

theorem Triad.punctured_carrier_ncard_ge_two_of_leg_length_gt_one
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i : Fin 3}
    (hlong : 1 < (T.leg i).length) :
    2 <= (T.carrier.deleteVerts (Set.range feet)).verts.ncard := by
  classical
  let p := T.leg i
  have hp_not_nil : ¬ p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p) (T.apex_not_foot i)
  have hpen_support : p.penultimate ∈ p.support :=
    List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hp_not_nil)
  have hpen_not_feet : p.penultimate ∉ Set.range feet := by
    rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      exact (p.adj_penultimate hp_not_nil).ne hj.symm
    · have hinternal : feet j ∈ Walk.InternalVertices p := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hj]
          exact hpen_support
        · exact (T.apex_not_foot j).symm
        · intro h_eq
          exact hji (hfeet_injective h_eq)
      exact T.internal_vertices_avoid_feet j i hinternal
  have hapex_mem :
      T.apex ∈ (T.carrier.deleteVerts (Set.range feet)).verts := by
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
    constructor
    · rw [← T.vertexSet_eq_carrier_verts]
      exact T.apex_mem_vertexSet
    · rintro ⟨j, hj⟩
      exact T.apex_not_foot j hj.symm
  have hpen_mem :
      p.penultimate ∈ (T.carrier.deleteVerts (Set.range feet)).verts := by
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
    constructor
    · rw [← T.vertexSet_eq_carrier_verts]
      exact ⟨i, hpen_support⟩
    · exact hpen_not_feet
  have hne : T.apex ≠ p.penultimate := by
    exact (Schematic.Math.GraphTheory.Walk.IsPath.penultimate_ne_start_of_length_gt_one
      (G := G) (p := p) (T.leg_isPath i) hlong).symm
  have hpair_subset :
      ({T.apex, p.penultimate} : Set V) ⊆
        (T.carrier.deleteVerts (Set.range feet)).verts := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hapex_mem
    · exact hpen_mem
  have hpair_card : ({T.apex, p.penultimate} : Set V).ncard = 2 :=
    Set.ncard_pair hne
  have hle :=
    Set.ncard_le_ncard hpair_subset
  omega

theorem Triad.punctured_carrier_ncard_ge_two_of_not_all_legs_length_one
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (hnot_short : Not (forall i : Fin 3, (T.leg i).length = 1)) :
    2 <= (T.carrier.deleteVerts (Set.range feet)).verts.ncard := by
  classical
  have hexists :
      Exists fun i : Fin 3 => (T.leg i).length ≠ 1 := by
    by_contra hnone
    apply hnot_short
    intro i
    by_contra hne
    exact hnone ⟨i, hne⟩
  rcases hexists with ⟨i, hi_ne⟩
  have hpos := T.leg_length_pos i
  have hlong : 1 < (T.leg i).length := by omega
  exact T.punctured_carrier_ncard_ge_two_of_leg_length_gt_one
    hfeet_injective hlong

theorem Triad.exists_delete_feet_component_supporting_punctured_carrier
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet) :
    Exists fun C : (G.induce (Set.range feet)ᶜ).ConnectedComponent =>
      (T.carrier.deleteVerts (Set.range feet)).verts ⊆
        induceComponentSupport (G := G) C := by
  classical
  let H : G.Subgraph := T.carrier.deleteVerts (Set.range feet)
  have hH_connected : H.Connected := by
    rw [SimpleGraph.Subgraph.connected_iff']
    simpa [H] using T.punctured_carrier_connected hfeet_injective
  have hH_induce_connected : (G.induce H.verts).Connected :=
    hH_connected.induce_verts
  have hH_subset : H.verts ⊆ (Set.range feet)ᶜ := by
    intro v hv
    change v ∈ (T.carrier.deleteVerts (Set.range feet)).verts at hv
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hv
    exact hv.2
  exact connected_set_subset_induceComponentSupport
    (G := G) hH_induce_connected hH_subset

theorem Triad.exists_large_delete_feet_component_supporting_punctured_carrier_of_not_all_legs_length_one
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (hnot_short : Not (forall i : Fin 3, (T.leg i).length = 1)) :
    Exists fun C : (G.induce (Set.range feet)ᶜ).ConnectedComponent =>
      (T.carrier.deleteVerts (Set.range feet)).verts ⊆
        induceComponentSupport (G := G) C ∧
        2 <= (induceComponentSupport (G := G) C).ncard := by
  classical
  obtain ⟨C, hC_subset⟩ :=
    T.exists_delete_feet_component_supporting_punctured_carrier
      hfeet_injective
  have hcarrier_large :
      2 <= (T.carrier.deleteVerts (Set.range feet)).verts.ncard :=
    T.punctured_carrier_ncard_ge_two_of_not_all_legs_length_one
      hfeet_injective hnot_short
  have hle :
      (T.carrier.deleteVerts (Set.range feet)).verts.ncard <=
        (induceComponentSupport (G := G) C).ncard :=
    Set.ncard_le_ncard hC_subset
  exact ⟨C, hC_subset, by omega⟩

theorem Triad.exists_path_from_component_vertex_to_first_punctured_carrier
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {C : (G.induce (Set.range feet)ᶜ).ConnectedComponent}
    {root : V}
    (hroot_C : root ∈ induceComponentSupport (G := G) C)
    (hT_subset_C :
      (T.carrier.deleteVerts (Set.range feet)).verts ⊆
        induceComponentSupport (G := G) C) :
    Exists fun x : V =>
      x ∈ (T.carrier.deleteVerts (Set.range feet)).verts ∧
        Exists fun p : G.Walk root x =>
          p.IsPath ∧
            (forall z : V, z ∈ p.support -> z ∉ Set.range feet) ∧
              forall z : V, z ∈ p.support -> z ∈ T.vertexSet -> z = x := by
  classical
  let K : Set V := (T.carrier.deleteVerts (Set.range feet)).verts
  have hapex_K : T.apex ∈ K := by
    change T.apex ∈ (T.carrier.deleteVerts (Set.range feet)).verts
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
    constructor
    · rw [← T.vertexSet_eq_carrier_verts]
      exact T.apex_mem_vertexSet
    · rintro ⟨i, hi⟩
      exact T.apex_not_foot i hi.symm
  have hapex_C : T.apex ∈ induceComponentSupport (G := G) C :=
    hT_subset_C hapex_K
  obtain ⟨p, hp_path, hp_support⟩ :=
    connected_induce_exists_path_support_subset
      (G := G) (A := induceComponentSupport (G := G) C)
      (induceComponentSupport_connected (G := G) C)
      hroot_C hapex_C
  obtain ⟨x, hx_support, hxK, hfirst⟩ :=
    Schematic.Math.GraphTheory.Walk.IsPath.exists_takeUntil_first_mem
      (G := G) (p := p) hp_path K hapex_K
  let q : G.Walk root x := p.takeUntil x hx_support
  have hq_path : q.IsPath := hp_path.takeUntil hx_support
  have hq_support_C :
      forall z : V, z ∈ q.support ->
        z ∈ induceComponentSupport (G := G) C := by
    intro z hz
    exact hp_support z
      (SimpleGraph.Walk.support_takeUntil_subset p hx_support hz)
  refine ⟨x, hxK, q, hq_path, ?_, ?_⟩
  · intro z hz
    exact induceComponentSupport_subset (G := G) C (hq_support_C z hz)
  · intro z hz hzT
    have hzK : z ∈ K := by
      change z ∈ (T.carrier.deleteVerts (Set.range feet)).verts
      rw [T.mem_punctured_carrier_verts_iff]
      exact ⟨hzT, by
        exact induceComponentSupport_subset (G := G) C (hq_support_C z hz)⟩
    exact hfirst z hz hzK

theorem Triad.exists_outside_neighbor_of_first_hit_path
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {root x : V}
    (hxT : x ∈ T.vertexSet)
    (hroot_not_T : root ∉ T.vertexSet)
    {p : G.Walk root x}
    (hpath_avoids_feet :
      forall z : V, z ∈ p.support -> z ∉ Set.range feet)
    (hfirst :
      forall z : V, z ∈ p.support -> z ∈ T.vertexSet -> z = x) :
    Exists fun y : V =>
      y ∉ T.vertexSet ∧ y ∉ Set.range feet ∧ G.Adj y x := by
  classical
  have hroot_ne_x : root ≠ x := by
    intro hrootx
    exact hroot_not_T (by simpa [← hrootx] using hxT)
  have hp_not_nil : ¬ p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p) hroot_ne_x
  let y : V := p.penultimate
  have hy_support : y ∈ p.support :=
    List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hp_not_nil)
  have hy_adj : G.Adj y x := by
    simpa [y] using p.adj_penultimate hp_not_nil
  have hy_not_T : y ∉ T.vertexSet := by
    intro hyT
    have hy_eq : y = x := hfirst y hy_support hyT
    exact hy_adj.ne hy_eq
  exact ⟨y, hy_not_T, hpath_avoids_feet y hy_support, hy_adj⟩

theorem Triad.apex_inside_neighbors_at_most_three_of_legs_chordless
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hchordless : forall i : Fin 3, (T.leg i).IsChordless) :
    (G.neighborSet T.apex ∩ T.vertexSet).ncard <= 3 := by
  let A : Fin 3 -> Set V := fun i =>
    G.neighborSet T.apex ∩ {v : V | v ∈ (T.leg i).support}
  have hsubset :
      G.neighborSet T.apex ∩ T.vertexSet ⊆ ⋃ i : Fin 3, A i := by
    rintro v ⟨hv_adj, i, hvi⟩
    exact ⟨A i, ⟨i, rfl⟩, hv_adj, hvi⟩
  have hA : forall i : Fin 3, (A i).ncard <= 1 := by
    intro i
    exact Schematic.Math.GraphTheory.Walk.IsPath.ncard_neighborSet_inter_support_le_one_of_start_isChordless
      (T.leg_isPath i) (hchordless i)
  exact le_trans (Set.ncard_le_ncard hsubset)
    (ncard_iUnion_fin3_le_of_forall_ncard_le_one (V := V) (A := A) hA)

theorem Triad.foot_inside_neighbors_at_most_three_of_leg_chordless
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3)
    (hchordless : (T.leg i).IsChordless)
    (hneighbors_subset :
      G.neighborSet (feet i) ∩ T.vertexSet ⊆
        (G.neighborSet (feet i) ∩
          {v : V | v ∈ (T.leg i).support}) ∪
            (Set.range feet \ {feet i})) :
    (G.neighborSet (feet i) ∩ T.vertexSet).ncard <= 3 := by
  have hown :
      (G.neighborSet (feet i) ∩
        {v : V | v ∈ (T.leg i).support}).ncard <= 1 :=
    Schematic.Math.GraphTheory.Walk.IsPath.ncard_neighborSet_inter_support_le_one_of_end_isChordless
      (T.leg_isPath i) hchordless
  have hfeet :
      (Set.range feet \ {feet i}).ncard <= 2 :=
    ncard_range_fin3_diff_singleton_le_two hfeet_injective i
  calc
    (G.neighborSet (feet i) ∩ T.vertexSet).ncard <=
        ((G.neighborSet (feet i) ∩
          {v : V | v ∈ (T.leg i).support}) ∪
            (Set.range feet \ {feet i})).ncard :=
      Set.ncard_le_ncard hneighbors_subset
    _ <=
        (G.neighborSet (feet i) ∩
          {v : V | v ∈ (T.leg i).support}).ncard +
            (Set.range feet \ {feet i}).ncard :=
      Set.ncard_union_le
        (G.neighborSet (feet i) ∩
          {v : V | v ∈ (T.leg i).support})
        (Set.range feet \ {feet i})
    _ <= 3 := by omega

theorem Triad.internal_inside_neighbors_at_most_three_of_leg_chordless
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {i : Fin 3}
    {v : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hchordless : (T.leg i).IsChordless)
    {X : Set V}
    (hX_card : X.ncard <= 1)
    (hneighbors_subset :
      G.neighborSet v ∩ T.vertexSet ⊆
        (G.neighborSet v ∩ {u : V | u ∈ (T.leg i).support}) ∪ X) :
    (G.neighborSet v ∩ T.vertexSet).ncard <= 3 := by
  have hown :
      (G.neighborSet v ∩ {u : V | u ∈ (T.leg i).support}).ncard <= 2 :=
    Schematic.Math.GraphTheory.Walk.IsPath.ncard_neighborSet_inter_support_le_two_of_isChordless
      (T.leg_isPath i) hchordless hv.1
  calc
    (G.neighborSet v ∩ T.vertexSet).ncard <=
        ((G.neighborSet v ∩ {u : V | u ∈ (T.leg i).support}) ∪ X).ncard :=
      Set.ncard_le_ncard hneighbors_subset
    _ <= (G.neighborSet v ∩ {u : V | u ∈ (T.leg i).support}).ncard + X.ncard :=
      Set.ncard_union_le
        (G.neighborSet v ∩ {u : V | u ∈ (T.leg i).support}) X
    _ <= 3 := by omega

theorem Triad.inside_neighbors_at_most_three_of_legs_chordless_and_internal_cross
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hchordless : forall i : Fin 3, (T.leg i).IsChordless)
    (hinternal_cross :
      forall {i : Fin 3} {v : V},
        v ∈ Walk.InternalVertices (T.leg i) ->
          Exists fun X : Set V =>
            X.ncard <= 1 ∧
              G.neighborSet v ∩ T.vertexSet ⊆
                (G.neighborSet v ∩ {u : V | u ∈ (T.leg i).support}) ∪ X) :
    forall v : V,
      v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ T.vertexSet).ncard <= 3 := by
  intro v hv
  rcases T.eq_apex_or_exists_internal_of_mem_punctured_carrier hv with rfl | ⟨i, hvi⟩
  · exact T.apex_inside_neighbors_at_most_three_of_legs_chordless hchordless
  · obtain ⟨X, hX_card, hsubset⟩ := hinternal_cross hvi
    exact T.internal_inside_neighbors_at_most_three_of_leg_chordless
      hvi (hchordless i) hX_card hsubset

theorem Triad.apex_inside_neighbors_at_most_three_of_lean
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet) :
    (G.neighborSet T.apex ∩ T.vertexSet).ncard <= 3 :=
  T.apex_inside_neighbors_at_most_three_of_legs_chordless
    (fun i => T.lean_leg_isChordless hlean hfeet_injective i)

theorem Triad.inside_neighbors_at_most_three_of_lean_and_internal_cross
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    (hinternal_cross :
      forall {i : Fin 3} {v : V},
        v ∈ Walk.InternalVertices (T.leg i) ->
          Exists fun X : Set V =>
            X.ncard <= 1 ∧
              G.neighborSet v ∩ T.vertexSet ⊆
                (G.neighborSet v ∩ {u : V | u ∈ (T.leg i).support}) ∪ X) :
    forall v : V,
      v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ T.vertexSet).ncard <= 3 :=
  T.inside_neighbors_at_most_three_of_legs_chordless_and_internal_cross
    (fun i => T.lean_leg_isChordless hlean hfeet_injective i)
    hinternal_cross

theorem Triad.inside_neighbors_at_most_three_of_lean
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet) :
    forall v : V,
      v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ T.vertexSet).ncard <= 3 :=
  T.inside_neighbors_at_most_three_of_lean_and_internal_cross hlean hfeet_injective
    (fun {i} {v} hv =>
      T.internal_cross_neighbors_subset_singleton_of_lean hlean hfeet_injective
        (i := i) (v := v) hv)

theorem Triad.foot_inside_neighbors_at_most_three_of_lean_and_foot_cross
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3)
    (hfoot_cross :
      G.neighborSet (feet i) ∩ T.vertexSet ⊆
        (G.neighborSet (feet i) ∩
          {v : V | v ∈ (T.leg i).support}) ∪
            (Set.range feet \ {feet i})) :
    (G.neighborSet (feet i) ∩ T.vertexSet).ncard <= 3 :=
  T.foot_inside_neighbors_at_most_three_of_leg_chordless
    hfeet_injective i (T.lean_leg_isChordless hlean hfeet_injective i)
    hfoot_cross

theorem Triad.foot_inside_neighbors_at_most_three_of_lean_long_legs
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3) :
    1 < (T.leg i).length ->
    (G.neighborSet (feet i) ∩ T.vertexSet).ncard <= 3 :=
  fun hlong_i =>
  T.foot_inside_neighbors_at_most_three_of_lean_and_foot_cross
    hlean hfeet_injective i
    (T.foot_cross_neighbors_subset_of_lean_long_legs
      hlean hfeet_injective i hlong_i)

theorem Triad.foot_inside_neighbors_at_most_three_of_lean_all_long_legs
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    (hlong : forall i : Fin 3, 1 < (T.leg i).length)
    (i : Fin 3) :
    (G.neighborSet (feet i) ∩ T.vertexSet).ncard <= 3 :=
  T.foot_inside_neighbors_at_most_three_of_lean_long_legs
    hlean hfeet_injective i (hlong i)

theorem Triad.vertexSet_subset_insert_apex_range_of_legs_length_eq_one
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hshort : forall i : Fin 3, (T.leg i).length = 1) :
    T.vertexSet ⊆ insert T.apex (Set.range feet) := by
  intro v hv
  rcases hv with ⟨i, hvi⟩
  by_cases hv_apex : v = T.apex
  · simp [hv_apex]
  by_cases hv_foot : v = feet i
  · exact Set.mem_insert_of_mem T.apex ⟨i, hv_foot.symm⟩
  exfalso
  exact
    (Walk.not_mem_internalVertices_of_length_eq_one
      (G := G) (p := T.leg i) (z := v) (hshort i))
      ⟨hvi, hv_apex, hv_foot⟩

theorem Triad.foot_inside_neighbors_at_most_three_of_legs_length_eq_one
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (hshort : forall i : Fin 3, (T.leg i).length = 1)
    (i : Fin 3) :
    (G.neighborSet (feet i) ∩ T.vertexSet).ncard <= 3 := by
  classical
  have hsubset :
      G.neighborSet (feet i) ∩ T.vertexSet ⊆
        insert T.apex (Set.range feet \ {feet i}) := by
    intro x hx
    have hx_cases :
        x = T.apex ∨ x ∈ Set.range feet := by
      simpa [Set.mem_insert_iff] using
        T.vertexSet_subset_insert_apex_range_of_legs_length_eq_one hshort hx.2
    rcases hx_cases with hx_apex | hx_feet
    · simp [hx_apex]
    · refine Set.mem_insert_of_mem T.apex ?_
      refine ⟨hx_feet, ?_⟩
      intro hx_eq
      have h_adj : G.Adj (feet i) x :=
        (SimpleGraph.mem_neighborSet (G := G) (feet i) x).mp hx.1
      exact h_adj.ne hx_eq.symm
  have hcard_le :
      (G.neighborSet (feet i) ∩ T.vertexSet).ncard <=
        (insert T.apex (Set.range feet \ {feet i})).ncard :=
    Set.ncard_le_ncard hsubset
  have hdiff_le : (Set.range feet \ {feet i}).ncard <= 2 :=
    ncard_range_fin3_diff_singleton_le_two hfeet_injective i
  have hinsert_le :
      (insert T.apex (Set.range feet \ {feet i})).ncard <= 3 := by
    exact ncard_insert_range_fin3_diff_singleton_le_three
      hfeet_injective i T.apex
  exact le_trans hcard_le hinsert_le

def Triad.ShortFootHasNoCrossNeighbor
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (i : Fin 3) : Prop :=
  forall {j : Fin 3} {y : V},
    i ≠ j ->
      y ∈ Walk.InternalVertices (T.leg j) ->
        Not (G.Adj (feet i) y)

theorem Triad.exists_short_foot_cross_of_not_no_short_cross
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hnot :
      Not (forall i : Fin 3,
        (T.leg i).length = 1 -> T.ShortFootHasNoCrossNeighbor i)) :
    Exists fun i : Fin 3 =>
      (T.leg i).length = 1 ∧
        Exists fun j : Fin 3 =>
          Exists fun y : V =>
            i ≠ j ∧ y ∈ Walk.InternalVertices (T.leg j) ∧
              G.Adj (feet i) y := by
  classical
  by_contra hnone
  apply hnot
  intro i hshort j y hij hyint hadj
  exact hnone ⟨i, hshort, j, y, hij, hyint, hadj⟩

theorem Triad.foot_cross_neighbors_subset_of_short_leg_no_cross
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i : Fin 3}
    (hno_cross : T.ShortFootHasNoCrossNeighbor i) :
    G.neighborSet (feet i) ∩ T.vertexSet ⊆
      (G.neighborSet (feet i) ∩
        {v : V | v ∈ (T.leg i).support}) ∪
          (Set.range feet \ {feet i}) := by
  apply T.foot_cross_neighbors_subset_of_no_internal_cross hfeet_injective i
  intro j y hij hy_internal hadj
  exact hno_cross hij hy_internal hadj

theorem Triad.foot_inside_neighbors_at_most_three_of_short_leg_no_cross
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    {i : Fin 3}
    (hno_cross : T.ShortFootHasNoCrossNeighbor i) :
    (G.neighborSet (feet i) ∩ T.vertexSet).ncard <= 3 :=
  T.foot_inside_neighbors_at_most_three_of_lean_and_foot_cross
    hlean hfeet_injective i
    (T.foot_cross_neighbors_subset_of_short_leg_no_cross
      hfeet_injective hno_cross)

theorem Triad.inside_neighbors_at_most_three_of_vertexSet_subset
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    (hsubset : T'.vertexSet ⊆ T.vertexSet)
    (hinside :
      forall v : V,
        v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
          (G.neighborSet v ∩ T.vertexSet).ncard <= 3) :
    forall v : V,
      v ∈ (T'.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ T'.vertexSet).ncard <= 3 := by
  intro v hv
  have hv' := (T'.mem_punctured_carrier_verts_iff).mp hv
  have hvT : v ∈ (T.carrier.deleteVerts (Set.range feet)).verts := by
    rw [T.mem_punctured_carrier_verts_iff]
    exact ⟨hsubset hv'.1, hv'.2⟩
  have hcard_le :
      (G.neighborSet v ∩ T'.vertexSet).ncard <=
        (G.neighborSet v ∩ T.vertexSet).ncard := by
    exact Set.ncard_le_ncard (by
      intro x hx
      exact ⟨hx.1, hsubset hx.2⟩)
  exact le_trans hcard_le (hinside v hvT)

theorem Triad.foot_has_neighbor_outside_of_vertexSet_subset
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    (hsubset : T'.vertexSet ⊆ T.vertexSet)
    (houtside :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧
            G.Adj u (feet i)) :
    forall i : Fin 3,
      Exists fun u : V =>
        u ∈ ((⊤ : G.Subgraph).deleteVerts T'.vertexSet).verts ∧
          G.Adj u (feet i) := by
  intro i
  obtain ⟨u, hu, hui⟩ := houtside i
  refine ⟨u, ?_, hui⟩
  rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hu ⊢
  exact ⟨by simp, fun huT' => hu.2 (hsubset huT')⟩

def RSTLeanTriadData.of_lean_subtriad
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    {T T' : Triad G feet}
    (hlean : T'.Lean)
    (hsubset : T'.vertexSet ⊆ T.vertexSet)
    (hcomplement_connected : (G.induce T'.vertexSetᶜ).Connected)
    (hroot_outside : root ∉ T.vertexSet)
    (hinside :
      forall v : V,
        v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ->
          (G.neighborSet v ∩ T.vertexSet).ncard <= 3)
    (hfoot_outside :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧
            G.Adj u (feet i)) :
    RSTLeanTriadData G feet root where
  triad := T'
  lean := hlean
  complement_connected := hcomplement_connected
  root_outside := by
    intro hroot
    exact hroot_outside (hsubset hroot)
  inside_neighbors_at_most_three :=
    Triad.inside_neighbors_at_most_three_of_vertexSet_subset
      (G := G) hsubset hinside
  foot_has_neighbor_outside :=
    Triad.foot_has_neighbor_outside_of_vertexSet_subset
      (G := G) hsubset hfoot_outside

end Schematic.Math.GraphTheory
