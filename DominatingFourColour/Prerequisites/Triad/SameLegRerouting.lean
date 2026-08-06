import DominatingFourColour.Prerequisites.Triad.CrossLegRerouting

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

theorem Triad.internal_takeUntil_reverse_append_leg_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i k : Fin 3}
    (hik : i ≠ k)
    {v : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i)) :
    (((T.leg i).takeUntil v hv.1).reverse.append (T.leg k)).IsPath := by
  have hpref : ((T.leg i).takeUntil v hv.1).reverse.IsPath := by
    have h := SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil (T.leg i) hv.1) (T.leg_isPath i)
    exact h.reverse
  refine Walk.IsPath.append_of_support_inter_eq_endpoint hpref (T.leg_isPath k) ?_
  intro z hzpref_rev hzk
  rw [SimpleGraph.Walk.support_reverse] at hzpref_rev
  have hzpref : z ∈ ((T.leg i).takeUntil v hv.1).support := List.mem_reverse.mp hzpref_rev
  have hzi : z ∈ (T.leg i).support :=
    SimpleGraph.Walk.support_takeUntil_subset (T.leg i) hv.1 hzpref
  exact T.diff_leg_support_inter_eq_apex hfeet_injective hik hzi hzk

theorem Triad.internal_takeUntil_reverse_append_leg_support_cases
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {i k : Fin 3}
    {v z : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hz : z ∈ (((T.leg i).takeUntil v hv.1).reverse.append (T.leg k)).support) :
    z ∈ ((T.leg i).takeUntil v hv.1).support ∨ z ∈ (T.leg k).support := by
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzpref_rev | hzk
  · left
    rw [SimpleGraph.Walk.support_reverse] at hzpref_rev
    exact List.mem_reverse.mp hzpref_rev
  · exact Or.inr hzk

def Triad.ownPrefixReroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    {v y : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hy : y ∈ (T.leg j).support)
    (hy_ne_apex : y ≠ T.apex)
    (hvy : G.Adj v y) :
    Triad G feet := by
  let p_i : G.Walk v (feet i) := (T.leg i).dropUntil v hv.1
  let p_j : G.Walk v (feet j) := hvy.toWalk.append ((T.leg j).dropUntil y hy)
  let p_k : G.Walk v (feet k) := ((T.leg i).takeUntil v hv.1).reverse.append (T.leg k)
  have hpath_i : p_i.IsPath := by
    simpa [p_i] using T.internal_dropUntil_isPath hv
  have hpath_j : p_j.IsPath := by
    simpa [p_j] using
      T.internal_cross_edge_dropUntil_isPath hfeet_injective hij hv hy hvy
  have hpath_k : p_k.IsPath := by
    simpa [p_k] using
      T.internal_takeUntil_reverse_append_leg_isPath hfeet_injective hik hv
  have hdis_i_j : Disjoint (Walk.InternalVertices p_i) (Walk.InternalVertices p_j) := by
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzi_old : z ∈ Walk.InternalVertices (T.leg i) := by
      simpa [p_i] using T.internal_dropUntil_internalVertices_subset hv hzi
    have hzj_old : z ∈ Walk.InternalVertices (T.leg j) := by
      simpa [p_j] using
        T.internal_cross_edge_dropUntil_internalVertices_subset hy hy_ne_apex hvy hzj
    exact Set.disjoint_left.mp (T.apex_only_common_vertex i j hij) hzi_old hzj_old
  have hdis_i_k : Disjoint (Walk.InternalVertices p_i) (Walk.InternalVertices p_k) := by
    rw [Set.disjoint_left]
    intro z hzi hzk
    have hcases := T.internal_takeUntil_reverse_append_leg_support_cases hv hzk.1
    rcases hcases with hzpref | hzlegk
    · exact Set.disjoint_left.mp
        (Walk.IsPath.takeUntil_support_disjoint_punctured_dropUntil_support
          (T.leg_isPath i) hv.1) hzpref ⟨hzi.1, hzi.2.1⟩
    · have hzi_old : z ∈ Walk.InternalVertices (T.leg i) := by
        simpa [p_i] using T.internal_dropUntil_internalVertices_subset hv hzi
      exact hzi_old.2.1
        (T.diff_leg_support_inter_eq_apex hfeet_injective hik hzi_old.1 hzlegk)
  have hdis_j_k : Disjoint (Walk.InternalVertices p_j) (Walk.InternalVertices p_k) := by
    rw [Set.disjoint_left]
    intro z hzj hzk
    have hzj_old : z ∈ Walk.InternalVertices (T.leg j) := by
      simpa [p_j] using
        T.internal_cross_edge_dropUntil_internalVertices_subset hy hy_ne_apex hvy hzj
    have hcases := T.internal_takeUntil_reverse_append_leg_support_cases hv hzk.1
    rcases hcases with hzpref | hzlegk
    · have hzi : z ∈ (T.leg i).support :=
        SimpleGraph.Walk.support_takeUntil_subset (T.leg i) hv.1 hzpref
      exact hzj_old.2.1
        (T.diff_leg_support_inter_eq_apex hfeet_injective (fun h => hij h.symm)
          hzj_old.1 hzi)
    · exact hzj_old.2.1
        (T.diff_leg_support_inter_eq_apex hfeet_injective hjk hzj_old.1 hzlegk)
  have havoid_i : forall l : Fin 3, feet l ∉ Walk.InternalVertices p_i := by
    intro l hfoot
    exact T.internal_vertices_avoid_feet l i
      (T.internal_dropUntil_internalVertices_subset hv (by simpa [p_i] using hfoot))
  have havoid_j : forall l : Fin 3, feet l ∉ Walk.InternalVertices p_j := by
    intro l hfoot
    exact T.internal_vertices_avoid_feet l j
      (T.internal_cross_edge_dropUntil_internalVertices_subset hy hy_ne_apex hvy
        (by simpa [p_j] using hfoot))
  have havoid_k : forall l : Fin 3, feet l ∉ Walk.InternalVertices p_k := by
    intro l hfoot
    have hcases := T.internal_takeUntil_reverse_append_leg_support_cases hv hfoot.1
    rcases hcases with hzpref | hzlegk
    · by_cases hli : l = i
      · subst l
        exact (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.leg_isPath i) hv.1 hv.2.2.symm) hzpref
      · have hfoot_i_internal : feet l ∈ Walk.InternalVertices (T.leg i) := by
          refine ⟨SimpleGraph.Walk.support_takeUntil_subset (T.leg i) hv.1 hzpref, ?_, ?_⟩
          · exact (T.apex_not_foot l).symm
          · intro h_eq
            exact hli (hfeet_injective h_eq)
        exact T.internal_vertices_avoid_feet l i hfoot_i_internal
    · by_cases hlk : l = k
      · subst l
        exact hfoot.2.2 rfl
      · have hfoot_k_internal : feet l ∈ Walk.InternalVertices (T.leg k) := by
          refine ⟨hzlegk, ?_, ?_⟩
          · exact (T.apex_not_foot l).symm
          · intro h_eq
            exact hlk (hfeet_injective h_eq)
        exact T.internal_vertices_avoid_feet l k hfoot_k_internal
  exact Triad.ofThreeLegs hij hik hjk p_i p_j p_k
    hpath_i hpath_j hpath_k (fun l => T.internal_ne_foot hv l)
    hdis_i_j hdis_i_k hdis_j_k havoid_i havoid_j havoid_k

theorem Triad.ownPrefixReroute_vertexSet_subset
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    {v y : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hy : y ∈ (T.leg j).support)
    (hy_ne_apex : y ≠ T.apex)
    (hvy : G.Adj v y) :
    (T.ownPrefixReroute hfeet_injective hij hik hjk hv hy hy_ne_apex hvy).vertexSet ⊆
      T.vertexSet := by
  intro z hz
  rcases hz with ⟨l, hzl⟩
  dsimp [Triad.ownPrefixReroute, Triad.ofThreeLegs] at hzl
  by_cases hli : l = i
  · subst l
    simp at hzl
    exact ⟨i, SimpleGraph.Walk.support_dropUntil_subset (T.leg i) hv.1 hzl⟩
  · by_cases hlj : l = j
    · subst l
      simp [hij.symm] at hzl
      rcases hzl with rfl | hzdrop
      · exact ⟨i, hv.1⟩
      · exact ⟨j, SimpleGraph.Walk.support_dropUntil_subset (T.leg j) hy hzdrop⟩
    · have hlk : l = k := fin3_eq_of_ne_ne hij hik hjk hli hlj
      subst l
      have hki : k ≠ i := fun h => hik h.symm
      have hkj : k ≠ j := fun h => hjk h.symm
      simp [hki, hkj] at hzl
      rcases hzl with hzprefix | hzlegk
      · exact ⟨i, SimpleGraph.Walk.support_takeUntil_subset (T.leg i) hv.1 hzprefix⟩
      · exact ⟨k, hzlegk⟩

theorem Triad.ownPrefixReroute_omits_earlier_cross_vertex
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    {v x y : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hx : x ∈ (T.leg j).support)
    (hy : y ∈ (T.leg j).support)
    (hx_ne_apex : x ≠ T.apex)
    (hy_ne_apex : y ≠ T.apex)
    (hidx : (T.leg j).support.idxOf x < (T.leg j).support.idxOf y)
    (hvy : G.Adj v y) :
    x ∉ (T.ownPrefixReroute hfeet_injective hij hik hjk hv hy hy_ne_apex hvy).vertexSet := by
  intro hx_new
  rcases hx_new with ⟨l, hxl⟩
  dsimp [Triad.ownPrefixReroute, Triad.ofThreeLegs] at hxl
  by_cases hli : l = i
  · subst l
    simp at hxl
    have hxi : x ∈ (T.leg i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (T.leg i) hv.1 hxl
    exact hx_ne_apex (T.diff_leg_support_inter_eq_apex hfeet_injective hij.symm hx hxi)
  · by_cases hlj : l = j
    · subst l
      simp [hij.symm] at hxl
      rcases hxl with h_eq_v | hxdrop
      · exact T.internal_not_mem_other_leg_support hfeet_injective hij hv (h_eq_v ▸ hx)
      · have hy_le_x := Walk.idxOf_le_of_mem_dropUntil (T.leg_isPath j) hy hxdrop
        omega
    · have hlk : l = k := fin3_eq_of_ne_ne hij hik hjk hli hlj
      subst l
      have hki : k ≠ i := fun h => hik h.symm
      have hkj : k ≠ j := fun h => hjk h.symm
      simp [hki, hkj] at hxl
      rcases hxl with hxprefix | hxk
      · have hxi : x ∈ (T.leg i).support :=
          SimpleGraph.Walk.support_takeUntil_subset (T.leg i) hv.1 hxprefix
        exact hx_ne_apex (T.diff_leg_support_inter_eq_apex hfeet_injective hij.symm hx hxi)
      · exact hx_ne_apex (T.diff_leg_support_inter_eq_apex hfeet_injective hjk hx hxk)

theorem Triad.not_lean_of_internal_adj_same_leg_ordered
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    {v x y : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hx : x ∈ (T.leg j).support)
    (hy : y ∈ (T.leg j).support)
    (hx_ne_apex : x ≠ T.apex)
    (hy_ne_apex : y ≠ T.apex)
    (hidx : (T.leg j).support.idxOf x < (T.leg j).support.idxOf y)
    (hvy : G.Adj v y) :
    ¬ T.Lean := by
  let T' : Triad G feet :=
    T.ownPrefixReroute hfeet_injective hij hik hjk hv hy hy_ne_apex hvy
  exact T.not_lean_of_contained_triad_omits_vertex T'
    (T.ownPrefixReroute_vertexSet_subset hfeet_injective hij hik hjk hv hy hy_ne_apex hvy)
    ⟨j, hx⟩
    (T.ownPrefixReroute_omits_earlier_cross_vertex hfeet_injective hij hik hjk hv hx hy
      hx_ne_apex hy_ne_apex hidx hvy)

theorem Triad.not_internal_adj_two_same_other_leg_of_lean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    {v x y : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hx : x ∈ (T.leg j).support)
    (hy : y ∈ (T.leg j).support)
    (hx_not_own : x ∉ (T.leg i).support)
    (hy_not_own : y ∉ (T.leg i).support)
    (hxy : x ≠ y)
    (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    False := by
  have hx_ne_apex : x ≠ T.apex := by
    intro hx_apex
    exact hx_not_own (by simp [hx_apex])
  have hy_ne_apex : y ≠ T.apex := by
    intro hy_apex
    exact hy_not_own (by simp [hy_apex])
  rcases lt_trichotomy
      ((T.leg j).support.idxOf x) ((T.leg j).support.idxOf y) with
    hlt | heq | hgt
  · exact (T.not_lean_of_internal_adj_same_leg_ordered hfeet_injective hij hik hjk hv
      hx hy hx_ne_apex hy_ne_apex hlt hvy) hlean
  · have hxy_eq : x = y := (List.idxOf_inj hx).mp heq
    exact hxy hxy_eq
  · exact (T.not_lean_of_internal_adj_same_leg_ordered hfeet_injective hij hik hjk hv
      hy hx hy_ne_apex hx_ne_apex hgt hvx) hlean

theorem Triad.internal_cross_neighbor_eq_of_lean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    {i j : Fin 3}
    (hij : i ≠ j)
    {v x y : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hx : x ∈ (T.leg j).support)
    (hx_not_own : x ∉ (T.leg i).support)
    (hvx : G.Adj v x)
    (hy_vertex : y ∈ T.vertexSet)
    (hy_not_own : y ∉ (T.leg i).support)
    (hvy : G.Adj v y) :
    y = x := by
  have hyj :
      y ∈ (T.leg j).support :=
    T.internal_cross_neighbor_same_leg_of_lean hlean hfeet_injective hij hv
      hx hx_not_own hvx hy_vertex hy_not_own hvy
  by_cases hyx : y = x
  · exact hyx
  · exfalso
    obtain ⟨k, hik, hjk⟩ := fin3_exists_ne_ne hij
    exact T.not_internal_adj_two_same_other_leg_of_lean
      hlean hfeet_injective hij hik hjk hv hx hyj hx_not_own hy_not_own
      (fun hxy => hyx hxy.symm) hvx hvy

theorem Triad.internal_cross_neighbors_subset_singleton_of_lean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    {i : Fin 3}
    {v : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i)) :
    Exists fun X : Set V =>
      X.ncard <= 1 ∧
        G.neighborSet v ∩ T.vertexSet ⊆
          (G.neighborSet v ∩ {u : V | u ∈ (T.leg i).support}) ∪ X := by
  classical
  by_cases hex :
      Exists fun x : V =>
        x ∈ G.neighborSet v ∧ x ∈ T.vertexSet ∧ x ∉ (T.leg i).support
  · rcases hex with ⟨x, hx_adj, hx_vertex, hx_not_own⟩
    rcases hx_vertex with ⟨j, hxj⟩
    have hij : i ≠ j := by
      intro h
      subst j
      exact hx_not_own hxj
    refine ⟨({x} : Set V), ?_, ?_⟩
    · simp
    · intro y hy
      by_cases hy_own : y ∈ (T.leg i).support
      · exact Or.inl ⟨hy.1, hy_own⟩
      · have hy_eq : y = x :=
          T.internal_cross_neighbor_eq_of_lean hlean hfeet_injective hij hv
            hxj hx_not_own hx_adj hy.2 hy_own hy.1
        exact Or.inr (by simp [hy_eq])
  · refine ⟨(∅ : Set V), ?_, ?_⟩
    · simp
    · intro y hy
      by_cases hy_own : y ∈ (T.leg i).support
      · exact Or.inl ⟨hy.1, hy_own⟩
      · exfalso
        exact hex ⟨y, hy.1, hy.2, hy_own⟩

end Schematic.Math.GraphTheory
