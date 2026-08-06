import DominatingFourColour.Prerequisites.Triad.LegReplacement

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

def Triad.twoCrossReroute
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
    (hy : y ∈ (T.leg k).support)
    (hx_ne_apex : x ≠ T.apex)
    (hy_ne_apex : y ≠ T.apex)
    (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    Triad G feet := by
  let p_i : G.Walk v (feet i) := (T.leg i).dropUntil v hv.1
  let p_j : G.Walk v (feet j) := hvx.toWalk.append ((T.leg j).dropUntil x hx)
  let p_k : G.Walk v (feet k) := hvy.toWalk.append ((T.leg k).dropUntil y hy)
  have hpath_i : p_i.IsPath := by
    simpa [p_i] using T.internal_dropUntil_isPath hv
  have hpath_j : p_j.IsPath := by
    simpa [p_j] using
      T.internal_cross_edge_dropUntil_isPath hfeet_injective hij hv hx hvx
  have hpath_k : p_k.IsPath := by
    simpa [p_k] using
      T.internal_cross_edge_dropUntil_isPath hfeet_injective hik hv hy hvy
  have hsubset_i :
      Walk.InternalVertices p_i ⊆ Walk.InternalVertices (T.leg i) := by
    intro z hz
    exact T.internal_dropUntil_internalVertices_subset hv (by simpa [p_i] using hz)
  have hsubset_j :
      Walk.InternalVertices p_j ⊆ Walk.InternalVertices (T.leg j) := by
    intro z hz
    exact T.internal_cross_edge_dropUntil_internalVertices_subset
      hx hx_ne_apex hvx (by simpa [p_j] using hz)
  have hsubset_k :
      Walk.InternalVertices p_k ⊆ Walk.InternalVertices (T.leg k) := by
    intro z hz
    exact T.internal_cross_edge_dropUntil_internalVertices_subset
      hy hy_ne_apex hvy (by simpa [p_k] using hz)
  exact Triad.ofThreeLegs hij hik hjk p_i p_j p_k
    hpath_i hpath_j hpath_k (fun l => T.internal_ne_foot hv l)
    (Disjoint.mono hsubset_i hsubset_j (T.apex_only_common_vertex i j hij))
    (Disjoint.mono hsubset_i hsubset_k (T.apex_only_common_vertex i k hik))
    (Disjoint.mono hsubset_j hsubset_k (T.apex_only_common_vertex j k hjk))
    (fun l hz => T.internal_vertices_avoid_feet l i (hsubset_i hz))
    (fun l hz => T.internal_vertices_avoid_feet l j (hsubset_j hz))
    (fun l hz => T.internal_vertices_avoid_feet l k (hsubset_k hz))

theorem Triad.twoCrossReroute_vertexSet_subset
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
    (hy : y ∈ (T.leg k).support)
    (hx_ne_apex : x ≠ T.apex)
    (hy_ne_apex : y ≠ T.apex)
    (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    (T.twoCrossReroute hfeet_injective hij hik hjk hv hx hy
      hx_ne_apex hy_ne_apex hvx hvy).vertexSet ⊆ T.vertexSet := by
  intro z hz
  rcases hz with ⟨l, hzl⟩
  dsimp [Triad.twoCrossReroute, Triad.ofThreeLegs] at hzl
  by_cases hli : l = i
  · subst l
    simp at hzl
    exact ⟨i, SimpleGraph.Walk.support_dropUntil_subset (T.leg i) hv.1 hzl⟩
  · by_cases hlj : l = j
    · subst l
      simp [hij.symm] at hzl
      rcases hzl with rfl | hzdrop
      · exact ⟨i, hv.1⟩
      · exact ⟨j, SimpleGraph.Walk.support_dropUntil_subset (T.leg j) hx hzdrop⟩
    · have hlk : l = k := fin3_eq_of_ne_ne hij hik hjk hli hlj
      subst l
      have hki : k ≠ i := fun h => hik h.symm
      have hkj : k ≠ j := fun h => hjk h.symm
      simp [hki, hkj] at hzl
      rcases hzl with rfl | hzdrop
      · exact ⟨i, hv.1⟩
      · exact ⟨k, SimpleGraph.Walk.support_dropUntil_subset (T.leg k) hy hzdrop⟩

theorem Triad.twoCrossReroute_omits_old_apex
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
    (hy : y ∈ (T.leg k).support)
    (hx_ne_apex : x ≠ T.apex)
    (hy_ne_apex : y ≠ T.apex)
    (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    T.apex ∉ (T.twoCrossReroute hfeet_injective hij hik hjk hv hx hy
      hx_ne_apex hy_ne_apex hvx hvy).vertexSet := by
  intro hap
  rcases hap with ⟨l, hl⟩
  dsimp [Triad.twoCrossReroute, Triad.ofThreeLegs] at hl
  by_cases hli : l = i
  · subst l
    simp at hl
    exact (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      (T.leg_isPath i) hv.1 hv.2.1) hl
  · by_cases hlj : l = j
    · subst l
      simp [hij.symm] at hl
      rcases hl with hap_v | hap_drop
      · exact hv.2.1 hap_v.symm
      · exact (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          (T.leg_isPath j) hx hx_ne_apex) hap_drop
    · have hlk : l = k := fin3_eq_of_ne_ne hij hik hjk hli hlj
      subst l
      have hki : k ≠ i := fun h => hik h.symm
      have hkj : k ≠ j := fun h => hjk h.symm
      simp [hki, hkj] at hl
      rcases hl with hap_v | hap_drop
      · exact hv.2.1 hap_v.symm
      · exact (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          (T.leg_isPath k) hy hy_ne_apex) hap_drop

theorem Triad.not_lean_of_internal_adj_two_cross_legs
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
    (hy : y ∈ (T.leg k).support)
    (hx_ne_apex : x ≠ T.apex)
    (hy_ne_apex : y ≠ T.apex)
    (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    ¬ T.Lean := by
  let T' : Triad G feet :=
    T.twoCrossReroute hfeet_injective hij hik hjk hv hx hy
      hx_ne_apex hy_ne_apex hvx hvy
  exact T.not_lean_of_contained_triad_omits_apex T'
    (T.twoCrossReroute_vertexSet_subset
      hfeet_injective hij hik hjk hv hx hy hx_ne_apex hy_ne_apex hvx hvy)
    (T.twoCrossReroute_omits_old_apex
      hfeet_injective hij hik hjk hv hx hy hx_ne_apex hy_ne_apex hvx hvy)

theorem Triad.not_internal_adj_two_distinct_other_legs_of_lean
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
    (hy : y ∈ (T.leg k).support)
    (hx_not_own : x ∉ (T.leg i).support)
    (hy_not_own : y ∉ (T.leg i).support)
    (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    False := by
  have hx_ne_apex : x ≠ T.apex := by
    intro hx_apex
    exact hx_not_own (by simp [hx_apex])
  have hy_ne_apex : y ≠ T.apex := by
    intro hy_apex
    exact hy_not_own (by simp [hy_apex])
  exact (T.not_lean_of_internal_adj_two_cross_legs
    hfeet_injective hij hik hjk hv hx hy hx_ne_apex hy_ne_apex hvx hvy) hlean

theorem Triad.internal_cross_neighbor_same_leg_of_lean
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
    y ∈ (T.leg j).support := by
  rcases hy_vertex with ⟨k, hyk⟩
  by_cases hki : k = i
  · subst k
    exact False.elim (hy_not_own hyk)
  · by_cases hkj : k = j
    · subst k
      exact hyk
    · exfalso
      have hik : i ≠ k := fun h => hki h.symm
      have hjk : j ≠ k := fun h => hkj h.symm
      exact T.not_internal_adj_two_distinct_other_legs_of_lean
        hlean hfeet_injective hij hik hjk hv hx hyk hx_not_own hy_not_own hvx hvy

theorem Triad.internal_cross_edge_takeUntil_reverse_append_leg_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    {v x : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hx : x ∈ (T.leg j).support)
    (hvx : G.Adj v x) :
    ((hvx.toWalk.append ((T.leg j).takeUntil x hx).reverse).append
      (T.leg k)).IsPath := by
  let q : G.Walk T.apex x := (T.leg j).takeUntil x hx
  have hq_path : q.reverse.IsPath := by
    have hq : q.IsPath := by
      exact SimpleGraph.Walk.isPath_of_isSubwalk
        (SimpleGraph.Walk.isSubwalk_takeUntil (T.leg j) hx)
        (T.leg_isPath j)
    exact hq.reverse
  have hv_not_qrev : v ∉ q.reverse.support := by
    intro hvq
    have hvq_support : v ∈ q.support := by
      rw [SimpleGraph.Walk.support_reverse] at hvq
      exact List.mem_reverse.mp hvq
    exact T.internal_not_mem_other_leg_support hfeet_injective hij hv
      (SimpleGraph.Walk.support_takeUntil_subset (T.leg j) hx hvq_support)
  have hprefix : (hvx.toWalk.append q.reverse).IsPath :=
    Walk.edge_append_isPath hvx hq_path hv_not_qrev
  refine Walk.IsPath.append_of_support_inter_eq_endpoint hprefix (T.leg_isPath k) ?_
  intro z hz_prefix hzk
  have hz_prefix' := Walk.edge_append_support_subset_insert (q := q.reverse) hvx hz_prefix
  rcases hz_prefix' with rfl | hzqrev
  · exact False.elim (T.internal_not_mem_other_leg_support hfeet_injective hik hv hzk)
  · have hzq_support : z ∈ q.support := by
      rw [SimpleGraph.Walk.support_reverse] at hzqrev
      exact List.mem_reverse.mp hzqrev
    have hzj : z ∈ (T.leg j).support :=
      SimpleGraph.Walk.support_takeUntil_subset (T.leg j) hx hzq_support
    exact T.diff_leg_support_inter_eq_apex hfeet_injective hjk hzj hzk

theorem Triad.internal_cross_edge_takeUntil_reverse_append_leg_support_subset_vertexSet
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {i j k : Fin 3}
    {v x : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hx : x ∈ (T.leg j).support)
    (hvx : G.Adj v x) :
    {z : V |
      z ∈ ((hvx.toWalk.append ((T.leg j).takeUntil x hx).reverse).append
        (T.leg k)).support} ⊆ T.vertexSet := by
  intro z hz
  change z ∈
    ((hvx.toWalk.append ((T.leg j).takeUntil x hx).reverse).append
      (T.leg k)).support at hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz_prefix | hzk
  · have hz_prefix' := Walk.edge_append_support_subset_insert
      (q := ((T.leg j).takeUntil x hx).reverse) hvx hz_prefix
    rcases hz_prefix' with rfl | hzqrev
    · exact ⟨i, hv.1⟩
    · have hzq : z ∈ ((T.leg j).takeUntil x hx).support := by
        rw [SimpleGraph.Walk.support_reverse] at hzqrev
        exact List.mem_reverse.mp hzqrev
      exact ⟨j, SimpleGraph.Walk.support_takeUntil_subset (T.leg j) hx hzq⟩
  · exact ⟨k, hzk⟩

theorem Triad.internal_cross_edge_takeUntil_reverse_append_leg_support_cases
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {j k : Fin 3}
    {v x z : V}
    (hx : x ∈ (T.leg j).support)
    (hvx : G.Adj v x)
    (hz :
      z ∈ ((hvx.toWalk.append ((T.leg j).takeUntil x hx).reverse).append
        (T.leg k)).support) :
    z = v ∨ z ∈ ((T.leg j).takeUntil x hx).support ∨
      z ∈ (T.leg k).support := by
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz_prefix | hzk
  · have hz_prefix' := Walk.edge_append_support_subset_insert
      (q := ((T.leg j).takeUntil x hx).reverse) hvx hz_prefix
    rcases hz_prefix' with rfl | hzqrev
    · exact Or.inl rfl
    · right
      left
      rw [SimpleGraph.Walk.support_reverse] at hzqrev
      exact List.mem_reverse.mp hzqrev
  · exact Or.inr (Or.inr hzk)

theorem Triad.internal_dropUntil_disjoint_cross_edge_takeUntil_reverse_append_leg
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    {v x : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hx : x ∈ (T.leg j).support)
    (hvx : G.Adj v x) :
    Disjoint
      (Walk.InternalVertices ((T.leg i).dropUntil v hv.1))
      (Walk.InternalVertices
        ((hvx.toWalk.append ((T.leg j).takeUntil x hx).reverse).append
          (T.leg k))) := by
  rw [Set.disjoint_left]
  intro z hzi hzkcomp
  have hzi_old : z ∈ Walk.InternalVertices (T.leg i) :=
    T.internal_dropUntil_internalVertices_subset hv hzi
  have hcases :=
    T.internal_cross_edge_takeUntil_reverse_append_leg_support_cases hx hvx hzkcomp.1
  rcases hcases with rfl | hzjk
  · exact hzi.2.1 rfl
  · rcases hzjk with hzprefix | hzlegk
    · have hzj : z ∈ (T.leg j).support :=
        SimpleGraph.Walk.support_takeUntil_subset (T.leg j) hx hzprefix
      exact hzi_old.2.1
        (T.diff_leg_support_inter_eq_apex hfeet_injective hij hzi_old.1 hzj)
    · exact hzi_old.2.1
        (T.diff_leg_support_inter_eq_apex hfeet_injective hik hzi_old.1 hzlegk)

theorem Triad.cross_edge_dropUntil_disjoint_cross_edge_takeUntil_reverse_append_leg
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {j k : Fin 3}
    (hjk : j ≠ k)
    {v x y : V}
    (hx : x ∈ (T.leg j).support)
    (hy : y ∈ (T.leg j).support)
    (hy_ne_apex : y ≠ T.apex)
    (hidx : (T.leg j).support.idxOf x < (T.leg j).support.idxOf y)
    (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    Disjoint
      (Walk.InternalVertices (hvy.toWalk.append ((T.leg j).dropUntil y hy)))
      (Walk.InternalVertices
        ((hvx.toWalk.append ((T.leg j).takeUntil x hx).reverse).append
          (T.leg k))) := by
  rw [Set.disjoint_left]
  intro z hz_suffix hz_compound
  have hz_old_j : z ∈ Walk.InternalVertices (T.leg j) :=
    T.internal_cross_edge_dropUntil_internalVertices_subset hy hy_ne_apex hvy hz_suffix
  have hcases :=
    T.internal_cross_edge_takeUntil_reverse_append_leg_support_cases hx hvx hz_compound.1
  rcases hcases with rfl | hzjk
  · exact hz_suffix.2.1 rfl
  · rcases hzjk with hzprefix | hzlegk
    · have hz_suffix_support := Walk.edge_append_support_subset_insert
        (q := (T.leg j).dropUntil y hy) hvy hz_suffix.1
      rcases hz_suffix_support with rfl | hzdrop
      · exact hz_suffix.2.1 rfl
      · exact Set.disjoint_left.mp
          (Walk.IsPath.takeUntil_support_disjoint_dropUntil_support_of_idx_lt
            (T.leg_isPath j) hx hy hidx) hzprefix hzdrop
    · exact hz_old_j.2.1
        (T.diff_leg_support_inter_eq_apex hfeet_injective hjk hz_old_j.1 hzlegk)

theorem Triad.internal_cross_edge_takeUntil_reverse_append_leg_avoids_feet
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j k : Fin 3}
    {v x : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hx : x ∈ (T.leg j).support)
    (hx_ne_foot : x ≠ feet j)
    (hvx : G.Adj v x) :
    forall l : Fin 3,
      feet l ∉ Walk.InternalVertices
        ((hvx.toWalk.append ((T.leg j).takeUntil x hx).reverse).append
          (T.leg k)) := by
  intro l hfoot
  have hcases :=
    T.internal_cross_edge_takeUntil_reverse_append_leg_support_cases hx hvx hfoot.1
  rcases hcases with h_eq_v | hcases
  · exact T.internal_ne_foot hv l h_eq_v.symm
  · rcases hcases with hprefix | hk_support
    · by_cases hlj : l = j
      · subst l
        exact (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.leg_isPath j) hx hx_ne_foot.symm) hprefix
      · have hfoot_j_internal : feet l ∈ Walk.InternalVertices (T.leg j) := by
          refine ⟨SimpleGraph.Walk.support_takeUntil_subset (T.leg j) hx hprefix, ?_, ?_⟩
          · exact (T.apex_not_foot l).symm
          · intro h_eq
            exact hlj (hfeet_injective h_eq)
        exact T.internal_vertices_avoid_feet l j hfoot_j_internal
    · by_cases hlk : l = k
      · subst l
        exact hfoot.2.2 rfl
      · have hfoot_k_internal : feet l ∈ Walk.InternalVertices (T.leg k) := by
          refine ⟨hk_support, ?_, ?_⟩
          · exact (T.apex_not_foot l).symm
          · intro h_eq
            exact hlk (hfeet_injective h_eq)
        exact T.internal_vertices_avoid_feet l k hfoot_k_internal

def Triad.sameLegReroute
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
    (hx_ne_foot : x ≠ feet j)
    (hy_ne_apex : y ≠ T.apex)
    (hidx : (T.leg j).support.idxOf x < (T.leg j).support.idxOf y)
    (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    Triad G feet := by
  let p_i : G.Walk v (feet i) := (T.leg i).dropUntil v hv.1
  let p_j : G.Walk v (feet j) := hvy.toWalk.append ((T.leg j).dropUntil y hy)
  let p_k : G.Walk v (feet k) :=
    (hvx.toWalk.append ((T.leg j).takeUntil x hx).reverse).append (T.leg k)
  have hpath_i : p_i.IsPath := by
    simpa [p_i] using T.internal_dropUntil_isPath hv
  have hpath_j : p_j.IsPath := by
    simpa [p_j] using
      T.internal_cross_edge_dropUntil_isPath hfeet_injective hij hv hy hvy
  have hpath_k : p_k.IsPath := by
    simpa [p_k] using
      T.internal_cross_edge_takeUntil_reverse_append_leg_isPath
        hfeet_injective hij hik hjk hv hx hvx
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
    simpa [p_i, p_k] using
      T.internal_dropUntil_disjoint_cross_edge_takeUntil_reverse_append_leg
        hfeet_injective hij hik hv hx hvx
  have hdis_j_k : Disjoint (Walk.InternalVertices p_j) (Walk.InternalVertices p_k) := by
    simpa [p_j, p_k] using
      T.cross_edge_dropUntil_disjoint_cross_edge_takeUntil_reverse_append_leg
        hfeet_injective hjk hx hy hy_ne_apex hidx hvx hvy
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
    exact T.internal_cross_edge_takeUntil_reverse_append_leg_avoids_feet
      hfeet_injective hv hx hx_ne_foot hvx l (by simpa [p_k] using hfoot)
  exact Triad.ofThreeLegs hij hik hjk p_i p_j p_k
    hpath_i hpath_j hpath_k (fun l => T.internal_ne_foot hv l)
    hdis_i_j hdis_i_k hdis_j_k havoid_i havoid_j havoid_k

theorem Triad.sameLegReroute_vertexSet_subset
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
    (hx_ne_foot : x ≠ feet j)
    (hy_ne_apex : y ≠ T.apex)
    (hidx : (T.leg j).support.idxOf x < (T.leg j).support.idxOf y)
    (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    (T.sameLegReroute hfeet_injective hij hik hjk hv hx hy
      hx_ne_foot hy_ne_apex hidx hvx hvy).vertexSet ⊆ T.vertexSet := by
  intro z hz
  rcases hz with ⟨l, hzl⟩
  dsimp [Triad.sameLegReroute, Triad.ofThreeLegs] at hzl
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
      rcases hzl with rfl | hzjk
      · exact ⟨i, hv.1⟩
      · rcases hzjk with hzprefix | hzlegk
        · exact ⟨j, SimpleGraph.Walk.support_takeUntil_subset (T.leg j) hx hzprefix⟩
        · exact ⟨k, hzlegk⟩

theorem Triad.sameLegReroute_omits_between_vertex
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    {v x y z : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hx : x ∈ (T.leg j).support)
    (hy : y ∈ (T.leg j).support)
    (hz : z ∈ (T.leg j).support)
    (hz_ne_apex : z ≠ T.apex)
    (hx_ne_foot : x ≠ feet j)
    (hy_ne_apex : y ≠ T.apex)
    (hxz : (T.leg j).support.idxOf x < (T.leg j).support.idxOf z)
    (hzy : (T.leg j).support.idxOf z < (T.leg j).support.idxOf y)
    (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    z ∉ (T.sameLegReroute hfeet_injective hij hik hjk hv hx hy
      hx_ne_foot hy_ne_apex (lt_trans hxz hzy) hvx hvy).vertexSet := by
  intro hz_new
  rcases hz_new with ⟨l, hzl⟩
  dsimp [Triad.sameLegReroute, Triad.ofThreeLegs] at hzl
  by_cases hli : l = i
  · subst l
    simp at hzl
    have hzi : z ∈ (T.leg i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (T.leg i) hv.1 hzl
    exact hz_ne_apex (T.diff_leg_support_inter_eq_apex hfeet_injective hij.symm hz hzi)
  · by_cases hlj : l = j
    · subst l
      simp [hij.symm] at hzl
      rcases hzl with h_eq_v | hzdrop
      · exact T.internal_not_mem_other_leg_support hfeet_injective hij hv (h_eq_v ▸ hz)
      · have hy_le_z := Walk.idxOf_le_of_mem_dropUntil (T.leg_isPath j) hy hzdrop
        omega
    · have hlk : l = k := fin3_eq_of_ne_ne hij hik hjk hli hlj
      subst l
      have hki : k ≠ i := fun h => hik h.symm
      have hkj : k ≠ j := fun h => hjk h.symm
      simp [hki, hkj] at hzl
      rcases hzl with h_eq_v | hcases
      · exact T.internal_not_mem_other_leg_support hfeet_injective hij hv (h_eq_v ▸ hz)
      · rcases hcases with hzprefix | hzk
        · have z_le_x := Walk.idxOf_le_of_mem_takeUntil hx hzprefix
          omega
        · exact hz_ne_apex (T.diff_leg_support_inter_eq_apex hfeet_injective hjk hz hzk)

theorem Triad.not_lean_of_internal_adj_same_leg_idx_gap
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
    (hx_ne_foot : x ≠ feet j)
    (hy_ne_apex : y ≠ T.apex)
    (hgap : (T.leg j).support.idxOf x + 1 < (T.leg j).support.idxOf y)
    (hvx : G.Adj v x)
    (hvy : G.Adj v y) :
    ¬ T.Lean := by
  obtain ⟨z, hz, hxz, hzy, hz_ne_apex⟩ :=
    Walk.exists_between_support_of_idx_gap (T.leg_isPath j) hy hgap
  have hidx : (T.leg j).support.idxOf x < (T.leg j).support.idxOf y := by omega
  let T' : Triad G feet :=
    T.sameLegReroute hfeet_injective hij hik hjk hv hx hy
      hx_ne_foot hy_ne_apex hidx hvx hvy
  exact T.not_lean_of_contained_triad_omits_vertex T'
    (T.sameLegReroute_vertexSet_subset
      hfeet_injective hij hik hjk hv hx hy hx_ne_foot hy_ne_apex hidx hvx hvy)
    ⟨j, hz⟩
    (T.sameLegReroute_omits_between_vertex hfeet_injective hij hik hjk hv hx hy hz
      hz_ne_apex hx_ne_foot hy_ne_apex hxz hzy hvx hvy)

end Schematic.Math.GraphTheory
