import DominatingFourColour.Prerequisites.Triad.CarrierPaths

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

def Triad.ofThreeLegs
    {feet : Fin 3 -> V}
    {apex : V}
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    (p_i : G.Walk apex (feet i))
    (p_j : G.Walk apex (feet j))
    (p_k : G.Walk apex (feet k))
    (hpath_i : p_i.IsPath)
    (hpath_j : p_j.IsPath)
    (hpath_k : p_k.IsPath)
    (hapex_not_foot : forall l : Fin 3, apex ≠ feet l)
    (hdis_ij : Disjoint (Walk.InternalVertices p_i) (Walk.InternalVertices p_j))
    (hdis_ik : Disjoint (Walk.InternalVertices p_i) (Walk.InternalVertices p_k))
    (hdis_jk : Disjoint (Walk.InternalVertices p_j) (Walk.InternalVertices p_k))
    (havoid_i : forall l : Fin 3, feet l ∉ Walk.InternalVertices p_i)
    (havoid_j : forall l : Fin 3, feet l ∉ Walk.InternalVertices p_j)
    (havoid_k : forall l : Fin 3, feet l ∉ Walk.InternalVertices p_k) :
    Triad G feet := by
  let leg : forall l : Fin 3, G.Walk apex (feet l) := fun l =>
    if hli : l = i then
      p_i.copy rfl (by simp [hli])
    else if hlj : l = j then
      p_j.copy rfl (by simp [hlj])
    else
      p_k.copy rfl (by
        have hlk : l = k := fin3_eq_of_ne_ne hij hik hjk hli hlj
        simp [hlk])
  have hpath : forall l : Fin 3, (leg l).IsPath := by
    apply Fin3.forall_of_three (P := fun l => (leg l).IsPath) hij hik hjk
    · simpa [leg] using hpath_i
    · simpa [leg, hij.symm] using hpath_j
    · simpa [leg, hik.symm, hjk.symm] using hpath_k
  have hdis : forall l m : Fin 3, l ≠ m ->
      Disjoint (Walk.InternalVertices (leg l)) (Walk.InternalVertices (leg m)) := by
    apply Fin3.pairwise_disjoint_of_three hij hik hjk
    · simpa [leg, hij.symm, Walk.internalVertices_copy] using hdis_ij
    · simpa [leg, hik.symm, hjk.symm, Walk.internalVertices_copy] using hdis_ik
    · simpa [leg, hij.symm, hik.symm, hjk.symm, Walk.internalVertices_copy] using hdis_jk
  have havoid : forall l m : Fin 3, feet l ∉ Walk.InternalVertices (leg m) := by
    intro l
    apply Fin3.forall_of_three
      (P := fun m => feet l ∉ Walk.InternalVertices (leg m)) hij hik hjk
    · simpa [leg, Walk.internalVertices_copy] using havoid_i l
    · simpa [leg, hij.symm, Walk.internalVertices_copy] using havoid_j l
    · simpa [leg, hik.symm, hjk.symm, Walk.internalVertices_copy] using havoid_k l
  exact {
    apex := apex
    apex_not_foot := hapex_not_foot
    leg := leg
    leg_isPath := hpath
    apex_only_common_vertex := hdis
    internal_vertices_avoid_feet := havoid
  }

def Triad.replaceLeg
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (i : Fin 3)
    (p : G.Walk T.apex (feet i))
    (hp : p.IsPath)
    (hdisjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint (Walk.InternalVertices p) (Walk.InternalVertices (T.leg j)))
    (havoid :
      forall j : Fin 3, feet j ∉ Walk.InternalVertices p) :
    Triad G feet where
  apex := T.apex
  apex_not_foot := T.apex_not_foot
  leg j :=
    if hji : j = i then
      p.copy rfl (by simp [hji])
    else
      T.leg j
  leg_isPath j := by
    by_cases hji : j = i
    · simp [hji, hp]
    · simp [hji, T.leg_isPath j]
  apex_only_common_vertex := by
    intro j k hjk
    have hdis := Fin3.pairwise_disjoint_update
      (fun j => Walk.InternalVertices (T.leg j)) i
      (Walk.InternalVertices p) T.apex_only_common_vertex hdisjoint j k hjk
    by_cases hji : j = i
    · subst j
      by_cases hki : k = i
      · exact False.elim (hjk hki.symm)
      · simpa [hki, Walk.internalVertices_copy] using hdis
    · by_cases hki : k = i
      · subst k
        simpa [hji, Walk.internalVertices_copy] using hdis
      · simpa [hji, hki] using hdis
  internal_vertices_avoid_feet := by
    intro j k
    by_cases hki : k = i
    · subst k
      simpa using havoid j
    · simpa [hki] using T.internal_vertices_avoid_feet j k

theorem Triad.lean_internal_mem_of_replace_leg_subset
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (i : Fin 3)
    (p : G.Walk T.apex (feet i))
    (hp : p.IsPath)
    (hdisjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint (Walk.InternalVertices p) (Walk.InternalVertices (T.leg j)))
    (havoid :
      forall j : Fin 3, feet j ∉ Walk.InternalVertices p)
    (hsubset : forall v : V, v ∈ p.support -> v ∈ (T.leg i).support)
    {z : V}
    (hz_internal : z ∈ Walk.InternalVertices (T.leg i)) :
    z ∈ p.support := by
  classical
  let T' : Triad G feet := T.replaceLeg i p hp hdisjoint havoid
  have hT'_subset : T'.vertexSet ⊆ T.vertexSet := by
    intro v hv
    rcases hv with ⟨j, hvj⟩
    by_cases hji : j = i
    · subst j
      refine ⟨i, hsubset v ?_⟩
      simpa [T', Triad.replaceLeg] using hvj
    · exact ⟨j, by simpa [T', Triad.replaceLeg, hji] using hvj⟩
  have hT_subset : T.vertexSet ⊆ T'.vertexSet :=
    hlean T' hT'_subset
  have hz_T : z ∈ T.vertexSet := ⟨i, hz_internal.1⟩
  have hz_T' : z ∈ T'.vertexSet := hT_subset hz_T
  rcases hz_T' with ⟨j, hzj⟩
  by_cases hji : j = i
  · subst j
    simpa [T', Triad.replaceLeg] using hzj
  · have hz_not_support_j : z ∉ (T.leg j).support := by
      intro hz_support_j
      have hz_internal_j : z ∈ Walk.InternalVertices (T.leg j) := by
        refine ⟨hz_support_j, hz_internal.2.1, ?_⟩
        intro hz_foot_j
        exact T.internal_vertices_avoid_feet j i
          (by simpa [hz_foot_j] using hz_internal)
      have hij : i ≠ j := fun hij => hji hij.symm
      exact Set.disjoint_left.mp (T.apex_only_common_vertex i j hij)
        hz_internal hz_internal_j
    exact False.elim
      (hz_not_support_j (by simpa [T', Triad.replaceLeg, hji] using hzj))

theorem Triad.lean_leg_support_subset_of_replace_leg_subset
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (i : Fin 3)
    (p : G.Walk T.apex (feet i))
    (hp : p.IsPath)
    (hdisjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint (Walk.InternalVertices p) (Walk.InternalVertices (T.leg j)))
    (havoid :
      forall j : Fin 3, feet j ∉ Walk.InternalVertices p)
    (hsubset : forall v : V, v ∈ p.support -> v ∈ (T.leg i).support) :
    {z : V | z ∈ (T.leg i).support} ⊆ {z : V | z ∈ p.support} := by
  intro z hz
  by_cases hz_apex : z = T.apex
  · simp [hz_apex]
  by_cases hz_foot : z = feet i
  · simp [hz_foot]
  exact T.lean_internal_mem_of_replace_leg_subset hlean i p hp hdisjoint havoid
    hsubset ⟨hz, hz_apex, hz_foot⟩

theorem Triad.replacement_internalVertices_disjoint_of_support_subset
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (i : Fin 3)
    (p : G.Walk T.apex (feet i))
    (hsubset : forall v : V, v ∈ p.support -> v ∈ (T.leg i).support) :
    forall j : Fin 3, j ≠ i ->
      Disjoint (Walk.InternalVertices p) (Walk.InternalVertices (T.leg j)) := by
  intro j hji
  rw [Set.disjoint_left]
  intro z hzp hzj
  have hzi : z ∈ Walk.InternalVertices (T.leg i) :=
    ⟨hsubset z hzp.1, hzp.2.1, hzp.2.2⟩
  exact Set.disjoint_left.mp
    (T.apex_only_common_vertex i j (fun hij => hji hij.symm)) hzi hzj

theorem Triad.replacement_internal_vertices_avoid_feet_of_support_subset
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3)
    (p : G.Walk T.apex (feet i))
    (hsubset : forall v : V, v ∈ p.support -> v ∈ (T.leg i).support) :
    forall j : Fin 3, feet j ∉ Walk.InternalVertices p := by
  intro j hfoot
  by_cases hji : j = i
  · subst j
    exact hfoot.2.2 rfl
  · have hfoot_old : feet j ∈ Walk.InternalVertices (T.leg i) := by
      refine ⟨hsubset (feet j) hfoot.1, (T.apex_not_foot j).symm, ?_⟩
      intro hfeet
      exact hji (hfeet_injective hfeet)
    exact T.internal_vertices_avoid_feet j i hfoot_old

theorem Triad.lean_leg_support_subset_of_path_support_subset
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3)
    (p : G.Walk T.apex (feet i))
    (hp : p.IsPath)
    (hsubset : forall v : V, v ∈ p.support -> v ∈ (T.leg i).support) :
    {z : V | z ∈ (T.leg i).support} ⊆ {z : V | z ∈ p.support} := by
  exact T.lean_leg_support_subset_of_replace_leg_subset hlean i p hp
    (T.replacement_internalVertices_disjoint_of_support_subset i p hsubset)
    (T.replacement_internal_vertices_avoid_feet_of_support_subset
      hfeet_injective i p hsubset)
    hsubset

theorem Triad.lean_leg_support_subset_chordShortcut_bypass
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3)
    {x y : V}
    (hx : x ∈ (T.leg i).support)
    (hy : y ∈ (T.leg i).support)
    (hxy : G.Adj x y) :
    {z : V | z ∈ (T.leg i).support} ⊆
      {z : V |
        z ∈ (Walk.chordShortcut (T.leg i) hx hy hxy).bypass.support} := by
  let q : G.Walk T.apex (feet i) :=
    (Walk.chordShortcut (T.leg i) hx hy hxy).bypass
  have hq_path : q.IsPath := by
    exact SimpleGraph.Walk.bypass_isPath _
  have hq_subset :
      forall v : V, v ∈ q.support -> v ∈ (T.leg i).support := by
    intro v hv
    exact Walk.chordShortcut_bypass_support_subset (T.leg i) hx hy hxy hv
  exact T.lean_leg_support_subset_of_path_support_subset
    hlean hfeet_injective i q hq_path hq_subset

theorem Triad.not_adj_of_lean_leg_idx_gap
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3)
    {x y : V}
    (hx : x ∈ (T.leg i).support)
    (hy : y ∈ (T.leg i).support)
    (hidx : (T.leg i).support.idxOf x + 1 < (T.leg i).support.idxOf y) :
    ¬ G.Adj x y := by
  intro hxy
  let r : G.Walk T.apex (feet i) :=
    Walk.chordShortcut (T.leg i) hx hy hxy
  let q : G.Walk T.apex (feet i) := r.bypass
  have hsupport :
      forall z : V, z ∈ (T.leg i).support -> z ∈ q.support := by
    intro z hz
    exact T.lean_leg_support_subset_chordShortcut_bypass
      hlean hfeet_injective i hx hy hxy hz
  have hlen_lower : (T.leg i).length <= q.length :=
    Schematic.Math.GraphTheory.Walk.IsPath.length_le_of_support_subset (T.leg_isPath i) hsupport
  have hlen_bypass : q.length <= r.length := by
    exact SimpleGraph.Walk.length_bypass_le r
  have hlen_short : r.length < (T.leg i).length := by
    exact Walk.chordShortcut_length_lt_of_idx_gap (T.leg i) hx hy hxy hidx
  omega

theorem Triad.lean_leg_isChordless
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hlean : T.Lean)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3) :
    (T.leg i).IsChordless := by
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
  intro x y hx hy hxy
  rcases Walk.toSubgraph_adj_or_idx_gap_of_support_adj
      (T.leg i) hx hy hxy with hsub | hgap
  · exact (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).mp hsub
  · rcases hgap with hgap | hgap
    · exact False.elim
        ((T.not_adj_of_lean_leg_idx_gap hlean hfeet_injective i hx hy hgap) hxy)
    · exact False.elim
        ((T.not_adj_of_lean_leg_idx_gap hlean hfeet_injective i hy hx hgap) hxy.symm)

theorem Triad.internal_cross_edge_dropUntil_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j : Fin 3}
    (hij : i ≠ j)
    {v x : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hx : x ∈ (T.leg j).support)
    (hvx : G.Adj v x) :
    (hvx.toWalk.append ((T.leg j).dropUntil x hx)).IsPath := by
  exact Walk.edge_append_dropUntil_isPath (T.leg_isPath j) hx hvx
    (T.internal_not_mem_other_leg_support hfeet_injective hij hv)

theorem Triad.internal_cross_edge_dropUntil_support_subset_vertexSet
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {i j : Fin 3}
    {v x : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (hx : x ∈ (T.leg j).support)
    (hvx : G.Adj v x) :
    {z : V | z ∈ (hvx.toWalk.append ((T.leg j).dropUntil x hx)).support} ⊆
      T.vertexSet := by
  intro z hz
  have hz' :=
    Walk.edge_append_dropUntil_support_subset_insert
      (p := T.leg j) hx hvx hz
  rcases hz' with rfl | hzj
  · exact ⟨i, hv.1⟩
  · exact ⟨j, hzj⟩

theorem Triad.internal_dropUntil_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {i : Fin 3}
    {v : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i)) :
    ((T.leg i).dropUntil v hv.1).IsPath := by
  exact SimpleGraph.Walk.isPath_of_isSubwalk
    (SimpleGraph.Walk.isSubwalk_dropUntil (T.leg i) hv.1)
    (T.leg_isPath i)

theorem Triad.internal_dropUntil_support_subset_vertexSet
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {i : Fin 3}
    {v : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i)) :
    {z : V | z ∈ ((T.leg i).dropUntil v hv.1).support} ⊆
      T.vertexSet := by
  intro z hz
  exact ⟨i, SimpleGraph.Walk.support_dropUntil_subset (T.leg i) hv.1 hz⟩

theorem Triad.internal_cross_edge_dropUntil_internalVertices_subset
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {j : Fin 3}
    {v x : V}
    (hx : x ∈ (T.leg j).support)
    (hx_ne_apex : x ≠ T.apex)
    (hvx : G.Adj v x) :
    Walk.InternalVertices (hvx.toWalk.append ((T.leg j).dropUntil x hx)) ⊆
      Walk.InternalVertices (T.leg j) := by
  exact Walk.edge_append_dropUntil_internalVertices_subset
    (T.leg_isPath j) hx hx_ne_apex hvx

theorem Triad.internal_dropUntil_internalVertices_subset
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {i : Fin 3}
    {v : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i)) :
    Walk.InternalVertices ((T.leg i).dropUntil v hv.1) ⊆
      Walk.InternalVertices (T.leg i) := by
  exact Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
    (T.leg_isPath i) hv.1 hv.2.1

end Schematic.Math.GraphTheory
