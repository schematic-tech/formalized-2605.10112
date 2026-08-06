import DominatingFourColour.Prerequisites.Triad.CommonNeighborCertificates

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

theorem Triad.punctured_carrier_verts_eq_vertexSet_diff_range
    {feet : Fin 3 -> V}
    (T : Triad G feet) :
    (T.carrier.deleteVerts (Set.range feet)).verts =
      T.vertexSet \ Set.range feet := by
  ext v
  simp [T.mem_carrier_verts_iff]

theorem Triad.mem_punctured_carrier_verts_iff
    {feet : Fin 3 -> V}
    (T : Triad G feet) {v : V} :
    v ∈ (T.carrier.deleteVerts (Set.range feet)).verts ↔
      v ∈ T.vertexSet ∧ v ∉ Set.range feet := by
  rw [T.punctured_carrier_verts_eq_vertexSet_diff_range, Set.mem_diff]

theorem Triad.eq_apex_or_exists_internal_of_mem_punctured_carrier
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {v : V}
    (hv : v ∈ (T.carrier.deleteVerts (Set.range feet)).verts) :
    v = T.apex ∨ Exists fun i : Fin 3 =>
      v ∈ Walk.InternalVertices (T.leg i) := by
  have hv' := (T.mem_punctured_carrier_verts_iff).mp hv
  rcases hv'.1 with ⟨i, hvi⟩
  by_cases hv_apex : v = T.apex
  · exact Or.inl hv_apex
  · exact Or.inr ⟨i, hvi, hv_apex, by
      intro hv_foot
      exact hv'.2 ⟨i, hv_foot.symm⟩⟩

theorem Triad.leg_toSubgraph_le_carrier {feet : Fin 3 -> V} (T : Triad G feet) (i : Fin 3) :
    (T.leg i).toSubgraph ≤ T.carrier := by
  exact le_iSup (fun i : Fin 3 => (T.leg i).toSubgraph) i

theorem Triad.carrier_connected {feet : Fin 3 -> V} (T : Triad G feet) :
    T.carrier.Connected := by
  rw [SimpleGraph.Subgraph.connected_iff_forall_exists_walk_subgraph]
  constructor
  · exact ⟨T.apex, by
      rw [← T.vertexSet_eq_carrier_verts]
      exact T.apex_mem_vertexSet⟩
  · intro u v hu hv
    rw [T.mem_carrier_verts_iff] at hu hv
    rcases hu with ⟨i, hui⟩
    rcases hv with ⟨j, hvj⟩
    have hui_verts : u ∈ (T.leg i).toSubgraph.verts := by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph]
      exact hui
    have hvj_verts : v ∈ (T.leg j).toSubgraph.verts := by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph]
      exact hvj
    have hpre_i := (T.leg i).toSubgraph_connected.preconnected
    have hpre_j := (T.leg j).toSubgraph_connected.preconnected
    rw [SimpleGraph.Subgraph.preconnected_iff_forall_exists_walk_subgraph] at hpre_i
    rw [SimpleGraph.Subgraph.preconnected_iff_forall_exists_walk_subgraph] at hpre_j
    obtain ⟨p, hp⟩ :=
      hpre_i hui_verts (T.leg i).start_mem_verts_toSubgraph
    obtain ⟨q, hq⟩ :=
      hpre_j (T.leg j).start_mem_verts_toSubgraph hvj_verts
    refine ⟨p.append q, ?_⟩
    rw [SimpleGraph.Walk.toSubgraph_append]
    exact sup_le
      (le_trans hp (T.leg_toSubgraph_le_carrier i))
      (le_trans hq (T.leg_toSubgraph_le_carrier j))

theorem Triad.exists_carrier_path_to_first_mem
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {R : Set V}
    (hR_nonempty : R.Nonempty)
    (hR_subset : R ⊆ T.vertexSet)
    (i : Fin 3) :
    Exists fun x : V =>
      Exists fun _hxR : x ∈ R =>
        Exists fun p : G.Walk (feet i) x =>
          p.IsPath ∧ p.toSubgraph ≤ T.carrier ∧
            forall z : V, z ∈ p.support -> z ∈ R -> z = x := by
  obtain ⟨r, hrR⟩ := hR_nonempty
  have hfoot_carrier : feet i ∈ T.carrier.verts := by
    rw [← T.vertexSet_eq_carrier_verts]
    exact T.foot_mem_vertexSet i
  have hr_carrier : r ∈ T.carrier.verts := by
    rw [← T.vertexSet_eq_carrier_verts]
    exact hR_subset hrR
  obtain ⟨p, hp_path, hp_le⟩ :=
    Subgraph.Connected.exists_path_between
      (G := G) (H := T.carrier) T.carrier_connected hfoot_carrier hr_carrier
  obtain ⟨x, hx_support, hxR, hfirst⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem (G := G) hp_path R hrR
  let q : G.Walk (feet i) x := p.takeUntil x hx_support
  refine ⟨x, hxR, q, ?_, ?_, ?_⟩
  · simpa [q] using hp_path.takeUntil hx_support
  · exact le_trans (Walk.toSubgraph_takeUntil_le p hx_support) hp_le
  · intro z hz hzR
    exact hfirst z (by simpa [q] using hz) hzR

theorem Triad.exists_carrier_path_to_nonfoot
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {x : V}
    (hxT : x ∈ T.vertexSet)
    (hx_not_feet : x ∉ Set.range feet)
    (i : Fin 3) :
    Exists fun p : G.Walk (feet i) x =>
      p.IsPath ∧ p.toSubgraph ≤ T.carrier ∧
        forall j : Fin 3, j ≠ i -> feet j ∉ p.support := by
  classical
  rcases hxT with ⟨k, hxk⟩
  by_cases hki : k = i
  · subst k
    let p : G.Walk (feet i) x := ((T.leg i).dropUntil x hxk).reverse
    have hpath_drop : ((T.leg i).dropUntil x hxk).IsPath := by
      exact SimpleGraph.Walk.isPath_of_isSubwalk
        (SimpleGraph.Walk.isSubwalk_dropUntil (T.leg i) hxk)
        (T.leg_isPath i)
    refine ⟨p, hpath_drop.reverse, ?_, ?_⟩
    · rw [SimpleGraph.Walk.toSubgraph_reverse]
      exact le_trans (Walk.toSubgraph_dropUntil_le (T.leg i) hxk)
        (T.leg_toSubgraph_le_carrier i)
    · intro j hji hfoot
      rw [SimpleGraph.Walk.support_reverse] at hfoot
      have hfoot_leg : feet j ∈ (T.leg i).support :=
        SimpleGraph.Walk.support_dropUntil_subset (T.leg i) hxk
          (List.mem_reverse.mp hfoot)
      have hidx : j = i :=
        (T.foot_mem_leg_support_iff hfeet_injective j i).mp hfoot_leg
      exact hji hidx
  · let p : G.Walk (feet i) x :=
      (T.leg i).reverse.append ((T.leg k).takeUntil x hxk)
    have htake_path : ((T.leg k).takeUntil x hxk).IsPath := by
      exact SimpleGraph.Walk.isPath_of_isSubwalk
        (SimpleGraph.Walk.isSubwalk_takeUntil (T.leg k) hxk)
        (T.leg_isPath k)
    have hpath : p.IsPath := by
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        (T.leg_isPath i).reverse htake_path ?_
      intro z hzleft hzright
      rw [SimpleGraph.Walk.support_reverse] at hzleft
      have hzright_leg : z ∈ (T.leg k).support :=
        SimpleGraph.Walk.support_takeUntil_subset (T.leg k) hxk hzright
      exact T.diff_leg_support_inter_eq_apex hfeet_injective
        (fun hik => hki hik.symm)
        (List.mem_reverse.mp hzleft) hzright_leg
    refine ⟨p, hpath, ?_, ?_⟩
    · rw [SimpleGraph.Walk.toSubgraph_append,
        SimpleGraph.Walk.toSubgraph_reverse]
      exact sup_le (T.leg_toSubgraph_le_carrier i)
        (le_trans (Walk.toSubgraph_takeUntil_le (T.leg k) hxk)
          (T.leg_toSubgraph_le_carrier k))
    · intro j hji hfoot
      rw [SimpleGraph.Walk.mem_support_append_iff] at hfoot
      rcases hfoot with hfoot_i | hfoot_k_prefix
      · rw [SimpleGraph.Walk.support_reverse] at hfoot_i
        have hfoot_i_support : feet j ∈ (T.leg i).support :=
          List.mem_reverse.mp hfoot_i
        have hidx : j = i :=
          (T.foot_mem_leg_support_iff hfeet_injective j i).mp hfoot_i_support
        exact hji hidx
      · have hfoot_k_support : feet j ∈ (T.leg k).support :=
          SimpleGraph.Walk.support_takeUntil_subset (T.leg k) hxk hfoot_k_prefix
        have hjk : j = k :=
          (T.foot_mem_leg_support_iff hfeet_injective j k).mp hfoot_k_support
        subst j
        have hendpoint_not : feet k ∉ ((T.leg k).takeUntil x hxk).support := by
          exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            (T.leg_isPath k) hxk (by
              intro hxfoot
              exact hx_not_feet ⟨k, hxfoot⟩)
        exact hendpoint_not hfoot_k_prefix

theorem Triad.exists_carrier_path_to_first_mem_of_nonfoot_target
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {R : Set V}
    (hR_subset : R ⊆ T.vertexSet)
    {x : V}
    (hxR : x ∈ R)
    (hx_not_feet : x ∉ Set.range feet)
    (i : Fin 3) :
    Exists fun z : V =>
      Exists fun _hzR : z ∈ R =>
        Exists fun p : G.Walk (feet i) z =>
          p.IsPath ∧ p.toSubgraph ≤ T.carrier ∧
            (forall w : V, w ∈ p.support -> w ∈ R -> w = z) ∧
              forall j : Fin 3, j ≠ i -> feet j ∉ p.support := by
  obtain ⟨p, hp_path, hp_le, hp_avoid⟩ :=
    T.exists_carrier_path_to_nonfoot hfeet_injective
      (hR_subset hxR) hx_not_feet i
  obtain ⟨z, hz_support, hzR, hfirst⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem (G := G) hp_path R hxR
  let q : G.Walk (feet i) z := p.takeUntil z hz_support
  refine ⟨z, hzR, q, ?_, ?_, ?_, ?_⟩
  · simpa [q] using hp_path.takeUntil hz_support
  · exact le_trans (Walk.toSubgraph_takeUntil_le p hz_support) hp_le
  · intro w hw hwR
    exact hfirst w (by simpa [q] using hw) hwR
  · intro j hji hfoot
    exact hp_avoid j hji
      (SimpleGraph.Walk.support_takeUntil_subset p hz_support
        (by simpa [q] using hfoot))

end Schematic.Math.GraphTheory

