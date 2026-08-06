import DominatingFourColour.Prerequisites.RSTFlaps.ProfileSelection

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

theorem Triad.flapVertexSet_connected
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap) :
    (G.induce (T.flapVertexSet B)).Connected :=
  induceComponentSupport_connected (G := G) B

theorem RST35NoSeparation.triad_flap_boundary_ncard_ge_three_of_large
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST35NoSeparation G feet)
    (T : Triad G feet)
    (B : T.Flap)
    (hlarge : 2 <= (T.flapVertexSet B).ncard) :
    3 <=
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet).ncard :=
  hno.component_boundary_ncard_ge_three_of_large
    (X := T.vertexSet) (fun i => T.foot_mem_vertexSet i) B hlarge

theorem IsFourConnected.triad_flap_boundary_ncard_ge_four
    [Fintype V]
    {feet : Fin 3 -> V}
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (T : Triad G feet)
    (B : T.Flap) :
    4 <=
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet).ncard :=
  hG.component_boundary_ncard_ge_four
    (X := T.vertexSet) (T.vertexSet_ncard_ge_four hfeet_injective) B

theorem Triad.foot_outside_of_flap_boundary_mem
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap)
    {i : Fin 3}
    (hmem :
      feet i ∈ relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet) :
    Exists fun u : V =>
      u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧
        G.Adj u (feet i) := by
  rcases hmem with ⟨_hfootT, u, huB, hui⟩
  refine ⟨u, ?_, hui⟩
  rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
  exact ⟨by simp, T.flapVertexSet_subset_complement B huB⟩

theorem Triad.foot_outside_of_feet_subset_flap_boundary
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap)
    (hfeet_boundary :
      forall i : Fin 3,
        feet i ∈ relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet) :
    forall i : Fin 3,
      Exists fun u : V =>
        u ∈ ((⊤ : G.Subgraph).deleteVerts T.vertexSet).verts ∧
          G.Adj u (feet i) := by
  intro i
  exact T.foot_outside_of_flap_boundary_mem B (hfeet_boundary i)

theorem Triad.exists_path_from_outside_to_flap_boundary_internal_avoids
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hcomplement_connected : (G.induce T.vertexSetᶜ).Connected)
    {root z : V}
    (hroot : root ∉ T.vertexSet)
    {B : T.Flap}
    (hz_boundary :
      z ∈ relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet) :
    Exists fun p : G.Walk root z =>
      p.IsPath ∧
        forall v : V, v ∈ Walk.InternalVertices p -> v ∉ T.vertexSet := by
  classical
  rcases hz_boundary with ⟨_hzT, u, huB, huz⟩
  have hu_compl : u ∈ T.vertexSetᶜ :=
    T.flapVertexSet_subset_complement B huB
  obtain ⟨q, hq_path, hq_support⟩ :=
    connected_induce_exists_path_support_subset
      (G := G) hcomplement_connected hroot hu_compl
  let r : G.Walk root z := q.append huz.toWalk
  have hr_support :
      forall v : V, v ∈ r.support -> v = z ∨ v ∉ T.vertexSet := by
    intro v hv
    change v ∈ (q.append huz.toWalk).support at hv
    rw [SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hvq | hvedge
    · exact Or.inr (hq_support v hvq)
    · simp at hvedge
      rcases hvedge with rfl | rfl
      · exact Or.inr hu_compl
      · exact Or.inl rfl
  refine ⟨r.toPath, r.toPath.property, ?_⟩
  intro v hvint hvT
  rcases hr_support v
      (SimpleGraph.Walk.support_toPath_subset r hvint.1) with hvz | hvnot
  · exact hvint.2.2 hvz
  · exact hvnot hvT

theorem Triad.exists_path_between_flap_boundary_vertices_internal_avoids
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hcomplement_connected : (G.induce T.vertexSetᶜ).Connected)
    {x y : V}
    {B : T.Flap}
    (hx_boundary :
      x ∈ relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet)
    (hy_boundary :
      y ∈ relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet) :
    Exists fun p : G.Walk x y =>
      p.IsPath ∧
        forall v : V, v ∈ Walk.InternalVertices p -> v ∉ T.vertexSet := by
  classical
  rcases hx_boundary with ⟨_hxT, ux, huxB, huxx⟩
  rcases hy_boundary with ⟨_hyT, uy, huyB, huyy⟩
  have hux_compl : ux ∈ T.vertexSetᶜ :=
    T.flapVertexSet_subset_complement B huxB
  have huy_compl : uy ∈ T.vertexSetᶜ :=
    T.flapVertexSet_subset_complement B huyB
  obtain ⟨q, _hq_path, hq_support⟩ :=
    connected_induce_exists_path_support_subset
      (G := G) hcomplement_connected hux_compl huy_compl
  let r : G.Walk x y := huxx.symm.toWalk.append (q.append huyy.toWalk)
  have hr_support :
      forall v : V, v ∈ r.support ->
        v = x ∨ v = y ∨ v ∉ T.vertexSet := by
    intro v hv
    change v ∈ (huxx.symm.toWalk.append
      (q.append huyy.toWalk)).support at hv
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hvedge | hvq | hvedge
    · simp at hvedge
      rcases hvedge with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hux_compl)
    · exact Or.inr (Or.inr (hq_support v hvq))
    · simp at hvedge
      rcases hvedge with rfl | rfl
      · exact Or.inr (Or.inr huy_compl)
      · exact Or.inr (Or.inl rfl)
  refine ⟨r.toPath, r.toPath.property, ?_⟩
  intro v hvint hvT
  rcases hr_support v
      (SimpleGraph.Walk.support_toPath_subset r hvint.1) with hvx | hvy_or
  · exact hvint.2.1 hvx
  · rcases hvy_or with hvy | hvnot
    · exact hvint.2.2 hvy
    · exact hvnot hvT

theorem Triad.exists_flap_containing_connected_set_of_subtriad
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet)
    {K : Set V}
    (hK_connected : (G.induce K).Connected)
    (hK_subset : K ⊆ T.vertexSetᶜ) :
    Exists fun B' : T'.Flap => K ⊆ T'.flapVertexSet B' := by
  have hK_subset_T' : K ⊆ T'.vertexSetᶜ := by
    intro v hvK hvT'
    exact hK_subset hvK (hT'_subset hvT')
  exact connected_set_subset_induceComponentSupport
    (G := G) hK_connected hK_subset_T'

theorem Triad.exists_flap_containing_connected_set
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {K : Set V}
    (hK_connected : (G.induce K).Connected)
    (hK_subset : K ⊆ T.vertexSetᶜ) :
    Exists fun B : T.Flap => K ⊆ T.flapVertexSet B :=
  connected_set_subset_induceComponentSupport
    (G := G) hK_connected hK_subset

theorem Triad.lean_of_distinguished_ncard_maximal_minimal
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard)
    (hmin :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
            T.vertexSet.ncard <= U.vertexSet.ncard) :
    T.Lean := by
  rw [Triad.lean_iff_no_strict_subtriad]
  rintro ⟨T', hstrict⟩
  obtain ⟨B', hB_subset⟩ :=
    T.exists_flap_containing_connected_set_of_subtriad
      (T' := T') hstrict.1 (T.flapVertexSet_connected B)
      (T.flapVertexSet_subset_complement B)
  have hW' : W ⊆ T'.flapVertexSet B' :=
    Set.Subset.trans hW hB_subset
  have hnew_le_old :
      (T'.flapVertexSet B').ncard <= (T.flapVertexSet B).ncard :=
    hmax T' B' hW'
  have hold_le_new :
      (T.flapVertexSet B).ncard <= (T'.flapVertexSet B').ncard :=
    Set.ncard_le_ncard hB_subset
  have hncard_eq :
      (T'.flapVertexSet B').ncard = (T.flapVertexSet B).ncard :=
    le_antisymm hnew_le_old hold_le_new
  have hmin_card : T.vertexSet.ncard <= T'.vertexSet.ncard :=
    hmin T' B' hW' hncard_eq
  have hstrict_card : T'.vertexSet.ncard < T.vertexSet.ncard :=
    Set.ncard_lt_ncard hstrict
  omega

theorem Triad.flapVertexSet_mem_of_adj
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap)
    {x y : V}
    (hx : x ∈ T.flapVertexSet B)
    (hy : y ∉ T.vertexSet)
    (hxy : G.Adj x y) :
    y ∈ T.flapVertexSet B :=
  induceComponentSupport_mem_of_adj (G := G) B hx hy hxy

theorem Triad.flapVertexSet_mem_of_walk
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap)
    {x y : V}
    (hx : x ∈ T.flapVertexSet B)
    (hy : y ∉ T.vertexSet)
    (p : G.Walk x y)
    (hp : forall z : V, z ∈ p.support -> z ∉ T.vertexSet) :
    y ∈ T.flapVertexSet B := by
  have hreach :
      (G.induce T.vertexSetᶜ).Reachable
        ⟨x, hp x p.start_mem_support⟩
        ⟨y, hp y p.end_mem_support⟩ :=
    Walk.reachable_induce_of_support_subset (A := T.vertexSetᶜ) p hp
  exact reachable_induce_compl_mem_of_closed
    (G := G) (S := T.vertexSet) (K := T.flapVertexSet B)
    (u := ⟨x, hp x p.start_mem_support⟩)
    (v := ⟨y, hy⟩)
    hx
    (by
      intro a b ha hb hbT hab
      exact hb (T.flapVertexSet_mem_of_adj B ha hbT hab))
    hreach

theorem Triad.flapVertexSet_ssubset_of_adj_removed_vertex
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B : T.Flap}
    {B' : T'.Flap}
    (hB_subset : T.flapVertexSet B ⊆ T'.flapVertexSet B')
    {x y : V}
    (hxT : x ∈ T.vertexSet)
    (hxT' : x ∉ T'.vertexSet)
    (hyB : y ∈ T.flapVertexSet B)
    (hyx : G.Adj y x) :
    T.flapVertexSet B ⊂ T'.flapVertexSet B' := by
  refine ⟨hB_subset, ?_⟩
  intro hnew_subset_old
  have hxB' : x ∈ T'.flapVertexSet B' :=
    T'.flapVertexSet_mem_of_adj B' (hB_subset hyB) hxT' hyx
  have hxB : x ∈ T.flapVertexSet B :=
    hnew_subset_old hxB'
  exact (T.flapVertexSet_subset_complement B hxB) hxT

theorem Triad.flapSizeProfileWith_lt_of_adj_removed_vertex
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B : T.Flap}
    {B' : T'.Flap}
    (hB_subset : T.flapVertexSet B ⊆ T'.flapVertexSet B')
    {x y : V}
    (hxT : x ∈ T.vertexSet)
    (hxT' : x ∉ T'.vertexSet)
    (hyB : y ∈ T.flapVertexSet B)
    (hyx : G.Adj y x) :
    T.flapSizeProfileWith B < T'.flapSizeProfileWith B' :=
  Triad.flapSizeProfileWith_lt_of_distinguished_flap_ssubset
    (G := G)
    (Triad.flapVertexSet_ssubset_of_adj_removed_vertex
      (G := G) hB_subset hxT hxT' hyB hyx)

theorem Triad.exists_flap_profile_larger_of_subtriad_removed_adjacent_to_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T T' : Triad G feet}
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet)
    {x y : V}
    (hxT : x ∈ T.vertexSet)
    (hxT' : x ∉ T'.vertexSet)
    (hyB : y ∈ T.flapVertexSet B)
    (hyx : G.Adj y x) :
    Exists fun B' : T'.Flap =>
      W ⊆ T'.flapVertexSet B' ∧
        T.flapSizeProfileWith B < T'.flapSizeProfileWith B' := by
  obtain ⟨B', hB_subset⟩ :=
    T.exists_flap_containing_connected_set_of_subtriad
      (T' := T') hT'_subset (T.flapVertexSet_connected B)
      (T.flapVertexSet_subset_complement B)
  refine ⟨B', Set.Subset.trans hW hB_subset, ?_⟩
  exact T.flapSizeProfileWith_lt_of_adj_removed_vertex
    (T' := T') (B := B) (B' := B') hB_subset hxT hxT' hyB hyx

theorem Triad.exists_flap_profile_larger_of_subtriad_omits_flap_boundary_vertex
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T T' : Triad G feet}
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet)
    {x : V}
    (hx_boundary :
      x ∈ relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet)
    (hxT' : x ∉ T'.vertexSet) :
    Exists fun B' : T'.Flap =>
      W ⊆ T'.flapVertexSet B' ∧
        T.flapSizeProfileWith B < T'.flapSizeProfileWith B' := by
  rcases hx_boundary with ⟨hxT, y, hyB, hyx⟩
  exact T.exists_flap_profile_larger_of_subtriad_removed_adjacent_to_flap
    (T' := T') hW hT'_subset hxT hxT' hyB hyx

theorem Triad.exists_flap_profile_larger_of_subtriad_union_omits_flap_boundary_vertex
    [Fintype V]
    {feet : Fin 3 -> V}
    {W X : Set V}
    {T T' : Triad G feet}
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ X)
    (hX_disjoint_B : Disjoint X (T.flapVertexSet B))
    {x : V}
    (hx_boundary :
      x ∈ relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet)
    (hxT' : x ∉ T'.vertexSet) :
    Exists fun B' : T'.Flap =>
      W ⊆ T'.flapVertexSet B' ∧
        T.flapSizeProfileWith B < T'.flapSizeProfileWith B' := by
  have hB_subset_T' :
      T.flapVertexSet B ⊆ T'.vertexSetᶜ := by
    intro y hyB hyT'
    rcases hT'_subset hyT' with hyT | hyX
    · exact (T.flapVertexSet_subset_complement B hyB) hyT
    · exact Set.disjoint_left.mp hX_disjoint_B hyX hyB
  obtain ⟨B', hB_subset⟩ :=
    T'.exists_flap_containing_connected_set
      (T.flapVertexSet_connected B) hB_subset_T'
  refine ⟨B', Set.Subset.trans hW hB_subset, ?_⟩
  rcases hx_boundary with ⟨hxT, y, hyB, hyx⟩
  exact T.flapSizeProfileWith_lt_of_adj_removed_vertex
    (T' := T') (B := B) (B' := B') hB_subset hxT hxT' hyB hyx

theorem Triad.exists_flap_ncard_larger_of_subtriad_union_omits_flap_boundary_vertex
    [Fintype V]
    {feet : Fin 3 -> V}
    {W X : Set V}
    {T T' : Triad G feet}
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ X)
    (hX_disjoint_B : Disjoint X (T.flapVertexSet B))
    {x : V}
    (hx_boundary :
      x ∈ relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet)
    (hxT' : x ∉ T'.vertexSet) :
    Exists fun B' : T'.Flap =>
      W ⊆ T'.flapVertexSet B' ∧
        (T.flapVertexSet B).ncard < (T'.flapVertexSet B').ncard := by
  have hB_subset_T' :
      T.flapVertexSet B ⊆ T'.vertexSetᶜ := by
    intro y hyB hyT'
    rcases hT'_subset hyT' with hyT | hyX
    · exact (T.flapVertexSet_subset_complement B hyB) hyT
    · exact Set.disjoint_left.mp hX_disjoint_B hyX hyB
  obtain ⟨B', hB_subset⟩ :=
    T'.exists_flap_containing_connected_set
      (T.flapVertexSet_connected B) hB_subset_T'
  refine ⟨B', Set.Subset.trans hW hB_subset, ?_⟩
  rcases hx_boundary with ⟨hxT, y, hyB, hyx⟩
  exact Set.ncard_lt_ncard
    (Triad.flapVertexSet_ssubset_of_adj_removed_vertex
      (G := G) (T := T) (T' := T') (B := B) (B' := B')
      hB_subset hxT hxT' hyB hyx)

theorem Triad.lean_of_profile_maximal_of_strict_subtriads_delete_adjacent_to_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hmax :
      forall (T' : Triad G feet) (B' : T'.Flap),
        W ⊆ T'.flapVertexSet B' ->
          T'.flapSizeProfileWith B' <= T.flapSizeProfileWith B)
    (hstrict_adjacent :
      forall T' : Triad G feet,
        T'.vertexSet ⊂ T.vertexSet ->
          Exists fun x : V =>
            x ∈ T.vertexSet ∧ x ∉ T'.vertexSet ∧
              Exists fun y : V => y ∈ T.flapVertexSet B ∧ G.Adj y x) :
    T.Lean := by
  refine T.lean_of_profile_maximal_of_strict_subtriad_profile_larger hmax ?_
  intro T' hstrict
  obtain ⟨x, hxT, hxT', y, hyB, hyx⟩ := hstrict_adjacent T' hstrict
  exact T.exists_flap_profile_larger_of_subtriad_removed_adjacent_to_flap
    (T' := T') hW hstrict.1 hxT hxT' hyB hyx

theorem Triad.flap_boundary_subset_subtriad_of_profile_maximal
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T T' : Triad G feet}
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B) :
    relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆ T'.vertexSet := by
  intro x hx_boundary
  by_contra hxT'
  obtain ⟨B', hW', hlt⟩ :=
    T.exists_flap_profile_larger_of_subtriad_omits_flap_boundary_vertex
      (T' := T') hW hT'_subset hx_boundary hxT'
  exact (not_lt_of_ge (hmax T' B' hW')) hlt

theorem RST31FlapChoiceIndex.exists_triad_flap_profile_maximal_with_boundary_persistence
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hnonempty :
      Exists fun T : Triad G feet =>
        Exists fun B : T.Flap => W ⊆ T.flapVertexSet B) :
    Exists fun T : Triad G feet =>
      Exists fun B : T.Flap =>
        T.AvoidsSet W ∧
          W ⊆ T.flapVertexSet B ∧
            (forall (U : Triad G feet) (C : U.Flap),
              W ⊆ U.flapVertexSet C ->
                U.flapSizeProfileWith C <= T.flapSizeProfileWith B) ∧
              forall T' : Triad G feet,
                T'.vertexSet ⊆ T.vertexSet ->
                  relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
                    T'.vertexSet := by
  obtain ⟨T, B, havoid, hW, hmax⟩ :=
    RST31FlapChoiceIndex.exists_triad_flap_profile_maximal
      (G := G) hnonempty
  refine ⟨T, B, havoid, hW, hmax, ?_⟩
  intro T' hT'_subset
  exact T.flap_boundary_subset_subtriad_of_profile_maximal
    (T' := T') hW hT'_subset hmax

theorem RST31FlapChoiceIndex.exists_triad_flap_profile_maximal_minimal_with_boundary_persistence
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hnonempty :
      Exists fun T : Triad G feet =>
        Exists fun B : T.Flap => W ⊆ T.flapVertexSet B) :
    Exists fun T : Triad G feet =>
      Exists fun B : T.Flap =>
        T.AvoidsSet W ∧
          W ⊆ T.flapVertexSet B ∧
            (forall (U : Triad G feet) (C : U.Flap),
              W ⊆ U.flapVertexSet C ->
                U.flapSizeProfileWith C <= T.flapSizeProfileWith B) ∧
              (forall (U : Triad G feet) (C : U.Flap),
                W ⊆ U.flapVertexSet C ->
                  U.flapSizeProfileWith C = T.flapSizeProfileWith B ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ∧
                forall T' : Triad G feet,
                  T'.vertexSet ⊆ T.vertexSet ->
                    relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
                      T'.vertexSet := by
  obtain ⟨T, B, havoid, hW, hmax, hmin⟩ :=
    RST31FlapChoiceIndex.exists_triad_flap_profile_maximal_minimal
      (G := G) hnonempty
  refine ⟨T, B, havoid, hW, hmax, hmin, ?_⟩
  intro T' hT'_subset
  exact T.flap_boundary_subset_subtriad_of_profile_maximal
    (T' := T') hW hT'_subset hmax

theorem RST31FlapChoiceIndex.exists_triad_flap_profile_maximal_minimal_with_boundary_persistence_of_vertex
    [Fintype V]
    {feet : Fin 3 -> V}
    (T₀ : Triad G feet)
    {root : V}
    (hroot : root ∉ T₀.vertexSet) :
    Exists fun T : Triad G feet =>
      Exists fun B : T.Flap =>
        T.AvoidsSet ({root} : Set V) ∧
          root ∈ T.flapVertexSet B ∧
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                U.flapSizeProfileWith C <= T.flapSizeProfileWith B) ∧
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  U.flapSizeProfileWith C = T.flapSizeProfileWith B ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ∧
                forall T' : Triad G feet,
                  T'.vertexSet ⊆ T.vertexSet ->
                    relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
                      T'.vertexSet := by
  obtain ⟨B₀, hrootB₀⟩ := T₀.exists_flap_containing_vertex_outside hroot
  have hsingle :
      ({root} : Set V) ⊆ T₀.flapVertexSet B₀ := by
    intro v hv
    have hvroot : v = root := by
      simpa using hv
    simpa [hvroot] using hrootB₀
  obtain ⟨T, B, havoid, hroot_subset, hmax, hmin, hboundary⟩ :=
    RST31FlapChoiceIndex.exists_triad_flap_profile_maximal_minimal_with_boundary_persistence
      (G := G) (feet := feet)
      (W := ({root} : Set V))
      ⟨T₀, B₀, hsingle⟩
  refine ⟨T, B, havoid, ?_, hmax, hmin, hboundary⟩
  exact hroot_subset (by simp)

end Schematic.Math.GraphTheory
