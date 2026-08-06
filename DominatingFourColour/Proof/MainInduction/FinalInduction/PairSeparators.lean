import DominatingFourColour.Proof.MainInduction.HypothesisAssembly
import DominatingFourColour.Proof.MainInduction.TripleSeparatorData

/-! Pair-separator analysis used by the final induction. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem colorable_of_pair_left_pair_nonclique_separation
    [Fintype V] [DecidableEq V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hvertex_minimal_pair :
      forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    (S : Separation G)
    (hS_proper : S.Proper)
    (hS_not_clique : Not (G.IsClique S.separator))
    (hS_left :
      (OrderedClique.pair v1 v2 edge).vertexSet ⊆ S.left)
    (hpair :
      Exists fun x : V =>
        Exists fun y : V =>
          x ≠ y ∧ S.separator = ({x, y} : Set V)) :
    G.Colorable 4 := by
  classical
  obtain ⟨x0, y0, hx0y0, hseparator0⟩ := hpair
  obtain ⟨x, y, hxy, hxy_set, hv1_ne_y, hv2_ne_x⟩ :=
    Separation.exists_oriented_pair_avoiding_ordered_pair
      (V := V) (v1 := v1) (v2 := v2)
      (x := x0) (y := y0) edge.ne hx0y0
  have hseparator : S.separator = ({x, y} : Set V) := by
    rw [hseparator0, ← hxy_set]
  have htwo_connected_pair : IsTwoConnected G :=
    two_connected_of_not_colorable_of_delete_vertex_colorable
      (G := G) hnot_four_colorable hvertex_minimal_pair
  have hv1_S_left : v1 ∈ S.left :=
    hS_left (by simp [OrderedClique.vertexSet])
  have hv2_S_left : v2 ∈ S.left :=
    hS_left (by simp [OrderedClique.vertexSet])
  rcases hS_proper.2 with ⟨b, hb_right, hb_not_left⟩
  have hb_right_only : b ∈ S.right \ S.left := ⟨hb_right, hb_not_left⟩
  have hx_left : x ∈ S.left := by
    have hx_sep : x ∈ S.separator := by
      rw [hseparator]
      simp
    exact hx_sep.1
  have hy_left : y ∈ S.left := by
    have hy_sep : y ∈ S.separator := by
      rw [hseparator]
      simp
    exact hy_sep.1
  have hb_ne_y : b ≠ y := by
    intro hby
    exact hb_not_left (by simpa [hby] using hy_left)
  have hb_ne_x : b ≠ x := by
    intro hbx
    exact hb_not_left (by simpa [hbx] using hx_left)
  obtain ⟨qx, hqx_path, hqx_left, hqx_avoid_y⟩ :=
    S.exists_left_path_to_other_separator_of_two_connected_pair
      htwo_connected_pair hseparator hv1_S_left hv1_ne_y hb_right_only hb_ne_y
  have hseparator_yx : S.separator = ({y, x} : Set V) := by
    rw [hseparator]
    ext z
    simp [or_comm]
  obtain ⟨qy, hqy_path, hqy_left, _hqy_avoid_x⟩ :=
    S.exists_left_path_to_other_separator_of_two_connected_pair
      htwo_connected_pair hseparator_yx hv2_S_left hv2_ne_x hb_right_only hb_ne_x
  obtain
    ⟨H1, hH1_connected, hv1_H1, hx_H1,
      hv2_H1_or_y, hy_not_H1, hH1_left, hH1_adj_y⟩ :=
    exists_connected_subgraph_avoiding_endpoint_adjacent_to_endpoint
      (G := G) (A := S.left) edge hv1_ne_y qx hqx_left hqx_avoid_y
      qy hqy_path hqy_left
  obtain ⟨Lq, _himage, hfirst, hno_Lq⟩ :=
    exists_collapse_pair_image_no_compatible_model_of_first_mem
      (G := G) edge H1 hH1_connected hv1_H1 hno_model_pair
  let C : GraphContraction G :=
    GraphContraction.collapseSubgraph G H1 hH1_connected
  have hcard_C_lt :
      Fintype.card C.Target < Fintype.card V := by
    by_cases hx_ne_v1 : x ≠ v1
    · exact
        GraphContraction.collapseSubgraph_target_card_lt
          G H1 hH1_connected hv1_H1 hx_H1 hx_ne_v1.symm
    · have hx_eq_v1 : x = v1 := not_not.mp hx_ne_v1
      have hv2_H1 : v2 ∈ H1.verts := by
        rcases hv2_H1_or_y with hv2_y | hv2_H1
        · have hxy_edge : G.Adj x y := by
            simpa [hx_eq_v1, ← hv2_y] using edge
          have hseparator_clique :
              G.IsClique S.separator := by
            intro a ha b hb hab_ne
            have ha_pair : a = x ∨ a = y := by
              have : a ∈ ({x, y} : Set V) := by
                simpa [hseparator] using ha
              simpa using this
            have hb_pair : b = x ∨ b = y := by
              have : b ∈ ({x, y} : Set V) := by
                simpa [hseparator] using hb
              simpa using this
            rcases ha_pair with ha_x | ha_y <;> rcases hb_pair with hb_x | hb_y
            · exact False.elim (hab_ne (ha_x.trans hb_x.symm))
            · simpa [ha_x, hb_y] using hxy_edge
            · simpa [ha_y, hb_x] using hxy_edge.symm
            · exact False.elim (hab_ne (ha_y.trans hb_y.symm))
          exact False.elim (hS_not_clique hseparator_clique)
        · exact hv2_H1
      exact
        GraphContraction.collapseSubgraph_target_card_lt
          G H1 hH1_connected hv1_H1 hv2_H1 edge.ne
  have hright_intersection :
      forall r : V, r ∈ S.right -> r ∈ H1.verts -> r = x := by
    intro r hr_right hr_H1
    have hr_left : r ∈ S.left := hH1_left hr_H1
    have hr_sep : r ∈ S.separator := ⟨hr_left, hr_right⟩
    have hr_pair : r = x ∨ r = y := by
      have : r ∈ ({x, y} : Set V) := by
        simpa [hseparator] using hr_sep
      simpa using this
    rcases hr_pair with hr_x | hr_y
    · exact hr_x
    · exact False.elim (hy_not_H1 (by simpa [hr_y] using hr_H1))
  have hleft_colorable : (G.induce S.left).Colorable 4 :=
    left_induce_colorable_of_smaller_induction_global_no_model
      (G := G) hIH S hS_proper hno_model_pair
  exact
    colorable_of_pair_separation_two_pair_collapses
      (G := G) hIH S hleft_colorable hxy hseparator H1 hH1_connected
      hx_H1 hy_not_H1 hright_intersection hH1_adj_y
      hcard_C_lt Lq hfirst hno_Lq

theorem three_connected_of_pair_induction_hypotheses
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hvertex_minimal_pair :
      forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4) :
    IsThreeConnected G := by
  classical
  have hconnected_pair : G.Connected :=
    connected_of_not_colorable_of_delete_vertex_colorable
      (G := G) hnot_four_colorable hvertex_minimal_pair
  have hcard : 3 < Nat.card V := by
    rw [Nat.card_eq_fintype_card]
    have hgt := card_gt_four_of_not_colorable_four (G := G) hnot_four_colorable
    omega
  refine three_connected_of_no_proper_separation_orderAtMost_two
    (G := G) hcard ?_
  intro S hproper horder_two
  by_cases horder_one : S.OrderAtMost 1
  · exact hnot_four_colorable
      (colorable_of_orderAtMost_one_separation_of_connected_of_delete_vertex_colorable
        (G := G) hconnected_pair hvertex_minimal_pair S hproper horder_one)
  · by_cases hseparator_clique : G.IsClique S.separator
    · exact hnot_four_colorable
        (colorable_of_separation_global_no_model_and_right_color_class_quotients_colorable
          (G := G) (L := .pair v1 v2 edge) hIH S hproper hno_model_pair
          (by
            intro left_coloring
            exact
              right_color_class_quotient_colorable_of_global_no_model_of_separator_clique
                (G := G) hIH S hproper hseparator_clique hno_model_pair
                left_coloring))
    · have hpair :
          Exists fun x : V =>
            Exists fun y : V =>
              x ≠ y ∧ S.separator = ({x, y} : Set V) :=
        S.exists_separator_pair_of_orderAtMost_two_not_orderAtMost_one
          horder_two horder_one
      rcases (OrderedClique.pair v1 v2 edge).vertexSet_subset_left_or_subset_right S with
        hleft | hright
      · exact hnot_four_colorable
          (colorable_of_pair_left_pair_nonclique_separation
            (G := G) hIH hnot_four_colorable edge hno_model_pair
            hvertex_minimal_pair S hproper hseparator_clique hleft hpair)
      · have hproper_symm : S.symm.Proper :=
          (S.proper_symm).mpr hproper
        have hseparator_clique_symm :
            Not (G.IsClique S.symm.separator) := by
          intro hclique
          exact hseparator_clique (by
            rwa [S.separator_symm] at hclique)
        have hpair_symm :
            Exists fun x : V =>
              Exists fun y : V =>
                x ≠ y ∧ S.symm.separator = ({x, y} : Set V) := by
          rcases hpair with ⟨x, y, hxy, hseparator⟩
          exact ⟨x, y, hxy, by
            rw [S.separator_symm]
            exact hseparator⟩
        have hleft_symm :
            (OrderedClique.pair v1 v2 edge).vertexSet ⊆ S.symm.left := by
          simpa [Separation.symm] using hright
        exact hnot_four_colorable
          (colorable_of_pair_left_pair_nonclique_separation
            (G := G) hIH hnot_four_colorable edge hno_model_pair
            hvertex_minimal_pair S.symm hproper_symm hseparator_clique_symm
            hleft_symm hpair_symm)

private theorem endpoint_adjacent_core_of_minimal_pair_left_nonclique
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hnot_four_colorable : Not (G.Colorable 4))
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (hvertex_minimal_pair :
      forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    (Asep : Separation G)
    (hthree_connected : IsThreeConnected G)
    (hAsep_left :
      (OrderedClique.pair v1 v2 edge).vertexSet ⊆ Asep.left)
    (hAsep_minimal :
      forall T : Separation G,
        PairLeftSmallNoncliqueSeparation G edge T ->
          Asep.left.ncard <= T.left.ncard)
    (core : G.Subgraph)
    (pathSupport : Set V)
    (hpath_core_disjoint : Disjoint pathSupport core.verts)
    (hv1_core : v1 ∈ core.verts)
    (e : V)
    (he_left : e ∈ Asep.left)
    (he_path : e ∈ pathSupport)
    (replacement :
      (forall h : V, h ∈ core.verts -> Not (G.Adj h e)) -> Separation G)
    (hreplacement_proper :
      forall hno, (replacement hno).Proper)
    (hreplacement_order :
      forall hno, (replacement hno).OrderAtMost 3)
    (hreplacement_left :
      forall hno, (replacement hno).left = Asep.left \ {e}) :
    Exists fun h : V => h ∈ core.verts ∧ G.Adj h e := by
  classical
  by_contra hnone
  have hno : forall h : V, h ∈ core.verts -> Not (G.Adj h e) := by
    intro h hh hadj
    exact hnone ⟨h, hh, hadj⟩
  let T := replacement hno
  have hT_proper : T.Proper := by
    simpa [T] using hreplacement_proper hno
  have hT_order : T.OrderAtMost 3 := by
    simpa [T] using hreplacement_order hno
  have hT_not_order_one : Not (T.OrderAtMost 1) := by
    intro hT_one
    exact isThreeConnected_no_proper_separation_orderAtMost_two
      (G := G) hthree_connected T hT_proper
      (T.orderAtMost_mono hT_one (by omega))
  have hT_left :
      (OrderedClique.pair v1 v2 edge).vertexSet ⊆ T.left := by
    intro a ha
    have ha_pair : a = v1 ∨ a = v2 := by
      change a ∈ ({v1, v2} : Set V) at ha
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
    rw [show T.left = Asep.left \ {e} by
      simpa [T] using hreplacement_left hno]
    rcases ha_pair with ha_v1 | ha_v2
    · exact ⟨by simpa [ha_v1] using
          hAsep_left (by simp [OrderedClique.vertexSet]), by
        intro ha_e
        have hae : a = e := by simpa [Set.mem_singleton_iff] using ha_e
        have hv1e : v1 = e := ha_v1.symm.trans hae
        exact Set.disjoint_left.mp hpath_core_disjoint he_path
          (by simpa [hv1e] using hv1_core)⟩
    · exact ⟨by simpa [ha_v2] using
          hAsep_left (by simp [OrderedClique.vertexSet]), by
        intro ha_e
        have hae : a = e := by simpa [Set.mem_singleton_iff] using ha_e
        have hv2e : v2 = e := ha_v2.symm.trans hae
        exact hno v1 hv1_core (by simpa [hv2e] using edge)⟩
  by_cases hT_clique : G.IsClique T.separator
  · exact hnot_four_colorable
      (colorable_of_proper_clique_separation_of_delete_vertex_colorable
        (G := G) hvertex_minimal_pair T hT_proper hT_clique)
  · have hT_pair : PairLeftSmallNoncliqueSeparation G edge T :=
      ⟨hT_proper, hT_order, hT_not_order_one, hT_clique, hT_left⟩
    have hminimal := hAsep_minimal T hT_pair
    have hT_smaller : T.left.ncard < Asep.left.ncard := by
      rw [show T.left = Asep.left \ {e} by
        simpa [T] using hreplacement_left hno]
      exact Set.ncard_diff_singleton_lt_of_mem he_left
    omega

theorem FoldedDuplicateLinkageDataInSet.endpointY_adjacent_core_of_minimal_pair_left_nonclique
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hnot_four_colorable : Not (G.Colorable 4))
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (hvertex_minimal_pair :
      forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    (Asep : Separation G)
    (hthree_connected : IsThreeConnected G)
    (hAsep_proper : Asep.Proper)
    (hAsep_left_only_large : 2 <= (Asep.left \ Asep.right).ncard)
    (hAsep_left :
      (OrderedClique.pair v1 v2 edge).vertexSet ⊆ Asep.left)
    (hAsep_minimal :
      forall T : Separation G,
        PairLeftSmallNoncliqueSeparation G edge T ->
          Asep.left.ncard <= T.left.ncard)
    {root x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G Asep.left root v1 x y z)
    (hseparator : Asep.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ Asep.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support) :
    Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h y := by
  apply endpoint_adjacent_core_of_minimal_pair_left_nonclique
    hnot_four_colorable edge hvertex_minimal_pair Asep hthree_connected
    hAsep_left hAsep_minimal
    F.pathXComponentCore {v : V | v ∈ F.toLinkage.pathYZ.support}
    F.pathYZ_disjoint_pathXComponentCore F.v1_mem_pathXComponentCore y
    (Asep.triple_vertices_mem_left hseparator).2.1
    F.toLinkage.pathYZ.start_mem_support
    (fun hno => F.endpointYReplacementSeparation
      hseparator hyz hpathYZ_chordless hcover hno)
  · intro hno
    exact F.endpointYReplacementSeparation_proper
      hseparator hyz hpathYZ_chordless hcover hno
      hAsep_proper hAsep_left_only_large
  · intro hno
    exact F.endpointYReplacementSeparation_orderAtMost_three
      hseparator hyz hpathYZ_chordless hcover hno
  · intro hno
    rfl

theorem FoldedDuplicateLinkageDataInSet.endpointZ_adjacent_core_of_minimal_pair_left_nonclique
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hnot_four_colorable : Not (G.Colorable 4))
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (hvertex_minimal_pair :
      forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    (Asep : Separation G)
    (hthree_connected : IsThreeConnected G)
    (hAsep_proper : Asep.Proper)
    (hAsep_left_only_large : 2 <= (Asep.left \ Asep.right).ncard)
    (hAsep_left :
      (OrderedClique.pair v1 v2 edge).vertexSet ⊆ Asep.left)
    (hAsep_minimal :
      forall T : Separation G,
        PairLeftSmallNoncliqueSeparation G edge T ->
          Asep.left.ncard <= T.left.ncard)
    {root x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G Asep.left root v1 x y z)
    (hseparator : Asep.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ Asep.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support) :
    Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h z := by
  apply endpoint_adjacent_core_of_minimal_pair_left_nonclique
    hnot_four_colorable edge hvertex_minimal_pair Asep hthree_connected
    hAsep_left hAsep_minimal
    F.pathXComponentCore {v : V | v ∈ F.toLinkage.pathYZ.support}
    F.pathYZ_disjoint_pathXComponentCore F.v1_mem_pathXComponentCore z
    (Asep.triple_vertices_mem_left hseparator).2.2
    F.toLinkage.pathYZ.end_mem_support
    (fun hno => F.endpointZReplacementSeparation
      hseparator hyz hpathYZ_chordless hcover hno)
  · intro hno
    exact F.endpointZReplacementSeparation_proper
      hseparator hyz hpathYZ_chordless hcover hno
      hAsep_proper hAsep_left_only_large
  · intro hno
    exact F.endpointZReplacementSeparation_orderAtMost_three
      hseparator hyz hpathYZ_chordless hcover hno
  · intro hno
    rfl

end Schematic.Math.GraphTheory
