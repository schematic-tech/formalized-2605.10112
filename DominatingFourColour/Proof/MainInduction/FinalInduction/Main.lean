import DominatingFourColour.Proof.MainInduction.FinalInduction.TripleCollapse

/-! The final strong induction proving the article's main hypothesis. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem main_induction_hypothesis
    [Fintype V]
    (G : SimpleGraph V)
    (L : OrderedClique G) :
    G.Colorable 4 ∨ CompatibleDominatingK5Model L := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n IH =>
      letI : DecidableEq V := Classical.decEq V
      letI : DecidableRel G.Adj := Classical.decRel (fun x y : V => G.Adj x y)
      have hIH :
          forall {W : Type u} [Fintype W],
            forall H : SimpleGraph W,
              Fintype.card W < Fintype.card V ->
                forall Lw : OrderedClique H,
                  H.Colorable 4 ∨ CompatibleDominatingK5Model Lw := by
        intro W _ H hcard_lt Lw
        letI : DecidableEq W := Classical.decEq W
        letI : DecidableRel H.Adj := Classical.decRel (fun x y : W => H.Adj x y)
        exact IH (Fintype.card W) (by simpa [hn] using hcard_lt)
          (V := W) H Lw rfl
      by_cases h_complete : forall u v : V, u ≠ v -> G.Adj u v
      · exact main_induction_hypothesis_of_complete G L h_complete
      · by_cases hcolor : G.Colorable 4
        · exact Or.inl hcolor
        · by_cases hmodel : CompatibleDominatingK5Model L
          · exact Or.inr hmodel
          · have _h_large : 5 < Fintype.card V :=
              card_gt_five_of_not_colorable_four_of_not_complete
                (G := G) hcolor h_complete
            exact main_induction_hypothesis_of_smaller_induction_and_pair_small_separation_colorings
              G L hIH (by
                intro Lpair _hinit_pair _hlen_pair hno_model_pair
                  S hproper horder
                have _h_large' : 5 < Fintype.card V := _h_large
                have _h_no_model' : Not (CompatibleDominatingK5Model Lpair) := hno_model_pair
                have hvertex_minimal_pair :
                    forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4 :=
                  delete_vertex_colorable_of_smaller_induction
                    (G := G) hIH hno_model_pair
                have hconnected_pair : G.Connected :=
                  connected_of_not_colorable_of_delete_vertex_colorable
                    (G := G) hcolor hvertex_minimal_pair
                by_cases horder_one : S.OrderAtMost 1
                · exact
                    colorable_of_orderAtMost_one_separation_of_connected_of_delete_vertex_colorable
                      (G := G) hconnected_pair hvertex_minimal_pair S hproper horder_one
                · by_cases hseparator_clique_global : G.IsClique S.separator
                  · exact
                      colorable_of_separation_global_no_model_and_right_color_class_quotients_colorable
                        (G := G) hIH S hproper hno_model_pair
                        (by
                          intro left_coloring
                          exact
                            right_color_class_quotient_colorable_of_global_no_model_of_separator_clique
                              (G := G) hIH S hproper hseparator_clique_global
                              hno_model_pair left_coloring)
                  · by_cases h_nil_clique :
                      (Exists fun hL : Lpair = (OrderedClique.nil : OrderedClique G) =>
                        G.IsClique S.separator)
                    · rcases h_nil_clique with ⟨rfl, hseparator_clique⟩
                      exact False.elim (hseparator_clique_global hseparator_clique)
                    · by_cases h_clique_contains_ordered :
                      Exists fun hseparator_clique : G.IsClique S.separator =>
                        Lpair.vertexSet ⊆ S.separator
                      · rcases h_clique_contains_ordered with
                        ⟨hseparator_clique, _hL_separator⟩
                        exact False.elim (hseparator_clique_global hseparator_clique)
                      · have _h_nil_separator_clique_obstruction :
                          Lpair = (OrderedClique.nil : OrderedClique G) ->
                            Not (G.IsClique S.separator) := by
                          intro hL hseparator_clique
                          exact h_nil_clique ⟨hL, hseparator_clique⟩
                        have _h_clique_separator_does_not_contain_ordered :
                          forall hseparator_clique : G.IsClique S.separator,
                            Not (Lpair.vertexSet ⊆ S.separator) := by
                          intro hseparator_clique hL_separator
                          exact h_clique_contains_ordered
                            ⟨hseparator_clique, hL_separator⟩
                        have _h_ordered_clique_side :
                          Lpair.vertexSet ⊆ S.left ∨ Lpair.vertexSet ⊆ S.right :=
                          Lpair.vertexSet_subset_left_or_subset_right S
                        have _h_not_both_sides_under_clique_separator :
                          forall hseparator_clique : G.IsClique S.separator,
                            Not (Lpair.vertexSet ⊆ S.left ∧ Lpair.vertexSet ⊆ S.right) := by
                          intro hseparator_clique hboth
                          exact
                            (_h_clique_separator_does_not_contain_ordered hseparator_clique)
                              (by
                                intro v hv
                                exact ⟨hboth.1 hv, hboth.2 hv⟩)
                        have _h_clique_separator_ordered_right_obstruction :
                          forall hseparator_clique : G.IsClique S.separator,
                            Lpair.vertexSet ⊆ S.right -> False := by
                          intro hseparator_clique hright
                          exact hcolor
                            (colorable_of_separation_global_no_model_and_right_color_class_quotients_colorable
                              (G := G) (L := Lpair) hIH S hproper hno_model_pair
                              (by
                                intro left_coloring
                                exact
                                  right_color_class_quotient_colorable_of_global_no_model_of_separator_clique
                                    (G := G) hIH S hproper hseparator_clique
                                    hno_model_pair left_coloring))
                        have _h_clique_separator_forces_ordered_left :
                          forall hseparator_clique : G.IsClique S.separator,
                            Lpair.vertexSet ⊆ S.left := by
                          intro hseparator_clique
                          rcases _h_ordered_clique_side with hleft | hright
                          · exact hleft
                          · exact False.elim
                              (_h_clique_separator_ordered_right_obstruction
                                hseparator_clique hright)
                        cases Lpair with
                        | nil =>
                            simp [OrderedClique.length] at _hlen_pair
                        | single v =>
                            simp [OrderedClique.length] at _hlen_pair
                        | pair v1 v2 edge =>
                            have hleft_nonclique_small_separation_colorable :
                                forall T : Separation G,
                                  T.Proper -> T.OrderAtMost 3 ->
                                    Not (T.OrderAtMost 1) ->
                                      Not (G.IsClique T.separator) ->
                                        (OrderedClique.pair v1 v2 edge).vertexSet ⊆ T.left ->
                                          G.Colorable 4 := by
                              intro T hTproper hTorder hTnot_order_one hTnot_clique hTleft
                              have hTsep_ncard_ge_two : 2 <= T.separator.ncard :=
                                T.separator_ncard_ge_two_of_not_orderAtMost_one hTnot_order_one
                              have hTsep_ncard_le_three : T.separator.ncard <= 3 :=
                                T.separator_ncard_le_of_orderAtMost hTorder
                              have hTpack :
                                  PairLeftSmallNoncliqueSeparation G edge T :=
                                ⟨hTproper, hTorder, hTnot_order_one, hTnot_clique, hTleft⟩
                              obtain ⟨Asep, hAsep, hAsep_minimal⟩ :=
                                exists_minimal_pair_left_small_nonclique_separation
                                  (G := G) (edge := edge) hTpack
                              have hAsep_proper : Asep.Proper := hAsep.1
                              have hAsep_order : Asep.OrderAtMost 3 := hAsep.2.1
                              have hAsep_not_order_one : Not (Asep.OrderAtMost 1) := hAsep.2.2.1
                              have hAsep_not_clique : Not (G.IsClique Asep.separator) := hAsep.2.2.2.1
                              have hAsep_left :
                                  (OrderedClique.pair v1 v2 edge).vertexSet ⊆ Asep.left :=
                                hAsep.2.2.2.2
                              have hAsep_ncard_ge_two : 2 <= Asep.separator.ncard :=
                                Asep.separator_ncard_ge_two_of_not_orderAtMost_one hAsep_not_order_one
                              have hAsep_ncard_le_three : Asep.separator.ncard <= 3 :=
                                Asep.separator_ncard_le_of_orderAtMost hAsep_order
                              have hAsep_order_two_or_three :
                                  Asep.OrderAtMost 2 ∨ Asep.separator.ncard = 3 := by
                                by_cases horder_two : Asep.OrderAtMost 2
                                · exact Or.inl horder_two
                                · have hge_three : 3 <= Asep.separator.ncard :=
                                    Asep.separator_ncard_ge_three_of_not_orderAtMost_two
                                      horder_two
                                  exact Or.inr (le_antisymm hAsep_ncard_le_three hge_three)
                              have hAsep_separator_pair_or_triple :
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      x ≠ y ∧ Asep.separator = ({x, y} : Set V)) ∨
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      Exists fun z : V =>
                                        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
                                          Asep.separator = ({x, y, z} : Set V)) := by
                                rcases hAsep_order_two_or_three with horder_two | hcard_three
                                · exact Or.inl
                                    (Asep.exists_separator_pair_of_orderAtMost_two_not_orderAtMost_one
                                      horder_two hAsep_not_order_one)
                                · have hnot_order_two : Not (Asep.OrderAtMost 2) := by
                                    intro horder_two
                                    have hle_two : Asep.separator.ncard <= 2 :=
                                      Asep.separator_ncard_le_of_orderAtMost horder_two
                                    omega
                                  exact Or.inr
                                    (Asep.exists_separator_triple_of_orderAtMost_three_not_orderAtMost_two
                                      hAsep_order hnot_order_two)
                              have hmin_degree_pair :
                                  forall v : V, 4 <= G.degree v :=
                                fun v =>
                                  degree_atLeast_four_of_not_colorable_four_of_delete_vertex_colorable
                                    (G := G) v hcolor (hvertex_minimal_pair v)
                              have htwo_connected_pair : IsTwoConnected G :=
                                two_connected_of_not_colorable_of_delete_vertex_colorable
                                  (G := G) hcolor hvertex_minimal_pair
                              have hAsep_left_only_large :
                                  2 <= (Asep.left \ Asep.right).ncard :=
                                Asep.left_only_ncard_ge_two_of_min_degree_four_orderAtMost_three
                                  hmin_degree_pair hAsep_proper hAsep_order
                              have hAsep_right_only_large :
                                  2 <= (Asep.right \ Asep.left).ncard :=
                                Asep.right_only_ncard_ge_two_of_min_degree_four_orderAtMost_three
                                  hmin_degree_pair hAsep_proper hAsep_order
                              have hv1_Asep_left : v1 ∈ Asep.left :=
                                hAsep_left (by simp [OrderedClique.vertexSet])
                              have hv2_Asep_left : v2 ∈ Asep.left :=
                                hAsep_left (by simp [OrderedClique.vertexSet])
                              have hAsep_pair_paths :
                                  forall x y : V,
                                    x ≠ y ->
                                      Asep.separator = ({x, y} : Set V) ->
                                        v1 ≠ y ->
                                          v2 ≠ x ->
                                            (Exists fun qx : G.Walk v1 x =>
                                              qx.IsPath ∧
                                                (forall z : V,
                                                  z ∈ qx.support -> z ∈ Asep.left) ∧
                                                  forall z : V,
                                                    z ∈ qx.support -> z ≠ y) ∧
                                            (Exists fun qy : G.Walk v2 y =>
                                              qy.IsPath ∧
                                                (forall z : V,
                                                  z ∈ qy.support -> z ∈ Asep.left) ∧
                                                  forall z : V,
                                                    z ∈ qy.support -> z ≠ x) := by
                                intro x y hxy hseparator hv1_ne_y hv2_ne_x
                                rcases hAsep_proper.2 with
                                  ⟨b, hb_right, hb_not_left⟩
                                have hb_right_only : b ∈ Asep.right \ Asep.left :=
                                  ⟨hb_right, hb_not_left⟩
                                have hx_left : x ∈ Asep.left := by
                                  have hx_sep : x ∈ Asep.separator := by
                                    rw [hseparator]
                                    simp
                                  exact hx_sep.1
                                have hy_left : y ∈ Asep.left := by
                                  have hy_sep : y ∈ Asep.separator := by
                                    rw [hseparator]
                                    simp
                                  exact hy_sep.1
                                have hb_ne_y : b ≠ y := by
                                  intro hby
                                  exact hb_not_left (by simpa [hby] using hy_left)
                                have hb_ne_x : b ≠ x := by
                                  intro hbx
                                  exact hb_not_left (by simpa [hbx] using hx_left)
                                obtain ⟨qx, hqx_path, hqx_left, hqx_avoid⟩ :=
                                  Asep.exists_left_path_to_other_separator_of_two_connected_pair
                                    htwo_connected_pair hseparator hv1_Asep_left
                                    hv1_ne_y hb_right_only hb_ne_y
                                have hseparator_yx :
                                    Asep.separator = ({y, x} : Set V) := by
                                  rw [hseparator]
                                  ext z
                                  simp [or_comm]
                                obtain ⟨qy, hqy_path, hqy_left, hqy_avoid⟩ :=
                                  Asep.exists_left_path_to_other_separator_of_two_connected_pair
                                    htwo_connected_pair hseparator_yx hv2_Asep_left
                                    hv2_ne_x hb_right_only hb_ne_x
                                exact ⟨⟨qx, hqx_path, hqx_left, hqx_avoid⟩,
                                  ⟨qy, hqy_path, hqy_left, hqy_avoid⟩⟩
                              have hAsep_pair_oriented_paths :
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      x ≠ y ∧ Asep.separator = ({x, y} : Set V) ∧
                                        v1 ≠ y ∧ v2 ≠ x ∧
                                          (Exists fun qx : G.Walk v1 x =>
                                            qx.IsPath ∧
                                              (forall z : V,
                                                z ∈ qx.support -> z ∈ Asep.left) ∧
                                                forall z : V,
                                                  z ∈ qx.support -> z ≠ y) ∧
                                          (Exists fun qy : G.Walk v2 y =>
                                            qy.IsPath ∧
                                              (forall z : V,
                                                z ∈ qy.support -> z ∈ Asep.left) ∧
                                                forall z : V,
                                                  z ∈ qy.support -> z ≠ x)) ∨
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      Exists fun z : V =>
                                        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
                                          Asep.separator = ({x, y, z} : Set V)) := by
                                rcases hAsep_separator_pair_or_triple with
                                  hpair | htriple
                                · rcases hpair with ⟨x, y, hxy, hseparator⟩
                                  obtain ⟨a, b, hab, hab_set, hv1_ne_b, hv2_ne_a⟩ :=
                                    Separation.exists_oriented_pair_avoiding_ordered_pair
                                      (V := V) (v1 := v1) (v2 := v2)
                                      (x := x) (y := y) edge.ne hxy
                                  have hseparator_ab :
                                      Asep.separator = ({a, b} : Set V) := by
                                    rw [hseparator, hab_set]
                                  have hpaths :=
                                    hAsep_pair_paths a b hab hseparator_ab
                                      hv1_ne_b hv2_ne_a
                                  exact Or.inl
                                    ⟨a, b, hab, hseparator_ab, hv1_ne_b,
                                      hv2_ne_a, hpaths.1, hpaths.2⟩
                                · exact Or.inr htriple
                              have hAsep_pair_H1_or_triple :
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      Exists fun H1 : G.Subgraph =>
                                        x ≠ y ∧
                                          Asep.separator = ({x, y} : Set V) ∧
                                            v1 ≠ y ∧ v2 ≠ x ∧
                                              H1.coe.Connected ∧
                                                v1 ∈ H1.verts ∧
                                                  x ∈ H1.verts ∧
                                                    (v2 = y ∨ v2 ∈ H1.verts) ∧
                                                      y ∉ H1.verts ∧
                                                        H1.verts ⊆ Asep.left ∧
                                                          Exists fun z : V =>
                                                            z ∈ H1.verts ∧
                                                              G.Adj z y) ∨
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      Exists fun z : V =>
                                        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
                                          Asep.separator = ({x, y, z} : Set V)) := by
                                rcases hAsep_pair_oriented_paths with
                                  hpair | htriple
                                · rcases hpair with
                                    ⟨x, y, hxy, hseparator, hv1_ne_y,
                                      hv2_ne_x, hqx, hqy⟩
                                  rcases hqx with
                                    ⟨qx, hqx_path, hqx_left, hqx_avoid_y⟩
                                  rcases hqy with
                                    ⟨qy, hqy_path, hqy_left, _hqy_avoid_x⟩
                                  obtain
                                    ⟨H1, hH1_connected, hv1_H1, hx_H1,
                                      hv2_H1_or_y, hy_not_H1, hH1_left,
                                      hH1_adj_y⟩ :=
                                    exists_connected_subgraph_avoiding_endpoint_adjacent_to_endpoint
                                      (G := G) (A := Asep.left) edge
                                      hv1_ne_y qx hqx_left hqx_avoid_y qy
                                      hqy_path hqy_left
                                  exact Or.inl
                                    ⟨x, y, H1, hxy, hseparator, hv1_ne_y,
                                      hv2_ne_x, hH1_connected, hv1_H1,
                                      hx_H1, hv2_H1_or_y, hy_not_H1,
                                      hH1_left, hH1_adj_y⟩
                                · exact Or.inr htriple
                              have hAsep_pair_H1_right_intersection_or_triple :
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      Exists fun H1 : G.Subgraph =>
                                        x ≠ y ∧
                                          Asep.separator = ({x, y} : Set V) ∧
                                            H1.coe.Connected ∧
                                              v1 ∈ H1.verts ∧
                                                x ∈ H1.verts ∧
                                                  (v2 = y ∨ v2 ∈ H1.verts) ∧
                                                    y ∉ H1.verts ∧
                                                      H1.verts ⊆ Asep.left ∧
                                                        (forall r : V,
                                                          r ∈ Asep.right ->
                                                            r ∈ H1.verts -> r = x)) ∨
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      Exists fun z : V =>
                                        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
                                          Asep.separator = ({x, y, z} : Set V)) := by
                                rcases hAsep_pair_H1_or_triple with
                                  hpair | htriple
                                · rcases hpair with
                                    ⟨x, y, H1, hxy, hseparator, _hv1_ne_y,
                                      _hv2_ne_x, hH1_connected, hv1_H1,
                                      hx_H1, hv2_H1_or_y, hy_not_H1,
                                      hH1_left, _hH1_adj_y⟩
                                  have hright_intersection :
                                      forall r : V,
                                        r ∈ Asep.right ->
                                          r ∈ H1.verts -> r = x := by
                                    intro r hr_right hr_H1
                                    have hr_left : r ∈ Asep.left :=
                                      hH1_left hr_H1
                                    have hr_sep : r ∈ Asep.separator :=
                                      ⟨hr_left, hr_right⟩
                                    have hr_pair : r = x ∨ r = y := by
                                      have : r ∈ ({x, y} : Set V) := by
                                        simpa [hseparator] using hr_sep
                                      simpa using this
                                    rcases hr_pair with hr_x | hr_y
                                    · exact hr_x
                                    · exact False.elim
                                        (hy_not_H1 (by simpa [hr_y] using hr_H1))
                                  exact Or.inl
                                    ⟨x, y, H1, hxy, hseparator,
                                      hH1_connected, hv1_H1, hx_H1,
                                      hv2_H1_or_y, hy_not_H1, hH1_left,
                                      hright_intersection⟩
                                · exact Or.inr htriple
                              have hAsep_pair_first_collapse_no_model_or_triple :
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      Exists fun H1 : G.Subgraph =>
                                        Exists fun hH1_connected : H1.coe.Connected =>
                                          Exists fun Lq :
                                            OrderedClique
                                              (GraphContraction.collapseSubgraph
                                                G H1 hH1_connected).graph =>
                                            x ≠ y ∧
                                              Asep.separator = ({x, y} : Set V) ∧
                                                v1 ≠ y ∧ v2 ≠ x ∧
                                                  v1 ∈ H1.verts ∧
                                                    x ∈ H1.verts ∧
                                                      (v2 = y ∨ v2 ∈ H1.verts) ∧
                                                        y ∉ H1.verts ∧
                                                          H1.verts ⊆ Asep.left ∧
                                                            (Exists fun z : V =>
                                                              z ∈ H1.verts ∧
                                                                G.Adj z y) ∧
                                                            OrderedCliqueContractionImage
                                                              (GraphContraction.collapseSubgraph
                                                                G H1 hH1_connected)
                                                              (.pair v1 v2 edge) Lq ∧
                                                              Lq.first? =
                                                                some
                                                                  (none :
                                                                    (GraphContraction.collapseSubgraph
                                                                      G H1 hH1_connected).Target) ∧
                                                                Not
                                                                  (CompatibleDominatingK5Model
                                                                    Lq)) ∨
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      Exists fun z : V =>
                                        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
                                          Asep.separator = ({x, y, z} : Set V)) := by
                                rcases hAsep_pair_H1_or_triple with
                                  hpair | htriple
                                · rcases hpair with
                                    ⟨x, y, H1, hxy, hseparator, hv1_ne_y,
                                      hv2_ne_x, hH1_connected, hv1_H1,
                                      hx_H1, hv2_H1_or_y, hy_not_H1,
                                      hH1_left, hH1_adj_y⟩
                                  obtain ⟨Lq, himage, hfirst, hno_Lq⟩ :=
                                    exists_collapse_pair_image_no_compatible_model_of_first_mem
                                      (G := G) edge H1 hH1_connected
                                      hv1_H1 hno_model_pair
                                  exact Or.inl
                                    ⟨x, y, H1, hH1_connected, Lq, hxy,
                                      hseparator, hv1_ne_y, hv2_ne_x,
                                      hv1_H1, hx_H1, hv2_H1_or_y,
                                      hy_not_H1, hH1_left, hH1_adj_y,
                                      himage, hfirst, hno_Lq⟩
                                · exact Or.inr htriple
                              have hAsep_pair_augmented_right_colorable_or_triple :
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      x ≠ y ∧
                                        Asep.separator = ({x, y} : Set V) ∧
                                          Asep.rightWithSeparatorClique.Colorable 4) ∨
                                  (Exists fun x : V =>
                                    Exists fun y : V =>
                                      Exists fun z : V =>
                                        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
                                          Asep.separator = ({x, y, z} : Set V)) := by
                                rcases hAsep_pair_first_collapse_no_model_or_triple with
                                  hpair | htriple
                                · rcases hpair with
                                    ⟨x, y, H1, hH1_connected, Lq, hxy,
                                      hseparator, hv1_ne_y, hv2_ne_x,
                                      hv1_H1, hx_H1, hv2_H1_or_y,
                                      hy_not_H1, hH1_left, hH1_adj_y,
                                      _himage, _hfirst, hno_Lq⟩
                                  let C : GraphContraction G :=
                                    GraphContraction.collapseSubgraph
                                      G H1 hH1_connected
                                  have hcard_lt :
                                      Fintype.card C.Target < Fintype.card V := by
                                    by_cases hx_ne_v1 : x ≠ v1
                                    · exact
                                        GraphContraction.collapseSubgraph_target_card_lt
                                          G H1 hH1_connected hv1_H1 hx_H1
                                          hx_ne_v1.symm
                                    · have hx_eq_v1 : x = v1 := not_not.mp hx_ne_v1
                                      have hv2_H1 : v2 ∈ H1.verts := by
                                        rcases hv2_H1_or_y with hv2_y | hv2_H1
                                        · have hxy_edge : G.Adj x y := by
                                            simpa [hx_eq_v1, ← hv2_y] using edge
                                          have hseparator_clique :
                                              G.IsClique Asep.separator := by
                                            intro a ha b hb hab_ne
                                            have ha_pair : a = x ∨ a = y := by
                                              have : a ∈ ({x, y} : Set V) := by
                                                simpa [hseparator] using ha
                                              simpa using this
                                            have hb_pair : b = x ∨ b = y := by
                                              have : b ∈ ({x, y} : Set V) := by
                                                simpa [hseparator] using hb
                                              simpa using this
                                            rcases ha_pair with ha_x | ha_y <;>
                                              rcases hb_pair with hb_x | hb_y
                                            · exact False.elim
                                                (hab_ne (ha_x.trans hb_x.symm))
                                            · simpa [ha_x, hb_y] using hxy_edge
                                            · simpa [ha_y, hb_x] using hxy_edge.symm
                                            · exact False.elim
                                                (hab_ne (ha_y.trans hb_y.symm))
                                          exact False.elim
                                            (hAsep_not_clique hseparator_clique)
                                        · exact hv2_H1
                                      exact
                                        GraphContraction.collapseSubgraph_target_card_lt
                                          G H1 hH1_connected hv1_H1 hv2_H1
                                          edge.ne
                                  have hcollapse_colorable : C.graph.Colorable 4 := by
                                    rcases hIH C.graph hcard_lt Lq with
                                      hcolor_C | hmodel_C
                                    · exact hcolor_C
                                    · exact False.elim (hno_Lq hmodel_C)
                                  have hright_intersection :
                                      forall r : V,
                                        r ∈ Asep.right ->
                                          r ∈ H1.verts -> r = x := by
                                    intro r hr_right hr_H1
                                    have hr_left : r ∈ Asep.left := hH1_left hr_H1
                                    have hr_sep : r ∈ Asep.separator :=
                                      ⟨hr_left, hr_right⟩
                                    have hr_pair : r = x ∨ r = y := by
                                      have : r ∈ ({x, y} : Set V) := by
                                        simpa [hseparator] using hr_sep
                                      simpa using this
                                    rcases hr_pair with hr_x | hr_y
                                    · exact hr_x
                                    · exact False.elim
                                        (hy_not_H1 (by simpa [hr_y] using hr_H1))
                                  have hright_colorable :
                                      Asep.rightWithSeparatorClique.Colorable 4 :=
                                    Asep.rightWithSeparatorClique_colorable_of_pair_collapse_colorable
                                      hseparator H1 hH1_connected hx_H1
                                      hy_not_H1 hright_intersection
                                      hH1_adj_y hcollapse_colorable
                                  exact Or.inl
                                    ⟨x, y, hxy, hseparator, hright_colorable⟩
                                · exact Or.inr htriple
                              obtain ⟨vA, hvA_left_only, hvA_ne_v1⟩ :=
                                Asep.exists_left_only_ne_of_two_left_only
                                  v1 hAsep_left_only_large
                              have hAsep_left_colorable :
                                  (G.induce Asep.left).Colorable 4 :=
                                left_induce_colorable_of_smaller_induction_global_no_model
                                  (G := G) hIH Asep hAsep_proper hno_model_pair
                              rcases hAsep_pair_first_collapse_no_model_or_triple with
                                hpair | htriple
                              · rcases hpair with
                                  ⟨x, y, H1, hH1_connected, Lq, hxy,
                                    hseparator, _hv1_ne_y, _hv2_ne_x,
                                    hv1_H1, hx_H1, hv2_H1_or_y,
                                    hy_not_H1, hH1_left, hH1_adj_y,
                                    _himage, hfirst, hno_Lq⟩
                                let C : GraphContraction G :=
                                  GraphContraction.collapseSubgraph
                                    G H1 hH1_connected
                                have hcard_C_lt :
                                    Fintype.card C.Target < Fintype.card V := by
                                  by_cases hx_ne_v1 : x ≠ v1
                                  · exact
                                      GraphContraction.collapseSubgraph_target_card_lt
                                        G H1 hH1_connected hv1_H1 hx_H1
                                        hx_ne_v1.symm
                                  · have hx_eq_v1 : x = v1 := not_not.mp hx_ne_v1
                                    have hv2_H1 : v2 ∈ H1.verts := by
                                      rcases hv2_H1_or_y with hv2_y | hv2_H1
                                      · have hxy_edge : G.Adj x y := by
                                          simpa [hx_eq_v1, ← hv2_y] using edge
                                        have hseparator_clique :
                                            G.IsClique Asep.separator := by
                                          intro a ha b hb hab_ne
                                          have ha_pair : a = x ∨ a = y := by
                                            have : a ∈ ({x, y} : Set V) := by
                                              simpa [hseparator] using ha
                                            simpa using this
                                          have hb_pair : b = x ∨ b = y := by
                                            have : b ∈ ({x, y} : Set V) := by
                                              simpa [hseparator] using hb
                                            simpa using this
                                          rcases ha_pair with ha_x | ha_y <;>
                                            rcases hb_pair with hb_x | hb_y
                                          · exact False.elim
                                              (hab_ne (ha_x.trans hb_x.symm))
                                          · simpa [ha_x, hb_y] using hxy_edge
                                          · simpa [ha_y, hb_x] using hxy_edge.symm
                                          · exact False.elim
                                              (hab_ne (ha_y.trans hb_y.symm))
                                        exact False.elim
                                          (hAsep_not_clique hseparator_clique)
                                      · exact hv2_H1
                                    exact
                                      GraphContraction.collapseSubgraph_target_card_lt
                                        G H1 hH1_connected hv1_H1 hv2_H1
                                        edge.ne
                                have hright_intersection :
                                    forall r : V,
                                      r ∈ Asep.right ->
                                        r ∈ H1.verts -> r = x := by
                                  intro r hr_right hr_H1
                                  have hr_left : r ∈ Asep.left := hH1_left hr_H1
                                  have hr_sep : r ∈ Asep.separator :=
                                    ⟨hr_left, hr_right⟩
                                  have hr_pair : r = x ∨ r = y := by
                                    have : r ∈ ({x, y} : Set V) := by
                                      simpa [hseparator] using hr_sep
                                    simpa using this
                                  rcases hr_pair with hr_x | hr_y
                                  · exact hr_x
                                  · exact False.elim
                                      (hy_not_H1 (by simpa [hr_y] using hr_H1))
                                exact
                                  colorable_of_pair_separation_two_pair_collapses
                                    (G := G) hIH Asep hAsep_left_colorable
                                    hxy hseparator H1 hH1_connected hx_H1
                                    hy_not_H1 hright_intersection hH1_adj_y
                                    hcard_C_lt Lq hfirst hno_Lq
                              · exact
                                  colorable_of_minimal_pair_left_triple_nonclique_separation
                                    (G := G) hIH hcolor edge hno_model_pair
                                    hvertex_minimal_pair Asep hAsep_proper
                                    hAsep_order hAsep_left
                                    hAsep_minimal hAsep_left_colorable
                                    htriple
                            rcases _h_ordered_clique_side with hleft | hright
                            · exact hleft_nonclique_small_separation_colorable
                                S hproper horder horder_one hseparator_clique_global hleft
                            · have hproper_symm : S.symm.Proper :=
                                (S.proper_symm).mpr hproper
                              have horder_symm : S.symm.OrderAtMost 3 :=
                                (S.orderAtMost_symm 3).mpr horder
                              have horder_one_symm : Not (S.symm.OrderAtMost 1) := by
                                intro h
                                exact horder_one ((S.orderAtMost_symm 1).mp h)
                              have hsep_ncard_ge_two_symm : 2 <= S.symm.separator.ncard :=
                                S.symm.separator_ncard_ge_two_of_not_orderAtMost_one horder_one_symm
                              have hsep_ncard_le_three_symm : S.symm.separator.ncard <= 3 :=
                                S.symm.separator_ncard_le_of_orderAtMost horder_symm
                              have hseparator_clique_symm :
                                  Not (G.IsClique S.symm.separator) := by
                                intro hclique
                                exact hseparator_clique_global (by
                                  rwa [S.separator_symm] at hclique)
                              have hleft_symm :
                                  (OrderedClique.pair v1 v2 edge).vertexSet ⊆ S.symm.left := by
                                simpa [Separation.symm] using hright
                              exact hleft_nonclique_small_separation_colorable
                                S.symm hproper_symm horder_symm horder_one_symm
                                hseparator_clique_symm hleft_symm)

end Schematic.Math.GraphTheory
