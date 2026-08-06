import DominatingFourColour.Proof.MainInduction.SeparationColoring

/-! Pair-collapse and general color-class quotient arguments. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem Separation.pair_rightColorClassQuotientMap_same_fibers_second_collapse
    (S : Separation G)
    {x y : V}
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V))
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hxH : x ∈ H.verts)
    (hy_not_H : y ∉ H.verts)
    (hright_intersection :
      forall r : V, r ∈ S.right -> r ∈ H.verts -> r = x)
    (hH_adj_y : Exists fun z : V => z ∈ H.verts ∧ G.Adj z y)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hxy_same :
      forall (hx_left : x ∈ S.left) (hy_left : y ∈ S.left),
        left_coloring ⟨x, hx_left⟩ = left_coloring ⟨y, hy_left⟩) :
    let C : GraphContraction G := GraphContraction.collapseSubgraph G H hH_connected
    let hxyC : C.graph.Adj (C.map x) (C.map y) :=
      Separation.pair_collapse_separator_adj
        H hH_connected hxH hy_not_H hH_adj_y
    let D := GraphContraction.collapseEdge C.graph hxyC
    forall a b : S.right,
      S.rightColorClassQuotientMap left_coloring a =
          S.rightColorClassQuotientMap left_coloring b ↔
        D.map (C.map (a : V)) = D.map (C.map (b : V)) := by
  classical
  intro C hxyC D a b
  have hx_sep : x ∈ S.separator := by
    rw [hseparator]
    simp
  have hy_sep : y ∈ S.separator := by
    rw [hseparator]
    simp
  have hx_left : x ∈ S.left := hx_sep.1
  have hx_right : x ∈ S.right := hx_sep.2
  have hy_left : y ∈ S.left := hy_sep.1
  have hy_right : y ∈ S.right := hy_sep.2
  let rx : S.right := ⟨x, hx_right⟩
  let ry : S.right := ⟨y, hy_right⟩
  have hC_right_injective :
      Function.Injective (fun r : S.right => C.map (r : V)) := by
    intro r s hrs
    have hcases :
        ((r : V) ∈ H.verts ∧ (s : V) ∈ H.verts) ∨
          ((r : V) = (s : V) ∧
            (r : V) ∉ H.verts ∧ (s : V) ∉ H.verts) := by
      simpa [C] using
        (GraphContraction.collapseSubgraph_map_eq_iff
          G H hH_connected (v := (r : V)) (w := (s : V))).mp hrs
    rcases hcases with hboth | hout
    · have hrx : (r : V) = x :=
        hright_intersection (r : V) r.2 hboth.1
      have hsx : (s : V) = x :=
        hright_intersection (s : V) s.2 hboth.2
      exact Subtype.ext (hrx.trans hsx.symm)
    · exact Subtype.ext hout.1
  have hpair_mem_iff :
      forall r : S.right,
        C.map (r : V) ∈ ({C.map x, C.map y} : Set C.Target) ↔
          (r : V) = x ∨ (r : V) = y := by
    intro r
    constructor
    · intro hr
      have hr_pair :
          C.map (r : V) = C.map x ∨ C.map (r : V) = C.map y := by
        simpa using hr
      rcases hr_pair with hrx | hry
      · have hr_eq_rx : r = rx := hC_right_injective (by simpa [rx] using hrx)
        exact Or.inl (congrArg (fun t : S.right => (t : V)) hr_eq_rx)
      · have hr_eq_ry : r = ry := hC_right_injective (by simpa [ry] using hry)
        exact Or.inr (congrArg (fun t : S.right => (t : V)) hr_eq_ry)
    · intro hr
      rcases hr with hrx | hry
      · subst hrx
        simp
      · subst hry
        simp
  constructor
  · intro hq
    have hbase :
        S.rightColorClassBaseMap left_coloring a =
          S.rightColorClassBaseMap left_coloring b :=
      congrArg Subtype.val hq
    by_cases ha_left : (a : V) ∈ S.left
    · by_cases hb_left : (b : V) ∈ S.left
      · have ha_pair : (a : V) = x ∨ (a : V) = y := by
          have ha_sep : (a : V) ∈ S.separator := ⟨ha_left, a.2⟩
          have : (a : V) ∈ ({x, y} : Set V) := by
            simpa [hseparator] using ha_sep
          simpa using this
        have hb_pair : (b : V) = x ∨ (b : V) = y := by
          have hb_sep : (b : V) ∈ S.separator := ⟨hb_left, b.2⟩
          have : (b : V) ∈ ({x, y} : Set V) := by
            simpa [hseparator] using hb_sep
          simpa using this
        have ha_pair' :
            C.map (a : V) ∈ ({C.map x, C.map y} : Set C.Target) :=
          (hpair_mem_iff a).mpr ha_pair
        have hb_pair' :
            C.map (b : V) ∈ ({C.map x, C.map y} : Set C.Target) :=
          (hpair_mem_iff b).mpr hb_pair
        simpa [D] using
          (GraphContraction.collapseEdge_map_eq_iff C.graph hxyC
            (v := C.map (a : V)) (w := C.map (b : V))).mpr
              (Or.inl ⟨ha_pair', hb_pair'⟩)
      · simp [Separation.rightColorClassBaseMap, ha_left, hb_left] at hbase
    · by_cases hb_left : (b : V) ∈ S.left
      · simp [Separation.rightColorClassBaseMap, ha_left, hb_left] at hbase
      · have hab_sub : a = b := by
          have hsub :
              (⟨a, ha_left⟩ :
                {r : S.right // (r : V) ∉ S.left}) = ⟨b, hb_left⟩ := by
            simpa [Separation.rightColorClassBaseMap, ha_left, hb_left] using hbase
          exact congrArg Subtype.val hsub
        rw [hab_sub]
  · intro hD
    have hcases :
        (C.map (a : V) ∈ ({C.map x, C.map y} : Set C.Target) ∧
          C.map (b : V) ∈ ({C.map x, C.map y} : Set C.Target)) ∨
          (C.map (a : V) = C.map (b : V) ∧
            C.map (a : V) ∉ ({C.map x, C.map y} : Set C.Target) ∧
            C.map (b : V) ∉ ({C.map x, C.map y} : Set C.Target)) := by
      simpa [D] using
        (GraphContraction.collapseEdge_map_eq_iff C.graph hxyC
          (v := C.map (a : V)) (w := C.map (b : V))).mp hD
    rcases hcases with hboth | hout
    · have ha_pair : (a : V) = x ∨ (a : V) = y :=
        (hpair_mem_iff a).mp hboth.1
      have hb_pair : (b : V) = x ∨ (b : V) = y :=
        (hpair_mem_iff b).mp hboth.2
      apply Subtype.ext
      change
        S.rightColorClassBaseMap left_coloring a =
          S.rightColorClassBaseMap left_coloring b
      rcases ha_pair with ha_x | ha_y <;> rcases hb_pair with hb_x | hb_y
      · have ha_left' : (a : V) ∈ S.left := by simpa [ha_x] using hx_left
        have hb_left' : (b : V) ∈ S.left := by simpa [hb_x] using hx_left
        simp only [Separation.rightColorClassBaseMap]
        rw [dif_pos ha_left', dif_pos hb_left']
        apply congrArg Sum.inl
        exact congrArg left_coloring (Subtype.ext (ha_x.trans hb_x.symm))
      · have ha_left' : (a : V) ∈ S.left := by simpa [ha_x] using hx_left
        have hb_left' : (b : V) ∈ S.left := by simpa [hb_y] using hy_left
        simp only [Separation.rightColorClassBaseMap]
        rw [dif_pos ha_left', dif_pos hb_left']
        apply congrArg Sum.inl
        have hca :
            left_coloring ⟨(a : V), ha_left'⟩ =
              left_coloring ⟨x, hx_left⟩ :=
          congrArg left_coloring (Subtype.ext ha_x)
        have hcb :
            left_coloring ⟨(b : V), hb_left'⟩ =
              left_coloring ⟨y, hy_left⟩ :=
          congrArg left_coloring (Subtype.ext hb_y)
        exact hca.trans ((hxy_same hx_left hy_left).trans hcb.symm)
      · have ha_left' : (a : V) ∈ S.left := by simpa [ha_y] using hy_left
        have hb_left' : (b : V) ∈ S.left := by simpa [hb_x] using hx_left
        simp only [Separation.rightColorClassBaseMap]
        rw [dif_pos ha_left', dif_pos hb_left']
        apply congrArg Sum.inl
        have hca :
            left_coloring ⟨(a : V), ha_left'⟩ =
              left_coloring ⟨y, hy_left⟩ :=
          congrArg left_coloring (Subtype.ext ha_y)
        have hcb :
            left_coloring ⟨(b : V), hb_left'⟩ =
              left_coloring ⟨x, hx_left⟩ :=
          congrArg left_coloring (Subtype.ext hb_x)
        exact hca.trans ((hxy_same hx_left hy_left).symm.trans hcb.symm)
      · have ha_left' : (a : V) ∈ S.left := by simpa [ha_y] using hy_left
        have hb_left' : (b : V) ∈ S.left := by simpa [hb_y] using hy_left
        simp only [Separation.rightColorClassBaseMap]
        rw [dif_pos ha_left', dif_pos hb_left']
        apply congrArg Sum.inl
        exact congrArg left_coloring (Subtype.ext (ha_y.trans hb_y.symm))
    · have hab : a = b := hC_right_injective hout.1
      rw [hab]

theorem Separation.pair_right_color_class_quotient_colorable_of_two_pair_collapses
    (S : Separation G)
    {x y : V}
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V))
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hxH : x ∈ H.verts)
    (hy_not_H : y ∉ H.verts)
    (hright_intersection :
      forall r : V, r ∈ S.right -> r ∈ H.verts -> r = x)
    (hH_adj_y : Exists fun z : V => z ∈ H.verts ∧ G.Adj z y) :
    let C : GraphContraction G := GraphContraction.collapseSubgraph G H hH_connected
    let hxyC : C.graph.Adj (C.map x) (C.map y) :=
      Separation.pair_collapse_separator_adj
        H hH_connected hxH hy_not_H hH_adj_y
    let D := GraphContraction.collapseEdge C.graph hxyC
    C.graph.Colorable 4 ->
      D.graph.Colorable 4 ->
        forall left_coloring : (G.induce S.left).Coloring (Fin 4),
          (contractionTargetGraph S.rightWithSeparatorClique
            (S.rightColorClassQuotientMap left_coloring)).Colorable 4 := by
  classical
  intro C hxyC D hfirst_colorable hsecond_colorable left_coloring
  have hx_sep : x ∈ S.separator := by
    rw [hseparator]
    simp
  have hy_sep : y ∈ S.separator := by
    rw [hseparator]
    simp
  have hx_left : x ∈ S.left := hx_sep.1
  have hy_left : y ∈ S.left := hy_sep.1
  by_cases hxy_same0 :
      left_coloring ⟨x, hx_left⟩ = left_coloring ⟨y, hy_left⟩
  · let g : S.right -> D.Target := fun r => D.map (C.map (r : V))
    have hg_color :
        (contractionTargetGraph S.rightWithSeparatorClique g).Colorable 4 := by
      rcases hsecond_colorable with ⟨colD⟩
      refine ⟨SimpleGraph.Coloring.mk (fun t : D.Target => colD t) ?_⟩
      intro p q hpq hsame
      rcases hpq with ⟨hpq_ne, a, b, hga, hgb, hab⟩
      have hC_adj : C.graph.Adj (C.map (a : V)) (C.map (b : V)) :=
        (S.rightWithSeparatorCliqueCollapseHomOfPair
          hseparator H hH_connected hxH hy_not_H
          hright_intersection hH_adj_y).map_adj hab
      have hD_adj : D.graph.Adj p q := by
        rcases D.map_adj hC_adj with hcollapse | hadj
        · have hpq : p = q := hga.symm.trans (hcollapse.trans hgb)
          exact False.elim (hpq_ne hpq)
        · simpa [g, hga, hgb] using hadj
      exact colD.valid hD_adj hsame
    have hsame_fibers :
        forall a b : S.right,
          S.rightColorClassQuotientMap left_coloring a =
              S.rightColorClassQuotientMap left_coloring b ↔
            g a = g b := by
      simpa [g, C, D] using
        S.pair_rightColorClassQuotientMap_same_fibers_second_collapse
          hxy hseparator H hH_connected hxH hy_not_H
          hright_intersection hH_adj_y left_coloring
          (by
            intro hx_left' hy_left'
            have hx_sub :
                (⟨x, hx_left'⟩ : S.left) = ⟨x, hx_left⟩ := Subtype.ext rfl
            have hy_sub :
                (⟨y, hy_left'⟩ : S.left) = ⟨y, hy_left⟩ := Subtype.ext rfl
            simpa [hx_sub, hy_sub] using hxy_same0)
    exact
      GraphContraction.contractionTargetGraph_colorable_of_same_fibers
        (G := S.rightWithSeparatorClique)
        (S.rightColorClassQuotientMap left_coloring) g hsame_fibers hg_color
  · have hright_colorable : S.rightWithSeparatorClique.Colorable 4 :=
      S.rightWithSeparatorClique_colorable_of_pair_collapse_colorable
        hseparator H hH_connected hxH hy_not_H hright_intersection
        hH_adj_y hfirst_colorable
    have hseparator_color_injective :
        forall a b : S.separator,
          left_coloring ⟨(a : V), a.2.1⟩ =
              left_coloring ⟨(b : V), b.2.1⟩ ->
            a = b := by
      intro a b hcolor
      have ha_pair : (a : V) = x ∨ (a : V) = y := by
        have : (a : V) ∈ ({x, y} : Set V) := by
          simpa [hseparator] using a.2
        simpa using this
      have hb_pair : (b : V) = x ∨ (b : V) = y := by
        have : (b : V) ∈ ({x, y} : Set V) := by
          simpa [hseparator] using b.2
        simpa using this
      rcases ha_pair with ha_x | ha_y <;> rcases hb_pair with hb_x | hb_y
      · exact Subtype.ext (ha_x.trans hb_x.symm)
      · have hxy_color :
            left_coloring ⟨x, hx_left⟩ =
              left_coloring ⟨y, hy_left⟩ := by
          have hca :
              left_coloring ⟨x, hx_left⟩ =
                left_coloring ⟨(a : V), a.2.1⟩ :=
            congrArg left_coloring (Subtype.ext ha_x.symm)
          have hcb :
              left_coloring ⟨(b : V), b.2.1⟩ =
                left_coloring ⟨y, hy_left⟩ :=
            congrArg left_coloring (Subtype.ext hb_y)
          exact hca.trans (hcolor.trans hcb)
        exact False.elim (hxy_same0 hxy_color)
      · have hxy_color :
            left_coloring ⟨x, hx_left⟩ =
              left_coloring ⟨y, hy_left⟩ := by
          have hca :
              left_coloring ⟨(a : V), a.2.1⟩ =
                left_coloring ⟨y, hy_left⟩ :=
            congrArg left_coloring (Subtype.ext ha_y)
          have hcb :
              left_coloring ⟨x, hx_left⟩ =
                left_coloring ⟨(b : V), b.2.1⟩ :=
            congrArg left_coloring (Subtype.ext hb_x.symm)
          exact hcb.trans (hcolor.symm.trans hca)
        exact False.elim (hxy_same0 hxy_color)
      · exact Subtype.ext (ha_y.trans hb_y.symm)
    exact
      right_color_class_quotient_colorable_of_rightWithSeparatorClique_colorable_of_separator_color_injective
        (G := G) S left_coloring hseparator_color_injective hright_colorable

theorem pair_second_collapse_colorable_of_first_collapse_no_model
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    {x y : V}
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hxH : x ∈ H.verts)
    (hy_not_H : y ∉ H.verts)
    (hH_adj_y : Exists fun z : V => z ∈ H.verts ∧ G.Adj z y) :
    let C : GraphContraction G := GraphContraction.collapseSubgraph G H hH_connected
    Fintype.card C.Target < Fintype.card V ->
      forall Lq : OrderedClique C.graph,
        Lq.first? = some (none : C.Target) ->
          Not (CompatibleDominatingK5Model Lq) ->
            let hxyC : C.graph.Adj (C.map x) (C.map y) :=
              Separation.pair_collapse_separator_adj
                H hH_connected hxH hy_not_H hH_adj_y
            let D := GraphContraction.collapseEdge C.graph hxyC
            D.graph.Colorable 4 := by
  classical
  intro C hcard_C_lt Lq hfirst hno_Lq hxyC D
  have hcard_D_C_lt : Fintype.card D.Target < Fintype.card C.Target := by
    simpa [D] using
      GraphContraction.collapseEdge_target_card_lt C.graph hxyC
  have hcard_D_lt : Fintype.card D.Target < Fintype.card V :=
    lt_trans hcard_D_C_lt hcard_C_lt
  have hx_map : C.map x = (none : C.Target) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_none_of_mem
        G H hH_connected hxH
  let H2 := GraphContraction.inducedPairSubgraph
    C.graph (C.map x) (C.map y)
  let hH2_connected : H2.coe.Connected :=
    GraphContraction.inducedPairSubgraph_connected hxyC
  have hnoneH2 : (none : C.Target) ∈ H2.verts := by
    rw [← hx_map]
    change C.map x = C.map x ∨ C.map x = C.map y
    exact Or.inl rfl
  obtain ⟨Lqq, _himage, _hfirst, hno_Lqq⟩ :=
    exists_collapse_image_no_compatible_model_of_first_mem
      (G := C.graph) Lq H2 hH2_connected hfirst hnoneH2 hno_Lq
  rcases hIH D.graph hcard_D_lt Lqq with hcolor | hmodel
  · exact hcolor
  · exact False.elim (hno_Lqq hmodel)

theorem colorable_of_pair_separation_two_pair_collapses
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hleft_colorable : (G.induce S.left).Colorable 4)
    {x y : V}
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V))
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hxH : x ∈ H.verts)
    (hy_not_H : y ∉ H.verts)
    (hright_intersection :
      forall r : V, r ∈ S.right -> r ∈ H.verts -> r = x)
    (hH_adj_y : Exists fun z : V => z ∈ H.verts ∧ G.Adj z y) :
    let C : GraphContraction G := GraphContraction.collapseSubgraph G H hH_connected
    Fintype.card C.Target < Fintype.card V ->
      forall Lq : OrderedClique C.graph,
        Lq.first? = some (none : C.Target) ->
          Not (CompatibleDominatingK5Model Lq) ->
            G.Colorable 4 := by
  classical
  intro C hcard_C_lt Lq hfirst hno_Lq
  have hfirst_colorable : C.graph.Colorable 4 := by
    rcases hIH C.graph hcard_C_lt Lq with hcolor | hmodel
    · exact hcolor
    · exact False.elim (hno_Lq hmodel)
  have hsecond_colorable :
      let hxyC : C.graph.Adj (C.map x) (C.map y) :=
        Separation.pair_collapse_separator_adj
          H hH_connected hxH hy_not_H hH_adj_y
      let D := GraphContraction.collapseEdge C.graph hxyC
      D.graph.Colorable 4 :=
    pair_second_collapse_colorable_of_first_collapse_no_model
      (G := G) hIH H hH_connected hxH hy_not_H
      hH_adj_y hcard_C_lt Lq hfirst hno_Lq
  rcases hleft_colorable with ⟨left_coloring⟩
  exact colorable_of_separation_right_color_class_range_quotient S left_coloring
    (S.pair_right_color_class_quotient_colorable_of_two_pair_collapses
      hxy hseparator H hH_connected hxH hy_not_H
      hright_intersection hH_adj_y
      hfirst_colorable hsecond_colorable left_coloring)

theorem right_color_class_quotient_colorable_of_global_no_model_of_separator_clique
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hseparator_clique : G.IsClique S.separator)
    (hno_model : Not (CompatibleDominatingK5Model L))
    (left_coloring : (G.induce S.left).Coloring (Fin 4)) :
    (contractionTargetGraph S.rightWithSeparatorClique
      (S.rightColorClassQuotientMap left_coloring)).Colorable 4 := by
  exact
    right_color_class_quotient_colorable_of_rightWithSeparatorClique_colorable_of_separator_clique
      (G := G) S hseparator_clique left_coloring
      (right_separator_clique_colorable_of_smaller_induction_global_no_model_restrict
        (G := G) hIH S hproper hseparator_clique hno_model)

noncomputable def Separation.rightColorClassContractionOrderedClique
    (S : Separation G)
    (L : OrderedClique G)
    (hright : L.vertexSet ⊆ S.right)
    (left_coloring : (G.induce S.left).Coloring (Fin 4)) :
    OrderedClique (S.rightColorClassContraction left_coloring).graph := by
  classical
  let C : GraphContraction S.rightWithSeparatorClique :=
    S.rightColorClassContraction left_coloring
  cases L with
  | nil =>
      exact .nil
  | single v =>
      let rv : S.right := ⟨v, hright (by simp [OrderedClique.vertexSet])⟩
      exact .single (C.map rv)
  | pair v1 v2 edge =>
      let rv1 : S.right := ⟨v1, hright (by simp [OrderedClique.vertexSet])⟩
      let rv2 : S.right := ⟨v2, hright (by simp [OrderedClique.vertexSet])⟩
      have hside : S.rightWithSeparatorClique.Adj rv1 rv2 := Or.inl edge
      have hmap_ne : C.map rv1 ≠ C.map rv2 := by
        simpa [C, Separation.rightColorClassContraction, GraphContraction.ofMap]
          using
            S.rightColorClassQuotientMap_no_true_edge_collapsed
              left_coloring rv1 rv2 (by simpa [rv1, rv2] using edge)
      have edgeq : C.graph.Adj (C.map rv1) (C.map rv2) := by
        rcases C.map_adj hside with hcollapse | hadj
        · exact False.elim (hmap_ne hcollapse)
        · exact hadj
      exact .pair (C.map rv1) (C.map rv2) edgeq

theorem Separation.rightColorClassContractionOrderedClique_image
    (S : Separation G)
    (L : OrderedClique G)
    (hright : L.vertexSet ⊆ S.right)
    (left_coloring : (G.induce S.left).Coloring (Fin 4)) :
    OrderedCliqueContractionImage
      (S.rightColorClassContraction left_coloring)
      (S.rightOrderedClique L hright)
      (S.rightColorClassContractionOrderedClique L hright left_coloring) := by
  classical
  let C : GraphContraction S.rightWithSeparatorClique :=
    S.rightColorClassContraction left_coloring
  cases L with
  | nil =>
      simp [Separation.rightOrderedClique,
        Separation.rightColorClassContractionOrderedClique]
      exact OrderedCliqueContractionImage.nil
  | single v =>
      let rv : S.right := ⟨v, hright (by simp [OrderedClique.vertexSet])⟩
      change OrderedCliqueContractionImage C (.single rv) (.single (C.map rv))
      exact OrderedCliqueContractionImage.single rv
  | pair v1 v2 edge =>
      let rv1 : S.right := ⟨v1, hright (by simp [OrderedClique.vertexSet])⟩
      let rv2 : S.right := ⟨v2, hright (by simp [OrderedClique.vertexSet])⟩
      have hside : S.rightWithSeparatorClique.Adj rv1 rv2 := Or.inl edge
      have hmap_ne : C.map rv1 ≠ C.map rv2 := by
        simpa [C, Separation.rightColorClassContraction, GraphContraction.ofMap]
          using
            S.rightColorClassQuotientMap_no_true_edge_collapsed
              left_coloring rv1 rv2 (by simpa [rv1, rv2] using edge)
      have edgeq : C.graph.Adj (C.map rv1) (C.map rv2) := by
        rcases C.map_adj hside with hcollapse | hadj
        · exact False.elim (hmap_ne hcollapse)
        · exact hadj
      change OrderedCliqueContractionImage C
        (.pair rv1 rv2 hside) (.pair (C.map rv1) (C.map rv2) edgeq)
      exact OrderedCliqueContractionImage.pair_uncollapsed hside edgeq

theorem right_color_class_contraction_ordered_model_lifts_of_singleton_branch_fibers
    (S : Separation G)
    (L : OrderedClique G)
    (hright : L.vertexSet ⊆ S.right)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hsingle :
      forall Tq : DominatingK5Model (S.rightColorClassContraction left_coloring).graph,
        LCompatible
            (S.rightColorClassContractionOrderedClique L hright left_coloring) Tq ->
          forall j : Fin 5,
            forall y : (S.rightColorClassContraction left_coloring).Target,
              y ∈ (Tq.branch j).verts ->
                forall v w : S.right,
                  (S.rightColorClassContraction left_coloring).map v = y ->
                    (S.rightColorClassContraction left_coloring).map w = y ->
                      v = w) :
    CompatibleDominatingK5Model
        (S.rightColorClassContractionOrderedClique L hright left_coloring) ->
      CompatibleDominatingK5Model (S.rightOrderedClique L hright) := by
  classical
  let C : GraphContraction S.rightWithSeparatorClique :=
    S.rightColorClassContraction left_coloring
  exact contraction_lifts_compatible_of_singleton_branch_fibers
    (G := S.rightWithSeparatorClique)
    (L := S.rightOrderedClique L hright)
    C
    (S.rightColorClassContractionOrderedClique L hright left_coloring)
    (S.rightColorClassContractionOrderedClique_image L hright left_coloring)
    (by
      intro Tq hTq j y hy v w hv hw
      exact hsingle Tq (by simpa [C] using hTq) j y hy v w
        (by simpa [C] using hv) (by simpa [C] using hw))

theorem right_color_class_contraction_ordered_model_lifts_global_of_separator_clique
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator)
    (L : OrderedClique G)
    (hright : L.vertexSet ⊆ S.right)
    (left_coloring : (G.induce S.left).Coloring (Fin 4)) :
    CompatibleDominatingK5Model
        (S.rightColorClassContractionOrderedClique L hright left_coloring) ->
      CompatibleDominatingK5Model L := by
  classical
  have hseparator_color_injective :
      forall a b : S.separator,
        left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩ ->
          a = b :=
    S.leftColoring_injective_on_separator_of_separator_clique
      left_coloring hseparator_clique
  intro hmodel
  exact compatible_model_lift_rightWithSeparatorClique_of_separator_clique
    S L hright hseparator_clique
    (right_color_class_contraction_ordered_model_lifts_of_singleton_branch_fibers
      (G := G) S L hright left_coloring
      (by
        intro Tq _hTq j y _hy v w hv hw
        exact S.rightColorClassContraction_fiber_singleton_of_separator_color_injective
          left_coloring hseparator_color_injective y v w hv hw)
      hmodel)

theorem no_right_color_class_contraction_ordered_model_of_global_no_model_of_separator_clique
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator)
    (L : OrderedClique G)
    (hright : L.vertexSet ⊆ S.right)
    (hno_model : Not (CompatibleDominatingK5Model L))
    (left_coloring : (G.induce S.left).Coloring (Fin 4)) :
    Not (CompatibleDominatingK5Model
      (S.rightColorClassContractionOrderedClique L hright left_coloring)) := by
  intro hmodel
  exact hno_model
    (right_color_class_contraction_ordered_model_lifts_global_of_separator_clique
      (G := G) S hseparator_clique L hright left_coloring hmodel)

theorem right_color_class_contraction_colorable_of_smaller_induction
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hno_model :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (S.rightColorClassContraction left_coloring).graph))) :
    (S.rightColorClassContraction left_coloring).graph.Colorable 4 := by
  classical
  have hno_model' :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (contractionTargetGraph S.rightWithSeparatorClique
            (S.rightColorClassQuotientMap left_coloring)))) := by
    simpa [Separation.rightColorClassContraction_graph_eq] using hno_model
  have hcolor :=
    right_color_class_quotient_colorable_of_smaller_induction
      (G := G) hIH S hproper left_coloring hno_model'
  simpa [Separation.rightColorClassContraction_graph_eq] using hcolor

theorem right_color_class_contraction_ordered_colorable_of_smaller_induction
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (L : OrderedClique G)
    (hright : L.vertexSet ⊆ S.right)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hno_model :
      Not (CompatibleDominatingK5Model
        (S.rightColorClassContractionOrderedClique L hright left_coloring))) :
    (S.rightColorClassContraction left_coloring).graph.Colorable 4 := by
  classical
  let C : GraphContraction S.rightWithSeparatorClique :=
    S.rightColorClassContraction left_coloring
  letI : Fintype C.Target := by
    change Fintype (S.rightColorClassTarget left_coloring)
    exact Separation.rightColorClassTargetFintype S left_coloring
  have hcard_lt :
      Fintype.card C.Target < Fintype.card V := by
    change Fintype.card (S.rightColorClassTarget left_coloring) < Fintype.card V
    exact S.rightColorClassTarget_card_lt_of_proper left_coloring hproper
  change C.graph.Colorable 4
  rcases hIH C.graph hcard_lt
      (S.rightColorClassContractionOrderedClique L hright left_coloring) with
    hcolor | hmodel
  · exact hcolor
  · exact False.elim (hno_model hmodel)

theorem right_color_class_contraction_arbitrary_ordered_colorable_of_smaller_induction
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (Lq : OrderedClique (S.rightColorClassContraction left_coloring).graph)
    (hno_model : Not (CompatibleDominatingK5Model Lq)) :
    (S.rightColorClassContraction left_coloring).graph.Colorable 4 := by
  classical
  let C : GraphContraction S.rightWithSeparatorClique :=
    S.rightColorClassContraction left_coloring
  letI : Fintype C.Target := by
    change Fintype (S.rightColorClassTarget left_coloring)
    exact Separation.rightColorClassTargetFintype S left_coloring
  have hcard_lt : Fintype.card C.Target < Fintype.card V := by
    change Fintype.card (S.rightColorClassTarget left_coloring) < Fintype.card V
    exact S.rightColorClassTarget_card_lt_of_proper left_coloring hproper
  change C.graph.Colorable 4
  rcases hIH C.graph hcard_lt Lq with hcolor | hmodel
  · exact hcolor
  · exact False.elim (hno_model hmodel)

theorem colorable_of_separation_left_coloring_and_right_color_class_quotient_no_model
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hno_model :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (contractionTargetGraph S.rightWithSeparatorClique
            (S.rightColorClassQuotientMap left_coloring))))) :
    G.Colorable 4 := by
  exact colorable_of_separation_right_color_class_range_quotient S left_coloring
    (right_color_class_quotient_colorable_of_smaller_induction
      (G := G) hIH S hproper left_coloring hno_model)

theorem colorable_of_separation_left_coloring_and_right_color_class_contraction_no_model
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hno_model :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (S.rightColorClassContraction left_coloring).graph))) :
    G.Colorable 4 := by
  exact colorable_of_separation_right_color_class_contraction S left_coloring
    (right_color_class_contraction_colorable_of_smaller_induction
      (G := G) hIH S hproper left_coloring hno_model)

theorem colorable_of_separation_left_coloring_and_right_ordered_color_class_contraction_no_model
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (L : OrderedClique G)
    (hright : L.vertexSet ⊆ S.right)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hno_model :
      Not (CompatibleDominatingK5Model
        (S.rightColorClassContractionOrderedClique L hright left_coloring))) :
    G.Colorable 4 := by
  exact colorable_of_separation_right_color_class_contraction S left_coloring
    (right_color_class_contraction_ordered_colorable_of_smaller_induction
      (G := G) hIH S hproper L hright left_coloring hno_model)

theorem colorable_of_separation_left_coloring_and_right_arbitrary_ordered_color_class_contraction_no_model
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (Lq : OrderedClique (S.rightColorClassContraction left_coloring).graph)
    (hno_model : Not (CompatibleDominatingK5Model Lq)) :
    G.Colorable 4 := by
  exact colorable_of_separation_right_color_class_contraction S left_coloring
    (right_color_class_contraction_arbitrary_ordered_colorable_of_smaller_induction
      (G := G) hIH S hproper left_coloring Lq hno_model)

theorem colorable_of_clique_separation_left_coloring_and_global_no_model_right_ordered_quotient
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hseparator_clique : G.IsClique S.separator)
    (hright : L.vertexSet ⊆ S.right)
    (hno_model : Not (CompatibleDominatingK5Model L))
    (left_coloring : (G.induce S.left).Coloring (Fin 4)) :
    G.Colorable 4 := by
  exact
    colorable_of_separation_left_coloring_and_right_ordered_color_class_contraction_no_model
      (G := G) hIH S hproper L hright left_coloring
      (no_right_color_class_contraction_ordered_model_of_global_no_model_of_separator_clique
        (G := G) S hseparator_clique L hright hno_model left_coloring)

theorem colorable_of_separation_left_colorable_and_right_color_class_quotients_no_model
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hleft : (G.induce S.left).Colorable 4)
    (hno_model :
      forall left_coloring : (G.induce S.left).Coloring (Fin 4),
        Not (CompatibleDominatingK5Model
          (OrderedClique.nil : OrderedClique
            (contractionTargetGraph S.rightWithSeparatorClique
              (S.rightColorClassQuotientMap left_coloring))))) :
    G.Colorable 4 := by
  rcases hleft with ⟨left_coloring⟩
  exact colorable_of_separation_left_coloring_and_right_color_class_quotient_no_model
    (G := G) hIH S hproper left_coloring (hno_model left_coloring)

theorem colorable_of_separation_left_colorable_and_right_color_class_quotients_colorable
    [Fintype V]
    (S : Separation G)
    (hleft : (G.induce S.left).Colorable 4)
    (hright_quotient :
      forall left_coloring : (G.induce S.left).Coloring (Fin 4),
        (contractionTargetGraph S.rightWithSeparatorClique
          (S.rightColorClassQuotientMap left_coloring)).Colorable 4) :
    G.Colorable 4 := by
  rcases hleft with ⟨left_coloring⟩
  exact colorable_of_separation_right_color_class_range_quotient S left_coloring
    (hright_quotient left_coloring)

theorem colorable_of_separation_left_and_right_color_class_quotients_no_model
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hno_left_model :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique (G.induce S.left))))
    (hno_right_quotient_model :
      forall left_coloring : (G.induce S.left).Coloring (Fin 4),
        Not (CompatibleDominatingK5Model
          (OrderedClique.nil : OrderedClique
            (contractionTargetGraph S.rightWithSeparatorClique
              (S.rightColorClassQuotientMap left_coloring))))) :
    G.Colorable 4 := by
    exact colorable_of_separation_left_colorable_and_right_color_class_quotients_no_model
      (G := G) hIH S hproper
      (left_induce_colorable_of_smaller_induction
        (G := G) hIH S hproper hno_left_model)
      hno_right_quotient_model

theorem colorable_of_separation_global_no_model_and_right_color_class_quotients_no_model
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hno_model : Not (CompatibleDominatingK5Model L))
    (hno_right_quotient_model :
      forall left_coloring : (G.induce S.left).Coloring (Fin 4),
        Not (CompatibleDominatingK5Model
          (OrderedClique.nil : OrderedClique
            (contractionTargetGraph S.rightWithSeparatorClique
              (S.rightColorClassQuotientMap left_coloring))))) :
    G.Colorable 4 := by
  exact colorable_of_separation_left_colorable_and_right_color_class_quotients_no_model
    (G := G) hIH S hproper
    (left_induce_colorable_of_smaller_induction_global_no_model
      (G := G) hIH S hproper hno_model)
    hno_right_quotient_model

theorem colorable_of_separation_global_no_model_and_right_color_class_quotients_colorable
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hno_model : Not (CompatibleDominatingK5Model L))
    (hright_quotient :
      forall left_coloring : (G.induce S.left).Coloring (Fin 4),
        (contractionTargetGraph S.rightWithSeparatorClique
          (S.rightColorClassQuotientMap left_coloring)).Colorable 4) :
    G.Colorable 4 := by
  exact colorable_of_separation_left_colorable_and_right_color_class_quotients_colorable
    (G := G) S
    (left_induce_colorable_of_smaller_induction_global_no_model
      (G := G) hIH S hproper hno_model)
    hright_quotient

end Schematic.Math.GraphTheory
