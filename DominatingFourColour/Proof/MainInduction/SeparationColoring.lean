import DominatingFourColour.Proof.MainInduction.FinalContraction

/-! Smaller-induction colorings and model lifts across a separation. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem exists_pair_counterexample_of_smaller_induction_and_no_small_separations
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    (hno_model : Not (CompatibleDominatingK5Model L))
    (hno_small_separations :
      forall S : Separation G, S.Proper -> S.OrderAtMost 3 -> False) :
    Exists fun L' : OrderedClique G =>
      L.InitialSegment L' ∧ L'.length = 2 ∧
        MainInductionCounterexample G L' := by
  classical
  obtain ⟨L', hinit, hlen, hno_model_L', hvertex_minimal⟩ :=
    exists_pair_extension_no_compatible_of_smaller_induction
      (G := G) hIH hnot_four_colorable hno_model
  refine ⟨L', hinit, hlen, ?_⟩
  refine {
    not_four_colorable := hnot_four_colorable
    no_compatible_model := hno_model_L'
    vertex_minimal := hvertex_minimal
    clique_maximal := ?_
    no_proper_separation_orderAtMost_three := hno_small_separations
  }
  intro L'' _hinit' _hno
  rw [hlen]
  cases L'' <;> simp [OrderedClique.length]

theorem left_separator_clique_colorable_of_smaller_induction
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hno_model :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique S.leftWithSeparatorClique))) :
    S.leftWithSeparatorClique.Colorable 4 := by
  classical
  letI : Fintype S.left := S.left.toFinite.fintype
  have hcard_lt : Fintype.card S.left < Fintype.card V := by
    have hnat := S.natCard_left_lt_of_proper hproper
    simpa [Nat.card_eq_fintype_card] using hnat
  rcases hIH S.leftWithSeparatorClique hcard_lt
      (OrderedClique.nil : OrderedClique S.leftWithSeparatorClique) with hcolor | hmodel
  · exact hcolor
  · exact False.elim (hno_model hmodel)

theorem left_separator_clique_colorable_of_smaller_induction_with_ordered_clique
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (L : OrderedClique G)
    (hleft : L.vertexSet ⊆ S.left)
    (hno_model :
      Not (CompatibleDominatingK5Model (S.leftOrderedClique L hleft))) :
    S.leftWithSeparatorClique.Colorable 4 := by
  classical
  letI : Fintype S.left := S.left.toFinite.fintype
  have hcard_lt : Fintype.card S.left < Fintype.card V := by
    have hnat := S.natCard_left_lt_of_proper hproper
    simpa [Nat.card_eq_fintype_card] using hnat
  rcases hIH S.leftWithSeparatorClique hcard_lt
      (S.leftOrderedClique L hleft) with hcolor | hmodel
  · exact hcolor
  · exact False.elim (hno_model hmodel)

theorem left_separator_clique_colorable_of_smaller_induction_global_no_model
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hleft : L.vertexSet ⊆ S.left)
    (hseparator_clique : G.IsClique S.separator)
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    S.leftWithSeparatorClique.Colorable 4 := by
  exact left_separator_clique_colorable_of_smaller_induction_with_ordered_clique
    (G := G) hIH S hproper L hleft
    (no_model_leftWithSeparatorClique_of_global_no_model_of_separator_clique
      S L hleft hseparator_clique hno_model)

theorem left_induce_colorable_of_smaller_induction
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hno_model :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique (G.induce S.left)))) :
    (G.induce S.left).Colorable 4 := by
    classical
    letI : Fintype S.left := S.left.toFinite.fintype
    have hcard_lt : Fintype.card S.left < Fintype.card V := by
      have hnat := S.natCard_left_lt_of_proper hproper
      simpa [Nat.card_eq_fintype_card] using hnat
    rcases hIH (G.induce S.left) hcard_lt
        (OrderedClique.nil : OrderedClique (G.induce S.left)) with hcolor | hmodel
    · exact hcolor
    · exact False.elim (hno_model hmodel)

theorem left_induce_colorable_of_smaller_induction_global_no_model
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    (G.induce S.left).Colorable 4 := by
  exact induce_colorable_of_smaller_induction_global_no_model
    (G := G) hIH S.left (S.natCard_left_lt_of_proper hproper) hno_model

theorem right_induce_colorable_of_smaller_induction_global_no_model
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    (G.induce S.right).Colorable 4 :=
  left_induce_colorable_of_smaller_induction_global_no_model
    (G := G) hIH S.symm ((S.proper_symm).2 hproper) hno_model

theorem left_induce_no_nil_model_of_global_no_nil_model
    {G : SimpleGraph V}
    (S : Separation G)
    (hno_model :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique G))) :
    Not (CompatibleDominatingK5Model
      (OrderedClique.nil : OrderedClique (G.induce S.left))) := by
  intro hside
  exact hno_model
    (deletion_lifts_nil_compatible_model (G := G) S.left
      (OrderedClique.nil : OrderedClique (G.induce S.left)) hside)

theorem right_separator_clique_colorable_of_smaller_induction
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hno_model :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique))) :
    S.rightWithSeparatorClique.Colorable 4 :=
  left_separator_clique_colorable_of_smaller_induction
    (G := G) hIH S.symm ((S.proper_symm).2 hproper) hno_model

theorem right_separator_clique_colorable_of_smaller_induction_with_ordered_clique
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (L : OrderedClique G)
    (hright : L.vertexSet ⊆ S.right)
    (hno_model :
      Not (CompatibleDominatingK5Model (S.rightOrderedClique L hright))) :
    S.rightWithSeparatorClique.Colorable 4 :=
  left_separator_clique_colorable_of_smaller_induction_with_ordered_clique
    (G := G) hIH S.symm ((S.proper_symm).2 hproper) L hright hno_model

theorem right_separator_clique_colorable_of_smaller_induction_global_no_model
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hright : L.vertexSet ⊆ S.right)
    (hseparator_clique : G.IsClique S.separator)
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    S.rightWithSeparatorClique.Colorable 4 :=
  left_separator_clique_colorable_of_smaller_induction_global_no_model
    (G := G) hIH S.symm ((S.proper_symm).2 hproper) hright
      (by simpa only [S.separator_symm] using hseparator_clique) hno_model

theorem right_separator_clique_colorable_of_smaller_induction_global_no_model_restrict
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hseparator_clique : G.IsClique S.separator)
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    S.rightWithSeparatorClique.Colorable 4 := by
  classical
  letI : Fintype S.right := S.right.toFinite.fintype
  have hcard_lt : Fintype.card S.right < Fintype.card V := by
    have hnat := S.natCard_right_lt_of_proper hproper
    simpa [Nat.card_eq_fintype_card] using hnat
  rcases hIH S.rightWithSeparatorClique hcard_lt
      (S.rightRestrictedOrderedClique L) with hcolor | hmodel
  · exact hcolor
  · exact False.elim
      ((no_model_rightWithSeparatorClique_restrict_of_global_no_model_of_separator_clique
        S L hseparator_clique hno_model) hmodel)

theorem right_color_class_quotient_colorable_of_smaller_induction
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
    (contractionTargetGraph S.rightWithSeparatorClique
      (S.rightColorClassQuotientMap left_coloring)).Colorable 4 := by
  classical
  have hcard_lt :
      Fintype.card (S.rightColorClassTarget left_coloring) < Fintype.card V :=
    S.rightColorClassTarget_card_lt_of_proper left_coloring hproper
  rcases hIH
      (contractionTargetGraph S.rightWithSeparatorClique
        (S.rightColorClassQuotientMap left_coloring))
      hcard_lt
      (OrderedClique.nil : OrderedClique
        (contractionTargetGraph S.rightWithSeparatorClique
          (S.rightColorClassQuotientMap left_coloring))) with hcolor | hmodel
  · exact hcolor
  · exact False.elim (hno_model hmodel)

theorem right_color_class_quotient_model_contains_K5_minor_of_separator_clique
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hmodel :
      CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (contractionTargetGraph S.rightWithSeparatorClique
            (S.rightColorClassQuotientMap left_coloring)))) :
    ContainsMinor K5Graph G := by
  classical
  let C : GraphContraction S.rightWithSeparatorClique :=
    S.rightColorClassContraction left_coloring
  have hmodelC :
      CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique C.graph) := by
    simpa [C, Separation.rightColorClassContraction_graph_eq] using hmodel
  have hminor_side : ContainsMinor K5Graph S.rightWithSeparatorClique :=
    compatible_quotient_contains_K5_minor_lift C hmodelC
  exact hminor_side.map (S.rightWithSeparatorCliqueHom hseparator_clique)
    Subtype.val_injective

theorem right_color_class_quotient_model_contains_K5_minor_in_augmented_right
    (S : Separation G)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hmodel :
      CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (contractionTargetGraph S.rightWithSeparatorClique
            (S.rightColorClassQuotientMap left_coloring)))) :
    ContainsMinor K5Graph S.rightWithSeparatorClique := by
  classical
  let C : GraphContraction S.rightWithSeparatorClique :=
    S.rightColorClassContraction left_coloring
  have hmodelC :
      CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique C.graph) := by
    simpa [C, Separation.rightColorClassContraction_graph_eq] using hmodel
  exact compatible_quotient_contains_K5_minor_lift C hmodelC

theorem right_color_class_contraction_nil_model_lifts_of_singleton_branch_fibers
    (S : Separation G)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hsingle :
      forall Tq : DominatingK5Model (S.rightColorClassContraction left_coloring).graph,
        LCompatible
            (OrderedClique.nil :
              OrderedClique (S.rightColorClassContraction left_coloring).graph) Tq ->
          forall j : Fin 5,
            forall y : (S.rightColorClassContraction left_coloring).Target,
              y ∈ (Tq.branch j).verts ->
                forall v w : S.right,
                  (S.rightColorClassContraction left_coloring).map v = y ->
                    (S.rightColorClassContraction left_coloring).map w = y ->
                      v = w) :
    CompatibleDominatingK5Model
        (OrderedClique.nil :
          OrderedClique (S.rightColorClassContraction left_coloring).graph) ->
      CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique) := by
  classical
  let C : GraphContraction S.rightWithSeparatorClique :=
    S.rightColorClassContraction left_coloring
  exact contraction_lifts_compatible_of_singleton_branch_fibers
    (G := S.rightWithSeparatorClique)
    (L := (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique))
    C
    (OrderedClique.nil : OrderedClique C.graph)
    OrderedCliqueContractionImage.nil
    (by
      intro Tq hTq j y hy v w hv hw
      exact hsingle Tq (by simpa [C] using hTq) j y hy v w
        (by simpa [C] using hv) (by simpa [C] using hw))

theorem right_color_class_quotient_nil_model_lifts_to_augmented_right_of_separator_color_injective
    (S : Separation G)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hseparator_color_injective :
      forall a b : S.separator,
        left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩ ->
          a = b) :
    CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (contractionTargetGraph S.rightWithSeparatorClique
            (S.rightColorClassQuotientMap left_coloring))) ->
      CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique) := by
  classical
  intro hmodel
  have hmodelC :
      CompatibleDominatingK5Model
        (OrderedClique.nil :
          OrderedClique (S.rightColorClassContraction left_coloring).graph) := by
    simpa [Separation.rightColorClassContraction_graph_eq] using hmodel
  exact right_color_class_contraction_nil_model_lifts_of_singleton_branch_fibers
    (G := G) S left_coloring
    (by
      intro _Tq _hTq _j y _hy v w hv hw
      exact S.rightColorClassContraction_fiber_singleton_of_separator_color_injective
        left_coloring hseparator_color_injective y v w hv hw)
    hmodelC

theorem no_right_color_class_quotient_nil_model_of_no_augmented_right_model_of_separator_color_injective
    (S : Separation G)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hseparator_color_injective :
      forall a b : S.separator,
        left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩ ->
          a = b)
    (hno_augmented_right :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique))) :
    Not (CompatibleDominatingK5Model
      (OrderedClique.nil : OrderedClique
        (contractionTargetGraph S.rightWithSeparatorClique
          (S.rightColorClassQuotientMap left_coloring)))) := by
  intro hmodel
  exact hno_augmented_right
    (right_color_class_quotient_nil_model_lifts_to_augmented_right_of_separator_color_injective
      (G := G) S left_coloring hseparator_color_injective hmodel)

theorem right_color_class_quotient_nil_model_lifts_global_of_separator_clique_of_singleton_branch_fibers
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hsingle :
      forall Tq : DominatingK5Model (S.rightColorClassContraction left_coloring).graph,
        LCompatible
            (OrderedClique.nil :
              OrderedClique (S.rightColorClassContraction left_coloring).graph) Tq ->
          forall j : Fin 5,
            forall y : (S.rightColorClassContraction left_coloring).Target,
              y ∈ (Tq.branch j).verts ->
                forall v w : S.right,
                  (S.rightColorClassContraction left_coloring).map v = y ->
                    (S.rightColorClassContraction left_coloring).map w = y ->
                      v = w) :
    CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (contractionTargetGraph S.rightWithSeparatorClique
            (S.rightColorClassQuotientMap left_coloring))) ->
      CompatibleDominatingK5Model (OrderedClique.nil : OrderedClique G) := by
  classical
  intro hmodel
  have hmodelC :
      CompatibleDominatingK5Model
        (OrderedClique.nil :
          OrderedClique (S.rightColorClassContraction left_coloring).graph) := by
    simpa [Separation.rightColorClassContraction_graph_eq] using hmodel
  exact compatible_nil_model_lift_rightWithSeparatorClique_of_separator_clique
    S hseparator_clique
    (right_color_class_contraction_nil_model_lifts_of_singleton_branch_fibers
      (G := G) S left_coloring hsingle hmodelC)

theorem right_color_class_quotient_nil_model_lifts_global_of_separator_clique
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator)
    (left_coloring : (G.induce S.left).Coloring (Fin 4)) :
    CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (contractionTargetGraph S.rightWithSeparatorClique
            (S.rightColorClassQuotientMap left_coloring))) ->
      CompatibleDominatingK5Model (OrderedClique.nil : OrderedClique G) := by
  classical
  have hseparator_color_injective :
      forall a b : S.separator,
        left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩ ->
          a = b :=
    S.leftColoring_injective_on_separator_of_separator_clique
      left_coloring hseparator_clique
  refine
    right_color_class_quotient_nil_model_lifts_global_of_separator_clique_of_singleton_branch_fibers
      (G := G) S hseparator_clique left_coloring ?_
  intro Tq _hTq j y _hy v w hv hw
  exact S.rightColorClassContraction_fiber_singleton_of_separator_color_injective
    left_coloring hseparator_color_injective y v w hv hw

theorem no_right_color_class_quotient_nil_model_of_global_no_nil_model_of_separator_clique
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator)
    (hno_model :
      Not (CompatibleDominatingK5Model (OrderedClique.nil : OrderedClique G)))
    (left_coloring : (G.induce S.left).Coloring (Fin 4)) :
    Not (CompatibleDominatingK5Model
      (OrderedClique.nil : OrderedClique
        (contractionTargetGraph S.rightWithSeparatorClique
          (S.rightColorClassQuotientMap left_coloring)))) := by
  intro hmodel
  exact hno_model
    (right_color_class_quotient_nil_model_lifts_global_of_separator_clique
      (G := G) S hseparator_clique left_coloring hmodel)

theorem right_color_class_quotient_colorable_of_rightWithSeparatorClique_colorable_of_separator_color_injective
    (S : Separation G)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hseparator_color_injective :
      forall a b : S.separator,
        left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩ ->
          a = b)
    (hright : S.rightWithSeparatorClique.Colorable 4) :
    (contractionTargetGraph S.rightWithSeparatorClique
      (S.rightColorClassQuotientMap left_coloring)).Colorable 4 := by
  classical
  let C : GraphContraction S.rightWithSeparatorClique :=
    S.rightColorClassContraction left_coloring
  have hinj : Function.Injective C.map := by
    simpa [C, Separation.rightColorClassContraction, GraphContraction.ofMap] using
      S.rightColorClassQuotientMap_injective_of_separator_color_injective
        left_coloring hseparator_color_injective
  have htarget : C.graph.Colorable 4 :=
    GraphContraction.target_colorable_of_colorable_of_injective C hinj hright
  simpa [C, Separation.rightColorClassContraction_graph_eq] using htarget

theorem right_color_class_quotient_colorable_of_rightWithSeparatorClique_colorable_of_separator_clique
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator)
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hright : S.rightWithSeparatorClique.Colorable 4) :
    (contractionTargetGraph S.rightWithSeparatorClique
      (S.rightColorClassQuotientMap left_coloring)).Colorable 4 := by
  exact
    right_color_class_quotient_colorable_of_rightWithSeparatorClique_colorable_of_separator_color_injective
      (G := G) S left_coloring
      (S.leftColoring_injective_on_separator_of_separator_clique
        left_coloring hseparator_clique)
      hright

theorem right_color_class_quotient_colorable_of_rightWithSeparatorClique_colorable_of_triple_colors_distinct
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V))
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hxy_color :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩)
    (hxz_color :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩)
    (hyz_color :
      left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ≠
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩)
    (hright : S.rightWithSeparatorClique.Colorable 4) :
    (contractionTargetGraph S.rightWithSeparatorClique
      (S.rightColorClassQuotientMap left_coloring)).Colorable 4 := by
  exact
    right_color_class_quotient_colorable_of_rightWithSeparatorClique_colorable_of_separator_color_injective
      (G := G) S left_coloring
      (S.leftColoring_injective_on_triple_separator_of_pairwise_ne
        left_coloring hseparator hxy_color hxz_color hyz_color)
      hright

theorem colorable_of_triple_separation_rightWithSeparatorClique_colorable_of_distinct_left_colors
    [Fintype V]
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V))
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hxy_color :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩)
    (hxz_color :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩)
    (hyz_color :
      left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ≠
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩)
    (hright : S.rightWithSeparatorClique.Colorable 4) :
    G.Colorable 4 := by
  exact colorable_of_separation_right_color_class_range_quotient S left_coloring
    (right_color_class_quotient_colorable_of_rightWithSeparatorClique_colorable_of_triple_colors_distinct
      (G := G) S hseparator left_coloring hxy_color hxz_color hyz_color hright)


end Schematic.Math.GraphTheory
