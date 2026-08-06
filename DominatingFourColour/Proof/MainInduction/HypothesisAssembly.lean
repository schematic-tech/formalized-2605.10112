import DominatingFourColour.Proof.MainInduction.PairQuotients

/-! Assembly of the smaller-induction and separation hypotheses. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem no_small_separation_of_smaller_induction_and_color_class_quotient_exclusions
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    (hno_left_model :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          Not (CompatibleDominatingK5Model
            (OrderedClique.nil : OrderedClique (G.induce S.left))))
    (hno_right_quotient_model :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          forall left_coloring : (G.induce S.left).Coloring (Fin 4),
            Not (CompatibleDominatingK5Model
              (OrderedClique.nil : OrderedClique
                (contractionTargetGraph S.rightWithSeparatorClique
                  (S.rightColorClassQuotientMap left_coloring))))) :
    forall S : Separation G, S.Proper -> S.OrderAtMost 3 -> False := by
    intro S hproper horder
    exact hnot_four_colorable
      (colorable_of_separation_left_and_right_color_class_quotients_no_model
        (G := G) hIH S hproper
        (hno_left_model S hproper horder)
        (hno_right_quotient_model S hproper horder))

theorem no_small_separation_of_smaller_induction_and_global_no_model_and_right_quotient_exclusions
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    (hno_model : Not (CompatibleDominatingK5Model L))
    (hno_right_quotient_model :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          forall left_coloring : (G.induce S.left).Coloring (Fin 4),
            Not (CompatibleDominatingK5Model
              (OrderedClique.nil : OrderedClique
                (contractionTargetGraph S.rightWithSeparatorClique
                  (S.rightColorClassQuotientMap left_coloring))))) :
    forall S : Separation G, S.Proper -> S.OrderAtMost 3 -> False := by
  intro S hproper horder
  exact hnot_four_colorable
    (colorable_of_separation_global_no_model_and_right_color_class_quotients_no_model
      (G := G) hIH S hproper hno_model
      (hno_right_quotient_model S hproper horder))

theorem no_small_separation_of_smaller_induction_and_global_no_model_and_right_quotient_colorings
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    (hno_model : Not (CompatibleDominatingK5Model L))
    (hright_quotient_colorable :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          forall left_coloring : (G.induce S.left).Coloring (Fin 4),
            (contractionTargetGraph S.rightWithSeparatorClique
              (S.rightColorClassQuotientMap left_coloring)).Colorable 4) :
    forall S : Separation G, S.Proper -> S.OrderAtMost 3 -> False := by
  intro S hproper horder
  exact hnot_four_colorable
    (colorable_of_separation_global_no_model_and_right_color_class_quotients_colorable
      (G := G) hIH S hproper hno_model
      (hright_quotient_colorable S hproper horder))

theorem exists_pair_counterexample_of_smaller_induction_and_color_class_quotient_exclusions
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    (hno_model : Not (CompatibleDominatingK5Model L))
    (hno_left_model :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          Not (CompatibleDominatingK5Model
            (OrderedClique.nil : OrderedClique (G.induce S.left))))
    (hno_right_quotient_model :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          forall left_coloring : (G.induce S.left).Coloring (Fin 4),
            Not (CompatibleDominatingK5Model
              (OrderedClique.nil : OrderedClique
                (contractionTargetGraph S.rightWithSeparatorClique
                  (S.rightColorClassQuotientMap left_coloring))))) :
    Exists fun L' : OrderedClique G =>
      L.InitialSegment L' ∧ L'.length = 2 ∧
        MainInductionCounterexample G L' := by
    exact exists_pair_counterexample_of_smaller_induction_and_no_small_separations
      (G := G) hIH hnot_four_colorable hno_model
      (no_small_separation_of_smaller_induction_and_color_class_quotient_exclusions
        (G := G) hIH hnot_four_colorable hno_left_model hno_right_quotient_model)

theorem exists_pair_counterexample_of_smaller_induction_and_global_no_model_and_right_quotient_exclusions
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    (hno_model : Not (CompatibleDominatingK5Model L))
    (hno_right_quotient_model :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          forall left_coloring : (G.induce S.left).Coloring (Fin 4),
            Not (CompatibleDominatingK5Model
              (OrderedClique.nil : OrderedClique
                (contractionTargetGraph S.rightWithSeparatorClique
                  (S.rightColorClassQuotientMap left_coloring))))) :
    Exists fun L' : OrderedClique G =>
      L.InitialSegment L' ∧ L'.length = 2 ∧
        MainInductionCounterexample G L' := by
  exact exists_pair_counterexample_of_smaller_induction_and_no_small_separations
    (G := G) hIH hnot_four_colorable hno_model
    (no_small_separation_of_smaller_induction_and_global_no_model_and_right_quotient_exclusions
      (G := G) hIH hnot_four_colorable hno_model hno_right_quotient_model)

theorem exists_pair_counterexample_of_smaller_induction_and_global_no_model_and_right_quotient_colorings
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    (hno_model : Not (CompatibleDominatingK5Model L))
    (hright_quotient_colorable :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          forall left_coloring : (G.induce S.left).Coloring (Fin 4),
            (contractionTargetGraph S.rightWithSeparatorClique
              (S.rightColorClassQuotientMap left_coloring)).Colorable 4) :
    Exists fun L' : OrderedClique G =>
      L.InitialSegment L' ∧ L'.length = 2 ∧
        MainInductionCounterexample G L' := by
  exact exists_pair_counterexample_of_smaller_induction_and_no_small_separations
    (G := G) hIH hnot_four_colorable hno_model
    (no_small_separation_of_smaller_induction_and_global_no_model_and_right_quotient_colorings
      (G := G) hIH hnot_four_colorable hno_model hright_quotient_colorable)

private theorem pair_counterexample_absurd_of_smaller_induction
    [Fintype V] [DecidableEq V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    {L : OrderedClique G}
    (hlen : L.length = 2)
    (C : MainInductionCounterexample G L) : False := by
  classical
  cases L with
  | nil =>
      simp [OrderedClique.length] at hlen
  | single v =>
      simp [OrderedClique.length] at hlen
  | pair v1 v2 edge =>
      exact counterexample_absurd_of_final_collapse_minimality
        (G := G) C (by
          intro u hu_ne_v2 hdeg hcard_lt hno_model
          exact final_collapse_colorable_of_smaller_induction
            (G := G) (edge := edge) hIH u hu_ne_v2 hcard_lt hno_model)

theorem main_induction_hypothesis_of_smaller_induction_and_right_quotient_exclusions
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (L : OrderedClique G)
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hno_right_quotient_model :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          forall left_coloring : (G.induce S.left).Coloring (Fin 4),
            Not (CompatibleDominatingK5Model
              (OrderedClique.nil : OrderedClique
                (contractionTargetGraph S.rightWithSeparatorClique
                  (S.rightColorClassQuotientMap left_coloring))))) :
    G.Colorable 4 ∨ CompatibleDominatingK5Model L := by
  classical
  by_cases hcolor : G.Colorable 4
  · exact Or.inl hcolor
  · by_cases hmodel : CompatibleDominatingK5Model L
    · exact Or.inr hmodel
    · obtain ⟨L', _hinit, hlen, C⟩ :=
        exists_pair_counterexample_of_smaller_induction_and_global_no_model_and_right_quotient_exclusions
          (G := G) hIH hcolor hmodel hno_right_quotient_model
      exact False.elim (pair_counterexample_absurd_of_smaller_induction hIH hlen C)

theorem main_induction_hypothesis_of_smaller_induction_and_right_quotient_colorings
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (L : OrderedClique G)
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hright_quotient_colorable :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          forall left_coloring : (G.induce S.left).Coloring (Fin 4),
            (contractionTargetGraph S.rightWithSeparatorClique
              (S.rightColorClassQuotientMap left_coloring)).Colorable 4) :
    G.Colorable 4 ∨ CompatibleDominatingK5Model L := by
  classical
  by_cases hcolor : G.Colorable 4
  · exact Or.inl hcolor
  · by_cases hmodel : CompatibleDominatingK5Model L
    · exact Or.inr hmodel
    · obtain ⟨L', _hinit, hlen, C⟩ :=
        exists_pair_counterexample_of_smaller_induction_and_global_no_model_and_right_quotient_colorings
          (G := G) hIH hcolor hmodel hright_quotient_colorable
      exact False.elim (pair_counterexample_absurd_of_smaller_induction hIH hlen C)

theorem main_induction_hypothesis_of_smaller_induction_and_pair_right_quotient_colorings
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (L : OrderedClique G)
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hpair_right_quotient_colorable :
      forall Lpair : OrderedClique G,
        L.InitialSegment Lpair ->
          Lpair.length = 2 ->
            Not (CompatibleDominatingK5Model Lpair) ->
              forall S : Separation G,
                S.Proper -> S.OrderAtMost 3 ->
                  forall left_coloring : (G.induce S.left).Coloring (Fin 4),
                    (contractionTargetGraph S.rightWithSeparatorClique
                      (S.rightColorClassQuotientMap left_coloring)).Colorable 4) :
    G.Colorable 4 ∨ CompatibleDominatingK5Model L := by
  classical
  by_cases hcolor : G.Colorable 4
  · exact Or.inl hcolor
  · by_cases hmodel : CompatibleDominatingK5Model L
    · exact Or.inr hmodel
    · obtain ⟨L', hinit, hlen, hno_model_L', hvertex_minimal⟩ :=
        exists_pair_extension_no_compatible_of_smaller_induction
          (G := G) hIH hcolor hmodel
      have hno_small :
          forall S : Separation G, S.Proper -> S.OrderAtMost 3 -> False := by
        exact
          no_small_separation_of_smaller_induction_and_global_no_model_and_right_quotient_colorings
            (G := G) hIH hcolor hno_model_L'
            (hpair_right_quotient_colorable L' hinit hlen hno_model_L')
      let C : MainInductionCounterexample G L' := {
        not_four_colorable := hcolor
        no_compatible_model := hno_model_L'
        vertex_minimal := hvertex_minimal
        clique_maximal := by
          intro L'' _hinit' _hno
          rw [hlen]
          cases L'' <;> simp [OrderedClique.length]
        no_proper_separation_orderAtMost_three := hno_small
      }
      exact False.elim (pair_counterexample_absurd_of_smaller_induction hIH hlen C)

theorem main_induction_hypothesis_of_smaller_induction_and_pair_small_separation_colorings
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (L : OrderedClique G)
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hpair_small_separation_colorable :
      forall Lpair : OrderedClique G,
        L.InitialSegment Lpair ->
          Lpair.length = 2 ->
            Not (CompatibleDominatingK5Model Lpair) ->
              forall S : Separation G,
                S.Proper -> S.OrderAtMost 3 -> G.Colorable 4) :
    G.Colorable 4 ∨ CompatibleDominatingK5Model L := by
  classical
  by_cases hcolor : G.Colorable 4
  · exact Or.inl hcolor
  · by_cases hmodel : CompatibleDominatingK5Model L
    · exact Or.inr hmodel
    · obtain ⟨L', hinit, hlen, hno_model_L', hvertex_minimal⟩ :=
        exists_pair_extension_no_compatible_of_smaller_induction
          (G := G) hIH hcolor hmodel
      have hno_small :
          forall S : Separation G, S.Proper -> S.OrderAtMost 3 -> False := by
        intro S hproper horder
        exact hcolor
          (hpair_small_separation_colorable L' hinit hlen hno_model_L'
            S hproper horder)
      let C : MainInductionCounterexample G L' := {
        not_four_colorable := hcolor
        no_compatible_model := hno_model_L'
        vertex_minimal := hvertex_minimal
        clique_maximal := by
          intro L'' _hinit' _hno
          rw [hlen]
          cases L'' <;> simp [OrderedClique.length]
        no_proper_separation_orderAtMost_three := hno_small
      }
      exact False.elim (pair_counterexample_absurd_of_smaller_induction hIH hlen C)

theorem separator_clique_side_colorings_of_smaller_induction
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hno_side_models :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          Not (CompatibleDominatingK5Model
            (OrderedClique.nil : OrderedClique S.leftWithSeparatorClique)) ∧
            Not (CompatibleDominatingK5Model
              (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique))) :
    forall S : Separation G,
      S.Proper -> S.OrderAtMost 3 ->
        S.leftWithSeparatorClique.Colorable 4 ∧
          S.rightWithSeparatorClique.Colorable 4 := by
  intro S hproper horder
  exact ⟨
    left_separator_clique_colorable_of_smaller_induction
      (G := G) hIH S hproper (hno_side_models S hproper horder).1,
      right_separator_clique_colorable_of_smaller_induction
        (G := G) hIH S hproper (hno_side_models S hproper horder).2⟩

theorem separator_clique_side_colorings_of_smaller_induction_global_no_nil_model
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hno_model :
      Not (CompatibleDominatingK5Model (OrderedClique.nil : OrderedClique G)))
    (S : Separation G)
    (hproper : S.Proper)
    (hseparator_clique : G.IsClique S.separator) :
    S.leftWithSeparatorClique.Colorable 4 ∧
      S.rightWithSeparatorClique.Colorable 4 := by
  exact ⟨
    left_separator_clique_colorable_of_smaller_induction
      (G := G) hIH S hproper
      (no_nil_model_leftWithSeparatorClique_of_global_no_nil_model_of_separator_clique
        S hseparator_clique hno_model),
    right_separator_clique_colorable_of_smaller_induction
      (G := G) hIH S hproper
      (no_nil_model_rightWithSeparatorClique_of_global_no_nil_model_of_separator_clique
        S hseparator_clique hno_model)⟩

theorem separator_clique_side_colorings_of_smaller_induction_global_no_model_of_ordered_clique_subset_separator
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hno_model : Not (CompatibleDominatingK5Model L))
    (S : Separation G)
    (hproper : S.Proper)
    (hseparator_clique : G.IsClique S.separator)
    (hL_separator : L.vertexSet ⊆ S.separator) :
    S.leftWithSeparatorClique.Colorable 4 ∧
      S.rightWithSeparatorClique.Colorable 4 := by
  have hleft : L.vertexSet ⊆ S.left := by
    intro v hv
    exact (hL_separator hv).1
  have hright : L.vertexSet ⊆ S.right := by
    intro v hv
    exact (hL_separator hv).2
  exact ⟨
    left_separator_clique_colorable_of_smaller_induction_global_no_model
      (G := G) hIH S hproper hleft hseparator_clique hno_model,
    right_separator_clique_colorable_of_smaller_induction_global_no_model
      (G := G) hIH S hproper hright hseparator_clique hno_model⟩

theorem no_proper_clique_separator_containing_ordered_clique_of_smaller_induction
    [Fintype V]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    (hno_model : Not (CompatibleDominatingK5Model L))
    (S : Separation G)
    (hproper : S.Proper)
    (hseparator_clique : G.IsClique S.separator)
    (hL_separator : L.vertexSet ⊆ S.separator) :
    False := by
  have hside :=
    separator_clique_side_colorings_of_smaller_induction_global_no_model_of_ordered_clique_subset_separator
      (G := G) hIH hno_model S hproper hseparator_clique hL_separator
  exact hnot_four_colorable
    (colorable_of_separation_with_separator_clique_colorings S hside.1 hside.2)

theorem exists_pair_counterexample_of_smaller_induction_and_separator_clique_side_colorings
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    (hno_model : Not (CompatibleDominatingK5Model L))
    (hseparator_side_colorings :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          S.leftWithSeparatorClique.Colorable 4 ∧
            S.rightWithSeparatorClique.Colorable 4) :
    Exists fun L' : OrderedClique G =>
      L.InitialSegment L' ∧ L'.length = 2 ∧
        MainInductionCounterexample G L' := by
  classical
  refine exists_pair_counterexample_of_smaller_induction_and_no_small_separations
    (G := G) hIH hnot_four_colorable hno_model ?_
  intro S hproper horder
  exact hnot_four_colorable
    (colorable_of_separation_with_separator_clique_colorings S
      (hseparator_side_colorings S hproper horder).1
      (hseparator_side_colorings S hproper horder).2)

theorem exists_pair_counterexample_of_smaller_induction_and_no_separator_side_models
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {L : OrderedClique G}
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    (hno_model : Not (CompatibleDominatingK5Model L))
    (hno_side_models :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          Not (CompatibleDominatingK5Model
            (OrderedClique.nil : OrderedClique S.leftWithSeparatorClique)) ∧
            Not (CompatibleDominatingK5Model
              (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique))) :
    Exists fun L' : OrderedClique G =>
      L.InitialSegment L' ∧ L'.length = 2 ∧
        MainInductionCounterexample G L' := by
  exact exists_pair_counterexample_of_smaller_induction_and_separator_clique_side_colorings
    (G := G) hIH hnot_four_colorable hno_model
    (separator_clique_side_colorings_of_smaller_induction
      (G := G) hIH hno_side_models)

theorem main_induction_hypothesis_of_smaller_induction_and_no_separator_side_models
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (L : OrderedClique G)
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hno_side_models :
      forall S : Separation G,
        S.Proper -> S.OrderAtMost 3 ->
          Not (CompatibleDominatingK5Model
            (OrderedClique.nil : OrderedClique S.leftWithSeparatorClique)) ∧
            Not (CompatibleDominatingK5Model
              (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique))) :
    G.Colorable 4 ∨ CompatibleDominatingK5Model L := by
  classical
  by_cases hcolor : G.Colorable 4
  · exact Or.inl hcolor
  · by_cases hmodel : CompatibleDominatingK5Model L
    · exact Or.inr hmodel
    · obtain ⟨L', _hinit, hlen, C⟩ :=
        exists_pair_counterexample_of_smaller_induction_and_no_separator_side_models
          (G := G) hIH hcolor hmodel hno_side_models
      exact False.elim (pair_counterexample_absurd_of_smaller_induction hIH hlen C)

theorem main_induction_hypothesis_of_no_separator_side_models_all
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (G : SimpleGraph V)
    (L : OrderedClique G)
    (hno_side_models_all :
      forall {W : Type u} [Fintype W] [DecidableEq W],
        forall H : SimpleGraph W, [DecidableRel H.Adj] ->
          forall S : Separation H,
            S.Proper -> S.OrderAtMost 3 ->
              Not (CompatibleDominatingK5Model
                (OrderedClique.nil : OrderedClique S.leftWithSeparatorClique)) ∧
              Not (CompatibleDominatingK5Model
                (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique))) :
    G.Colorable 4 ∨ CompatibleDominatingK5Model L := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n IH =>
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
          (V := W) (G := H) H Lw rfl
      exact main_induction_hypothesis_of_smaller_induction_and_no_separator_side_models
        G L hIH
        (by
          intro S hproper horder
          exact hno_side_models_all (H := G) S hproper horder)

theorem main_induction_hypothesis_of_complete
    [Fintype V]
    (G : SimpleGraph V)
    (L : OrderedClique G)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v) :
    G.Colorable 4 ∨ CompatibleDominatingK5Model L := by
  classical
  by_cases h_card : 5 <= Fintype.card V
  · exact Or.inr
      (compatible_dominating_K5_model_of_complete_card_ge_five h_card h_complete L)
  · have h_card_le : Fintype.card V <= 4 := by omega
    exact Or.inl
      (SimpleGraph.Colorable.mono h_card_le G.colorable_of_fintype)


end Schematic.Math.GraphTheory
