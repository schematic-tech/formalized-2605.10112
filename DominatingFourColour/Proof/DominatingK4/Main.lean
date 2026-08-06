import DominatingFourColour.Proof.DominatingK4.Complete
import DominatingFourColour.Proof.DominatingK4.Separations
import DominatingFourColour.Proof.DominatingK4.TwoConnected

/-!
The dominating-K4 lemma, following the article's induction and cycle-rerouting proof.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph
open DominatingK4

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem lemma_dominating_K4
    [Fintype V] [DecidableRel G.Adj]
    (h_connected : G.Connected)
    (h_card : 4 <= Fintype.card V)
    (L : Finset V)
    (h_clique : G.IsClique (L : Set V))
    (h_card_L : L.card <= 2)
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L)
    (h_high_degree_L_singleton :
      (Exists fun v : V => v ∈ L ∧ 3 <= G.degree v) -> L.card = 1) :
    Exists fun T : DominatingK4Model G =>
      forall v : V, v ∈ L -> v ∈ (T.branch (0 : Fin 4)).verts := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n IH =>
      have IH' : InductionHypothesis.{u} (Fintype.card V) := by
        intro W _ H _ hlt hconn hcardW LW hcliqueW hcardLW hlowW hhighW
        have hlt_n : Fintype.card W < n := by
          simpa [hn] using hlt
        exact IH (Fintype.card W) hlt_n (V := W) (G := H)
          hconn hcardW LW hcliqueW hcardLW hlowW hhighW rfl
      by_cases h_complete : forall u v : V, u ≠ v -> G.Adj u v
      · by_cases hL_empty : L.card = 0
        · obtain ⟨T⟩ :=
            exists_dominating_K4_model_of_complete
              (G := G) h_card h_complete
          refine ⟨T, ?_⟩
          intro v hv
          have hL_eq_empty : L = ∅ := Finset.card_eq_zero.mp hL_empty
          simp [hL_eq_empty] at hv
        · have hL_pos : 0 < L.card := Nat.pos_of_ne_zero hL_empty
          obtain ⟨v, hvL⟩ := Finset.card_pos.mp hL_pos
          have hdeg : 3 <= G.degree v :=
            degree_atLeast_three_of_complete (G := G) h_card h_complete v
          have hL_card_one : L.card = 1 :=
            h_high_degree_L_singleton ⟨v, hvL, hdeg⟩
          obtain ⟨T, hvT⟩ :=
            exists_dominating_K4_model_of_complete_with_first
              (G := G) h_card h_complete v
          refine ⟨T, ?_⟩
          intro w hwL
          obtain ⟨a, hLa⟩ := Finset.card_eq_one.mp hL_card_one
          have hv_eq_a : v = a := by
            simpa [hLa] using hvL
          have hw_eq_v : w = v := by
            have hw_eq_a : w = a := by
              simpa [hLa] using hwL
            exact hw_eq_a.trans hv_eq_a.symm
          simpa [hw_eq_v] using hvT
      · by_cases h_card_four : Fintype.card V = 4
        · exact False.elim (h_complete
            (complete_of_card_four_low_degree_clique
              (G := G) h_card_four L h_clique h_low_degree_in_L))
        · by_cases h_two_connected : IsTwoConnected G
          · exact lemma_dominating_K4_of_two_connected
              (G := G) h_two_connected h_card L h_clique h_card_L
              h_low_degree_in_L h_high_degree_L_singleton
          · exact lemma_dominating_K4_of_not_two_connected
              (G := G) IH' h_connected h_card h_two_connected
              L h_clique h_low_degree_in_L

end Schematic.Math.GraphTheory
