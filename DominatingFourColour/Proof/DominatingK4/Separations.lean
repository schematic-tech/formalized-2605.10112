import DominatingFourColour.Proof.DominatingK4.BranchEnlargement

/-!
The non-two-connected case of the dominating-K4 induction.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace DominatingK4

/-- The induction contract used by the separation branch of `lemma_dominating_K4`. -/
def InductionHypothesis (n : Nat) : Prop :=
  forall {W : Type u} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
    Fintype.card W < n ->
      H.Connected ->
        4 <= Fintype.card W ->
          forall L : Finset W,
            H.IsClique (L : Set W) ->
              L.card <= 2 ->
                (forall v : W, H.degree v <= 2 -> v ∈ L) ->
                  ((Exists fun v : W => v ∈ L ∧ 3 <= H.degree v) -> L.card = 1) ->
                    Exists fun T : DominatingK4Model H =>
                      forall v : W, v ∈ L -> v ∈ (T.branch (0 : Fin 4)).verts

theorem right_side_low_degree_only_separator
    [Fintype V] [DecidableRel G.Adj]
    (S : Separation G)
    [Fintype S.right] [DecidableRel (G.induce S.right).Adj]
    {sep : V}
    (hsep_right : sep ∈ S.right)
    (hseparator_unique : forall x : V, x ∈ S.left -> x ∈ S.right -> x = sep)
    (L : Finset V)
    (hL_subset_left : forall v : V, v ∈ L -> v ∈ S.left)
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L) :
    forall v : S.right,
      (G.induce S.right).degree v <= 2 ->
        v = ⟨sep, hsep_right⟩ := by
  intro v hv_degree
  by_cases hv_left : (v : V) ∈ S.left
  · exact Subtype.ext (hseparator_unique v hv_left v.2)
  · have hdegree_eq :
        (G.induce S.right).degree v = G.degree (v : V) :=
      S.degree_induce_right_eq_of_mem_right_not_left v.2 hv_left
    have hv_low_G : G.degree (v : V) <= 2 := by
      simpa [hdegree_eq] using hv_degree
    have hvL : (v : V) ∈ L := h_low_degree_in_L v hv_low_G
    exact False.elim (hv_left (hL_subset_left v hvL))

theorem right_side_card_atLeast_four_of_left_low_degree_clique
    [Fintype V] [DecidableRel G.Adj]
    (S : Separation G)
    [Fintype S.right] [DecidableRel (G.induce S.right).Adj]
    (hproper : S.Proper)
    (L : Finset V)
    (hL_subset_left : forall v : V, v ∈ L -> v ∈ S.left)
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L) :
    4 <= Fintype.card S.right := by
  rcases hproper.2 with ⟨v, hv_right, hv_not_left⟩
  have hv_not_low : ¬ G.degree v <= 2 := by
    intro hv_low
    exact hv_not_left (hL_subset_left v (h_low_degree_in_L v hv_low))
  have hv_degree : 3 <= G.degree v := by omega
  have hdegree_eq :
      (G.induce S.right).degree ⟨v, hv_right⟩ = G.degree v :=
    S.degree_induce_right_eq_of_mem_right_not_left hv_right hv_not_left
  have hdegree_right : 3 <= (G.induce S.right).degree ⟨v, hv_right⟩ := by
    simpa [hdegree_eq]
  have hlt :
      (G.induce S.right).degree ⟨v, hv_right⟩ < Fintype.card S.right :=
    SimpleGraph.degree_lt_card_verts (G := G.induce S.right) ⟨v, hv_right⟩
  omega

theorem lemma_dominating_K4_of_one_separation_left
    [Fintype V] [DecidableRel G.Adj]
    (IH : InductionHypothesis.{u} (Fintype.card V))
    (h_connected : G.Connected)
    (S : Separation G)
    [Fintype S.right] [DecidableRel (G.induce S.right).Adj]
    (hproper : S.Proper)
    {sep : V}
    (hsep_left : sep ∈ S.left)
    (hsep_right : sep ∈ S.right)
    (hseparator_unique : forall x : V, x ∈ S.left -> x ∈ S.right -> x = sep)
    (L : Finset V)
    (hL_subset_left : forall v : V, v ∈ L -> v ∈ S.left)
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L) :
    Exists fun T : DominatingK4Model G =>
      forall v : V, v ∈ L -> v ∈ (T.branch (0 : Fin 4)).verts := by
  classical
  let sepR : S.right := ⟨sep, hsep_right⟩
  let Lright : Finset S.right := {sepR}
  have hright_card : 4 <= Fintype.card S.right :=
    right_side_card_atLeast_four_of_left_low_degree_clique
      (G := G) S hproper L hL_subset_left h_low_degree_in_L
  have hright_lt : Fintype.card S.right < Fintype.card V := by
    rcases hproper.1 with ⟨x, _hx_left, hx_not_right⟩
    simpa using
      (Fintype.card_subtype_lt
        (p := fun x : V => x ∈ S.right) (x := x) hx_not_right)
  have hright_connected : (G.induce S.right).Connected :=
    S.induce_right_connected_of_connected_unique_separator
      h_connected hsep_right hseparator_unique
  have hclique_right : (G.induce S.right).IsClique (Lright : Set S.right) := by
    intro a ha b hb hab
    simp [Lright] at ha hb
    exact False.elim (hab (ha.trans hb.symm))
  have hcard_Lright : Lright.card <= 2 := by
    simp [Lright]
  have hlow_right :
      forall v : S.right, (G.induce S.right).degree v <= 2 -> v ∈ Lright := by
    intro v hv
    have hv_eq :
        v = sepR :=
      right_side_low_degree_only_separator
        (G := G) S hsep_right hseparator_unique
        L hL_subset_left h_low_degree_in_L v hv
    simp [Lright, hv_eq]
  have hhigh_right :
      (Exists fun v : S.right =>
        v ∈ Lright ∧ 3 <= (G.induce S.right).degree v) ->
          Lright.card = 1 := by
    simp [Lright]
  obtain ⟨T, hT⟩ :=
    IH (W := S.right) (G.induce S.right)
      hright_lt hright_connected hright_card
      Lright hclique_right hcard_Lright hlow_right hhigh_right
  have hsep_branch : sepR ∈ (T.branch (0 : Fin 4)).verts :=
    hT sepR (by simp [Lright])
  have hleft_connected_induce : (G.induce S.left).Connected :=
    S.induce_left_connected_of_connected_unique_separator
      h_connected hsep_left hseparator_unique
  have hleft_connected :
      (((⊤ : G.Subgraph).induce S.left).coe).Connected := by
    exact ((SimpleGraph.connected_induce_iff (G := G) (s := S.left)).mp
      hleft_connected_induce).coe
  obtain ⟨T', hT'⟩ :=
    dominating_K4_lift_across_one_separation
      (G := G) S sep hleft_connected hsep_left hsep_right
      hseparator_unique T hsep_branch
  exact ⟨T', fun v hvL => hT' v (hL_subset_left v hvL)⟩

theorem lemma_dominating_K4_of_not_two_connected
    [Fintype V] [DecidableRel G.Adj]
    (IH : InductionHypothesis.{u} (Fintype.card V))
    (h_connected : G.Connected)
    (h_card : 4 <= Fintype.card V)
    (h_not_two_connected : Not (IsTwoConnected G))
    (L : Finset V)
    (h_clique : G.IsClique (L : Set V))
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L) :
    Exists fun T : DominatingK4Model G =>
      forall v : V, v ∈ L -> v ∈ (T.branch (0 : Fin 4)).verts := by
  classical
  have h_card_nat : 1 + 1 < Nat.card V := by
    rw [Nat.card_eq_fintype_card]
    omega
  obtain ⟨S, hproper, horder⟩ :=
    not_kplusone_connected_has_proper_small_separation
      (G := G) 1 h_card_nat h_not_two_connected
  obtain ⟨sep, hsep_left, hsep_right, hseparator_unique⟩ :=
    S.exists_unique_separator_of_connected_orderAtMost_one
      h_connected hproper (by simpa using horder)
  rcases S.finset_clique_subset_left_or_subset_right L h_clique with
    hL_subset_left | hL_subset_right
  · letI : Fintype S.right := S.right.toFinite.fintype
    haveI : DecidableRel (G.induce S.right).Adj := Classical.decRel _
    exact lemma_dominating_K4_of_one_separation_left
      (G := G) IH h_connected S hproper hsep_left hsep_right
      hseparator_unique L hL_subset_left h_low_degree_in_L
  · let S' : Separation G := S.symm
    letI : Fintype S'.right := S'.right.toFinite.fintype
    haveI : DecidableRel (G.induce S'.right).Adj := Classical.decRel _
    have hproper' : S'.Proper := (S.proper_symm).2 hproper
    have hseparator_unique' :
        forall x : V, x ∈ S'.left -> x ∈ S'.right -> x = sep := by
      intro x hx_left hx_right
      exact hseparator_unique x hx_right hx_left
    exact lemma_dominating_K4_of_one_separation_left
      (G := G) IH h_connected S' hproper' hsep_right hsep_left
      hseparator_unique' L hL_subset_right h_low_degree_in_L

end DominatingK4

end Schematic.Math.GraphTheory
