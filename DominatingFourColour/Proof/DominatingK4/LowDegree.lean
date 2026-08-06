import DominatingFourColour.Proof.DominatingK4.Main

/-!
The low-degree consequences of the dominating-K4 lemma.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph
open DominatingK4

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem no_dominating_K4_has_two_nonadjacent_low_degree_vertices_connected
    [Fintype V] [DecidableRel G.Adj]
    (h_connected : G.Connected)
    (h_card : 4 <= Fintype.card V)
    (h_no_model : HasNoDominatingKModel G 4) :
    Exists fun u : V =>
      Exists fun v : V =>
        u ≠ v ∧ Not (G.Adj u v) ∧ G.degree u <= 2 ∧ G.degree v <= 2 := by
  classical
  by_contra hno
  let L : Finset V := Finset.univ.filter fun v => G.degree v <= 2
  have hLmem (v : V) : v ∈ L ↔ G.degree v <= 2 := by
    simp [L]
  have hclique : G.IsClique (L : Set V) := by
    intro u hu v hv huv
    by_contra huv_not
    exact hno ⟨u, v, huv, huv_not, (hLmem u).1 hu, (hLmem v).1 hv⟩
  have hcardL : L.card <= 2 := by
    by_contra hle
    have hgt : 2 < L.card := Nat.lt_of_not_ge hle
    rcases Finset.two_lt_card.mp hgt with
      ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
    let Sfin : Finset V := {a, b, c}
    have hSfin_card : Sfin.card = 3 := by
      simp [Sfin, hab, hac, hbc]
    have hlt_univ : Sfin.card < (Finset.univ : Finset V).card := by
      rw [hSfin_card, Finset.card_univ]
      exact h_card
    obtain ⟨d, _hd_univ, hdS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_univ
    have hS_nonempty : ((Sfin : Set V)).Nonempty := by
      exact ⟨a, by simp [Sfin]⟩
    have hS_compl : ((Sfin : Set V)ᶜ).Nonempty := by
      exact ⟨d, by simpa using hdS⟩
    obtain ⟨u, huS, v, hvS, huv⟩ :=
      Connected.exists_adjacent_crossing (G := G) h_connected hS_nonempty hS_compl
    have hab_adj : G.Adj a b := hclique ha hb hab
    have hac_adj : G.Adj a c := hclique ha hc hac
    have hbc_adj : G.Adj b c := hclique hb hc hbc
    have hv_ne_a : v ≠ a := by
      intro h
      exact hvS (by simp [Sfin, h])
    have hv_ne_b : v ≠ b := by
      intro h
      exact hvS (by simp [Sfin, h])
    have hv_ne_c : v ≠ c := by
      intro h
      exact hvS (by simp [Sfin, h])
    have hlow_a : G.degree a <= 2 := (hLmem a).1 ha
    have hlow_b : G.degree b <= 2 := (hLmem b).1 hb
    have hlow_c : G.degree c <= 2 := (hLmem c).1 hc
    simp [Sfin] at huS
    rcases huS with hu_eq_a | hu_eq_b | hu_eq_c
    · rw [hu_eq_a] at huv
      have hdeg3 : 3 <= G.degree a :=
        degree_atLeast_three_of_three_neighbors hab_adj hac_adj huv
          hbc hv_ne_b.symm hv_ne_c.symm
      omega
    · rw [hu_eq_b] at huv
      have hdeg3 : 3 <= G.degree b :=
        degree_atLeast_three_of_three_neighbors hab_adj.symm hbc_adj huv
          hac hv_ne_a.symm hv_ne_c.symm
      omega
    · rw [hu_eq_c] at huv
      have hdeg3 : 3 <= G.degree c :=
        degree_atLeast_three_of_three_neighbors hac_adj.symm hbc_adj.symm huv
          hab hv_ne_a.symm hv_ne_b.symm
      omega
  have hhigh :
      (Exists fun v : V => v ∈ L ∧ 3 <= G.degree v) -> L.card = 1 := by
    rintro ⟨v, hvL, hvdeg⟩
    have hvlow : G.degree v <= 2 := (hLmem v).1 hvL
    omega
  obtain ⟨T, _hT⟩ :=
    lemma_dominating_K4 (G := G) h_connected h_card L hclique hcardL
      (fun v hv => (hLmem v).2 hv) hhigh
  exact h_no_model ⟨T⟩

namespace DominatingK4

theorem connectedComponent_has_low_degree_vertex
    [Fintype V] [DecidableRel G.Adj]
    (h_no_model : HasNoDominatingKModel G 4)
    (C : G.ConnectedComponent) :
    Exists fun v : V => v ∈ C.supp ∧ G.degree v <= 2 := by
  classical
  by_cases hlarge : 4 <= C.supp.ncard
  · letI : Fintype C := C.supp.toFinite.fintype
    haveI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    have hcardC : 4 <= Fintype.card C := by
      rw [← Nat.card_eq_fintype_card]
      change 4 <= Nat.card C.supp
      rw [Nat.card_coe_set_eq]
      exact hlarge
    have h_no_component_model : HasNoDominatingKModel C.toSimpleGraph 4 := by
      rintro ⟨T⟩
      exact h_no_model ⟨T.ofConnectedComponent C⟩
    obtain ⟨u, _v, _huv_ne, _huv_not_adj, hu_degree, _hv_degree⟩ :=
      no_dominating_K4_has_two_nonadjacent_low_degree_vertices_connected
        (G := C.toSimpleGraph)
        (SimpleGraph.ConnectedComponent.connected_toSimpleGraph C)
        hcardC h_no_component_model
    refine ⟨u, u.2, ?_⟩
    rw [connectedComponent_degree_eq C u]
    exact hu_degree
  · have hsmall : C.supp.ncard <= 3 := by omega
    obtain ⟨v, hv⟩ := C.nonempty_supp
    exact ⟨v, hv, degree_le_two_of_mem_component_ncard_le_three C hv hsmall⟩

end DominatingK4

theorem no_dominating_K4_has_two_nonadjacent_low_degree_vertices
    [Fintype V] [DecidableRel G.Adj]
    (h_card : 4 <= Fintype.card V)
    (h_no_model : HasNoDominatingKModel G 4) :
    Exists fun u : V =>
      Exists fun v : V =>
        u ≠ v ∧ Not (G.Adj u v) ∧ G.degree u <= 2 ∧ G.degree v <= 2 := by
  classical
  by_cases h_connected : G.Connected
  · exact no_dominating_K4_has_two_nonadjacent_low_degree_vertices_connected
      h_connected h_card h_no_model
  · have h_nonempty : Nonempty V := by
      exact Fintype.card_pos_iff.mp (by omega)
    have h_not_preconnected : Not G.Preconnected := by
      intro hpre
      haveI : Nonempty V := h_nonempty
      exact h_connected { preconnected := hpre }
    obtain ⟨x, hx⟩ := not_forall.mp h_not_preconnected
    obtain ⟨y, hxy_not_reachable⟩ := not_forall.mp hx
    let Cx : G.ConnectedComponent := G.connectedComponentMk x
    let Cy : G.ConnectedComponent := G.connectedComponentMk y
    have hcomponents_ne : Cx ≠ Cy := by
      intro hxy
      exact hxy_not_reachable (SimpleGraph.ConnectedComponent.exact hxy)
    obtain ⟨u, huC, hu_degree⟩ :=
      connectedComponent_has_low_degree_vertex (G := G) h_no_model Cx
    obtain ⟨v, hvC, hv_degree⟩ :=
      connectedComponent_has_low_degree_vertex (G := G) h_no_model Cy
    have hu_comp : G.connectedComponentMk u = Cx := by
      exact huC
    have hv_comp : G.connectedComponentMk v = Cy := by
      exact hvC
    have huv_ne : u ≠ v := by
      intro huv
      apply hcomponents_ne
      rw [← hu_comp, ← hv_comp, huv]
    have huv_not_adj : Not (G.Adj u v) := by
      intro huv
      apply hcomponents_ne
      exact hu_comp.symm.trans
        ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv).trans hv_comp)
    exact ⟨u, v, huv_ne, huv_not_adj, hu_degree, hv_degree⟩

end Schematic.Math.GraphTheory

