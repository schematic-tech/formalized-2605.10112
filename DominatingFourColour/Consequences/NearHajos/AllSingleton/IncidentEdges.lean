import DominatingFourColour.Consequences.NearHajos.AllSingleton.MinimalTreeCarrier

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem K5UnsplitSubdivisionData.incidentGraphEdges
    {V : Type u} {G : SimpleGraph V}
    (D : K5UnsplitSubdivisionData G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
          edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  let h01 : K5Graph.Adj (0 : Fin 5) (1 : Fin 5) := by decide
  let h02 : K5Graph.Adj (0 : Fin 5) (2 : Fin 5) := by decide
  exact D.model.incidentGraphEdges_of_edgeUnsplit h01 h02
    (by decide) D.edge₁_unsplit D.edge₂_unsplit

theorem K5UnsplitSubdivisionData.distinct_incidentGraphEdges
    {V : Type u} {G : SimpleGraph V}
    (D : K5UnsplitSubdivisionData G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        edge₁ ≠ edge₂ ∧
          (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
            edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  let h01 : K5Graph.Adj (0 : Fin 5) (1 : Fin 5) := by decide
  let h02 : K5Graph.Adj (0 : Fin 5) (2 : Fin 5) := by decide
  exact D.model.distinct_incidentGraphEdges_of_edgeUnsplit h01 h02
    (by decide) D.edge₁_unsplit D.edge₂_unsplit

theorem K5HatUnsplitSubdivisionData.incidentGraphEdges
    {V : Type u} {G : SimpleGraph V}
    (D : K5HatUnsplitSubdivisionData G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
          edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  let c : Fin 6 := K5Hat.k4CoreEmbedding D.coreCenter
  let l : Fin 6 := K5Hat.k4CoreEmbedding D.coreLeft
  let r : Fin 6 := K5Hat.k4CoreEmbedding D.coreRight
  let hcl : K5Hat.Adj c l := K5Hat.k4CoreEmbedding_adj D.coreCenter_ne_left
  let hcr : K5Hat.Adj c r := K5Hat.k4CoreEmbedding_adj D.coreCenter_ne_right
  exact D.model.incidentGraphEdges_of_edgeUnsplit hcl hcr
    (K5Hat.k4CoreEmbedding.injective.ne D.coreLeft_ne_right)
    D.edge₁_unsplit D.edge₂_unsplit

theorem K5HatUnsplitSubdivisionData.distinct_incidentGraphEdges
    {V : Type u} {G : SimpleGraph V}
    (D : K5HatUnsplitSubdivisionData G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        edge₁ ≠ edge₂ ∧
          (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
            edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  let c : Fin 6 := K5Hat.k4CoreEmbedding D.coreCenter
  let l : Fin 6 := K5Hat.k4CoreEmbedding D.coreLeft
  let r : Fin 6 := K5Hat.k4CoreEmbedding D.coreRight
  let hcl : K5Hat.Adj c l := K5Hat.k4CoreEmbedding_adj D.coreCenter_ne_left
  let hcr : K5Hat.Adj c r := K5Hat.k4CoreEmbedding_adj D.coreCenter_ne_right
  exact D.model.distinct_incidentGraphEdges_of_edgeUnsplit hcl hcr
    (K5Hat.k4CoreEmbedding.injective.ne D.coreLeft_ne_right)
    D.edge₁_unsplit D.edge₂_unsplit

theorem NearHajosStrengtheningConclusion.incidentGraphEdges
    {V : Type u} {G : SimpleGraph V}
    (h : NearHajosStrengtheningConclusion G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
          edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  rcases h with hK5 | hHat
  · rcases hK5 with ⟨D⟩
    exact D.incidentGraphEdges
  · rcases hHat with ⟨D⟩
    exact D.incidentGraphEdges

theorem NearHajosStrengtheningConclusion.distinct_incidentGraphEdges
    {V : Type u} {G : SimpleGraph V}
    (h : NearHajosStrengtheningConclusion G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        edge₁ ≠ edge₂ ∧
          (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
            edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  rcases h with hK5 | hHat
  · rcases hK5 with ⟨D⟩
    exact D.distinct_incidentGraphEdges
  · rcases hHat with ⟨D⟩
    exact D.distinct_incidentGraphEdges

theorem clique_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (e : Fin 5 ↪ V)
    (h_adj : forall x y : Fin 5, x ≠ y -> G.Adj (e x) (e y)) :
    NearHajosStrengtheningConclusion G := by
  let M : StrictSubdivisionModel K5Graph G :=
    StrictSubdivisionModel.ofCompleteGraphEmbedding e
      h_adj
  exact Or.inl ⟨{
    model := M
    edge₁_unsplit :=
      StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit e h_adj
        (show K5Graph.Adj (0 : Fin 5) (1 : Fin 5) from by decide)
    edge₂_unsplit :=
      StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit e h_adj
        (show K5Graph.Adj (0 : Fin 5) (2 : Fin 5) from by decide)
  }⟩

theorem k5_one_edge_subdivided_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (e : Fin 5 ↪ V)
    (h_adj :
      forall x y : Fin 5,
        x ≠ y ->
          ¬ ((x = (2 : Fin 5) ∧ y = (4 : Fin 5)) ∨
              (x = (4 : Fin 5) ∧ y = (2 : Fin 5))) ->
            G.Adj (e x) (e y))
    (p : G.Walk (e (2 : Fin 5)) (e (4 : Fin 5)))
    (hp : p.IsPath)
    (hp_internal_no_branch :
      forall {z : V},
        z ∈ Walk.InternalVertices p -> forall i : Fin 5, z ≠ e i) :
    NearHajosStrengtheningConclusion G := by
  classical
  let M : StrictSubdivisionModel K5Graph G := {
    branchVertex := e
    branchVertex_injective := e.injective
    edgePath := by
      intro x y hxy
      by_cases h24 : x = (2 : Fin 5) ∧ y = (4 : Fin 5)
      · rcases h24 with ⟨rfl, rfl⟩
        exact p
      · by_cases h42 : x = (4 : Fin 5) ∧ y = (2 : Fin 5)
        · rcases h42 with ⟨rfl, rfl⟩
          exact p.reverse
        · exact (h_adj x y hxy.ne (by exact not_or.mpr ⟨h24, h42⟩)).toWalk
    edgePath_isPath := by
      intro x y hxy
      by_cases h24 : x = (2 : Fin 5) ∧ y = (4 : Fin 5)
      · have hx : x = (2 : Fin 5) := h24.1
        have hy : y = (4 : Fin 5) := h24.2
        subst x
        subst y
        convert hp using 1
      · by_cases h42 : x = (4 : Fin 5) ∧ y = (2 : Fin 5)
        · have hx : x = (4 : Fin 5) := h42.1
          have hy : y = (2 : Fin 5) := h42.2
          subst x
          subst y
          convert hp.reverse using 1
        · simpa [h24, h42] using
            SimpleGraph.Walk.IsPath.of_adj
              (h_adj x y hxy.ne (by exact not_or.mpr ⟨h24, h42⟩))
    no_internal_branch_vertices := True
    internally_disjoint_edge_paths := True
    no_internal_branch_vertices' := by
      intro x y hxy z hz i hzi
      by_cases h24 : x = (2 : Fin 5) ∧ y = (4 : Fin 5)
      · have hx : x = (2 : Fin 5) := h24.1
        have hy : y = (4 : Fin 5) := h24.2
        subst x
        subst y
        have hz_p : z ∈ Walk.InternalVertices p := by
          convert hz using 1
        exact hp_internal_no_branch hz_p i hzi
      · by_cases h42 : x = (4 : Fin 5) ∧ y = (2 : Fin 5)
        · have hx : x = (4 : Fin 5) := h42.1
          have hy : y = (2 : Fin 5) := h42.2
          subst x
          subst y
          have hz_rev : z ∈ Walk.InternalVertices p.reverse := by
            convert hz using 1
          have hz' : z ∈ Walk.InternalVertices p := by
            simpa [Walk.internalVertices_reverse] using hz_rev
          exact hp_internal_no_branch hz' i hzi
        · have hz_walk :
              z ∈ Walk.InternalVertices
                (h_adj x y hxy.ne
                  (by exact not_or.mpr ⟨h24, h42⟩)).toWalk := by
            simpa [h24, h42] using hz
          exact (Walk.not_mem_internalVertices_toWalk
            (h_adj x y hxy.ne (by exact not_or.mpr ⟨h24, h42⟩)) hz_walk).elim
    internally_disjoint_edge_paths' := by
      intro x y x' y' hxy hx'y' hne
      rw [Set.disjoint_left]
      intro z hz hz'
      by_cases h24 : x = (2 : Fin 5) ∧ y = (4 : Fin 5)
      · rcases h24 with ⟨rfl, rfl⟩
        by_cases h24' : x' = (2 : Fin 5) ∧ y' = (4 : Fin 5)
        · rcases h24' with ⟨rfl, rfl⟩
          exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
        · by_cases h42' : x' = (4 : Fin 5) ∧ y' = (2 : Fin 5)
          · rcases h42' with ⟨rfl, rfl⟩
            exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
          · have hz'_walk :
                z ∈ Walk.InternalVertices
                  (h_adj x' y' hx'y'.ne
                    (by exact not_or.mpr ⟨h24', h42'⟩)).toWalk := by
              simpa [h24', h42'] using hz'
            exact (Walk.not_mem_internalVertices_toWalk
              (h_adj x' y' hx'y'.ne (by exact not_or.mpr ⟨h24', h42'⟩)) hz'_walk).elim
      · by_cases h42 : x = (4 : Fin 5) ∧ y = (2 : Fin 5)
        · rcases h42 with ⟨rfl, rfl⟩
          by_cases h24' : x' = (2 : Fin 5) ∧ y' = (4 : Fin 5)
          · rcases h24' with ⟨rfl, rfl⟩
            exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
          · by_cases h42' : x' = (4 : Fin 5) ∧ y' = (2 : Fin 5)
            · rcases h42' with ⟨rfl, rfl⟩
              exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
            · have hz'_walk :
                  z ∈ Walk.InternalVertices
                    (h_adj x' y' hx'y'.ne
                      (by exact not_or.mpr ⟨h24', h42'⟩)).toWalk := by
                simpa [h24', h42'] using hz'
              exact (Walk.not_mem_internalVertices_toWalk
                (h_adj x' y' hx'y'.ne (by exact not_or.mpr ⟨h24', h42'⟩)) hz'_walk).elim
        · have hz_walk :
              z ∈ Walk.InternalVertices
                (h_adj x y hxy.ne
                  (by exact not_or.mpr ⟨h24, h42⟩)).toWalk := by
            simpa [h24, h42] using hz
          exact (Walk.not_mem_internalVertices_toWalk
            (h_adj x y hxy.ne (by exact not_or.mpr ⟨h24, h42⟩)) hz_walk).elim
  }
  exact Or.inl ⟨{
    model := M
    edge₁_unsplit := by
      simp [M, StrictSubdivisionModel.EdgeUnsplit]
    edge₂_unsplit := by
      simp [M, StrictSubdivisionModel.EdgeUnsplit]
  }⟩

private def fin5SwapThirdFourth : Fin 5 ↪ Fin 5 where
  toFun
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 4
    | 4 => 3
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢

theorem k5_one_edge_23_subdivided_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (e : Fin 5 ↪ V)
    (h_adj :
      forall x y : Fin 5,
        x ≠ y ->
          ¬ ((x = (2 : Fin 5) ∧ y = (3 : Fin 5)) ∨
              (x = (3 : Fin 5) ∧ y = (2 : Fin 5))) ->
            G.Adj (e x) (e y))
    (p : G.Walk (e (2 : Fin 5)) (e (3 : Fin 5)))
    (hp : p.IsPath)
    (hp_internal_no_branch :
      forall {z : V},
        z ∈ Walk.InternalVertices p -> forall i : Fin 5, z ≠ e i) :
    NearHajosStrengtheningConclusion G := by
  classical
  let σ : Fin 5 ↪ Fin 5 := fin5SwapThirdFourth
  let e' : Fin 5 ↪ V := σ.trans e
  have h_adj' :
      forall x y : Fin 5,
        x ≠ y ->
          ¬ ((x = (2 : Fin 5) ∧ y = (4 : Fin 5)) ∨
              (x = (4 : Fin 5) ∧ y = (2 : Fin 5))) ->
            G.Adj (e' x) (e' y) := by
    intro x y hxy hnot
    have hσ_ne : σ x ≠ σ y := by
      intro h
      exact hxy (σ.injective h)
    have hnotσ :
        ¬ ((σ x = (2 : Fin 5) ∧ σ y = (3 : Fin 5)) ∨
            (σ x = (3 : Fin 5) ∧ σ y = (2 : Fin 5))) := by
      intro hspecial
      exact hnot (by
        fin_cases x <;> fin_cases y <;>
          simp [σ, fin5SwapThirdFourth] at hspecial ⊢)
    exact h_adj (σ x) (σ y) hσ_ne hnotσ
  have hp_internal_no_branch' :
      forall {z : V},
        z ∈ Walk.InternalVertices p -> forall i : Fin 5, z ≠ e' i := by
    intro z hz i
    exact hp_internal_no_branch hz (σ i)
  simpa [e', σ, fin5SwapThirdFourth] using
    k5_one_edge_subdivided_near_hajos_with_two_incident_unsplit_edges
      e' h_adj' p hp hp_internal_no_branch'

end Schematic.Math.GraphTheory
