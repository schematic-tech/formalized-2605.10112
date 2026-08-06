import DominatingFourColour.Consequences.NearHajos.Basic.SecondSingleton

set_option maxHeartbeats 800000

/-! The strengthened near-Hajos conclusion and its transport API. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

def NearHajosStrengtheningConclusion
    {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (K5UnsplitSubdivisionData G) ∨
    Nonempty (K5HatUnsplitSubdivisionData G)

theorem K5UnsplitSubdivisionData.containsSubdivision
    {V : Type u} {G : SimpleGraph V}
    (D : K5UnsplitSubdivisionData G) :
    ContainsSubdivision K5Graph G :=
  ⟨D.model⟩

theorem K5HatUnsplitSubdivisionData.containsSubdivision
    {V : Type u} {G : SimpleGraph V}
    (D : K5HatUnsplitSubdivisionData G) :
    ContainsSubdivision K5Hat G :=
  ⟨D.model⟩

def K5UnsplitSubdivisionData.map
    {V : Type u} {U : Type v} {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (D : K5UnsplitSubdivisionData G) :
    K5UnsplitSubdivisionData G' where
  model := D.model.map f hf
  edge₁_unsplit := by
    simpa [StrictSubdivisionModel.EdgeUnsplit, StrictSubdivisionModel.map,
      SubdivisionModel.map] using D.edge₁_unsplit
  edge₂_unsplit := by
    simpa [StrictSubdivisionModel.EdgeUnsplit, StrictSubdivisionModel.map,
      SubdivisionModel.map] using D.edge₂_unsplit

def K5HatUnsplitSubdivisionData.map
    {V : Type u} {U : Type v} {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (D : K5HatUnsplitSubdivisionData G) :
    K5HatUnsplitSubdivisionData G' where
  model := D.model.map f hf
  coreCenter := D.coreCenter
  coreLeft := D.coreLeft
  coreRight := D.coreRight
  coreCenter_ne_left := D.coreCenter_ne_left
  coreCenter_ne_right := D.coreCenter_ne_right
  coreLeft_ne_right := D.coreLeft_ne_right
  edge₁_unsplit := by
    simpa [StrictSubdivisionModel.EdgeUnsplit, StrictSubdivisionModel.map,
      SubdivisionModel.map] using D.edge₁_unsplit
  edge₂_unsplit := by
    simpa [StrictSubdivisionModel.EdgeUnsplit, StrictSubdivisionModel.map,
      SubdivisionModel.map] using D.edge₂_unsplit

def K5UnsplitSubdivisionData.k4Core
    {V : Type u} {G : SimpleGraph V}
    (D : K5UnsplitSubdivisionData G) :
    K4UnsplitSubdivisionData G where
  model := D.model.domainRestrict K5Graph.k4CoreEmbedding
    (by
      intro x y hxy
      exact K5Graph.k4CoreEmbedding_adj (by
        simpa [K4Graph, CompleteGraphOn] using hxy.ne))
  edge₁_unsplit := by
    rw [StrictSubdivisionModel.domainRestrict_edgeUnsplit]
    simpa [K5Graph.k4CoreEmbedding] using D.edge₁_unsplit
  edge₂_unsplit := by
    rw [StrictSubdivisionModel.domainRestrict_edgeUnsplit]
    simpa [K5Graph.k4CoreEmbedding] using D.edge₂_unsplit

noncomputable def K5HatUnsplitSubdivisionData.k4Core
    {V : Type u} {G : SimpleGraph V}
    (D : K5HatUnsplitSubdivisionData G) :
    K4UnsplitSubdivisionData G := by
  classical
  let hσ_exists :
      Exists fun σ : Fin 4 ↪ Fin 4 =>
        σ (0 : Fin 4) = D.coreCenter ∧
          σ (1 : Fin 4) = D.coreLeft ∧
            σ (2 : Fin 4) = D.coreRight :=
    fin4_exists_embedding_zero_one_two
      D.coreCenter_ne_left D.coreCenter_ne_right D.coreLeft_ne_right
  let σ : Fin 4 ↪ Fin 4 := Classical.choose hσ_exists
  have hσ_spec := Classical.choose_spec hσ_exists
  have hσ0 : σ (0 : Fin 4) = D.coreCenter := by
    simpa [σ] using hσ_spec.1
  have hσ1 : σ (1 : Fin 4) = D.coreLeft := by
    simpa [σ] using hσ_spec.2.1
  have hσ2 : σ (2 : Fin 4) = D.coreRight := by
    simpa [σ] using hσ_spec.2.2
  let e : Fin 4 ↪ Fin 6 := σ.trans K5Hat.k4CoreEmbedding
  let h_adj :
      forall {x y : Fin 4}, K4Graph.Adj x y ->
        K5Hat.Adj (e x) (e y) := by
    intro x y hxy
    exact K5Hat.k4CoreEmbedding_adj (by
      intro hσ
      exact hxy.ne (σ.injective hσ))
  refine ⟨D.model.domainRestrict e h_adj, ?_, ?_⟩
  · rw [StrictSubdivisionModel.domainRestrict_edgeUnsplit]
    have h_adjeq :
        h_adj (show K4Graph.Adj (0 : Fin 4) (1 : Fin 4) from by decide) =
          (by
            simpa [e, hσ0, hσ1] using
              (K5Hat.k4CoreEmbedding_adj D.coreCenter_ne_left)) := by
      apply Subsingleton.elim
    rw [h_adjeq]
    exact StrictSubdivisionModel.edgeUnsplit_of_eq D.model
      (by simp [e, hσ0])
      (by simp [e, hσ1])
      D.edge₁_unsplit
  · rw [StrictSubdivisionModel.domainRestrict_edgeUnsplit]
    have h_adjeq :
        h_adj (show K4Graph.Adj (0 : Fin 4) (2 : Fin 4) from by decide) =
          (by
            simpa [e, hσ0, hσ2] using
              (K5Hat.k4CoreEmbedding_adj D.coreCenter_ne_right)) := by
      apply Subsingleton.elim
    rw [h_adjeq]
    exact StrictSubdivisionModel.edgeUnsplit_of_eq D.model
      (by simp [e, hσ0])
      (by simp [e, hσ2])
      D.edge₂_unsplit

theorem NearHajosStrengtheningConclusion.containsSubdivision
    {V : Type u} {G : SimpleGraph V}
    (h : NearHajosStrengtheningConclusion G) :
    ContainsSubdivision K5Graph G ∨ ContainsSubdivision K5Hat G := by
  rcases h with hK5 | hHat
  · rcases hK5 with ⟨D⟩
    exact Or.inl D.containsSubdivision
  · rcases hHat with ⟨D⟩
    exact Or.inr D.containsSubdivision

theorem NearHajosStrengtheningConclusion.k4Core
    {V : Type u} {G : SimpleGraph V}
    (h : NearHajosStrengtheningConclusion G) :
    Nonempty (K4UnsplitSubdivisionData G) := by
  rcases h with hK5 | hHat
  · rcases hK5 with ⟨D⟩
    exact ⟨D.k4Core⟩
  · rcases hHat with ⟨D⟩
    exact ⟨D.k4Core⟩

theorem StrictSubdivisionModel.distinct_incidentGraphEdges_of_edgeUnsplit
    {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {center left right : W}
    (hcenter_left : H.Adj center left)
    (hcenter_right : H.Adj center right)
    (hleft_ne_right : left ≠ right)
    (hcenter_left_unsplit : M.EdgeUnsplit hcenter_left)
    (hcenter_right_unsplit : M.EdgeUnsplit hcenter_right) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        edge₁ ≠ edge₂ ∧
          (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
            edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  let edge₁ : Sym2 V := s(M.branchVertex center, M.branchVertex left)
  let edge₂ : Sym2 V := s(M.branchVertex center, M.branchVertex right)
  refine ⟨edge₁, edge₂, ?_, ?_, ?_⟩
  · intro hedges
    have hcenter_ne_left : M.branchVertex center ≠ M.branchVertex left := by
      intro h
      exact hcenter_left.ne (M.branchVertex_injective h)
    have hleft_eq_right : M.branchVertex left = M.branchVertex right := by
      have hmem : M.branchVertex left ∈ edge₂ := by
        rw [← hedges]
        exact Sym2.mem_mk_right _ _
      rw [Sym2.mem_iff] at hmem
      exact hmem.resolve_left fun h => hcenter_ne_left h.symm
    exact hleft_ne_right (M.branchVertex_injective hleft_eq_right)
  · exact ⟨M.branchVertex center,
      Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
  · exact ⟨(SimpleGraph.mem_edgeSet (G := G)).2
        (M.adj_of_edgeUnsplit hcenter_left hcenter_left_unsplit),
      (SimpleGraph.mem_edgeSet (G := G)).2
        (M.adj_of_edgeUnsplit hcenter_right hcenter_right_unsplit)⟩

theorem StrictSubdivisionModel.incidentGraphEdges_of_edgeUnsplit
    {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {center left right : W}
    (hcenter_left : H.Adj center left)
    (hcenter_right : H.Adj center right)
    (hleft_ne_right : left ≠ right)
    (hcenter_left_unsplit : M.EdgeUnsplit hcenter_left)
    (hcenter_right_unsplit : M.EdgeUnsplit hcenter_right) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
          edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  rcases M.distinct_incidentGraphEdges_of_edgeUnsplit
      hcenter_left hcenter_right hleft_ne_right
      hcenter_left_unsplit hcenter_right_unsplit with
    ⟨edge₁, edge₂, _, hincident, hedge₁, hedge₂⟩
  exact ⟨edge₁, edge₂, hincident, hedge₁, hedge₂⟩

theorem K4UnsplitSubdivisionData.incidentGraphEdges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
          edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  let h01 : K4Graph.Adj (0 : Fin 4) (1 : Fin 4) := by decide
  let h02 : K4Graph.Adj (0 : Fin 4) (2 : Fin 4) := by decide
  exact D.model.incidentGraphEdges_of_edgeUnsplit h01 h02
    (by decide) D.edge₁_unsplit D.edge₂_unsplit

theorem K4UnsplitSubdivisionData.distinct_incidentGraphEdges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        edge₁ ≠ edge₂ ∧
          (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
            edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  let h01 : K4Graph.Adj (0 : Fin 4) (1 : Fin 4) := by decide
  let h02 : K4Graph.Adj (0 : Fin 4) (2 : Fin 4) := by decide
  exact D.model.distinct_incidentGraphEdges_of_edgeUnsplit h01 h02
    (by decide) D.edge₁_unsplit D.edge₂_unsplit

theorem NearHajosStrengtheningConclusion.k4Core_distinct_incidentGraphEdges
    {V : Type u} {G : SimpleGraph V}
    (h : NearHajosStrengtheningConclusion G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        edge₁ ≠ edge₂ ∧
          (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
            edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  rcases h.k4Core with ⟨D⟩
  exact D.distinct_incidentGraphEdges

theorem NearHajosStrengtheningConclusion.map
    {V : Type u} {U : Type v} {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (h : NearHajosStrengtheningConclusion G) :
    NearHajosStrengtheningConclusion G' := by
  rcases h with hK5 | hHat
  · rcases hK5 with ⟨D⟩
    exact Or.inl ⟨D.map f hf⟩
  · rcases hHat with ⟨D⟩
    exact Or.inr ⟨D.map f hf⟩

end Schematic.Math.GraphTheory
