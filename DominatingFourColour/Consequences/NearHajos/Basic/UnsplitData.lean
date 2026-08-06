import DominatingFourColour.Consequences.SingletonModels

set_option maxHeartbeats 800000

/-!
Formalization of Corollary `NearHajos` and the strengthened edge-unsplitting
remark following it.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

structure K5UnsplitSubdivisionData
    {V : Type u} (G : SimpleGraph V) where
  model : StrictSubdivisionModel K5Graph G
  edge₁_unsplit :
    model.EdgeUnsplit (show K5Graph.Adj (0 : Fin 5) (1 : Fin 5) from by decide)
  edge₂_unsplit :
    model.EdgeUnsplit (show K5Graph.Adj (0 : Fin 5) (2 : Fin 5) from by decide)

structure K5HatUnsplitSubdivisionData
    {V : Type u} (G : SimpleGraph V) where
  model : StrictSubdivisionModel K5Hat G
  coreCenter : Fin 4 := 0
  coreLeft : Fin 4 := 1
  coreRight : Fin 4 := 2
  coreCenter_ne_left : coreCenter ≠ coreLeft := by decide
  coreCenter_ne_right : coreCenter ≠ coreRight := by decide
  coreLeft_ne_right : coreLeft ≠ coreRight := by decide
  edge₁_unsplit :
    model.EdgeUnsplit
      (K5Hat.k4CoreEmbedding_adj coreCenter_ne_left)
  edge₂_unsplit :
    model.EdgeUnsplit
      (K5Hat.k4CoreEmbedding_adj coreCenter_ne_right)

structure K4UnsplitSubdivisionData
    {V : Type u} (G : SimpleGraph V) where
  model : StrictSubdivisionModel K4Graph G
  edge₁_unsplit :
    model.EdgeUnsplit (show K4Graph.Adj (0 : Fin 4) (1 : Fin 4) from by decide)
  edge₂_unsplit :
    model.EdgeUnsplit (show K4Graph.Adj (0 : Fin 4) (2 : Fin 4) from by decide)

def K4UnsplitSubdivisionData.ofCliqueEmbedding
    {V : Type u} {G : SimpleGraph V}
    (e : Fin 4 ↪ V)
    (h_adj : forall x y : Fin 4, x ≠ y -> G.Adj (e x) (e y)) :
    K4UnsplitSubdivisionData G where
  model := StrictSubdivisionModel.ofCompleteGraphEmbedding e h_adj
  edge₁_unsplit :=
    StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit e h_adj
      (show K4Graph.Adj (0 : Fin 4) (1 : Fin 4) from by decide)
  edge₂_unsplit :=
    StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit e h_adj
      (show K4Graph.Adj (0 : Fin 4) (2 : Fin 4) from by decide)

def K4UnsplitSubdivisionData.relabel
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    (h01 :
      forall hσ01 : K4Graph.Adj (σ (0 : Fin 4)) (σ (1 : Fin 4)),
        D.model.EdgeUnsplit hσ01)
    (h02 :
      forall hσ02 : K4Graph.Adj (σ (0 : Fin 4)) (σ (2 : Fin 4)),
        D.model.EdgeUnsplit hσ02) :
    K4UnsplitSubdivisionData G := by
  classical
  have h_adj :
      forall {i j : Fin 4}, K4Graph.Adj i j ->
        K4Graph.Adj (σ i) (σ j) := by
    intro i j hij
    have hij_ne : i ≠ j := by
      simpa [K4Graph, CompleteGraphOn] using hij
    simpa [K4Graph, CompleteGraphOn] using
      (show σ i ≠ σ j from by
        intro hσ
        exact hij_ne (σ.injective hσ))
  refine ⟨D.model.domainRestrict σ h_adj, ?_, ?_⟩
  · rw [StrictSubdivisionModel.domainRestrict_edgeUnsplit]
    exact h01 _
  · rw [StrictSubdivisionModel.domainRestrict_edgeUnsplit]
    exact h02 _

theorem K4UnsplitSubdivisionData.edgeUnsplit_of_embedding_preimage_zero_one
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    {c l : Fin 4}
    (hc : σ c = (0 : Fin 4))
    (hl : σ l = (1 : Fin 4))
    (hcl : K4Graph.Adj (σ c) (σ l)) :
    D.model.EdgeUnsplit hcl := by
  exact StrictSubdivisionModel.edgeUnsplit_of_eq D.model
    (x := (0 : Fin 4)) (y := (1 : Fin 4))
    (x' := σ c) (y' := σ l)
    (by simp [hc]) (by simp [hl])
    D.edge₁_unsplit

theorem K4UnsplitSubdivisionData.edgeUnsplit_of_embedding_preimage_zero_two
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    {c r : Fin 4}
    (hc : σ c = (0 : Fin 4))
    (hr : σ r = (2 : Fin 4))
    (hcr : K4Graph.Adj (σ c) (σ r)) :
    D.model.EdgeUnsplit hcr := by
  exact StrictSubdivisionModel.edgeUnsplit_of_eq D.model
    (x := (0 : Fin 4)) (y := (2 : Fin 4))
    (x' := σ c) (y' := σ r)
    (by simp [hc]) (by simp [hr])
    D.edge₂_unsplit

noncomputable def K4UnsplitSubdivisionData.ofTriangleCone
    {V : Type u} {G : SimpleGraph V}
    {v₀ v₁ v₂ apex : V}
    (hbranch_injective :
      Function.Injective
        (fun i : Fin 4 =>
          match i with
          | 0 => v₀
          | 1 => v₁
          | 2 => v₂
          | 3 => apex))
    (h₀₁ : G.Adj v₀ v₁)
    (h₀₂ : G.Adj v₀ v₂)
    (p₁₂ : G.Walk v₁ v₂)
    (hp₁₂ : p₁₂.IsPath)
    (arm : forall i : Fin 3,
      G.Walk apex
        (match i with
          | 0 => v₀
          | 1 => v₁
          | 2 => v₂))
    (harm_path : forall i : Fin 3, (arm i).IsPath)
    (hp₁₂_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p₁₂ ->
        forall w : Fin 4,
          z ≠
            match w with
            | 0 => v₀
            | 1 => v₁
            | 2 => v₂
            | 3 => apex)
    (harm_internal_no_branch :
      forall i : Fin 3, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          forall w : Fin 4,
            z ≠
              match w with
              | 0 => v₀
              | 1 => v₁
              | 2 => v₂
              | 3 => apex)
    (harm_internal_disjoint :
      forall {i j : Fin 3}, i ≠ j ->
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (arm j)))
    (harm_p₁₂_disjoint :
      forall i : Fin 3,
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices p₁₂)) :
    K4UnsplitSubdivisionData G := by
  classical
  let branch : Fin 4 -> V
    | 0 => v₀
    | 1 => v₁
    | 2 => v₂
    | 3 => apex
  let edgePath :
      forall {i j : Fin 4}, K4Graph.Adj i j ->
        G.Walk (branch i) (branch j) := by
    intro i j hij
    refine
      match i, j with
      | 0, 0 => False.elim (by simp [K4Graph, CompleteGraphOn] at hij)
      | 0, 1 => h₀₁.toWalk
      | 0, 2 => h₀₂.toWalk
      | 0, 3 => (arm (0 : Fin 3)).reverse
      | 1, 0 => h₀₁.symm.toWalk
      | 1, 1 => False.elim (by simp [K4Graph, CompleteGraphOn] at hij)
      | 1, 2 => p₁₂
      | 1, 3 => (arm (1 : Fin 3)).reverse
      | 2, 0 => h₀₂.symm.toWalk
      | 2, 1 => p₁₂.reverse
      | 2, 2 => False.elim (by simp [K4Graph, CompleteGraphOn] at hij)
      | 2, 3 => (arm (2 : Fin 3)).reverse
      | 3, 0 => arm (0 : Fin 3)
      | 3, 1 => arm (1 : Fin 3)
      | 3, 2 => arm (2 : Fin 3)
      | 3, 3 => False.elim (by simp [K4Graph, CompleteGraphOn] at hij)
  have hedgePath_isPath :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j),
        (edgePath hij).IsPath := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [K4Graph, CompleteGraphOn, edgePath] at hij ⊢
    · exact h₀₁.ne
    · exact h₀₂.ne
    · exact harm_path (0 : Fin 3)
    · exact h₀₁.symm.ne
    · exact hp₁₂
    · exact harm_path (1 : Fin 3)
    · exact h₀₂.symm.ne
    · exact hp₁₂
    · exact harm_path (2 : Fin 3)
    · exact harm_path (0 : Fin 3)
    · exact harm_path (1 : Fin 3)
    · exact harm_path (2 : Fin 3)
  have hdirect_empty {a b : V} (hab : G.Adj a b) {z : V}
      (hz : z ∈ Walk.InternalVertices hab.toWalk) : False :=
    Walk.not_mem_internalVertices_toWalk hab hz
  have hno_internal :
      (SubdivisionModel.mk branch hbranch_injective edgePath
        (by intro i j hij; exact hedgePath_isPath hij) True True).NoInternalBranchVertices := by
    intro i j hij z hz w hzw
    fin_cases i <;> fin_cases j <;>
      simp [K4Graph, CompleteGraphOn, edgePath, branch] at hij hz ⊢
    · exact (hdirect_empty h₀₁ hz).elim
    · exact (hdirect_empty h₀₂ hz).elim
    · exact harm_internal_no_branch (0 : Fin 3)
        (by simpa [Walk.internalVertices_reverse] using hz) w hzw
    · exact (hdirect_empty h₀₁.symm hz).elim
    · exact hp₁₂_internal_no_branch hz w hzw
    · exact harm_internal_no_branch (1 : Fin 3)
        (by simpa [Walk.internalVertices_reverse] using hz) w hzw
    · exact (hdirect_empty h₀₂.symm hz).elim
    · exact hp₁₂_internal_no_branch
        (by simpa [Walk.internalVertices_reverse] using hz) w hzw
    · exact harm_internal_no_branch (2 : Fin 3)
        (by simpa [Walk.internalVertices_reverse] using hz) w hzw
    · exact harm_internal_no_branch (0 : Fin 3) hz w hzw
    · exact harm_internal_no_branch (1 : Fin 3) hz w hzw
    · exact harm_internal_no_branch (2 : Fin 3) hz w hzw
  let edgeActive : Fin 4 -> Fin 4 -> Option (Fin 4)
    | 0, 3 => some (0 : Fin 4)
    | 3, 0 => some (0 : Fin 4)
    | 1, 2 => some (1 : Fin 4)
    | 2, 1 => some (1 : Fin 4)
    | 1, 3 => some (2 : Fin 4)
    | 3, 1 => some (2 : Fin 4)
    | 2, 3 => some (3 : Fin 4)
    | 3, 2 => some (3 : Fin 4)
    | _, _ => none
  let pathInternal : Fin 4 -> Set V
    | 0 => Walk.InternalVertices (arm (0 : Fin 3))
    | 1 => Walk.InternalVertices p₁₂
    | 2 => Walk.InternalVertices (arm (1 : Fin 3))
    | 3 => Walk.InternalVertices (arm (2 : Fin 3))
  have hactive_internal :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (edgePath hij) ->
          Exists fun k : Fin 4 =>
            edgeActive i j = some k ∧ z ∈ pathInternal k := by
    intro i j hij z hz
    fin_cases i <;> fin_cases j <;>
      simp [K4Graph, CompleteGraphOn, edgePath] at hij hz
    · exact (hdirect_empty h₀₁ hz).elim
    · exact (hdirect_empty h₀₂ hz).elim
    · refine ⟨(0 : Fin 4), by simp [edgeActive],
        by simpa [pathInternal, Walk.internalVertices_reverse] using hz⟩
    · exact (hdirect_empty h₀₁.symm hz).elim
    · refine ⟨(1 : Fin 4), by simp [edgeActive],
        by simpa [pathInternal] using hz⟩
    · refine ⟨(2 : Fin 4), by simp [edgeActive],
        by simpa [pathInternal, Walk.internalVertices_reverse] using hz⟩
    · exact (hdirect_empty h₀₂.symm hz).elim
    · refine ⟨(1 : Fin 4), by simp [edgeActive],
        by simpa [pathInternal, Walk.internalVertices_reverse] using hz⟩
    · refine ⟨(3 : Fin 4), by simp [edgeActive],
        by simpa [pathInternal, Walk.internalVertices_reverse] using hz⟩
    · refine ⟨(0 : Fin 4), by simp [edgeActive],
        by simpa [pathInternal] using hz⟩
    · refine ⟨(2 : Fin 4), by simp [edgeActive],
        by simpa [pathInternal] using hz⟩
    · refine ⟨(3 : Fin 4), by simp [edgeActive],
        by simpa [pathInternal] using hz⟩
  have hactive_kind_unique :
      forall {i j k l : Fin 4}
        (hij : K4Graph.Adj i j) (hkl : K4Graph.Adj k l)
        {a b : Fin 4},
          edgeActive i j = some a ->
            edgeActive k l = some b ->
              a = b ->
                (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
    intro i j k l hij hkl a b ha hb hab
    subst b
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [K4Graph, CompleteGraphOn, edgeActive] at hij hkl ha hb ⊢
    all_goals
      subst a
      simp at *
  have hpathInternal_disjoint :
      forall {a b : Fin 4}, a ≠ b ->
        Disjoint (pathInternal a) (pathInternal b) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp [pathInternal] at hab ⊢
    · exact harm_p₁₂_disjoint (0 : Fin 3)
    · exact harm_internal_disjoint (by decide : (0 : Fin 3) ≠ 1)
    · exact harm_internal_disjoint (by decide : (0 : Fin 3) ≠ 2)
    · exact Disjoint.symm (harm_p₁₂_disjoint (0 : Fin 3))
    · exact Disjoint.symm (harm_p₁₂_disjoint (1 : Fin 3))
    · exact Disjoint.symm (harm_p₁₂_disjoint (2 : Fin 3))
    · exact harm_internal_disjoint (by decide : (1 : Fin 3) ≠ 0)
    · exact harm_p₁₂_disjoint (1 : Fin 3)
    · exact harm_internal_disjoint (by decide : (1 : Fin 3) ≠ 2)
    · exact harm_internal_disjoint (by decide : (2 : Fin 3) ≠ 0)
    · exact harm_p₁₂_disjoint (2 : Fin 3)
    · exact harm_internal_disjoint (by decide : (2 : Fin 3) ≠ 1)
  let M : StrictSubdivisionModel K4Graph G := {
    branchVertex := branch
    branchVertex_injective := hbranch_injective
    edgePath := edgePath
    edgePath_isPath := by intro i j hij; exact hedgePath_isPath hij
    no_internal_branch_vertices := True
    internally_disjoint_edge_paths := True
    no_internal_branch_vertices' := hno_internal
    internally_disjoint_edge_paths' := by
      intro i j k l hij hkl hne
      rw [Set.disjoint_left]
      intro z hz hz'
      rcases hactive_internal hij hz with ⟨a, ha, hza⟩
      rcases hactive_internal hkl hz' with ⟨b, hb, hzb⟩
      by_cases hab : a = b
      · exact False.elim (hne (hactive_kind_unique hij hkl ha hb hab))
      · exact Set.disjoint_left.mp (hpathInternal_disjoint hab) hza hzb
  }
  refine ⟨M, ?_, ?_⟩
  · change (edgePath (show K4Graph.Adj (0 : Fin 4) (1 : Fin 4) from by decide)).length = 1
    simp [edgePath]
  · change (edgePath (show K4Graph.Adj (0 : Fin 4) (2 : Fin 4) from by decide)).length = 1
    simp [edgePath]

theorem K4UnsplitSubdivisionData.ofTriangleCone_branchVertex_not_mem
    {V : Type u} {G : SimpleGraph V}
    {v₀ v₁ v₂ apex : V}
    {hbranch_injective :
      Function.Injective
        (fun i : Fin 4 =>
          match i with
          | 0 => v₀
          | 1 => v₁
          | 2 => v₂
          | 3 => apex)}
    {h₀₁ : G.Adj v₀ v₁}
    {h₀₂ : G.Adj v₀ v₂}
    {p₁₂ : G.Walk v₁ v₂}
    {hp₁₂ : p₁₂.IsPath}
    {arm : forall i : Fin 3,
      G.Walk apex
        (match i with
          | 0 => v₀
          | 1 => v₁
          | 2 => v₂)}
    {harm_path : forall i : Fin 3, (arm i).IsPath}
    {hp₁₂_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p₁₂ ->
        forall w : Fin 4,
          z ≠
            match w with
            | 0 => v₀
            | 1 => v₁
            | 2 => v₂
            | 3 => apex}
    {harm_internal_no_branch :
      forall i : Fin 3, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          forall w : Fin 4,
            z ≠
              match w with
              | 0 => v₀
              | 1 => v₁
              | 2 => v₂
              | 3 => apex}
    {harm_internal_disjoint :
      forall {i j : Fin 3}, i ≠ j ->
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (arm j))}
    {harm_p₁₂_disjoint :
      forall i : Fin 3,
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices p₁₂)}
    {C : Set V}
    (hv₀ : v₀ ∉ C)
    (hv₁ : v₁ ∉ C)
    (hv₂ : v₂ ∉ C)
    (hapex : apex ∉ C) :
    forall i : Fin 4,
      (K4UnsplitSubdivisionData.ofTriangleCone
        hbranch_injective h₀₁ h₀₂ p₁₂ hp₁₂ arm harm_path
        hp₁₂_internal_no_branch harm_internal_no_branch
        harm_internal_disjoint harm_p₁₂_disjoint).model.branchVertex i ∉ C := by
  intro i
  fin_cases i <;>
    simpa [K4UnsplitSubdivisionData.ofTriangleCone] using
      (by first | exact hv₀ | exact hv₁ | exact hv₂ | exact hapex)

theorem K4UnsplitSubdivisionData.ofTriangleCone_internal_not_mem
    {V : Type u} {G : SimpleGraph V}
    {v₀ v₁ v₂ apex : V}
    {hbranch_injective :
      Function.Injective
        (fun i : Fin 4 =>
          match i with
          | 0 => v₀
          | 1 => v₁
          | 2 => v₂
          | 3 => apex)}
    {h₀₁ : G.Adj v₀ v₁}
    {h₀₂ : G.Adj v₀ v₂}
    {p₁₂ : G.Walk v₁ v₂}
    {hp₁₂ : p₁₂.IsPath}
    {arm : forall i : Fin 3,
      G.Walk apex
        (match i with
          | 0 => v₀
          | 1 => v₁
          | 2 => v₂)}
    {harm_path : forall i : Fin 3, (arm i).IsPath}
    {hp₁₂_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p₁₂ ->
        forall w : Fin 4,
          z ≠
            match w with
            | 0 => v₀
            | 1 => v₁
            | 2 => v₂
            | 3 => apex}
    {harm_internal_no_branch :
      forall i : Fin 3, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          forall w : Fin 4,
            z ≠
              match w with
              | 0 => v₀
              | 1 => v₁
              | 2 => v₂
              | 3 => apex}
    {harm_internal_disjoint :
      forall {i j : Fin 3}, i ≠ j ->
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (arm j))}
    {harm_p₁₂_disjoint :
      forall i : Fin 3,
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices p₁₂)}
    {C : Set V}
    (hp₁₂_not_C :
      forall {z : V}, z ∈ Walk.InternalVertices p₁₂ -> z ∉ C)
    (harm_not_C :
      forall i : Fin 3, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) -> z ∉ C) :
    forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
      z ∈ Walk.InternalVertices
        ((K4UnsplitSubdivisionData.ofTriangleCone
          hbranch_injective h₀₁ h₀₂ p₁₂ hp₁₂ arm harm_path
          hp₁₂_internal_no_branch harm_internal_no_branch
          harm_internal_disjoint harm_p₁₂_disjoint).model.edgePath hij) ->
        z ∉ C := by
  intro i j hij z hz
  have hdirect_empty {a b : V} (hab : G.Adj a b) {z : V}
      (hz : z ∈ Walk.InternalVertices hab.toWalk) : False :=
    Walk.not_mem_internalVertices_toWalk hab hz
  fin_cases i <;> fin_cases j <;>
    simp [K4Graph, CompleteGraphOn,
      K4UnsplitSubdivisionData.ofTriangleCone] at hij hz ⊢
  · exact (hdirect_empty h₀₁ hz).elim
  · exact (hdirect_empty h₀₂ hz).elim
  · exact harm_not_C (0 : Fin 3)
      (by simpa [Walk.internalVertices_reverse] using hz)
  · exact (hdirect_empty h₀₁.symm hz).elim
  · exact hp₁₂_not_C hz
  · exact harm_not_C (1 : Fin 3)
      (by simpa [Walk.internalVertices_reverse] using hz)
  · exact (hdirect_empty h₀₂.symm hz).elim
  · exact hp₁₂_not_C
      (by simpa [Walk.internalVertices_reverse] using hz)
  · exact harm_not_C (2 : Fin 3)
      (by simpa [Walk.internalVertices_reverse] using hz)
  · exact harm_not_C (0 : Fin 3) hz
  · exact harm_not_C (1 : Fin 3) hz
  · exact harm_not_C (2 : Fin 3) hz


end Schematic.Math.GraphTheory
