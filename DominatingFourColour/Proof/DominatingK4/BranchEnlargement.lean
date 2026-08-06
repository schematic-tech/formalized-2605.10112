import DominatingFourColour.Basic

/-!
Enlarging a branch set and lifting a dominating model across a one-separation.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace DominatingK4

theorem disjoint_sup_left_verts
    {A B C : G.Subgraph}
    (hAC : Disjoint A.verts C.verts)
    (hBC : Disjoint B.verts C.verts) :
    Disjoint (A ⊔ B).verts C.verts := by
  rw [SimpleGraph.Subgraph.verts_sup]
  exact hAC.sup_left hBC

theorem disjoint_sup_right_verts
    {A B C : G.Subgraph}
    (hCA : Disjoint C.verts A.verts)
    (hCB : Disjoint C.verts B.verts) :
    Disjoint C.verts (A ⊔ B).verts := by
  rw [SimpleGraph.Subgraph.verts_sup]
  exact hCA.sup_right hCB

end DominatingK4

open DominatingK4

/-- Enlarge the first branch of a dominating model by a connected, late-branch-disjoint subgraph. -/
def DominatingModel.enlargeFirstBranch
    {t : Nat}
    (T : DominatingModel G (t + 1))
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hmeet : ((T.branch 0) ⊓ H).verts.Nonempty)
    (hH_disjoint :
      forall j : Fin (t + 1), j ≠ 0 -> Disjoint H.verts (T.branch j).verts) :
    DominatingModel G (t + 1) where
  branch i := if i = 0 then T.branch 0 ⊔ H else T.branch i
  connected := by
    intro i
    by_cases hi : i = 0
    · subst i
      exact (SimpleGraph.Subgraph.connected_sup
        (SimpleGraph.Subgraph.connected_iff'.mpr (T.connected 0)).preconnected
        (SimpleGraph.Subgraph.connected_iff'.mpr hH_connected).preconnected
        hmeet).coe
    · rw [if_neg hi]
      exact T.connected i
  vertex_disjoint := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := hij.symm
      simp only [if_pos, if_neg hj]
      exact disjoint_sup_left_verts
        (T.vertex_disjoint 0 j hij)
        (hH_disjoint j hj)
    · by_cases hj : j = 0
      · subst j
        simp only [if_neg hi, if_pos]
        exact disjoint_sup_right_verts
          (T.vertex_disjoint i 0 hij)
          (hH_disjoint i hi).symm
      · simp only [if_neg hi, if_neg hj]
        exact T.vertex_disjoint i j hij
  dominates := by
    intro i j hij v hv
    have hj : j ≠ 0 := by
      intro hj
      subst j
      exact (Fin.not_lt_zero i) hij
    simp only [if_neg hj] at hv
    by_cases hi : i = 0
    · subst i
      simp only [if_pos, SimpleGraph.Subgraph.verts_sup]
      obtain ⟨u, hu, huv⟩ := T.dominates 0 j hij v hv
      exact ⟨u, Or.inl hu, huv⟩
    · simp only [if_neg hi]
      exact T.dominates i j hij v hv

def DominatingK4Model.enlargeFirstBranch
    (T : DominatingK4Model G)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hmeet : ((T.branch (0 : Fin 4)) ⊓ H).verts.Nonempty)
    (hH_disjoint_late : forall j : Fin 4, 0 < (j : Nat) ->
      Disjoint H.verts (T.branch j).verts) :
    DominatingK4Model G :=
  DominatingModel.enlargeFirstBranch (t := 3) T H hH_connected hmeet
    (fun j hj => hH_disjoint_late j (Fin.pos_iff_ne_zero.2 hj))

theorem dominating_K4_lift_across_one_separation
    (S : Separation G)
    (sep : V)
    (hleft_connected : (((⊤ : G.Subgraph).induce S.left).coe).Connected)
    (hsep_left : sep ∈ S.left)
    (hsep_right : sep ∈ S.right)
    (hseparator_unique : forall x : V, x ∈ S.left -> x ∈ S.right -> x = sep)
    (T : DominatingK4Model (G.induce S.right))
    (hsep_branch :
      (⟨sep, hsep_right⟩ : S.right) ∈ (T.branch (0 : Fin 4)).verts) :
    Exists fun T' : DominatingK4Model G =>
      forall x : V, x ∈ S.left -> x ∈ (T'.branch (0 : Fin 4)).verts := by
  classical
  let Tg : DominatingK4Model G := T.ofInduce
  let H : G.Subgraph := (⊤ : G.Subgraph).induce S.left
  have hsep_lift_branch : sep ∈ (Tg.branch (0 : Fin 4)).verts := by
    simp only [Tg, DominatingModel.ofInduce, DominatingModel.map,
      SimpleGraph.Subgraph.map_verts,
      Set.mem_image]
    exact ⟨⟨sep, hsep_right⟩, hsep_branch, rfl⟩
  have hmeet : ((Tg.branch (0 : Fin 4)) ⊓ H).verts.Nonempty := by
    refine ⟨sep, ?_, ?_⟩
    · exact hsep_lift_branch
    · simp [H, hsep_left]
  have hH_disjoint_late : forall j : Fin 4, 0 < (j : Nat) ->
      Disjoint H.verts (Tg.branch j).verts := by
    intro j hj
    rw [Set.disjoint_left]
    intro x hxH hxT
    have hx_left : x ∈ S.left := by
      simpa [H] using hxH
    have hx_right : x ∈ S.right := by
      simp only [Tg, DominatingModel.ofInduce, DominatingModel.map,
        SimpleGraph.Subgraph.map_verts,
        Set.mem_image] at hxT
      rcases hxT with ⟨y, _hy, hyx⟩
      rw [← hyx]
      exact y.2
    have hx_sep : x = sep := hseparator_unique x hx_left hx_right
    have hzero_ne_j : (0 : Fin 4) ≠ j := by
      intro h
      subst j
      simp at hj
    have hxT_sub : (⟨sep, hsep_right⟩ : S.right) ∈ (T.branch j).verts := by
      simp only [Tg, DominatingModel.ofInduce, DominatingModel.map,
        SimpleGraph.Subgraph.map_verts,
        Set.mem_image] at hxT
      rcases hxT with ⟨y, hy, hyx⟩
      have hy_eq : y = ⟨sep, hsep_right⟩ := by
        apply Subtype.ext
        exact hyx.trans hx_sep
      simpa [hy_eq] using hy
    exact Set.disjoint_left.mp (T.vertex_disjoint (0 : Fin 4) j hzero_ne_j)
      hsep_branch hxT_sub
  let T' : DominatingK4Model G :=
    Tg.enlargeFirstBranch H hleft_connected hmeet hH_disjoint_late
  refine ⟨T', ?_⟩
  intro x hx_left
  change x ∈ ((Tg.branch (0 : Fin 4) ⊔ H).verts)
  rw [SimpleGraph.Subgraph.verts_sup]
  exact Or.inr (by simp [H, hx_left])

end Schematic.Math.GraphTheory
