import DominatingFourColour.Consequences.NearHajos.Basic.K4Extraction

set_option maxHeartbeats 800000

/-! Attachment carriers from the tail branch of a dominating K5 model. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem DominatingK5Model.exists_tail_k4UnsplitSubdivisionData_first_branch_attachments
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G) :
    Exists fun K : K4UnsplitSubdivisionData G =>
      Exists fun attach : Fin 4 -> V =>
        (forall i : Fin 4,
          attach i ∈ (T.branch (0 : Fin 5)).verts ∧
            G.Adj (attach i) (K.model.branchVertex i)) ∧
          (forall i : Fin 4,
            K.model.branchVertex i ∉ (T.branch (0 : Fin 5)).verts) ∧
            (forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
              z ∈ Walk.InternalVertices (K.model.edgePath hij) ->
                z ∉ (T.branch (0 : Fin 5)).verts) := by
  classical
  rcases T.tailK4.exists_k4UnsplitSubdivisionData_in_branches with
    ⟨K, hK_branch_mem_tail, hK_avoid_tail⟩
  have htail_disjoint_first :
      forall i : Fin 4,
        Disjoint (T.tailK4.branch i).verts (T.branch (0 : Fin 5)).verts := by
    intro i
    exact T.tailK4_branch_disjoint_first i
  have hK_avoid_first := hK_avoid_tail (T.branch (0 : Fin 5)).verts
    htail_disjoint_first
  have hK0_mem : K.model.branchVertex (0 : Fin 4) ∈ (T.branch (3 : Fin 5)).verts := by
    simpa [DominatingK5Model.tailK4, k4TriangleConeBranchIndex] using
      hK_branch_mem_tail (0 : Fin 4)
  have hK1_mem : K.model.branchVertex (1 : Fin 4) ∈ (T.branch (4 : Fin 5)).verts := by
    simpa [DominatingK5Model.tailK4, k4TriangleConeBranchIndex] using
      hK_branch_mem_tail (1 : Fin 4)
  have hK2_mem : K.model.branchVertex (2 : Fin 4) ∈ (T.branch (2 : Fin 5)).verts := by
    simpa [DominatingK5Model.tailK4, k4TriangleConeBranchIndex] using
      hK_branch_mem_tail (2 : Fin 4)
  have hK3_mem : K.model.branchVertex (3 : Fin 4) ∈ (T.branch (1 : Fin 5)).verts := by
    simpa [DominatingK5Model.tailK4, k4TriangleConeBranchIndex] using
      hK_branch_mem_tail (3 : Fin 4)
  obtain ⟨a0, ha0, ha0K⟩ :=
    T.dominates (0 : Fin 5) (3 : Fin 5) (by decide)
      (K.model.branchVertex (0 : Fin 4)) hK0_mem
  obtain ⟨a1, ha1, ha1K⟩ :=
    T.dominates (0 : Fin 5) (4 : Fin 5) (by decide)
      (K.model.branchVertex (1 : Fin 4)) hK1_mem
  obtain ⟨a2, ha2, ha2K⟩ :=
    T.dominates (0 : Fin 5) (2 : Fin 5) (by decide)
      (K.model.branchVertex (2 : Fin 4)) hK2_mem
  obtain ⟨a3, ha3, ha3K⟩ :=
    T.dominates (0 : Fin 5) (1 : Fin 5) (by decide)
      (K.model.branchVertex (3 : Fin 4)) hK3_mem
  let attach : Fin 4 -> V
    | 0 => a0
    | 1 => a1
    | 2 => a2
    | 3 => a3
  refine ⟨K, attach, ?_, hK_avoid_first.1, hK_avoid_first.2⟩
  intro i
  fin_cases i <;> simp [attach, ha0, ha1, ha2, ha3, ha0K, ha1K, ha2K, ha3K]

theorem DominatingK5Model.exists_tail_k4UnsplitSubdivisionData_first_branch_minimal_attachment_carrier
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G) :
    Exists fun K : K4UnsplitSubdivisionData G =>
      Exists fun attach : Fin 4 -> V =>
        (forall i : Fin 4,
          attach i ∈ (T.branch (0 : Fin 5)).verts ∧
            G.Adj (attach i) (K.model.branchVertex i)) ∧
          (forall i : Fin 4,
            K.model.branchVertex i ∉ (T.branch (0 : Fin 5)).verts) ∧
            (forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
              z ∈ Walk.InternalVertices (K.model.edgePath hij) ->
                z ∉ (T.branch (0 : Fin 5)).verts) ∧
              Exists fun B : G.Subgraph =>
                B ≤ T.branch (0 : Fin 5) ∧
                  B.coe.Connected ∧
                    (forall i : Fin 4, attach i ∈ B.verts) ∧
                      forall B' : G.Subgraph,
                        B' ≤ T.branch (0 : Fin 5) ->
                          B'.coe.Connected ->
                            (forall i : Fin 4, attach i ∈ B'.verts) ->
                              B'.verts ⊆ B.verts ->
                                B.verts ⊆ B'.verts := by
  classical
  obtain ⟨K, attach, hattach, hK_branch_not_first,
    hK_internal_not_first⟩ :=
    T.exists_tail_k4UnsplitSubdivisionData_first_branch_attachments
  obtain ⟨B, hB_le, hB_connected, hB_terminal, hB_minimal⟩ :=
    Subgraph.Connected.exists_minimal_connected_subgraph_containing
      (G := G) (T.connected (0 : Fin 5)) attach (fun i => (hattach i).1)
  exact ⟨K, attach, hattach, hK_branch_not_first, hK_internal_not_first,
    B, hB_le, hB_connected, hB_terminal, hB_minimal⟩

theorem DominatingK5Model.exists_tail_k4UnsplitSubdivisionData_first_branch_minimal_attachment_tree_carrier
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G) :
    Exists fun K : K4UnsplitSubdivisionData G =>
      Exists fun attach : Fin 4 -> V =>
        (forall i : Fin 4,
          attach i ∈ (T.branch (0 : Fin 5)).verts ∧
            G.Adj (attach i) (K.model.branchVertex i)) ∧
          (forall i : Fin 4,
            K.model.branchVertex i ∉ (T.branch (0 : Fin 5)).verts) ∧
            (forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
              z ∈ Walk.InternalVertices (K.model.edgePath hij) ->
                z ∉ (T.branch (0 : Fin 5)).verts) ∧
              Exists fun B : G.Subgraph =>
                B ≤ T.branch (0 : Fin 5) ∧
                  B.coe.Connected ∧
                    (forall i : Fin 4, attach i ∈ B.verts) ∧
                      (forall B' : G.Subgraph,
                        B' ≤ T.branch (0 : Fin 5) ->
                          B'.coe.Connected ->
                            (forall i : Fin 4, attach i ∈ B'.verts) ->
                              B'.verts ⊆ B.verts ->
                                B.verts ⊆ B'.verts) ∧
                        Exists fun TB : B.coe.Subgraph =>
                          TB.coe.IsTree ∧ TB.IsSpanning := by
  classical
  obtain ⟨K, attach, hattach, hK_branch_not_first,
    hK_internal_not_first, B, hB_le, hB_connected, hB_terminal,
    hB_minimal⟩ :=
    T.exists_tail_k4UnsplitSubdivisionData_first_branch_minimal_attachment_carrier
  obtain ⟨TB, hTB_tree, hTB_spanning, _hTB_terminal⟩ :=
    Subgraph.Connected.exists_spanning_tree_coe_subgraph_containing
      (B := B) hB_connected attach hB_terminal
  exact ⟨K, attach, hattach, hK_branch_not_first, hK_internal_not_first,
    B, hB_le, hB_connected, hB_terminal, hB_minimal, TB, hTB_tree,
    hTB_spanning⟩

noncomputable def dominating_K4_model_all_singleton_k4UnsplitSubdivisionData
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK4Model G)
    (hsingle : forall i : Fin 4, BranchIsSingleton T i) :
    K4UnsplitSubdivisionData G :=
  K4UnsplitSubdivisionData.ofCliqueEmbedding
    (T.singletonBranchEmbedding hsingle)
    (fun _ _ hne => T.singletonBranchEmbedding_adj hsingle hne)

noncomputable def dominating_K5_model_tail_all_singleton_k4UnsplitSubdivisionData
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i) :
    K4UnsplitSubdivisionData G :=
  dominating_K4_model_all_singleton_k4UnsplitSubdivisionData T.tailK4 htail

noncomputable def ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5)) :
    K4UnsplitSubdivisionData G := by
  classical
  let x : V := hsecond.choose
  have hx_single : (D.model.branch (1 : Fin 5)).verts = {x} :=
    hsecond.choose_spec
  let w : V := D.fourth_singleton.choose
  let v : V := D.fifth_singleton.choose
  have hx_mem : x ∈ (D.model.branch (1 : Fin 5)).verts := by
    simp [hx_single]
  have hw_mem : w ∈ (D.model.branch (3 : Fin 5)).verts := by
    exact D.fourth_mem
  have hv_mem : v ∈ (D.model.branch (4 : Fin 5)).verts := by
    exact D.fifth_mem
  let aw := D.model.dominates (2 : Fin 5) (3 : Fin 5) (by decide) w hw_mem
  let a : V := aw.choose
  have ha : a ∈ (D.model.branch (2 : Fin 5)).verts := aw.choose_spec.1
  have haw : G.Adj a w := aw.choose_spec.2
  let bv := D.model.dominates (2 : Fin 5) (4 : Fin 5) (by decide) v hv_mem
  let b : V := bv.choose
  have hb : b ∈ (D.model.branch (2 : Fin 5)).verts := bv.choose_spec.1
  have hbv : G.Adj b v := bv.choose_spec.2
  let a₂ : (D.model.branch (2 : Fin 5)).verts := ⟨a, ha⟩
  let b₂ : (D.model.branch (2 : Fin 5)).verts := ⟨b, hb⟩
  let path₂_exists := (D.model.connected (2 : Fin 5)).exists_isPath a₂ b₂
  let p₂ : (D.model.branch (2 : Fin 5)).coe.Walk a₂ b₂ := path₂_exists.choose
  have hp₂ : p₂.IsPath := path₂_exists.choose_spec
  let p : G.Walk a b := p₂.map (D.model.branch (2 : Fin 5)).hom
  have hp : p.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hp₂
  have hp_support_branch2 :
      forall {z : V}, z ∈ p.support ->
        z ∈ (D.model.branch (2 : Fin 5)).verts := by
    intro z hz
    exact Walk.support_map_subgraph_hom_subset
      (H := D.model.branch (2 : Fin 5)) p₂ (by simpa [p] using hz)
  have hv_not_p_support : v ∉ p.support := by
    intro hvp
    exact (Set.disjoint_left.mp
      (D.model.vertex_disjoint (2 : Fin 5) (4 : Fin 5) (by decide))
      (hp_support_branch2 hvp)) hv_mem
  let special : G.Walk v a := (p.concat hbv).reverse
  have hspecial_path : special.IsPath := by
    exact (hp.concat hv_not_p_support hbv).reverse
  have hxw : G.Adj x w := by
    simpa [x, w] using hsecond.choose_adj_of_lt (by decide) hw_mem
  have hxv : G.Adj x v := by
    simpa [x, v] using hsecond.choose_adj_of_lt (by decide) hv_mem
  have hxa : G.Adj x a := by
    simpa [x, a] using hsecond.choose_adj_of_lt (by decide) ha
  have hwv : G.Adj w v := D.tail_singletons_adjacent
  have hwa : G.Adj w a := haw.symm
  let eFun : Fin 4 -> V
    | 0 => x
    | 1 => w
    | 2 => v
    | 3 => a
  let branchIndex : Fin 4 -> Fin 5
    | 0 => 1
    | 1 => 3
    | 2 => 4
    | 3 => 2
  have he_injective : Function.Injective eFun := by
    apply D.model.branchVertex_injective_of_index_injective branchIndex
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [branchIndex] at hij ⊢
    · intro i
      fin_cases i
      · simpa [eFun, branchIndex] using hx_mem
      · simpa [eFun, branchIndex] using hw_mem
      · simpa [eFun, branchIndex] using hv_mem
      · simpa [eFun, branchIndex] using ha
  let e : Fin 4 ↪ V := ⟨eFun, he_injective⟩
  have hspecial_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices special ->
        forall i : Fin 4, z ≠ e i := by
    intro z hz i
    have hz_forward : z ∈ Walk.InternalVertices (p.concat hbv) := by
      simpa [special] using (Walk.mem_internalVertices_reverse_iff (p.concat hbv)).mp hz
    have hz_p_support : z ∈ p.support :=
      Walk.mem_support_of_mem_internalVertices_concat p hbv hz_forward
    have hz_branch2 : z ∈ (D.model.branch (2 : Fin 5)).verts :=
      hp_support_branch2 hz_p_support
    fin_cases i
    · intro hzx
      exact (Set.disjoint_left.mp
        (D.model.vertex_disjoint (2 : Fin 5) (1 : Fin 5) (by decide))
        hz_branch2) (by simpa [e, eFun, hzx] using hx_mem)
    · intro hzw
      exact (Set.disjoint_left.mp
        (D.model.vertex_disjoint (2 : Fin 5) (3 : Fin 5) (by decide))
        hz_branch2) (by simpa [e, eFun, w, hzw] using hw_mem)
    · exact hz.2.1
    · exact hz.2.2
  have h_adj :
      forall {i j : Fin 4},
        K4Graph.Adj i j ->
          ¬ ((i = (2 : Fin 4) ∧ j = (3 : Fin 4)) ∨
              (i = (3 : Fin 4) ∧ j = (2 : Fin 4))) ->
            G.Adj (e i) (e j) := by
    intro i j hij hnot
    fin_cases i <;> fin_cases j <;>
      simp [K4Graph, CompleteGraphOn, e, eFun] at hij hnot ⊢
    · exact hxw
    · exact hxv
    · exact hxa
    · exact hxw.symm
    · exact hwv
    · exact hwa
    · exact hxv.symm
    · exact hwv.symm
    · exact hxa.symm
    · exact hwa.symm
  let M : StrictSubdivisionModel K4Graph G :=
    StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath
      e special hspecial_path h_adj hspecial_internal_no_branch
  refine ⟨M, ?_, ?_⟩
  · exact
      StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath_edgeUnsplit_of_not_special
        e special hspecial_path h_adj hspecial_internal_no_branch
        (show K4Graph.Adj (0 : Fin 4) (1 : Fin 4) from by decide)
        (by
          intro h
          rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h)
  · exact
      StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath_edgeUnsplit_of_not_special
        e special hspecial_path h_adj hspecial_internal_no_branch
        (show K4Graph.Adj (0 : Fin 4) (2 : Fin 4) from by decide)
        (by
          intro h
          rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h)


end Schematic.Math.GraphTheory
