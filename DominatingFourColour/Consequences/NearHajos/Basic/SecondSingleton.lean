import DominatingFourColour.Consequences.NearHajos.Basic.TailAttachments

set_option maxHeartbeats 800000

/-! The second-singleton branch and its K4 attachment carrier. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

set_option maxHeartbeats 0 in
theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_k4_edgeUnsplit_of_not_special
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    {i j : Fin 4}
    (hij : K4Graph.Adj i j)
    (hnot :
      ¬ ((i = (2 : Fin 4) ∧ j = (3 : Fin 4)) ∨
          (i = (3 : Fin 4) ∧ j = (2 : Fin 4)))) :
    (D.second_singleton_k4UnsplitSubdivisionData hsecond).model.EdgeUnsplit hij := by
  classical
  simp [ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
    StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath,
    graphEmbeddingWithOneEdgePath_walk_of_not_special, hnot,
    StrictSubdivisionModel.EdgeUnsplit]

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_k4_branchVertex_not_first
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5)) :
    forall i : Fin 4,
      (D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i ∉
        (D.model.branch (0 : Fin 5)).verts := by
  classical
  intro i hmem
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
  fin_cases i
  · exact (Set.disjoint_left.mp
      (D.model.vertex_disjoint (1 : Fin 5) (0 : Fin 5) (by decide))
      (by simpa [ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
        x] using hx_mem)) hmem
  · exact (Set.disjoint_left.mp
      (D.model.vertex_disjoint (3 : Fin 5) (0 : Fin 5) (by decide))
      (by simpa [ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
        w] using hw_mem)) hmem
  · exact (Set.disjoint_left.mp
      (D.model.vertex_disjoint (4 : Fin 5) (0 : Fin 5) (by decide))
      (by simpa [ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
        v] using hv_mem)) hmem
  · exact (Set.disjoint_left.mp
      (D.model.vertex_disjoint (2 : Fin 5) (0 : Fin 5) (by decide))
      (by simpa [ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
        a, aw] using ha)) hmem

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_k4_internal_not_first
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5)) :
    forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
      z ∈ Walk.InternalVertices
          ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.edgePath hij) ->
        z ∉ (D.model.branch (0 : Fin 5)).verts := by
  classical
  intro i j hij z hz hfirst
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
  have hxw : G.Adj x w := by
    simpa [x, w] using hsecond.choose_adj_of_lt (by decide) hw_mem
  have hxv : G.Adj x v := by
    simpa [x, v] using hsecond.choose_adj_of_lt (by decide) hv_mem
  have hxa : G.Adj x a := by
    simpa [x, a] using hsecond.choose_adj_of_lt (by decide) ha
  have hwv : G.Adj w v := D.tail_singletons_adjacent
  have hwa : G.Adj w a := haw.symm
  let bv := D.model.dominates (2 : Fin 5) (4 : Fin 5) (by decide) v hv_mem
  let b : V := bv.choose
  have hb : b ∈ (D.model.branch (2 : Fin 5)).verts := bv.choose_spec.1
  have hbv : G.Adj b v := bv.choose_spec.2
  let a₂ : (D.model.branch (2 : Fin 5)).verts := ⟨a, ha⟩
  let b₂ : (D.model.branch (2 : Fin 5)).verts := ⟨b, hb⟩
  let path₂_exists := (D.model.connected (2 : Fin 5)).exists_isPath a₂ b₂
  let p₂ : (D.model.branch (2 : Fin 5)).coe.Walk a₂ b₂ := path₂_exists.choose
  let p : G.Walk a b := p₂.map (D.model.branch (2 : Fin 5)).hom
  have hp_support_branch2 :
      forall {z : V}, z ∈ p.support ->
        z ∈ (D.model.branch (2 : Fin 5)).verts := by
    intro z hz
    exact Walk.support_map_subgraph_hom_subset
      (H := D.model.branch (2 : Fin 5)) p₂ (by simpa [p] using hz)
  have hspecial_support_branch2 :
      forall {z : V}, z ∈ Walk.InternalVertices ((p.concat hbv).reverse) ->
        z ∈ (D.model.branch (2 : Fin 5)).verts := by
    intro z hz
    have hz_forward : z ∈ Walk.InternalVertices (p.concat hbv) := by
      exact (Walk.mem_internalVertices_reverse_iff (p.concat hbv)).mp hz
    exact hp_support_branch2
      (Walk.mem_support_of_mem_internalVertices_concat p hbv hz_forward)
  have hspecial_reverse_support_branch2 :
      forall {z : V}, z ∈ Walk.InternalVertices (p.concat hbv) ->
        z ∈ (D.model.branch (2 : Fin 5)).verts := by
    intro z hz
    exact hp_support_branch2
      (Walk.mem_support_of_mem_internalVertices_concat p hbv hz)
  have hcontradict_branch2
      (hz_branch2 : z ∈ (D.model.branch (2 : Fin 5)).verts) : False :=
    (Set.disjoint_left.mp
      (D.model.vertex_disjoint (2 : Fin 5) (0 : Fin 5) (by decide))
      hz_branch2) hfirst
  let eFun : Fin 4 -> V
    | 0 => x
    | 1 => w
    | 2 => v
    | 3 => a
  have h_adj_local :
      forall {i j : Fin 4},
        K4Graph.Adj i j ->
          ¬ ((i = (2 : Fin 4) ∧ j = (3 : Fin 4)) ∨
              (i = (3 : Fin 4) ∧ j = (2 : Fin 4))) ->
            G.Adj (eFun i) (eFun j) := by
    intro i j hij hnot
    fin_cases i <;> fin_cases j <;>
      simp [K4Graph, CompleteGraphOn, eFun] at hij hnot ⊢
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
  by_cases hspecial :
      (i = (2 : Fin 4) ∧ j = (3 : Fin 4)) ∨
        (i = (3 : Fin 4) ∧ j = (2 : Fin 4))
  · rcases hspecial with hforward | hreverse
    · rcases hforward with ⟨rfl, rfl⟩
      exact hcontradict_branch2
        (hspecial_support_branch2
          (by
            simpa [ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
              StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath,
              graphEmbeddingWithOneEdgePath_walk_forward, w, v, a, aw, bv, p] using hz))
    · rcases hreverse with ⟨rfl, rfl⟩
      exact hcontradict_branch2
        (hspecial_reverse_support_branch2
          (by
            simpa [ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
              StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath,
              graphEmbeddingWithOneEdgePath_walk_reverse, w, v, a, aw, bv, p] using hz))
  · exact False.elim
      (by
        have hz_toWalk :
            z ∈ Walk.InternalVertices ((h_adj_local hij hspecial).toWalk) := by
          simpa [ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
            StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath,
            graphEmbeddingWithOneEdgePath_walk_of_not_special,
            hspecial, K4Graph, CompleteGraphOn, x, w, v, a, aw, bv,
            eFun, h_adj_local] using hz
        exact Walk.not_mem_internalVertices_toWalk
          (h_adj_local hij hspecial) hz_toWalk)

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_first_branch_attachments
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5)) :
    Exists fun attach : Fin 4 -> V =>
      forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i) := by
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
  let d0 := D.model.dominates (0 : Fin 5) (1 : Fin 5) (by decide) x hx_mem
  let d1 := D.model.dominates (0 : Fin 5) (3 : Fin 5) (by decide) w hw_mem
  let d2 := D.model.dominates (0 : Fin 5) (4 : Fin 5) (by decide) v hv_mem
  let d3 := D.model.dominates (0 : Fin 5) (2 : Fin 5) (by decide) a ha
  let attach : Fin 4 -> V
    | 0 => d0.choose
    | 1 => d1.choose
    | 2 => d2.choose
    | 3 => d3.choose
  refine ⟨attach, ?_⟩
  intro i
  fin_cases i
  · exact ⟨d0.choose_spec.1, by
      simpa [attach,
        ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
        x] using d0.choose_spec.2⟩
  · exact ⟨d1.choose_spec.1, by
      simpa [attach,
        ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
        w] using d1.choose_spec.2⟩
  · exact ⟨d2.choose_spec.1, by
      simpa [attach,
        ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
        v] using d2.choose_spec.2⟩
  · exact ⟨d3.choose_spec.1, by
      simpa [attach,
        ThirdBranchPathAndTailInducedCycleData.second_singleton_k4UnsplitSubdivisionData,
        a, aw] using d3.choose_spec.2⟩

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_first_branch_minimal_carrier
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5)) :
    Exists fun attach : Fin 4 -> V =>
      (forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
        Exists fun B : G.Subgraph =>
          B ≤ D.model.branch (0 : Fin 5) ∧
            B.coe.Connected ∧
              (forall i : Fin 4, attach i ∈ B.verts) ∧
                forall B' : G.Subgraph,
                  B' ≤ D.model.branch (0 : Fin 5) ->
                    B'.coe.Connected ->
                      (forall i : Fin 4, attach i ∈ B'.verts) ->
                        B'.verts ⊆ B.verts ->
                          B.verts ⊆ B'.verts := by
  classical
  obtain ⟨attach, hattach⟩ :=
    D.second_singleton_core_first_branch_attachments hsecond
  obtain ⟨B, hB_le, hB_connected, hB_terminal, hB_minimal⟩ :=
    Subgraph.Connected.exists_minimal_connected_subgraph_containing
      (G := G) (D.model.connected (0 : Fin 5)) attach (fun i => (hattach i).1)
  exact ⟨attach, hattach, B, hB_le, hB_connected, hB_terminal, hB_minimal⟩

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_first_branch_minimal_tree_carrier
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5)) :
    Exists fun attach : Fin 4 -> V =>
      (forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
        Exists fun B : G.Subgraph =>
          B ≤ D.model.branch (0 : Fin 5) ∧
            B.coe.Connected ∧
              (forall i : Fin 4, attach i ∈ B.verts) ∧
                (forall B' : G.Subgraph,
                  B' ≤ D.model.branch (0 : Fin 5) ->
                    B'.coe.Connected ->
                      (forall i : Fin 4, attach i ∈ B'.verts) ->
                        B'.verts ⊆ B.verts ->
                          B.verts ⊆ B'.verts) ∧
                  Exists fun TB : B.coe.Subgraph =>
                    TB.coe.IsTree ∧ TB.IsSpanning := by
  classical
  obtain ⟨attach, hattach, B, hB_le, hB_connected, hB_terminal, hB_minimal⟩ :=
    D.second_singleton_core_first_branch_minimal_carrier hsecond
  obtain ⟨TB, hTB_tree, hTB_spanning, _hTB_terminal⟩ :=
    Subgraph.Connected.exists_spanning_tree_coe_subgraph_containing
      (B := B) hB_connected attach hB_terminal
  exact ⟨attach, hattach, B, hB_le, hB_connected, hB_terminal, hB_minimal,
    TB, hTB_tree, hTB_spanning⟩

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_first_branch_large_minimal_attachment_carrier
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (hno_small :
      Not (Exists fun attach : Fin 4 -> V =>
        Exists fun B : G.Subgraph =>
          (forall i : Fin 4,
            attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
              G.Adj (attach i)
                ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
            B ≤ D.model.branch (0 : Fin 5) ∧
              (forall i : Fin 4, attach i ∈ B.verts) ∧
                B.verts.ncard <= 2)) :
    Exists fun attach : Fin 4 -> V =>
      (forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
        Exists fun B : G.Subgraph =>
          B ≤ D.model.branch (0 : Fin 5) ∧
            B.coe.Connected ∧
              (forall i : Fin 4, attach i ∈ B.verts) ∧
                (forall B' : G.Subgraph,
                  B' ≤ D.model.branch (0 : Fin 5) ->
                    B'.coe.Connected ->
                      (forall i : Fin 4, attach i ∈ B'.verts) ->
                        B'.verts ⊆ B.verts ->
                          B.verts ⊆ B'.verts) ∧
                  3 <= B.verts.ncard := by
  classical
  obtain ⟨attach, hattach, B, hB_le, hB_connected, hB_terminal, hB_minimal⟩ :=
    D.second_singleton_core_first_branch_minimal_carrier hsecond
  have hB_large : 3 <= B.verts.ncard := by
    by_contra hlt
    have hB_small : B.verts.ncard <= 2 := by omega
    exact hno_small ⟨attach, B, hattach, hB_le, hB_terminal, hB_small⟩
  exact ⟨attach, hattach, B, hB_le, hB_connected, hB_terminal, hB_minimal,
    hB_large⟩

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_first_branch_large_minimal_attachment_carrier_three_distinct
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (hno_two :
      Not (Exists fun attach : Fin 4 -> V =>
        Exists fun u : V =>
          Exists fun v : V =>
            (forall i : Fin 4,
              attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
                G.Adj (attach i)
                  ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
              u ∈ (D.model.branch (0 : Fin 5)).verts ∧
                v ∈ (D.model.branch (0 : Fin 5)).verts ∧
                  (forall i : Fin 4, attach i = u ∨ attach i = v)))
    (hno_small :
      Not (Exists fun attach : Fin 4 -> V =>
        Exists fun B : G.Subgraph =>
          (forall i : Fin 4,
            attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
              G.Adj (attach i)
                ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
            B ≤ D.model.branch (0 : Fin 5) ∧
              (forall i : Fin 4, attach i ∈ B.verts) ∧
                B.verts.ncard <= 2)) :
    Exists fun attach : Fin 4 -> V =>
      (forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
        3 <= (Set.range attach).ncard ∧
          Exists fun B : G.Subgraph =>
            B ≤ D.model.branch (0 : Fin 5) ∧
              B.coe.Connected ∧
                (forall i : Fin 4, attach i ∈ B.verts) ∧
                  (forall B' : G.Subgraph,
                    B' ≤ D.model.branch (0 : Fin 5) ->
                      B'.coe.Connected ->
                        (forall i : Fin 4, attach i ∈ B'.verts) ->
                          B'.verts ⊆ B.verts ->
                            B.verts ⊆ B'.verts) ∧
                    3 <= B.verts.ncard := by
  classical
  obtain ⟨attach, hattach, B, hB_le, hB_connected, hB_terminal,
    hB_minimal, hB_large⟩ :=
    D.second_singleton_core_first_branch_large_minimal_attachment_carrier
      hsecond hno_small
  have hnot_two_attach :
      Not (Exists fun u : V =>
        Exists fun v : V =>
          u ∈ (D.model.branch (0 : Fin 5)).verts ∧
            v ∈ (D.model.branch (0 : Fin 5)).verts ∧
              forall i : Fin 4, attach i = u ∨ attach i = v) := by
    rintro ⟨u, v, hu, hv, hvalues⟩
    exact hno_two ⟨attach, u, v, hattach, hu, hv, hvalues⟩
  have hattach_range_large :
      3 <= (Set.range attach).ncard :=
    fin4_range_ncard_ge_three_of_not_two_values_in_set
      (V := V) (A := (D.model.branch (0 : Fin 5)).verts)
      attach (fun i => (hattach i).1) hnot_two_attach
  exact ⟨attach, hattach, hattach_range_large, B, hB_le, hB_connected,
    hB_terminal, hB_minimal, hB_large⟩

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_first_branch_large_minimal_attachment_carrier_three_distinct_indices
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (hno_two :
      Not (Exists fun attach : Fin 4 -> V =>
        Exists fun u : V =>
          Exists fun v : V =>
            (forall i : Fin 4,
              attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
                G.Adj (attach i)
                  ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
              u ∈ (D.model.branch (0 : Fin 5)).verts ∧
                v ∈ (D.model.branch (0 : Fin 5)).verts ∧
                  (forall i : Fin 4, attach i = u ∨ attach i = v)))
    (hno_small :
      Not (Exists fun attach : Fin 4 -> V =>
        Exists fun B : G.Subgraph =>
          (forall i : Fin 4,
            attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
              G.Adj (attach i)
                ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
            B ≤ D.model.branch (0 : Fin 5) ∧
              (forall i : Fin 4, attach i ∈ B.verts) ∧
                B.verts.ncard <= 2)) :
    Exists fun attach : Fin 4 -> V =>
      (forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
        Exists fun i : Fin 4 =>
          Exists fun j : Fin 4 =>
            Exists fun k : Fin 4 =>
              attach i ≠ attach j ∧
                attach i ≠ attach k ∧
                  attach j ≠ attach k ∧
                    Exists fun B : G.Subgraph =>
                      B ≤ D.model.branch (0 : Fin 5) ∧
                        B.coe.Connected ∧
                          (forall i : Fin 4, attach i ∈ B.verts) ∧
                            (forall B' : G.Subgraph,
                              B' ≤ D.model.branch (0 : Fin 5) ->
                                B'.coe.Connected ->
                                  (forall i : Fin 4, attach i ∈ B'.verts) ->
                                    B'.verts ⊆ B.verts ->
                                      B.verts ⊆ B'.verts) ∧
                              3 <= B.verts.ncard := by
  classical
  obtain ⟨attach, hattach, hattach_large, B, hB_le, hB_connected,
    hB_terminal, hB_minimal, hB_large⟩ :=
    D.second_singleton_core_first_branch_large_minimal_attachment_carrier_three_distinct
      hsecond hno_two hno_small
  obtain ⟨i, j, k, hij, hik, hjk⟩ :=
    fin4_exists_three_pairwise_distinct_values_of_range_ncard_ge_three
      attach hattach_large
  exact ⟨attach, hattach, i, j, k, hij, hik, hjk, B, hB_le, hB_connected,
    hB_terminal, hB_minimal, hB_large⟩

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_first_branch_large_minimal_attachment_tree_carrier
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (hno_two :
      Not (Exists fun attach : Fin 4 -> V =>
        Exists fun u : V =>
          Exists fun v : V =>
            (forall i : Fin 4,
              attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
                G.Adj (attach i)
                  ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
              u ∈ (D.model.branch (0 : Fin 5)).verts ∧
                v ∈ (D.model.branch (0 : Fin 5)).verts ∧
                  (forall i : Fin 4, attach i = u ∨ attach i = v)))
    (hno_small :
      Not (Exists fun attach : Fin 4 -> V =>
        Exists fun B : G.Subgraph =>
          (forall i : Fin 4,
            attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
              G.Adj (attach i)
                ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
            B ≤ D.model.branch (0 : Fin 5) ∧
              (forall i : Fin 4, attach i ∈ B.verts) ∧
                B.verts.ncard <= 2)) :
    Exists fun attach : Fin 4 -> V =>
      (forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
        Exists fun i : Fin 4 =>
          Exists fun j : Fin 4 =>
            Exists fun k : Fin 4 =>
              attach i ≠ attach j ∧
                attach i ≠ attach k ∧
                  attach j ≠ attach k ∧
                    Exists fun B : G.Subgraph =>
                      B ≤ D.model.branch (0 : Fin 5) ∧
                        B.coe.Connected ∧
                          (forall i : Fin 4, attach i ∈ B.verts) ∧
                            (forall B' : G.Subgraph,
                              B' ≤ D.model.branch (0 : Fin 5) ->
                                B'.coe.Connected ->
                                  (forall i : Fin 4, attach i ∈ B'.verts) ->
                                    B'.verts ⊆ B.verts ->
                                      B.verts ⊆ B'.verts) ∧
                              3 <= B.verts.ncard ∧
                                Exists fun TB : B.coe.Subgraph =>
                                  TB.coe.IsTree ∧ TB.IsSpanning := by
  classical
  obtain ⟨attach, hattach, i, j, k, hij, hik, hjk, B, hB_le,
    hB_connected, hB_terminal, hB_minimal, hB_large⟩ :=
    D.second_singleton_core_first_branch_large_minimal_attachment_carrier_three_distinct_indices
      hsecond hno_two hno_small
  obtain ⟨TB, hTB_tree, hTB_spanning, _hTB_terminal⟩ :=
    Subgraph.Connected.exists_spanning_tree_coe_subgraph_containing
      (B := B) hB_connected attach hB_terminal
  exact ⟨attach, hattach, i, j, k, hij, hik, hjk, B, hB_le, hB_connected,
    hB_terminal, hB_minimal, hB_large, TB, hTB_tree, hTB_spanning⟩


end Schematic.Math.GraphTheory
