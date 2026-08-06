import DominatingFourColour.Consequences.NearHajos.Basic.UnsplitData

set_option maxHeartbeats 800000

/-! Extracting two-unsplit-edge K4 subdivisions from dominating K4 models. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem DominatingK4Model.exists_two_unsplit_spine_cone_data
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK4Model G) :
    Exists fun root : V =>
      Exists fun x₁ : V =>
        Exists fun x₂ : V =>
          Exists fun x₃ : V =>
            Exists fun y₁₃ : V =>
              Exists fun attach : Fin 3 -> V =>
                Exists fun stem : forall i : Fin 3, G.Walk root (attach i) =>
                  root ∈ (T.branch (0 : Fin 4)).verts ∧
                    x₁ ∈ (T.branch (1 : Fin 4)).verts ∧
                      x₂ ∈ (T.branch (2 : Fin 4)).verts ∧
                        x₃ ∈ (T.branch (3 : Fin 4)).verts ∧
                          y₁₃ ∈ (T.branch (1 : Fin 4)).verts ∧
                            (forall i : Fin 3,
                              attach i ∈ (T.branch (0 : Fin 4)).verts) ∧
                              G.Adj x₁ x₂ ∧
                                G.Adj x₂ x₃ ∧
                                  G.Adj y₁₃ x₃ ∧
                                    G.Adj (attach (0 : Fin 3)) x₁ ∧
                                      G.Adj (attach (1 : Fin 3)) x₂ ∧
                                        G.Adj (attach (2 : Fin 3)) x₃ ∧
                                          Exists fun p₁₃ : G.Walk x₁ y₁₃ =>
                                            p₁₃.IsPath ∧
                                              p₁₃.toSubgraph ≤
                                                T.branch (1 : Fin 4) ∧
                                                (forall i : Fin 3,
                                                  (stem i).IsPath) ∧
                                                  (forall i : Fin 3,
                                                    (stem i).toSubgraph ≤
                                                      T.branch (0 : Fin 4)) ∧
                                                    (forall {i j : Fin 3}, i ≠ j ->
                                                      Disjoint
                                                        {z : V | z ∈ (stem i).support ∧
                                                          z ≠ root}
                                                        {z : V | z ∈ (stem j).support ∧
                                                          z ≠ root}) := by
  classical
  obtain ⟨x₃, hx₃⟩ := (T.connected (3 : Fin 4)).nonempty
  obtain ⟨x₂, hx₂, hx₂x₃⟩ :=
    T.dominates (2 : Fin 4) (3 : Fin 4) (by decide) x₃ hx₃
  obtain ⟨x₁, hx₁, hx₁x₂⟩ :=
    T.dominates (1 : Fin 4) (2 : Fin 4) (by decide) x₂ hx₂
  obtain ⟨y₁₃, hy₁₃, hy₁₃x₃⟩ :=
    T.dominates (1 : Fin 4) (3 : Fin 4) (by decide) x₃ hx₃
  obtain ⟨a₁, ha₁, ha₁x₁⟩ :=
    T.dominates (0 : Fin 4) (1 : Fin 4) (by decide) x₁ hx₁
  obtain ⟨a₂, ha₂, ha₂x₂⟩ :=
    T.dominates (0 : Fin 4) (2 : Fin 4) (by decide) x₂ hx₂
  obtain ⟨a₃, ha₃, ha₃x₃⟩ :=
    T.dominates (0 : Fin 4) (3 : Fin 4) (by decide) x₃ hx₃
  let attach : Fin 3 -> V
    | 0 => a₁
    | 1 => a₂
    | 2 => a₃
  have hattach_mem : forall i : Fin 3,
      attach i ∈ (T.branch (0 : Fin 4)).verts := by
    intro i
    fin_cases i <;> simp [attach, ha₁, ha₂, ha₃]
  let terminal₀ : Fin 3 -> (T.branch (0 : Fin 4)).verts :=
    fun i => ⟨attach i, hattach_mem i⟩
  obtain ⟨T₀, hT₀_tree, hT₀_spanning, hT₀_terminal⟩ :=
    Subgraph.Connected.exists_spanning_tree_coe_subgraph_containing
      (B := T.branch (0 : Fin 4)) (T.connected (0 : Fin 4))
      attach hattach_mem
  let terminalT₀ : Fin 3 -> T₀.verts :=
    fun i => ⟨terminal₀ i, by
      simpa [terminal₀] using hT₀_terminal i⟩
  obtain ⟨rootT₀, stemT₀, hstemT₀_le, hstemT₀_path,
    hstemT₀_disjoint⟩ :=
    Subgraph.tree_exists_three_terminal_rooted_paths
      (G := (T.branch (0 : Fin 4)).coe) (T := T₀)
      hT₀_tree terminalT₀
  let root : V := (rootT₀ : (T.branch (0 : Fin 4)).verts)
  let stem : forall i : Fin 3, G.Walk root (attach i) := fun i =>
    ((stemT₀ i).map (T.branch (0 : Fin 4)).hom).copy rfl (by
      rfl)
  have hstem_path : forall i : Fin 3, (stem i).IsPath := by
    intro i
    simpa [stem] using
      (SimpleGraph.Walk.isPath_copy
        ((stemT₀ i).map (T.branch (0 : Fin 4)).hom) rfl (by rfl)).mpr
        (SimpleGraph.Walk.map_isPath_of_injective
          SimpleGraph.Subgraph.hom_injective (hstemT₀_path i))
  have hstem_le : forall i : Fin 3,
      (stem i).toSubgraph ≤ T.branch (0 : Fin 4) := by
    intro i
    simpa [stem] using Walk.map_subgraph_toSubgraph_le
      (H := T.branch (0 : Fin 4)) (stemT₀ i)
  have hstem_disjoint :
      forall {i j : Fin 3}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stem i).support ∧ z ≠ root}
          {z : V | z ∈ (stem j).support ∧ z ≠ root} := by
    intro i j hij
    have hraw :
        Disjoint
          {z : V | z ∈ ((stemT₀ i).map (T.branch (0 : Fin 4)).hom).support ∧
            z ≠ root}
          {z : V | z ∈ ((stemT₀ j).map (T.branch (0 : Fin 4)).hom).support ∧
            z ≠ root} :=
      Subgraph.walk_family_mapped_punctured_supports_disjoint
        (B := T.branch (0 : Fin 4)) stemT₀ hstemT₀_disjoint hij
    simpa [stem] using hraw
  let x₁B : (T.branch (1 : Fin 4)).verts := ⟨x₁, hx₁⟩
  let y₁₃B : (T.branch (1 : Fin 4)).verts := ⟨y₁₃, hy₁₃⟩
  obtain ⟨p₁₃, hp₁₃_path, hp₁₃_le⟩ :=
    Subgraph.Connected.exists_path_between
      (G := G) (H := T.branch (1 : Fin 4))
      (T.connected (1 : Fin 4)) hx₁ hy₁₃
  refine ⟨root, x₁, x₂, x₃, y₁₃, attach, stem, ?_, hx₁, hx₂, hx₃,
    hy₁₃, hattach_mem, hx₁x₂, hx₂x₃, hy₁₃x₃, ?_, ?_, ?_,
    p₁₃, hp₁₃_path, hp₁₃_le, hstem_path, hstem_le, hstem_disjoint⟩
  · exact rootT₀.1.2
  · simpa [attach] using ha₁x₁
  · simpa [attach] using ha₂x₂
  · simpa [attach] using ha₃x₃

/-- Branch indices of the triangle-cone K4 model inside a dominating K4 model. -/
def k4TriangleConeBranchIndex : Fin 4 -> Fin 4
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0

theorem DominatingK4Model.exists_k4UnsplitSubdivisionData_in_branches
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK4Model G) :
    Exists fun K : K4UnsplitSubdivisionData G =>
      (forall i : Fin 4,
        K.model.branchVertex i ∈ (T.branch (k4TriangleConeBranchIndex i)).verts) ∧
        forall C : Set V,
          (forall i : Fin 4, Disjoint (T.branch i).verts C) ->
            (forall i : Fin 4, K.model.branchVertex i ∉ C) ∧
              (forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
                z ∈ Walk.InternalVertices (K.model.edgePath hij) -> z ∉ C) := by
  classical
  rcases T.exists_two_unsplit_spine_cone_data with
    ⟨root, x₁, x₂, x₃, y₁₃, attach, stem,
      hroot, hx₁, hx₂, hx₃, hy₁₃, hattach_mem,
      hx₁x₂, hx₂x₃, hy₁₃x₃, ha₁x₁, ha₂x₂, ha₃x₃,
      p₁₃, hp₁₃_path, hp₁₃_le, hstem_path, hstem_le, hstem_disjoint⟩
  let side : G.Walk x₃ x₁ := (p₁₃.concat hy₁₃x₃).reverse
  let stemIndex : Fin 3 -> Fin 3
    | 0 => 1
    | 1 => 2
    | 2 => 0
  let arm : forall i : Fin 3,
      G.Walk root
        (match i with
          | 0 => x₂
          | 1 => x₃
          | 2 => x₁)
    | 0 => (stem (1 : Fin 3)).concat ha₂x₂
    | 1 => (stem (2 : Fin 3)).concat ha₃x₃
    | 2 => (stem (0 : Fin 3)).concat ha₁x₁
  have hbranch_injective :
      Function.Injective
        (fun i : Fin 4 =>
          match i with
          | 0 => x₂
          | 1 => x₃
          | 2 => x₁
          | 3 => root) := by
    apply T.branchVertex_injective_of_index_injective
        k4TriangleConeBranchIndex
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [k4TriangleConeBranchIndex] at hij ⊢
    · intro i
      fin_cases i
      · exact hx₂
      · exact hx₃
      · exact hx₁
      · exact hroot
  have hx₃_not_p₁₃ : x₃ ∉ p₁₃.support := by
    intro hx₃_support
    have hx₃_branch1 : x₃ ∈ (T.branch (1 : Fin 4)).verts :=
      Walk.support_subset_of_toSubgraph_le hp₁₃_le hx₃_support
    exact (Set.disjoint_left.mp
      (T.vertex_disjoint (3 : Fin 4) (1 : Fin 4) (by decide)) hx₃)
      hx₃_branch1
  have hside_path : side.IsPath := by
    have hconcat : (p₁₃.concat hy₁₃x₃).IsPath :=
      hp₁₃_path.concat hx₃_not_p₁₃ hy₁₃x₃
    simpa [side] using hconcat.reverse
  have hstem_support_branch0 : forall i : Fin 3, {z : V | z ∈ (stem i).support} ⊆
      (T.branch (0 : Fin 4)).verts := by
    intro i
    exact Walk.support_subset_of_toSubgraph_le (hstem_le i)
  have hnot_x₂_stem1 : x₂ ∉ (stem (1 : Fin 3)).support := by
    intro hx
    exact (Set.disjoint_left.mp
      (T.vertex_disjoint (2 : Fin 4) (0 : Fin 4) (by decide)) hx₂)
      (hstem_support_branch0 (1 : Fin 3) hx)
  have hnot_x₃_stem2 : x₃ ∉ (stem (2 : Fin 3)).support := by
    intro hx
    exact (Set.disjoint_left.mp
      (T.vertex_disjoint (3 : Fin 4) (0 : Fin 4) (by decide)) hx₃)
      (hstem_support_branch0 (2 : Fin 3) hx)
  have hnot_x₁_stem0 : x₁ ∉ (stem (0 : Fin 3)).support := by
    intro hx
    exact (Set.disjoint_left.mp
      (T.vertex_disjoint (1 : Fin 4) (0 : Fin 4) (by decide)) hx₁)
      (hstem_support_branch0 (0 : Fin 3) hx)
  have harm_path : forall i : Fin 3, (arm i).IsPath := by
    intro i
    fin_cases i
    · simpa [arm] using (hstem_path (1 : Fin 3)).concat hnot_x₂_stem1 ha₂x₂
    · simpa [arm] using (hstem_path (2 : Fin 3)).concat hnot_x₃_stem2 ha₃x₃
    · simpa [arm] using (hstem_path (0 : Fin 3)).concat hnot_x₁_stem0 ha₁x₁
  have hside_internal_branch1 :
      forall {z : V}, z ∈ Walk.InternalVertices side ->
        z ∈ (T.branch (1 : Fin 4)).verts := by
    intro z hz
    have hz_forward : z ∈ Walk.InternalVertices (p₁₃.concat hy₁₃x₃) := by
      simpa [side] using (Walk.mem_internalVertices_reverse_iff (p₁₃.concat hy₁₃x₃)).mp hz
    have hz_p₁₃ : z ∈ p₁₃.support :=
      Walk.mem_support_of_mem_internalVertices_concat p₁₃ hy₁₃x₃ hz_forward
    exact Walk.support_subset_of_toSubgraph_le hp₁₃_le hz_p₁₃
  have hp₁₂_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices side ->
        forall w : Fin 4,
          z ≠
            match w with
            | 0 => x₂
            | 1 => x₃
            | 2 => x₁
            | 3 => root := by
    intro z hz w
    fin_cases w <;> simp
    · intro hzx₂
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (1 : Fin 4) (2 : Fin 4) (by decide))
        (hside_internal_branch1 hz)) (by simpa [hzx₂] using hx₂)
    · exact hz.2.1
    · exact hz.2.2
    · intro hzroot
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (1 : Fin 4) (0 : Fin 4) (by decide))
        (hside_internal_branch1 hz)) (by simpa [hzroot] using hroot)
  have harm_internal_to_stem :
      forall i : Fin 3, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          z ∈ (stem (stemIndex i)).support ∧ z ≠ root := by
    intro i z hz
    fin_cases i
    · simpa [arm, stemIndex] using
        Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
          (stem (1 : Fin 3)) ha₂x₂ hz
    · simpa [arm, stemIndex] using
        Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
          (stem (2 : Fin 3)) ha₃x₃ hz
    · simpa [arm, stemIndex] using
        Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
          (stem (0 : Fin 3)) ha₁x₁ hz
  have harm_internal_branch0 :
      forall i : Fin 3, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          z ∈ (T.branch (0 : Fin 4)).verts := by
    intro i z hz
    exact hstem_support_branch0 (stemIndex i) (harm_internal_to_stem i hz).1
  have harm_internal_no_branch :
      forall i : Fin 3, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          forall w : Fin 4,
            z ≠
              match w with
              | 0 => x₂
              | 1 => x₃
              | 2 => x₁
              | 3 => root := by
    intro i z hz w
    fin_cases w <;> simp
    · intro hzx₂
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (0 : Fin 4) (2 : Fin 4) (by decide))
        (harm_internal_branch0 i hz)) (by simpa [hzx₂] using hx₂)
    · intro hzx₃
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (0 : Fin 4) (3 : Fin 4) (by decide))
        (harm_internal_branch0 i hz)) (by simpa [hzx₃] using hx₃)
    · intro hzx₁
      exact (Set.disjoint_left.mp
        (T.vertex_disjoint (0 : Fin 4) (1 : Fin 4) (by decide))
        (harm_internal_branch0 i hz)) (by simpa [hzx₁] using hx₁)
    · exact (harm_internal_to_stem i hz).2
  have hstemIndex_injective : Function.Injective stemIndex := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [stemIndex] at hij ⊢
  have harm_internal_disjoint :
      forall {i j : Fin 3}, i ≠ j ->
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (arm j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hidx : stemIndex i ≠ stemIndex j := by
      intro hsame
      exact hij (hstemIndex_injective hsame)
    exact Set.disjoint_left.mp (hstem_disjoint hidx)
      (harm_internal_to_stem i hzi) (harm_internal_to_stem j hzj)
  have harm_side_disjoint :
      forall i : Fin 3,
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices side) := by
    intro i
    rw [Set.disjoint_left]
    intro z hzi hzside
    exact (Set.disjoint_left.mp
      (T.vertex_disjoint (0 : Fin 4) (1 : Fin 4) (by decide))
      (harm_internal_branch0 i hzi)) (hside_internal_branch1 hzside)
  let K : K4UnsplitSubdivisionData G :=
    K4UnsplitSubdivisionData.ofTriangleCone
    hbranch_injective hx₂x₃ hx₁x₂.symm side hside_path arm harm_path
    hp₁₂_internal_no_branch harm_internal_no_branch harm_internal_disjoint
    harm_side_disjoint
  refine ⟨K, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [K, K4UnsplitSubdivisionData.ofTriangleCone,
        k4TriangleConeBranchIndex, hx₂, hx₃, hx₁, hroot]
  · intro C hC
    have hx₂_not_C : x₂ ∉ C := by
      intro hmem
      exact Set.disjoint_left.mp (hC (2 : Fin 4)) hx₂ hmem
    have hx₃_not_C : x₃ ∉ C := by
      intro hmem
      exact Set.disjoint_left.mp (hC (3 : Fin 4)) hx₃ hmem
    have hx₁_not_C : x₁ ∉ C := by
      intro hmem
      exact Set.disjoint_left.mp (hC (1 : Fin 4)) hx₁ hmem
    have hroot_not_C : root ∉ C := by
      intro hmem
      exact Set.disjoint_left.mp (hC (0 : Fin 4)) hroot hmem
    have hside_not_C :
        forall {z : V}, z ∈ Walk.InternalVertices side -> z ∉ C := by
      intro z hz hmem
      exact Set.disjoint_left.mp (hC (1 : Fin 4))
        (hside_internal_branch1 hz) hmem
    have harm_not_C :
        forall i : Fin 3, forall {z : V},
          z ∈ Walk.InternalVertices (arm i) -> z ∉ C := by
      intro i z hz hmem
      exact Set.disjoint_left.mp (hC (0 : Fin 4))
        (harm_internal_branch0 i hz) hmem
    constructor
    · simpa [K] using
        (K4UnsplitSubdivisionData.ofTriangleCone_branchVertex_not_mem
          (hbranch_injective := hbranch_injective)
          (h₀₁ := hx₂x₃) (h₀₂ := hx₁x₂.symm)
          (p₁₂ := side) (hp₁₂ := hside_path)
          (arm := arm) (harm_path := harm_path)
          (hp₁₂_internal_no_branch := hp₁₂_internal_no_branch)
          (harm_internal_no_branch := harm_internal_no_branch)
          (harm_internal_disjoint := harm_internal_disjoint)
          (harm_p₁₂_disjoint := harm_side_disjoint)
          hx₂_not_C hx₃_not_C hx₁_not_C hroot_not_C)
    · intro i j hij z hz
      exact
        (K4UnsplitSubdivisionData.ofTriangleCone_internal_not_mem
          (hbranch_injective := hbranch_injective)
          (h₀₁ := hx₂x₃) (h₀₂ := hx₁x₂.symm)
          (p₁₂ := side) (hp₁₂ := hside_path)
          (arm := arm) (harm_path := harm_path)
          (hp₁₂_internal_no_branch := hp₁₂_internal_no_branch)
          (harm_internal_no_branch := harm_internal_no_branch)
          (harm_internal_disjoint := harm_internal_disjoint)
          (harm_p₁₂_disjoint := harm_side_disjoint)
          hside_not_C harm_not_C hij (by simpa [K] using hz))

theorem DominatingK4Model.exists_k4UnsplitSubdivisionData
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK4Model G) :
    Nonempty (K4UnsplitSubdivisionData G) := by
  rcases T.exists_k4UnsplitSubdivisionData_in_branches with ⟨K, _hK⟩
  exact ⟨K⟩


end Schematic.Math.GraphTheory
