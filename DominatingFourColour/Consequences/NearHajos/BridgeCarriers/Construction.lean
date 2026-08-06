import DominatingFourColour.Consequences.NearHajos.RootedCarriers

/-! Build the subdivided `K5Hat` model from a bridge and four arms. -/

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

private abbrev K5HatBridgeVertex : Type :=
  Fin 2 ⊕ Fin 4

private def K5HatBridgeGraph : SimpleGraph K5HatBridgeVertex where
  Adj
    | Sum.inl a, Sum.inl b => a ≠ b
    | Sum.inl a, Sum.inr i =>
        (a = 0 ∧ (i = 0 ∨ i = 1)) ∨
          (a = 1 ∧ (i = 2 ∨ i = 3))
    | Sum.inr i, Sum.inl a =>
        (a = 0 ∧ (i = 0 ∨ i = 1)) ∨
          (a = 1 ∧ (i = 2 ∨ i = 3))
    | Sum.inr i, Sum.inr j => i ≠ j
  symm := by
    rintro (a | i) (b | j) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := ⟨by
    rintro (a | i) h <;> simp_all⟩

private def fin6ToK5HatBridge : Fin 6 ↪ K5HatBridgeVertex where
  toFun
    | 0 => Sum.inl 0
    | 1 => Sum.inl 1
    | 2 => Sum.inr 0
    | 3 => Sum.inr 1
    | 4 => Sum.inr 2
    | 5 => Sum.inr 3
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢

private theorem fin6ToK5HatBridge_adj
    {x y : Fin 6}
    (hxy : K5Hat.Adj x y) :
    K5HatBridgeGraph.Adj (fin6ToK5HatBridge x) (fin6ToK5HatBridge y) := by
  fin_cases x <;> fin_cases y <;> simp [K5Hat, fin6ToK5HatBridge,
    K5HatBridgeGraph] at hxy ⊢

private theorem k5HatBridgeGraph_near_hajos_with_two_incident_unsplit_edges_at
    {V : Type u} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K5HatBridgeGraph G)
    {coreCenter coreLeft coreRight : Fin 4}
    (hcenter_left : coreCenter ≠ coreLeft)
    (hcenter_right : coreCenter ≠ coreRight)
    (hleft_right : coreLeft ≠ coreRight)
    (edge₁_unsplit :
      M.EdgeUnsplit
        (show K5HatBridgeGraph.Adj (Sum.inr coreCenter) (Sum.inr coreLeft) from
          by simpa [K5HatBridgeGraph] using hcenter_left))
    (edge₂_unsplit :
      M.EdgeUnsplit
        (show K5HatBridgeGraph.Adj (Sum.inr coreCenter) (Sum.inr coreRight) from
          by simpa [K5HatBridgeGraph] using hcenter_right)) :
    NearHajosStrengtheningConclusion G := by
  let e : Fin 6 ↪ K5HatBridgeVertex := fin6ToK5HatBridge
  let h_adj :
      forall {x y : Fin 6}, K5Hat.Adj x y ->
        K5HatBridgeGraph.Adj (e x) (e y) := by
    intro x y hxy
    exact fin6ToK5HatBridge_adj hxy
  let Mhat : StrictSubdivisionModel K5Hat G := M.domainRestrict e h_adj
  have he_core :
      forall i : Fin 4, e (K5Hat.k4CoreEmbedding i) = Sum.inr i := by
    intro i
    fin_cases i <;> rfl
  exact Or.inr ⟨{
    model := Mhat
    coreCenter := coreCenter
    coreLeft := coreLeft
    coreRight := coreRight
    coreCenter_ne_left := hcenter_left
    coreCenter_ne_right := hcenter_right
    coreLeft_ne_right := hleft_right
    edge₁_unsplit := by
      let hcl : K5Hat.Adj
          (K5Hat.k4CoreEmbedding coreCenter)
          (K5Hat.k4CoreEmbedding coreLeft) :=
        K5Hat.k4CoreEmbedding_adj hcenter_left
      change (M.domainRestrict e h_adj).EdgeUnsplit hcl
      rw [StrictSubdivisionModel.domainRestrict_edgeUnsplit]
      exact StrictSubdivisionModel.edgeUnsplit_of_eq M
        (he_core coreCenter).symm
        (he_core coreLeft).symm
        edge₁_unsplit
    edge₂_unsplit := by
      let hcr : K5Hat.Adj
          (K5Hat.k4CoreEmbedding coreCenter)
          (K5Hat.k4CoreEmbedding coreRight) :=
        K5Hat.k4CoreEmbedding_adj hcenter_right
      change (M.domainRestrict e h_adj).EdgeUnsplit hcr
      rw [StrictSubdivisionModel.domainRestrict_edgeUnsplit]
      exact StrictSubdivisionModel.edgeUnsplit_of_eq M
        (he_core coreCenter).symm
        (he_core coreRight).symm
        edge₂_unsplit
  }⟩

private theorem k5HatBridgeGraph_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K5HatBridgeGraph G)
    (edge₁_unsplit :
      M.EdgeUnsplit
        (show K5HatBridgeGraph.Adj (Sum.inr (0 : Fin 4)) (Sum.inr (1 : Fin 4)) from
          by simp [K5HatBridgeGraph]))
    (edge₂_unsplit :
      M.EdgeUnsplit
        (show K5HatBridgeGraph.Adj (Sum.inr (0 : Fin 4)) (Sum.inr (2 : Fin 4)) from
          by simp [K5HatBridgeGraph])) :
    NearHajosStrengtheningConclusion G := by
  exact
    k5HatBridgeGraph_near_hajos_with_two_incident_unsplit_edges_at
      M (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (1 : Fin 4) ≠ 2)
      edge₁_unsplit edge₂_unsplit

def k4BridgeEndpoint {V : Type u} (left right : V) : Fin 4 -> V
  | 0 => left
  | 1 => left
  | 2 => right
  | 3 => right

def k4BridgeEndpointSubgraph
    {V : Type u} {G : SimpleGraph V}
    (B : G.Subgraph) (left right : B.verts) : Fin 4 -> B.verts
  | 0 => left
  | 1 => left
  | 2 => right
  | 3 => right

set_option maxHeartbeats 0 in
theorem K4UnsplitSubdivisionData.bridge_paths_k5hat_relabel_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    {left right : V}
    (hleft_ne_right : left ≠ right)
    (hleft_not_branch : forall i : Fin 4, left ≠ D.model.branchVertex (σ i))
    (hright_not_branch : forall i : Fin 4, right ≠ D.model.branchVertex (σ i))
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        forall i : Fin 4, z ≠ D.model.branchVertex (σ i))
    (hcore_internal_no_left :
      forall {i j : Fin 4} (hij : K4Graph.Adj (σ i) (σ j)) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ left)
    (hcore_internal_no_right :
      forall {i j : Fin 4} (hij : K4Graph.Adj (σ i) (σ j)) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ right)
    (hbridge_core_disjoint :
      forall {i j : Fin 4} (hij : K4Graph.Adj (σ i) (σ j)) {z : V},
        z ∈ Walk.InternalVertices p ->
          z ∈ Walk.InternalVertices (D.model.edgePath hij) -> False)
    (arm :
      forall i : Fin 4,
        G.Walk (k4BridgeEndpoint left right i) (D.model.branchVertex (σ i)))
    (harm_path : forall i : Fin 4, (arm i).IsPath)
    (harm_internal_no_special :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          z ≠ left ∧ z ≠ right ∧
            forall j : Fin 4, z ≠ D.model.branchVertex (σ j))
    (hbridge_arm_disjoint :
      forall i : Fin 4,
        Disjoint (Walk.InternalVertices p) (Walk.InternalVertices (arm i)))
    (harm_internal_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (arm j)))
    (harm_core_disjoint :
      forall {i j k : Fin 4} (hjk : K4Graph.Adj (σ j) (σ k)),
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (D.model.edgePath hjk))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let branch : K5HatBridgeVertex -> V
    | Sum.inl 0 => left
    | Sum.inl 1 => right
    | Sum.inr i => D.model.branchVertex (σ i)
  have hbranch_injective : Function.Injective branch := by
    intro x y hxy
    cases x with
    | inl a =>
        cases y with
        | inl b =>
            fin_cases a <;> fin_cases b <;> simp [branch] at hxy ⊢
            exact False.elim (hleft_ne_right hxy)
            exact False.elim (hleft_ne_right hxy.symm)
        | inr j =>
            fin_cases a <;> simp [branch] at hxy ⊢
            · exact False.elim ((hleft_not_branch j) hxy)
            · exact False.elim ((hright_not_branch j) hxy)
    | inr i =>
        cases y with
        | inl b =>
            fin_cases b <;> simp [branch] at hxy ⊢
            · exact False.elim ((hleft_not_branch i) hxy.symm)
            · exact False.elim ((hright_not_branch i) hxy.symm)
        | inr j =>
            exact congrArg Sum.inr (σ.injective (D.model.branchVertex_injective hxy))
  have hcentral_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        forall w : K5HatBridgeVertex, z ≠ branch w := by
    intro z hz w
    cases w with
    | inl a =>
        fin_cases a
        · simpa [branch] using hz.2.1
        · simpa [branch] using hz.2.2
    | inr i =>
        simpa [branch] using hp_internal_no_branch hz i
  have harm_no_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          forall w : K5HatBridgeVertex, z ≠ branch w := by
    intro i z hz w
    have hspecial := harm_internal_no_special i hz
    cases w with
    | inl a =>
        fin_cases a
        · simpa [branch] using hspecial.1
        · simpa [branch] using hspecial.2.1
    | inr j =>
        simpa [branch] using hspecial.2.2 j
  have hcore_no_branch :
      forall {i j : Fin 4} (hij : K4Graph.Adj (σ i) (σ j)) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) ->
          forall w : K5HatBridgeVertex, z ≠ branch w := by
    intro i j hij z hz w
    cases w with
    | inl a =>
        fin_cases a
        · simpa [branch] using hcore_internal_no_left hij hz
        · simpa [branch] using hcore_internal_no_right hij hz
    | inr k =>
        simpa [branch] using D.model.no_internal_branch_vertices' hij hz (σ k)
  have h_adj :
      forall {i j : Fin 4},
        K5HatBridgeGraph.Adj (Sum.inr i) (Sum.inr j) ->
          K4Graph.Adj (σ i) (σ j) := by
    intro i j hij
    have hij_ne : i ≠ j := by
      simpa [K5HatBridgeGraph] using hij
    simpa [K4Graph, CompleteGraphOn] using
      (show σ i ≠ σ j from by
        intro hσ
        exact hij_ne (σ.injective hσ))
  let M : StrictSubdivisionModel K5HatBridgeGraph G := {
    branchVertex := branch
    branchVertex_injective := hbranch_injective
    edgePath := by
      intro x y hxy
      cases x with
      | inl a =>
          cases y with
          | inl b =>
              revert hxy
              exact
                match a, b with
                | 0, 0 => fun hxy => False.elim (hxy rfl)
                | 0, 1 => fun _ => p
                | 1, 0 => fun _ => p.reverse
                | 1, 1 => fun hxy => False.elim (hxy rfl)
          | inr i =>
              revert hxy
              exact
                match a, i with
                | 0, 0 => fun _ => arm 0
                | 0, 1 => fun _ => arm 1
                | 0, 2 => fun hxy => False.elim (by simp [K5HatBridgeGraph] at hxy)
                | 0, 3 => fun hxy => False.elim (by simp [K5HatBridgeGraph] at hxy)
                | 1, 0 => fun hxy => False.elim (by simp [K5HatBridgeGraph] at hxy)
                | 1, 1 => fun hxy => False.elim (by simp [K5HatBridgeGraph] at hxy)
                | 1, 2 => fun _ => arm 2
                | 1, 3 => fun _ => arm 3
      | inr i =>
          cases y with
          | inl a =>
              revert hxy
              exact
                match i, a with
                | 0, 0 => fun _ => (arm 0).reverse
                | 1, 0 => fun _ => (arm 1).reverse
                | 2, 0 => fun hxy => False.elim (by simp [K5HatBridgeGraph] at hxy)
                | 3, 0 => fun hxy => False.elim (by simp [K5HatBridgeGraph] at hxy)
                | 0, 1 => fun hxy => False.elim (by simp [K5HatBridgeGraph] at hxy)
                | 1, 1 => fun hxy => False.elim (by simp [K5HatBridgeGraph] at hxy)
                | 2, 1 => fun _ => (arm 2).reverse
                | 3, 1 => fun _ => (arm 3).reverse
          | inr j =>
              have hij : K4Graph.Adj (σ i) (σ j) := h_adj hxy
              exact D.model.edgePath hij
    edgePath_isPath := by
      intro x y hxy
      cases x with
      | inl a =>
          cases y with
          | inl b =>
              fin_cases a <;> fin_cases b <;> simp [K5HatBridgeGraph] at hxy
              · exact hp
              · exact hp.reverse
          | inr i =>
              fin_cases a <;> fin_cases i <;> simp [K5HatBridgeGraph] at hxy
              · exact harm_path 0
              · exact harm_path 1
              · exact harm_path 2
              · exact harm_path 3
      | inr i =>
          cases y with
          | inl a =>
              fin_cases a <;> fin_cases i <;> simp [K5HatBridgeGraph] at hxy
              · exact (harm_path 0).reverse
              · exact (harm_path 1).reverse
              · exact (harm_path 2).reverse
              · exact (harm_path 3).reverse
          | inr j =>
              have hij : K4Graph.Adj (σ i) (σ j) := h_adj hxy
              change (D.model.edgePath hij).IsPath
              exact D.model.edgePath_isPath hij
    no_internal_branch_vertices := True
    internally_disjoint_edge_paths := True
    no_internal_branch_vertices' := by
      intro x y hxy z hz w hzw
      cases x with
      | inl a =>
          cases y with
          | inl b =>
              fin_cases a <;> fin_cases b <;> simp [K5HatBridgeGraph] at hxy
              · exact (hcentral_no_branch hz w) hzw
              · have hz' : z ∈ Walk.InternalVertices p := by
                  simpa [Walk.internalVertices_reverse] using hz
                exact (hcentral_no_branch hz' w) hzw
          | inr i =>
              fin_cases a <;> fin_cases i <;> simp [K5HatBridgeGraph] at hxy
              · exact (harm_no_branch 0 hz w) hzw
              · exact (harm_no_branch 1 hz w) hzw
              · exact (harm_no_branch 2 hz w) hzw
              · exact (harm_no_branch 3 hz w) hzw
      | inr i =>
          cases y with
          | inl a =>
              fin_cases a <;> fin_cases i <;> simp [K5HatBridgeGraph] at hxy
              · have hz' : z ∈ Walk.InternalVertices (arm 0) := by
                  exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz
                exact (harm_no_branch 0 hz' w) hzw
              · have hz' : z ∈ Walk.InternalVertices (arm 1) := by
                  exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz
                exact (harm_no_branch 1 hz' w) hzw
              · have hz' : z ∈ Walk.InternalVertices (arm 2) := by
                  exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz
                exact (harm_no_branch 2 hz' w) hzw
              · have hz' : z ∈ Walk.InternalVertices (arm 3) := by
                  exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz
                exact (harm_no_branch 3 hz' w) hzw
          | inr j =>
              have hij : K4Graph.Adj (σ i) (σ j) := h_adj hxy
              exact (hcore_no_branch hij hz w) hzw
    internally_disjoint_edge_paths' := by
      intro x y x' y' hxy hx'y' hne
      rw [Set.disjoint_left]
      intro z hz hz'
      cases x with
      | inl a =>
          cases y with
          | inl b =>
              fin_cases a <;> fin_cases b <;> simp [K5HatBridgeGraph] at hxy
              · cases x' with
                | inl a' =>
                    cases y' with
                    | inl b' =>
                        fin_cases a' <;> fin_cases b' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                        · exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                    | inr i' =>
                        fin_cases a' <;> fin_cases i' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (hbridge_arm_disjoint 0) hz hz'
                        · exact Set.disjoint_left.mp (hbridge_arm_disjoint 1) hz hz'
                        · exact Set.disjoint_left.mp (hbridge_arm_disjoint 2) hz hz'
                        · exact Set.disjoint_left.mp (hbridge_arm_disjoint 3) hz hz'
                | inr i' =>
                    cases y' with
                    | inl a' =>
                        fin_cases a' <;> fin_cases i' <;> simp [K5HatBridgeGraph] at hx'y'
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 0) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz'
                          exact Set.disjoint_left.mp (hbridge_arm_disjoint 0) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 1) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz'
                          exact Set.disjoint_left.mp (hbridge_arm_disjoint 1) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 2) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz'
                          exact Set.disjoint_left.mp (hbridge_arm_disjoint 2) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 3) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz'
                          exact Set.disjoint_left.mp (hbridge_arm_disjoint 3) hz hz'_arm
                    | inr j' =>
                        have hi'j' : K4Graph.Adj (σ i') (σ j') := h_adj hx'y'
                        exact hbridge_core_disjoint hi'j' hz hz'
              · have hz_p : z ∈ Walk.InternalVertices p := by
                  simpa [Walk.internalVertices_reverse] using hz
                cases x' with
                | inl a' =>
                    cases y' with
                    | inl b' =>
                        fin_cases a' <;> fin_cases b' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                        · exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                    | inr i' =>
                        fin_cases a' <;> fin_cases i' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (hbridge_arm_disjoint 0) hz_p hz'
                        · exact Set.disjoint_left.mp (hbridge_arm_disjoint 1) hz_p hz'
                        · exact Set.disjoint_left.mp (hbridge_arm_disjoint 2) hz_p hz'
                        · exact Set.disjoint_left.mp (hbridge_arm_disjoint 3) hz_p hz'
                | inr i' =>
                    cases y' with
                    | inl a' =>
                        fin_cases a' <;> fin_cases i' <;> simp [K5HatBridgeGraph] at hx'y'
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 0) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz'
                          exact Set.disjoint_left.mp (hbridge_arm_disjoint 0) hz_p hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 1) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz'
                          exact Set.disjoint_left.mp (hbridge_arm_disjoint 1) hz_p hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 2) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz'
                          exact Set.disjoint_left.mp (hbridge_arm_disjoint 2) hz_p hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 3) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz'
                          exact Set.disjoint_left.mp (hbridge_arm_disjoint 3) hz_p hz'_arm
                    | inr j' =>
                        have hi'j' : K4Graph.Adj (σ i') (σ j') := h_adj hx'y'
                        exact hbridge_core_disjoint hi'j' hz_p hz'
          | inr i =>
              fin_cases a <;> fin_cases i <;> simp [K5HatBridgeGraph] at hxy
              · cases x' with
                | inl a' =>
                    cases y' with
                    | inl b' =>
                        fin_cases a' <;> fin_cases b' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 0)) hz hz'
                        · have hz'_p : z ∈ Walk.InternalVertices p := by
                            simpa [Walk.internalVertices_reverse] using hz'
                          exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 0)) hz hz'_p
                    | inr j' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 1)) hz hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 2)) hz hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 3)) hz hz'
                | inr j' =>
                    cases y' with
                    | inl a' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 0) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz'
                          exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 1) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 1)) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 2) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 2)) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 3) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 3)) hz hz'_arm
                    | inr k' =>
                        have hj'k' : K4Graph.Adj (σ j') (σ k') := h_adj hx'y'
                        exact Set.disjoint_left.mp (harm_core_disjoint (i := (0 : Fin 4)) hj'k') hz hz'
              · cases x' with
                | inl a' =>
                    cases y' with
                    | inl b' =>
                        fin_cases a' <;> fin_cases b' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 1)) hz hz'
                        · have hz'_p : z ∈ Walk.InternalVertices p := by
                            simpa [Walk.internalVertices_reverse] using hz'
                          exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 1)) hz hz'_p
                    | inr j' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 0)) hz hz'
                        · exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 2)) hz hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 3)) hz hz'
                | inr j' =>
                    cases y' with
                    | inl a' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 0) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 0)) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 1) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz'
                          exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 2) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 2)) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 3) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 3)) hz hz'_arm
                    | inr k' =>
                        have hj'k' : K4Graph.Adj (σ j') (σ k') := h_adj hx'y'
                        exact Set.disjoint_left.mp (harm_core_disjoint (i := (1 : Fin 4)) hj'k') hz hz'
              · cases x' with
                | inl a' =>
                    cases y' with
                    | inl b' =>
                        fin_cases a' <;> fin_cases b' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 2)) hz hz'
                        · have hz'_p : z ∈ Walk.InternalVertices p := by
                            simpa [Walk.internalVertices_reverse] using hz'
                          exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 2)) hz hz'_p
                    | inr j' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 0)) hz hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 1)) hz hz'
                        · exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 3)) hz hz'
                | inr j' =>
                    cases y' with
                    | inl a' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 0) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 0)) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 1) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 1)) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 2) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz'
                          exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 3) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 3)) hz hz'_arm
                    | inr k' =>
                        have hj'k' : K4Graph.Adj (σ j') (σ k') := h_adj hx'y'
                        exact Set.disjoint_left.mp (harm_core_disjoint (i := (2 : Fin 4)) hj'k') hz hz'
              · cases x' with
                | inl a' =>
                    cases y' with
                    | inl b' =>
                        fin_cases a' <;> fin_cases b' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 3)) hz hz'
                        · have hz'_p : z ∈ Walk.InternalVertices p := by
                            simpa [Walk.internalVertices_reverse] using hz'
                          exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 3)) hz hz'_p
                    | inr j' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 0)) hz hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 1)) hz hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 2)) hz hz'
                        · exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                | inr j' =>
                    cases y' with
                    | inl a' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 0) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 0)) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 1) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 1)) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 2) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 2)) hz hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 3) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz'
                          exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                    | inr k' =>
                        have hj'k' : K4Graph.Adj (σ j') (σ k') := h_adj hx'y'
                        exact Set.disjoint_left.mp (harm_core_disjoint (i := (3 : Fin 4)) hj'k') hz hz'
      | inr i =>
          cases y with
          | inl a =>
              fin_cases a <;> fin_cases i <;> simp [K5HatBridgeGraph] at hxy
              · have hz_arm : z ∈ Walk.InternalVertices (arm 0) := by
                  exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz
                cases x' with
                | inl a' =>
                    cases y' with
                    | inl b' =>
                        fin_cases a' <;> fin_cases b' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 0)) hz_arm hz'
                        · have hz'_p : z ∈ Walk.InternalVertices p := by
                            simpa [Walk.internalVertices_reverse] using hz'
                          exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 0)) hz_arm hz'_p
                    | inr j' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 1)) hz_arm hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 2)) hz_arm hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 3)) hz_arm hz'
                | inr j' =>
                    cases y' with
                    | inl a' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 0) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz'
                          exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 1) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 1)) hz_arm hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 2) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 2)) hz_arm hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 3) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (0 : Fin 4) ≠ 3)) hz_arm hz'_arm
                    | inr k' =>
                        have hj'k' : K4Graph.Adj (σ j') (σ k') := h_adj hx'y'
                        exact Set.disjoint_left.mp (harm_core_disjoint (i := (0 : Fin 4)) hj'k') hz_arm hz'
              · have hz_arm : z ∈ Walk.InternalVertices (arm 1) := by
                  exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz
                cases x' with
                | inl a' =>
                    cases y' with
                    | inl b' =>
                        fin_cases a' <;> fin_cases b' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 1)) hz_arm hz'
                        · have hz'_p : z ∈ Walk.InternalVertices p := by
                            simpa [Walk.internalVertices_reverse] using hz'
                          exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 1)) hz_arm hz'_p
                    | inr j' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 0)) hz_arm hz'
                        · exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 2)) hz_arm hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 3)) hz_arm hz'
                | inr j' =>
                    cases y' with
                    | inl a' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 0) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 0)) hz_arm hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 1) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz'
                          exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 2) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 2)) hz_arm hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 3) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (1 : Fin 4) ≠ 3)) hz_arm hz'_arm
                    | inr k' =>
                        have hj'k' : K4Graph.Adj (σ j') (σ k') := h_adj hx'y'
                        exact Set.disjoint_left.mp (harm_core_disjoint (i := (1 : Fin 4)) hj'k') hz_arm hz'
              · have hz_arm : z ∈ Walk.InternalVertices (arm 2) := by
                  exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz
                cases x' with
                | inl a' =>
                    cases y' with
                    | inl b' =>
                        fin_cases a' <;> fin_cases b' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 2)) hz_arm hz'
                        · have hz'_p : z ∈ Walk.InternalVertices p := by
                            simpa [Walk.internalVertices_reverse] using hz'
                          exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 2)) hz_arm hz'_p
                    | inr j' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 0)) hz_arm hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 1)) hz_arm hz'
                        · exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 3)) hz_arm hz'
                | inr j' =>
                    cases y' with
                    | inl a' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 0) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 0)) hz_arm hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 1) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 1)) hz_arm hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 2) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz'
                          exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 3) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (2 : Fin 4) ≠ 3)) hz_arm hz'_arm
                    | inr k' =>
                        have hj'k' : K4Graph.Adj (σ j') (σ k') := h_adj hx'y'
                        exact Set.disjoint_left.mp (harm_core_disjoint (i := (2 : Fin 4)) hj'k') hz_arm hz'
              · have hz_arm : z ∈ Walk.InternalVertices (arm 3) := by
                  exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz
                cases x' with
                | inl a' =>
                    cases y' with
                    | inl b' =>
                        fin_cases a' <;> fin_cases b' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 3)) hz_arm hz'
                        · have hz'_p : z ∈ Walk.InternalVertices p := by
                            simpa [Walk.internalVertices_reverse] using hz'
                          exact Set.disjoint_left.mp (Disjoint.symm (hbridge_arm_disjoint 3)) hz_arm hz'_p
                    | inr j' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 0)) hz_arm hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 1)) hz_arm hz'
                        · exact Set.disjoint_left.mp (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 2)) hz_arm hz'
                        · exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                | inr j' =>
                    cases y' with
                    | inl a' =>
                        fin_cases a' <;> fin_cases j' <;> simp [K5HatBridgeGraph] at hx'y'
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 0) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 0)) hz_arm hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 1) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 1)) hz_arm hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 2) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz'
                          exact Set.disjoint_left.mp
                            (harm_internal_disjoint (by decide : (3 : Fin 4) ≠ 2)) hz_arm hz'_arm
                        · have hz'_arm : z ∈ Walk.InternalVertices (arm 3) := by
                            exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz'
                          exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                    | inr k' =>
                        have hj'k' : K4Graph.Adj (σ j') (σ k') := h_adj hx'y'
                        exact Set.disjoint_left.mp (harm_core_disjoint (i := (3 : Fin 4)) hj'k') hz_arm hz'
          | inr j =>
              have hij : K4Graph.Adj (σ i) (σ j) := h_adj hxy
              cases x' with
              | inl a' =>
                  cases y' with
                  | inl b' =>
                      fin_cases a' <;> fin_cases b' <;> simp [K5HatBridgeGraph] at hx'y'
                      · exact hbridge_core_disjoint hij hz' hz
                      · have hz'_p : z ∈ Walk.InternalVertices p := by
                          simpa [Walk.internalVertices_reverse] using hz'
                        exact hbridge_core_disjoint hij hz'_p hz
                  | inr i' =>
                      fin_cases a' <;> fin_cases i' <;> simp [K5HatBridgeGraph] at hx'y'
                      · exact Set.disjoint_left.mp
                          (Disjoint.symm (harm_core_disjoint (i := (0 : Fin 4)) hij)) hz hz'
                      · exact Set.disjoint_left.mp
                          (Disjoint.symm (harm_core_disjoint (i := (1 : Fin 4)) hij)) hz hz'
                      · exact Set.disjoint_left.mp
                          (Disjoint.symm (harm_core_disjoint (i := (2 : Fin 4)) hij)) hz hz'
                      · exact Set.disjoint_left.mp
                          (Disjoint.symm (harm_core_disjoint (i := (3 : Fin 4)) hij)) hz hz'
              | inr i' =>
                  cases y' with
                  | inl a' =>
                      fin_cases a' <;> fin_cases i' <;> simp [K5HatBridgeGraph] at hx'y'
                      · have hz'_arm : z ∈ Walk.InternalVertices (arm 0) := by
                          exact (Walk.mem_internalVertices_reverse_iff (arm 0)).mp hz'
                        exact Set.disjoint_left.mp
                          (Disjoint.symm (harm_core_disjoint (i := (0 : Fin 4)) hij)) hz hz'_arm
                      · have hz'_arm : z ∈ Walk.InternalVertices (arm 1) := by
                          exact (Walk.mem_internalVertices_reverse_iff (arm 1)).mp hz'
                        exact Set.disjoint_left.mp
                          (Disjoint.symm (harm_core_disjoint (i := (1 : Fin 4)) hij)) hz hz'_arm
                      · have hz'_arm : z ∈ Walk.InternalVertices (arm 2) := by
                          exact (Walk.mem_internalVertices_reverse_iff (arm 2)).mp hz'
                        exact Set.disjoint_left.mp
                          (Disjoint.symm (harm_core_disjoint (i := (2 : Fin 4)) hij)) hz hz'_arm
                      · have hz'_arm : z ∈ Walk.InternalVertices (arm 3) := by
                          exact (Walk.mem_internalVertices_reverse_iff (arm 3)).mp hz'
                        exact Set.disjoint_left.mp
                          (Disjoint.symm (harm_core_disjoint (i := (3 : Fin 4)) hij)) hz hz'_arm
                  | inr j' =>
                      have hi'j' : K4Graph.Adj (σ i') (σ j') := h_adj hx'y'
                      have hne' :
                          ¬ ((σ i = σ i' ∧ σ j = σ j') ∨
                              (σ i = σ j' ∧ σ j = σ i')) := by
                        intro hsame
                        apply hne
                        rcases hsame with hsame | hsame
                        · exact Or.inl
                            ⟨congrArg Sum.inr (σ.injective hsame.1),
                              congrArg Sum.inr (σ.injective hsame.2)⟩
                        · exact Or.inr
                            ⟨congrArg Sum.inr (σ.injective hsame.1),
                              congrArg Sum.inr (σ.injective hsame.2)⟩
                      exact Set.disjoint_left.mp
                        (D.model.internally_disjoint_edge_paths' hij hi'j' hne') hz hz'
  }
  obtain ⟨coreCenter, coreLeft, coreRight, hcenter, hleft, hright,
    hcenter_left, hcenter_right, hleft_right⟩ :=
    fin4_embedding_preimages_zero_one_two σ
  exact
    k5HatBridgeGraph_near_hajos_with_two_incident_unsplit_edges_at M
      hcenter_left hcenter_right hleft_right
      (by
        simpa [M, StrictSubdivisionModel.EdgeUnsplit] using
          D.edgeUnsplit_of_embedding_preimage_zero_one σ hcenter hleft _)
      (by
        simpa [M, StrictSubdivisionModel.EdgeUnsplit] using
          D.edgeUnsplit_of_embedding_preimage_zero_two σ hcenter hright _)

end Schematic.Math.GraphTheory
