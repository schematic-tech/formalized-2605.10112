import DominatingFourColour.Consequences.NearHajos.CarrierCases.Rooted

/-! Pair-split and two-value attachment reductions. -/

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

set_option maxHeartbeats 0 in
theorem K4UnsplitSubdivisionData.bridge_path_k5hat_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    {left right : V}
    (hleft_ne_right : left ≠ right)
    (hleft_not_branch : forall i : Fin 4, left ≠ D.model.branchVertex i)
    (hright_not_branch : forall i : Fin 4, right ≠ D.model.branchVertex i)
    (p : G.Walk left right)
    (hp : p.IsPath)
    (hp_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        forall i : Fin 4, z ≠ D.model.branchVertex i)
    (hcore_internal_no_left :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ left)
    (hcore_internal_no_right :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ right)
    (hbridge_core_disjoint :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices p ->
          z ∈ Walk.InternalVertices (D.model.edgePath hij) -> False)
    (hleft0 : G.Adj left (D.model.branchVertex 0))
    (hleft1 : G.Adj left (D.model.branchVertex 1))
    (hright2 : G.Adj right (D.model.branchVertex 2))
    (hright3 : G.Adj right (D.model.branchVertex 3)) :
    NearHajosStrengtheningConclusion G := by
  let arm : forall i : Fin 4,
      G.Walk (k4BridgeEndpoint left right i) (D.model.branchVertex i)
    | 0 => hleft0.toWalk
    | 1 => hleft1.toWalk
    | 2 => hright2.toWalk
    | 3 => hright3.toWalk
  refine
    D.bridge_paths_k5hat_near_hajos_with_two_incident_unsplit_edges
      hleft_ne_right hleft_not_branch hright_not_branch p hp
      hp_internal_no_branch hcore_internal_no_left hcore_internal_no_right
      hbridge_core_disjoint arm ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [arm]
    · exact SimpleGraph.Walk.IsPath.of_adj hleft0
    · exact SimpleGraph.Walk.IsPath.of_adj hleft1
    · exact SimpleGraph.Walk.IsPath.of_adj hright2
    · exact SimpleGraph.Walk.IsPath.of_adj hright3
  · intro i z hz
    fin_cases i <;> simp [arm] at hz
    · exact (Walk.not_mem_internalVertices_toWalk hleft0 hz).elim
    · exact (Walk.not_mem_internalVertices_toWalk hleft1 hz).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright2 hz).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright3 hz).elim
  · intro i
    rw [Set.disjoint_left]
    intro z _hz_bridge hz_arm
    fin_cases i <;> simp [arm] at hz_arm
    · exact (Walk.not_mem_internalVertices_toWalk hleft0 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hleft1 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright2 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright3 hz_arm).elim
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hz_arm _hz_arm_other
    fin_cases i <;> simp [arm] at hz_arm
    · exact (Walk.not_mem_internalVertices_toWalk hleft0 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hleft1 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright2 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright3 hz_arm).elim
  · intro i j k hjk
    rw [Set.disjoint_left]
    intro z hz_arm _hz_core
    fin_cases i <;> simp [arm] at hz_arm
    · exact (Walk.not_mem_internalVertices_toWalk hleft0 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hleft1 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright2 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright3 hz_arm).elim

theorem K4UnsplitSubdivisionData.carrier_pair_split_attachment_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (B : G.Subgraph)
    (hB_connected : B.coe.Connected)
    {left right : V}
    (hleft_mem : left ∈ B.verts)
    (hright_mem : right ∈ B.verts)
    (hleft_ne_right : left ≠ right)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    (hleft0 : G.Adj left (D.model.branchVertex (0 : Fin 4)))
    (hleft1 : G.Adj left (D.model.branchVertex (1 : Fin 4)))
    (hright2 : G.Adj right (D.model.branchVertex (2 : Fin 4)))
    (hright3 : G.Adj right (D.model.branchVertex (3 : Fin 4))) :
    NearHajosStrengtheningConclusion G := by
  classical
  obtain ⟨p, hp, hp_le⟩ :=
    Subgraph.Connected.exists_path_between hB_connected hleft_mem hright_mem
  have hleft_not_branch : forall i : Fin 4, left ≠ D.model.branchVertex i := by
    intro i h
    exact hbranch_not_B i (by simpa [h] using hleft_mem)
  have hright_not_branch : forall i : Fin 4, right ≠ D.model.branchVertex i := by
    intro i h
    exact hbranch_not_B i (by simpa [h] using hright_mem)
  have hp_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        forall i : Fin 4, z ≠ D.model.branchVertex i := by
    intro z hz i h
    have hzB : z ∈ B.verts :=
      hp_le.left (by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        exact hz.1)
    exact hbranch_not_B i (by simpa [h] using hzB)
  have hcore_internal_no_left :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ left := by
    intro i j hij z hz h
    exact hcore_internal_not_B hij hz (by simpa [h] using hleft_mem)
  have hcore_internal_no_right :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ right := by
    intro i j hij z hz h
    exact hcore_internal_not_B hij hz (by simpa [h] using hright_mem)
  have hbridge_core_disjoint :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices p ->
          z ∈ Walk.InternalVertices (D.model.edgePath hij) -> False := by
    intro i j hij z hz_p hz_core
    exact hcore_internal_not_B hij hz_core
      (hp_le.left (by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        exact hz_p.1))
  exact
    D.bridge_path_k5hat_near_hajos_with_two_incident_unsplit_edges
      hleft_ne_right hleft_not_branch hright_not_branch p hp
      hp_internal_no_branch hcore_internal_no_left hcore_internal_no_right
      hbridge_core_disjoint hleft0 hleft1 hright2 hright3

theorem K4UnsplitSubdivisionData.carrier_pair_split_attachment_relabel_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    (h01 :
      forall hσ01 : K4Graph.Adj (σ (0 : Fin 4)) (σ (1 : Fin 4)),
        D.model.EdgeUnsplit hσ01)
    (h02 :
      forall hσ02 : K4Graph.Adj (σ (0 : Fin 4)) (σ (2 : Fin 4)),
        D.model.EdgeUnsplit hσ02)
    (B : G.Subgraph)
    (hB_connected : B.coe.Connected)
    {left right : V}
    (hleft_mem : left ∈ B.verts)
    (hright_mem : right ∈ B.verts)
    (hleft_ne_right : left ≠ right)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    (hleft0 : G.Adj left (D.model.branchVertex (σ (0 : Fin 4))))
    (hleft1 : G.Adj left (D.model.branchVertex (σ (1 : Fin 4))))
    (hright2 : G.Adj right (D.model.branchVertex (σ (2 : Fin 4))))
    (hright3 : G.Adj right (D.model.branchVertex (σ (3 : Fin 4)))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let K : K4UnsplitSubdivisionData G := D.relabel σ h01 h02
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
  exact
    K.carrier_pair_split_attachment_near_hajos_with_two_incident_unsplit_edges
      B hB_connected hleft_mem hright_mem hleft_ne_right
      (by
        intro i hmem
        exact hbranch_not_B (σ i)
          (by simpa [K, K4UnsplitSubdivisionData.relabel] using hmem))
      (by
        intro i j hij z hz hmem
        exact hcore_internal_not_B (h_adj hij)
          (by simpa [K, K4UnsplitSubdivisionData.relabel] using hz)
          (by simpa [K, K4UnsplitSubdivisionData.relabel] using hmem))
      (by simpa [K, K4UnsplitSubdivisionData.relabel] using hleft0)
      (by simpa [K, K4UnsplitSubdivisionData.relabel] using hleft1)
      (by simpa [K, K4UnsplitSubdivisionData.relabel] using hright2)
      (by simpa [K, K4UnsplitSubdivisionData.relabel] using hright3)

theorem K4UnsplitSubdivisionData.carrier_pair_split_03_12_attachment_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (B : G.Subgraph)
    (hB_connected : B.coe.Connected)
    {left right : V}
    (hleft_mem : left ∈ B.verts)
    (hright_mem : right ∈ B.verts)
    (hleft_ne_right : left ≠ right)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    (hleft0 : G.Adj left (D.model.branchVertex (0 : Fin 4)))
    (hleft3 : G.Adj left (D.model.branchVertex (3 : Fin 4)))
    (hright1 : G.Adj right (D.model.branchVertex (1 : Fin 4)))
    (hright2 : G.Adj right (D.model.branchVertex (2 : Fin 4))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let σ03 : Fin 4 ↪ Fin 4 := {
    toFun
      | 0 => 0
      | 1 => 3
      | 2 => 1
      | 3 => 2
    inj' := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp at h ⊢ }
  obtain ⟨p, hp, hp_le⟩ :=
    Subgraph.Connected.exists_path_between hB_connected hleft_mem hright_mem
  have hleft_not_branch : forall i : Fin 4, left ≠ D.model.branchVertex (σ03 i) := by
    intro i h
    exact hbranch_not_B (σ03 i) (by simpa [h] using hleft_mem)
  have hright_not_branch : forall i : Fin 4, right ≠ D.model.branchVertex (σ03 i) := by
    intro i h
    exact hbranch_not_B (σ03 i) (by simpa [h] using hright_mem)
  have hp_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p ->
        forall i : Fin 4, z ≠ D.model.branchVertex (σ03 i) := by
    intro z hz i h
    have hzB : z ∈ B.verts :=
      hp_le.left (by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        exact hz.1)
    exact hbranch_not_B (σ03 i) (by simpa [h] using hzB)
  have hcore_internal_no_left :
      forall {i j : Fin 4} (hij : K4Graph.Adj (σ03 i) (σ03 j)) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ left := by
    intro i j hij z hz h
    exact hcore_internal_not_B hij hz (by simpa [h] using hleft_mem)
  have hcore_internal_no_right :
      forall {i j : Fin 4} (hij : K4Graph.Adj (σ03 i) (σ03 j)) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ right := by
    intro i j hij z hz h
    exact hcore_internal_not_B hij hz (by simpa [h] using hright_mem)
  have hbridge_core_disjoint :
      forall {i j : Fin 4} (hij : K4Graph.Adj (σ03 i) (σ03 j)) {z : V},
        z ∈ Walk.InternalVertices p ->
          z ∈ Walk.InternalVertices (D.model.edgePath hij) -> False := by
    intro i j hij z hz_p hz_core
    exact hcore_internal_not_B hij hz_core
      (hp_le.left (by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        exact hz_p.1))
  let arm : forall i : Fin 4,
      G.Walk (k4BridgeEndpoint left right i) (D.model.branchVertex (σ03 i))
    | 0 => hleft0.toWalk
    | 1 => hleft3.toWalk
    | 2 => hright1.toWalk
    | 3 => hright2.toWalk
  refine
    D.bridge_paths_k5hat_relabel_near_hajos_with_two_incident_unsplit_edges
      σ03 hleft_ne_right hleft_not_branch hright_not_branch p hp
      hp_internal_no_branch hcore_internal_no_left hcore_internal_no_right
      hbridge_core_disjoint arm ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [arm, σ03]
    · exact SimpleGraph.Walk.IsPath.of_adj hleft0
    · exact SimpleGraph.Walk.IsPath.of_adj hleft3
    · exact SimpleGraph.Walk.IsPath.of_adj hright1
    · exact SimpleGraph.Walk.IsPath.of_adj hright2
  · intro i z hz
    fin_cases i <;> simp [arm, σ03] at hz
    · exact (Walk.not_mem_internalVertices_toWalk hleft0 hz).elim
    · exact (Walk.not_mem_internalVertices_toWalk hleft3 hz).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright1 hz).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright2 hz).elim
  · intro i
    rw [Set.disjoint_left]
    intro z _hz_bridge hz_arm
    fin_cases i <;> simp [arm, σ03] at hz_arm
    · exact (Walk.not_mem_internalVertices_toWalk hleft0 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hleft3 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright1 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright2 hz_arm).elim
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hz_arm _hz_arm_other
    fin_cases i <;> simp [arm, σ03] at hz_arm
    · exact (Walk.not_mem_internalVertices_toWalk hleft0 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hleft3 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright1 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright2 hz_arm).elim
  · intro i j k hjk
    rw [Set.disjoint_left]
    intro z hz_arm _hz_core
    fin_cases i <;> simp [arm, σ03] at hz_arm
    · exact (Walk.not_mem_internalVertices_toWalk hleft0 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hleft3 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright1 hz_arm).elim
    · exact (Walk.not_mem_internalVertices_toWalk hright2 hz_arm).elim

set_option maxHeartbeats 0 in
theorem K4UnsplitSubdivisionData.carrier_two_value_attachment_near_hajos_or_pair03_12
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (B : G.Subgraph)
    (hB_connected : B.coe.Connected)
    {u v : V}
    (huB : u ∈ B.verts)
    (hvB : v ∈ B.verts)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ B.verts ∧ G.Adj (attach i) (D.model.branchVertex i))
    (hvalues : forall i : Fin 4, attach i = u ∨ attach i = v) :
    NearHajosStrengtheningConclusion G ∨
      ((G.Adj u (D.model.branchVertex (0 : Fin 4)) ∧
          G.Adj u (D.model.branchVertex (3 : Fin 4)) ∧
            G.Adj v (D.model.branchVertex (1 : Fin 4)) ∧
              G.Adj v (D.model.branchVertex (2 : Fin 4))) ∨
        (G.Adj v (D.model.branchVertex (0 : Fin 4)) ∧
          G.Adj v (D.model.branchVertex (3 : Fin 4)) ∧
            G.Adj u (D.model.branchVertex (1 : Fin 4)) ∧
              G.Adj u (D.model.branchVertex (2 : Fin 4)))) := by
  classical
  by_cases huv : u = v
  · exact Or.inl
      (D.carrier_common_attachment_near_hajos_with_two_incident_unsplit_edges
        B.verts huB hbranch_not_B hcore_internal_not_B
        (by
          intro i
          rcases hvalues i with hi | hi
          · simpa [hi] using (hattach i).2
          · simpa [hi, huv] using (hattach i).2))
  have hu_adj :
      forall i : Fin 4, attach i = u ->
        G.Adj u (D.model.branchVertex i) := by
    intro i hi
    simpa [hi] using (hattach i).2
  have hv_adj :
      forall i : Fin 4, attach i = v ->
        G.Adj v (D.model.branchVertex i) := by
    intro i hi
    simpa [hi] using (hattach i).2
  let σ02 : Fin 4 ↪ Fin 4 := {
    toFun
      | 0 => 0
      | 1 => 2
      | 2 => 1
      | 3 => 3
    inj' := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp at h ⊢ }
  have hpair02
      {left right : V}
      (hleft_mem : left ∈ B.verts)
      (hright_mem : right ∈ B.verts)
      (hleft_ne_right : left ≠ right)
      (hleft0 : G.Adj left (D.model.branchVertex (0 : Fin 4)))
      (hleft2 : G.Adj left (D.model.branchVertex (2 : Fin 4)))
      (hright1 : G.Adj right (D.model.branchVertex (1 : Fin 4)))
      (hright3 : G.Adj right (D.model.branchVertex (3 : Fin 4))) :
      NearHajosStrengtheningConclusion G := by
    exact
      D.carrier_pair_split_attachment_relabel_near_hajos_with_two_incident_unsplit_edges
        σ02
        (by
          intro hσ01
          simpa [σ02, StrictSubdivisionModel.EdgeUnsplit] using D.edge₂_unsplit)
        (by
          intro hσ02
          simpa [σ02, StrictSubdivisionModel.EdgeUnsplit] using D.edge₁_unsplit)
        B hB_connected hleft_mem hright_mem hleft_ne_right
        hbranch_not_B hcore_internal_not_B
        (by simpa [σ02] using hleft0)
        (by simpa [σ02] using hleft2)
        (by simpa [σ02] using hright1)
        (by simpa [σ02] using hright3)
  rcases hvalues 0 with h0u | h0v
  · rcases hvalues 1 with h1u | h1v
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact Or.inl
            (D.carrier_common_attachment_near_hajos_with_two_incident_unsplit_edges
              B.verts huB hbranch_not_B hcore_internal_not_B
              (by
                intro i
                fin_cases i
                · exact hu_adj 0 h0u
                · exact hu_adj 1 h1u
                · exact hu_adj 2 h2u
                · exact hu_adj 3 h3u))
        · exact Or.inl
            (D.carrier_one_long_arm_cone_near_hajos_with_two_incident_unsplit_edges
              B hB_connected (3 : Fin 4) huB hvB hbranch_not_B
              hcore_internal_not_B
              (by
                intro i hi
                fin_cases i
                · exact hu_adj 0 h0u
                · exact hu_adj 1 h1u
                · exact hu_adj 2 h2u
                · exact False.elim (hi rfl))
              (hv_adj 3 h3v))
      · rcases hvalues 3 with h3u | h3v
        · exact Or.inl
            (D.carrier_one_long_arm_cone_near_hajos_with_two_incident_unsplit_edges
              B hB_connected (2 : Fin 4) huB hvB hbranch_not_B
              hcore_internal_not_B
              (by
                intro i hi
                fin_cases i
                · exact hu_adj 0 h0u
                · exact hu_adj 1 h1u
                · exact False.elim (hi rfl)
                · exact hu_adj 3 h3u)
              (hv_adj 2 h2v))
        · exact Or.inl
            (D.carrier_pair_split_attachment_near_hajos_with_two_incident_unsplit_edges
              B hB_connected huB hvB huv hbranch_not_B hcore_internal_not_B
              (hu_adj 0 h0u) (hu_adj 1 h1u) (hv_adj 2 h2v)
              (hv_adj 3 h3v))
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact Or.inl
            (D.carrier_one_long_arm_cone_near_hajos_with_two_incident_unsplit_edges
              B hB_connected (1 : Fin 4) huB hvB hbranch_not_B
              hcore_internal_not_B
              (by
                intro i hi
                fin_cases i
                · exact hu_adj 0 h0u
                · exact False.elim (hi rfl)
                · exact hu_adj 2 h2u
                · exact hu_adj 3 h3u)
              (hv_adj 1 h1v))
        · exact Or.inl
            (hpair02 huB hvB huv (hu_adj 0 h0u) (hu_adj 2 h2u)
              (hv_adj 1 h1v) (hv_adj 3 h3v))
      · rcases hvalues 3 with h3u | h3v
        · exact Or.inr (Or.inl
            ⟨hu_adj 0 h0u, hu_adj 3 h3u, hv_adj 1 h1v, hv_adj 2 h2v⟩)
        · exact Or.inl
            (D.carrier_one_long_arm_cone_near_hajos_with_two_incident_unsplit_edges
              B hB_connected (0 : Fin 4) hvB huB hbranch_not_B
              hcore_internal_not_B
              (by
                intro i hi
                fin_cases i
                · exact False.elim (hi rfl)
                · exact hv_adj 1 h1v
                · exact hv_adj 2 h2v
                · exact hv_adj 3 h3v)
              (hu_adj 0 h0u))
  · rcases hvalues 1 with h1u | h1v
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact Or.inl
            (D.carrier_one_long_arm_cone_near_hajos_with_two_incident_unsplit_edges
              B hB_connected (0 : Fin 4) huB hvB hbranch_not_B
              hcore_internal_not_B
              (by
                intro i hi
                fin_cases i
                · exact False.elim (hi rfl)
                · exact hu_adj 1 h1u
                · exact hu_adj 2 h2u
                · exact hu_adj 3 h3u)
              (hv_adj 0 h0v))
        · exact Or.inr (Or.inr
            ⟨hv_adj 0 h0v, hv_adj 3 h3v, hu_adj 1 h1u, hu_adj 2 h2u⟩)
      · rcases hvalues 3 with h3u | h3v
        · exact Or.inl
            (hpair02 hvB huB (fun h => huv h.symm)
              (hv_adj 0 h0v) (hv_adj 2 h2v) (hu_adj 1 h1u)
              (hu_adj 3 h3u))
        · exact Or.inl
            (D.carrier_one_long_arm_cone_near_hajos_with_two_incident_unsplit_edges
              B hB_connected (1 : Fin 4) hvB huB hbranch_not_B
              hcore_internal_not_B
              (by
                intro i hi
                fin_cases i
                · exact hv_adj 0 h0v
                · exact False.elim (hi rfl)
                · exact hv_adj 2 h2v
                · exact hv_adj 3 h3v)
              (hu_adj 1 h1u))
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact Or.inl
            (D.carrier_pair_split_attachment_near_hajos_with_two_incident_unsplit_edges
              B hB_connected hvB huB (fun h => huv h.symm) hbranch_not_B
              hcore_internal_not_B (hv_adj 0 h0v) (hv_adj 1 h1v)
              (hu_adj 2 h2u) (hu_adj 3 h3u))
        · exact Or.inl
            (D.carrier_one_long_arm_cone_near_hajos_with_two_incident_unsplit_edges
              B hB_connected (2 : Fin 4) hvB huB hbranch_not_B
              hcore_internal_not_B
              (by
                intro i hi
                fin_cases i
                · exact hv_adj 0 h0v
                · exact hv_adj 1 h1v
                · exact False.elim (hi rfl)
                · exact hv_adj 3 h3v)
              (hu_adj 2 h2u))
      · rcases hvalues 3 with h3u | h3v
        · exact Or.inl
            (D.carrier_one_long_arm_cone_near_hajos_with_two_incident_unsplit_edges
              B hB_connected (3 : Fin 4) hvB huB hbranch_not_B
              hcore_internal_not_B
              (by
                intro i hi
                fin_cases i
                · exact hv_adj 0 h0v
                · exact hv_adj 1 h1v
                · exact hv_adj 2 h2v
                · exact False.elim (hi rfl))
              (hu_adj 3 h3u))
        · exact Or.inl
            (D.carrier_common_attachment_near_hajos_with_two_incident_unsplit_edges
              B.verts hvB hbranch_not_B hcore_internal_not_B
              (by
                intro i
                fin_cases i
                · exact hv_adj 0 h0v
                · exact hv_adj 1 h1v
                · exact hv_adj 2 h2v
                · exact hv_adj 3 h3v))

theorem K4UnsplitSubdivisionData.carrier_two_value_attachment_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (B : G.Subgraph)
    (hB_connected : B.coe.Connected)
    {u v : V}
    (huB : u ∈ B.verts)
    (hvB : v ∈ B.verts)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ B.verts ∧ G.Adj (attach i) (D.model.branchVertex i))
    (hvalues : forall i : Fin 4, attach i = u ∨ attach i = v) :
    NearHajosStrengtheningConclusion G := by
  classical
  rcases
    D.carrier_two_value_attachment_near_hajos_or_pair03_12
      B hB_connected huB hvB hbranch_not_B hcore_internal_not_B
      attach hattach hvalues with hdone | hobstruction
  · exact hdone
  · by_cases huv : u = v
    · exact
        D.carrier_common_attachment_near_hajos_with_two_incident_unsplit_edges
          B.verts huB hbranch_not_B hcore_internal_not_B
          (by
            intro i
            rcases hvalues i with hi | hi
            · simpa [hi] using (hattach i).2
            · simpa [hi, huv] using (hattach i).2)
    · rcases hobstruction with hforward | hreverse
      · exact
          D.carrier_pair_split_03_12_attachment_near_hajos_with_two_incident_unsplit_edges
            B hB_connected huB hvB huv hbranch_not_B hcore_internal_not_B
            hforward.1 hforward.2.1 hforward.2.2.1 hforward.2.2.2
      · exact
          D.carrier_pair_split_03_12_attachment_near_hajos_with_two_incident_unsplit_edges
            B hB_connected hvB huB (fun h => huv h.symm)
            hbranch_not_B hcore_internal_not_B
            hreverse.1 hreverse.2.1 hreverse.2.2.1 hreverse.2.2.2

end Schematic.Math.GraphTheory
