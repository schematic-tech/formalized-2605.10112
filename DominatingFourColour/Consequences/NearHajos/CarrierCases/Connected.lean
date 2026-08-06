import DominatingFourColour.Consequences.NearHajos.CarrierCases.PairAttachments

/-! Connected small-carrier reductions and the final carrier alternative. -/

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_three_one_connected_first_branch_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (B : G.Subgraph)
    (hB_le : B ≤ D.model.branch (0 : Fin 5))
    (hB_connected : B.coe.Connected)
    {apex tip : V}
    (hapex_mem : apex ∈ B.verts)
    (htip_mem : tip ∈ B.verts)
    (hapex0 :
      G.Adj apex
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (0 : Fin 4)))
    (hapex1 :
      G.Adj apex
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (1 : Fin 4)))
    (hapex2 :
      G.Adj apex
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (2 : Fin 4)))
    (htip3 :
      G.Adj tip
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (3 : Fin 4))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let K : K4UnsplitSubdivisionData G :=
    D.second_singleton_k4UnsplitSubdivisionData hsecond
  exact
    K.carrier_three_one_attachment_near_hajos_with_two_incident_unsplit_edges
      B hB_connected hapex_mem htip_mem
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).1
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).2
      hapex0 hapex1 hapex2 htip3

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_pair_split_connected_first_branch_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (B : G.Subgraph)
    (hB_le : B ≤ D.model.branch (0 : Fin 5))
    (hB_connected : B.coe.Connected)
    {left right : V}
    (hleft_mem : left ∈ B.verts)
    (hright_mem : right ∈ B.verts)
    (hleft_ne_right : left ≠ right)
    (hleft0 :
      G.Adj left
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (0 : Fin 4)))
    (hleft1 :
      G.Adj left
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (1 : Fin 4)))
    (hright2 :
      G.Adj right
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (2 : Fin 4)))
    (hright3 :
      G.Adj right
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (3 : Fin 4))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let K : K4UnsplitSubdivisionData G :=
    D.second_singleton_k4UnsplitSubdivisionData hsecond
  exact
    K.carrier_pair_split_attachment_near_hajos_with_two_incident_unsplit_edges
      B hB_connected hleft_mem hright_mem hleft_ne_right
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).1
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).2
      hleft0 hleft1 hright2 hright3

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_pair_split_02_13_connected_first_branch_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (B : G.Subgraph)
    (hB_le : B ≤ D.model.branch (0 : Fin 5))
    (hB_connected : B.coe.Connected)
    {left right : V}
    (hleft_mem : left ∈ B.verts)
    (hright_mem : right ∈ B.verts)
    (hleft_ne_right : left ≠ right)
    (hleft0 :
      G.Adj left
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (0 : Fin 4)))
    (hleft2 :
      G.Adj left
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (2 : Fin 4)))
    (hright1 :
      G.Adj right
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (1 : Fin 4)))
    (hright3 :
      G.Adj right
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (3 : Fin 4))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let K : K4UnsplitSubdivisionData G :=
    D.second_singleton_k4UnsplitSubdivisionData hsecond
  let σ : Fin 4 ↪ Fin 4 := {
    toFun
      | 0 => 0
      | 1 => 2
      | 2 => 1
      | 3 => 3
    inj' := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp at h ⊢ }
  exact
    K.carrier_pair_split_attachment_relabel_near_hajos_with_two_incident_unsplit_edges
      σ
      (by
        intro hσ01
        exact D.second_singleton_k4_edgeUnsplit_of_not_special hsecond hσ01
          (by decide))
      (by
        intro hσ02
        exact D.second_singleton_k4_edgeUnsplit_of_not_special hsecond hσ02
          (by decide))
      B hB_connected hleft_mem hright_mem hleft_ne_right
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).1
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).2
      (by simpa [σ] using hleft0)
      (by simpa [σ] using hleft2)
      (by simpa [σ] using hright1)
      (by simpa [σ] using hright3)

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_pair_split_03_12_connected_first_branch_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (B : G.Subgraph)
    (hB_le : B ≤ D.model.branch (0 : Fin 5))
    (hB_connected : B.coe.Connected)
    {left right : V}
    (hleft_mem : left ∈ B.verts)
    (hright_mem : right ∈ B.verts)
    (hleft_ne_right : left ≠ right)
    (hleft0 :
      G.Adj left
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (0 : Fin 4)))
    (hleft3 :
      G.Adj left
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (3 : Fin 4)))
    (hright1 :
      G.Adj right
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (1 : Fin 4)))
    (hright2 :
      G.Adj right
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex
          (2 : Fin 4))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let K : K4UnsplitSubdivisionData G :=
    D.second_singleton_k4UnsplitSubdivisionData hsecond
  let σ : Fin 4 ↪ Fin 4 := {
    toFun
      | 0 => 0
      | 1 => 3
      | 2 => 1
      | 3 => 2
    inj' := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp at h ⊢ }
  exact
    K.carrier_pair_split_attachment_relabel_near_hajos_with_two_incident_unsplit_edges
      σ
      (by
        intro hσ01
        exact D.second_singleton_k4_edgeUnsplit_of_not_special hsecond hσ01
          (by decide))
      (by
        intro hσ02
        exact D.second_singleton_k4_edgeUnsplit_of_not_special hsecond hσ02
          (by decide))
      B hB_connected hleft_mem hright_mem hleft_ne_right
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).1
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).2
      (by simpa [σ] using hleft0)
      (by simpa [σ] using hleft3)
      (by simpa [σ] using hright1)
      (by simpa [σ] using hright2)

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_one_long_arm_cone_connected_first_branch_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (B : G.Subgraph)
    (hB_le : B ≤ D.model.branch (0 : Fin 5))
    (hB_connected : B.coe.Connected)
    (long : Fin 4)
    {apex tip : V}
    (hapex_mem : apex ∈ B.verts)
    (htip_mem : tip ∈ B.verts)
    (hadj_apex :
      forall i : Fin 4, i ≠ long ->
        G.Adj apex
          ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i))
    (htip_long :
      G.Adj tip
        ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex long)) :
    NearHajosStrengtheningConclusion G := by
  classical
  let K : K4UnsplitSubdivisionData G :=
    D.second_singleton_k4UnsplitSubdivisionData hsecond
  exact
    K.carrier_one_long_arm_cone_near_hajos_with_two_incident_unsplit_edges
      B hB_connected long hapex_mem htip_mem
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).1
      (D.second_singleton_k4_avoids_subgraph hsecond hB_le).2
      hadj_apex htip_long

set_option maxHeartbeats 0 in
theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_two_value_connected_first_branch_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (B : G.Subgraph)
    (hB_le : B ≤ D.model.branch (0 : Fin 5))
    (hB_connected : B.coe.Connected)
    {u v : V}
    (huB : u ∈ B.verts)
    (hvB : v ∈ B.verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i))
    (hvalues : forall i : Fin 4, attach i = u ∨ attach i = v) :
    NearHajosStrengtheningConclusion G := by
  classical
  by_cases huv : u = v
  · exact
      D.second_singleton_core_common_attachment_near_hajos hsecond
        (hB_le.left huB)
        (by
          intro i
          rcases hvalues i with hi | hi
          · simpa [hi] using (hattach i).2
          · simpa [hi, huv] using (hattach i).2)
  have hu_adj :
      forall i : Fin 4, attach i = u ->
        G.Adj u
          ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i) := by
    intro i hi
    simpa [hi] using (hattach i).2
  have hv_adj :
      forall i : Fin 4, attach i = v ->
        G.Adj v
          ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i) := by
    intro i hi
    simpa [hi] using (hattach i).2
  rcases hvalues 0 with h0u | h0v
  · rcases hvalues 1 with h1u | h1v
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact
            D.second_singleton_core_common_attachment_near_hajos hsecond
              (hB_le.left huB) (by
                intro i
                fin_cases i
                · exact hu_adj 0 h0u
                · exact hu_adj 1 h1u
                · exact hu_adj 2 h2u
                · exact hu_adj 3 h3u)
        · exact
            D.second_singleton_core_one_long_arm_cone_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected (3 : Fin 4) huB hvB
              (by
                intro i hi
                fin_cases i
                · exact hu_adj 0 h0u
                · exact hu_adj 1 h1u
                · exact hu_adj 2 h2u
                · exact False.elim (hi rfl))
              (hv_adj 3 h3v)
      · rcases hvalues 3 with h3u | h3v
        · exact
            D.second_singleton_core_one_long_arm_cone_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected (2 : Fin 4) huB hvB
              (by
                intro i hi
                fin_cases i
                · exact hu_adj 0 h0u
                · exact hu_adj 1 h1u
                · exact False.elim (hi rfl)
                · exact hu_adj 3 h3u)
              (hv_adj 2 h2v)
        · exact
            D.second_singleton_core_pair_split_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected huB hvB huv
              (hu_adj 0 h0u) (hu_adj 1 h1u)
              (hv_adj 2 h2v) (hv_adj 3 h3v)
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact
            D.second_singleton_core_one_long_arm_cone_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected (1 : Fin 4) huB hvB
              (by
                intro i hi
                fin_cases i
                · exact hu_adj 0 h0u
                · exact False.elim (hi rfl)
                · exact hu_adj 2 h2u
                · exact hu_adj 3 h3u)
              (hv_adj 1 h1v)
        · exact
            D.second_singleton_core_pair_split_02_13_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected huB hvB huv
              (hu_adj 0 h0u) (hu_adj 2 h2u)
              (hv_adj 1 h1v) (hv_adj 3 h3v)
      · rcases hvalues 3 with h3u | h3v
        · exact
            D.second_singleton_core_pair_split_03_12_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected huB hvB huv
              (hu_adj 0 h0u) (hu_adj 3 h3u)
              (hv_adj 1 h1v) (hv_adj 2 h2v)
        · exact
            D.second_singleton_core_one_long_arm_cone_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected (0 : Fin 4) hvB huB
              (by
                intro i hi
                fin_cases i
                · exact False.elim (hi rfl)
                · exact hv_adj 1 h1v
                · exact hv_adj 2 h2v
                · exact hv_adj 3 h3v)
              (hu_adj 0 h0u)
  · rcases hvalues 1 with h1u | h1v
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact
            D.second_singleton_core_one_long_arm_cone_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected (0 : Fin 4) huB hvB
              (by
                intro i hi
                fin_cases i
                · exact False.elim (hi rfl)
                · exact hu_adj 1 h1u
                · exact hu_adj 2 h2u
                · exact hu_adj 3 h3u)
              (hv_adj 0 h0v)
        · exact
            D.second_singleton_core_pair_split_03_12_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected hvB huB (fun h => huv h.symm)
              (hv_adj 0 h0v) (hv_adj 3 h3v)
              (hu_adj 1 h1u) (hu_adj 2 h2u)
      · rcases hvalues 3 with h3u | h3v
        · exact
            D.second_singleton_core_pair_split_02_13_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected hvB huB (fun h => huv h.symm)
              (hv_adj 0 h0v) (hv_adj 2 h2v)
              (hu_adj 1 h1u) (hu_adj 3 h3u)
        · exact
            D.second_singleton_core_one_long_arm_cone_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected (1 : Fin 4) hvB huB
              (by
                intro i hi
                fin_cases i
                · exact hv_adj 0 h0v
                · exact False.elim (hi rfl)
                · exact hv_adj 2 h2v
                · exact hv_adj 3 h3v)
              (hu_adj 1 h1u)
    · rcases hvalues 2 with h2u | h2v
      · rcases hvalues 3 with h3u | h3v
        · exact
            D.second_singleton_core_pair_split_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected hvB huB (fun h => huv h.symm)
              (hv_adj 0 h0v) (hv_adj 1 h1v)
              (hu_adj 2 h2u) (hu_adj 3 h3u)
        · exact
            D.second_singleton_core_one_long_arm_cone_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected (2 : Fin 4) hvB huB
              (by
                intro i hi
                fin_cases i
                · exact hv_adj 0 h0v
                · exact hv_adj 1 h1v
                · exact False.elim (hi rfl)
                · exact hv_adj 3 h3v)
              (hu_adj 2 h2u)
      · rcases hvalues 3 with h3u | h3v
        · exact
            D.second_singleton_core_one_long_arm_cone_connected_first_branch_near_hajos
              hsecond B hB_le hB_connected (3 : Fin 4) hvB huB
              (by
                intro i hi
                fin_cases i
                · exact hv_adj 0 h0v
                · exact hv_adj 1 h1v
                · exact hv_adj 2 h2v
                · exact False.elim (hi rfl))
              (hu_adj 3 h3u)
        · exact
            D.second_singleton_core_common_attachment_near_hajos hsecond
              (hB_le.left hvB) (by
                intro i
                fin_cases i
                · exact hv_adj 0 h0v
                · exact hv_adj 1 h1v
                · exact hv_adj 2 h2v
                · exact hv_adj 3 h3v)

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_small_connected_attachment_carrier_near_hajos
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i))
    (B : G.Subgraph)
    (hB_le : B ≤ D.model.branch (0 : Fin 5))
    (hB_connected : B.coe.Connected)
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_card : B.verts.ncard <= 2) :
    NearHajosStrengtheningConclusion G := by
  classical
  obtain ⟨u, v, huB, hvB, hvalues⟩ :=
    fin4_map_into_set_ncard_le_two_has_two_values
      (V := V) (A := B.verts) attach hB_terminal hB_card
  exact
    D.second_singleton_core_two_value_connected_first_branch_near_hajos
      hsecond B hB_le hB_connected huB hvB attach hattach hvalues

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_two_value_first_branch_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    {u v : V}
    (hu_mem : u ∈ (D.model.branch (0 : Fin 5)).verts)
    (hv_mem : v ∈ (D.model.branch (0 : Fin 5)).verts)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i))
    (hvalues : forall i : Fin 4, attach i = u ∨ attach i = v) :
    NearHajosStrengtheningConclusion G := by
  exact
    D.second_singleton_core_two_value_connected_first_branch_near_hajos
      hsecond (D.model.branch (0 : Fin 5)) le_rfl
      (D.model.connected (0 : Fin 5)) hu_mem hv_mem attach hattach hvalues

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_two_value_first_branch_exists_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (htwo :
      Exists fun attach : Fin 4 -> V =>
        Exists fun u : V =>
          Exists fun v : V =>
            (forall i : Fin 4,
              attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
                G.Adj (attach i)
                  ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
              u ∈ (D.model.branch (0 : Fin 5)).verts ∧
                v ∈ (D.model.branch (0 : Fin 5)).verts ∧
                  (forall i : Fin 4, attach i = u ∨ attach i = v)) :
    NearHajosStrengtheningConclusion G := by
  rcases htwo with ⟨attach, u, v, hattach, hu, hv, hvalues⟩
  exact
    D.second_singleton_core_two_value_first_branch_near_hajos
      hsecond hu hv attach hattach hvalues

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_small_attachment_carrier_near_hajos
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i)
            ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i))
    (B : G.Subgraph)
    (hB_le : B ≤ D.model.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_card : B.verts.ncard <= 2) :
    NearHajosStrengtheningConclusion G := by
  classical
  obtain ⟨u, v, huB, hvB, hvalues⟩ :=
    fin4_map_into_set_ncard_le_two_has_two_values
      (V := V) (A := B.verts) attach hB_terminal hB_card
  exact
    D.second_singleton_core_two_value_first_branch_near_hajos
      hsecond (hB_le.left huB) (hB_le.left hvB) attach hattach hvalues

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_small_attachment_carrier_exists_near_hajos
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (hsmall :
      Exists fun attach : Fin 4 -> V =>
        Exists fun B : G.Subgraph =>
          (forall i : Fin 4,
            attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
              G.Adj (attach i)
                ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
            B ≤ D.model.branch (0 : Fin 5) ∧
              (forall i : Fin 4, attach i ∈ B.verts) ∧
                B.verts.ncard <= 2) :
    NearHajosStrengtheningConclusion G := by
  rcases hsmall with ⟨attach, B, hattach, hB_le, hB_terminal, hB_card⟩
  exact
    D.second_singleton_core_small_attachment_carrier_near_hajos
      hsecond attach hattach B hB_le hB_terminal hB_card

theorem ThirdBranchPathAndTailInducedCycleData.second_singleton_core_near_hajos_or_large_tree_carrier
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5)) :
    NearHajosStrengtheningConclusion G ∨
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
  by_cases htwo :
      Exists fun attach : Fin 4 -> V =>
        Exists fun u : V =>
          Exists fun v : V =>
            (forall i : Fin 4,
              attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
                G.Adj (attach i)
                  ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
              u ∈ (D.model.branch (0 : Fin 5)).verts ∧
                v ∈ (D.model.branch (0 : Fin 5)).verts ∧
                  (forall i : Fin 4, attach i = u ∨ attach i = v)
  · exact Or.inl
      (D.second_singleton_core_two_value_first_branch_exists_near_hajos
        hsecond htwo)
  · by_cases hsmall :
      Exists fun attach : Fin 4 -> V =>
        Exists fun B : G.Subgraph =>
          (forall i : Fin 4,
            attach i ∈ (D.model.branch (0 : Fin 5)).verts ∧
              G.Adj (attach i)
                ((D.second_singleton_k4UnsplitSubdivisionData hsecond).model.branchVertex i)) ∧
            B ≤ D.model.branch (0 : Fin 5) ∧
              (forall i : Fin 4, attach i ∈ B.verts) ∧
                B.verts.ncard <= 2
    · exact Or.inl
        (D.second_singleton_core_small_attachment_carrier_exists_near_hajos
          hsecond hsmall)
    · exact Or.inr
        (D.second_singleton_core_first_branch_large_minimal_attachment_tree_carrier
          hsecond htwo hsmall)

end Schematic.Math.GraphTheory
