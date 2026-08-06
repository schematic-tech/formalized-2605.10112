import DominatingFourColour.Consequences.NearHajos.Basic.Conclusion

/-! Rooted and cone carrier constructions. -/

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

private def fin5K4CoreOrApex : Fin 5 ↪ Option (Fin 4) where
  toFun
    | 0 => some 0
    | 1 => some 1
    | 2 => some 2
    | 3 => some 3
    | 4 => none
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢

set_option maxHeartbeats 0 in
theorem K4UnsplitSubdivisionData.cone_paths_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (apex : V)
    (hapex_not_branch : forall i : Fin 4, apex ≠ D.model.branchVertex i)
    (arm : forall i : Fin 4, G.Walk apex (D.model.branchVertex i))
    (harm_path : forall i : Fin 4, (arm i).IsPath)
    (harm_internal_no_branch :
      forall i : Fin 4, forall {z : V},
        z ∈ Walk.InternalVertices (arm i) ->
          forall w : Option (Fin 4),
            z ≠
              match w with
              | none => apex
              | some j => D.model.branchVertex j)
    (hcore_internal_no_apex :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ apex)
    (harm_internal_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (arm j)))
    (harm_core_disjoint :
      forall {i j k : Fin 4} (hjk : K4Graph.Adj j k),
        Disjoint
          (Walk.InternalVertices (arm i))
          (Walk.InternalVertices (D.model.edgePath hjk))) :
    NearHajosStrengtheningConclusion G := by
  classical
  let branch : Option (Fin 4) -> V
    | none => apex
    | some i => D.model.branchVertex i
  have hbranch_injective : Function.Injective branch := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some j =>
            exact False.elim ((hapex_not_branch j) hxy)
    | some i =>
        cases y with
        | none =>
            exact False.elim ((hapex_not_branch i) hxy.symm)
        | some j =>
            exact congrArg some (D.model.branchVertex_injective hxy)
  let H : SimpleGraph (Option (Fin 4)) :=
    SimpleGraph.completeGraph (Option (Fin 4))
  let M : StrictSubdivisionModel H G := {
    branchVertex := branch
    branchVertex_injective := hbranch_injective
    edgePath := by
      intro x y hxy
      cases x with
      | none =>
          cases y with
          | none => exact False.elim (hxy.ne rfl)
          | some j => exact arm j
      | some i =>
          cases y with
          | none => exact (arm i).reverse
          | some j =>
              have hij : K4Graph.Adj i j := by
                simpa [K4Graph, CompleteGraphOn] using
                  (show i ≠ j from by
                    intro hij
                    exact hxy.ne (by simp [hij]))
              exact D.model.edgePath hij
    edgePath_isPath := by
      intro x y hxy
      cases x with
      | none =>
          cases y with
          | none => exact False.elim (hxy.ne rfl)
          | some j => exact harm_path j
      | some i =>
          cases y with
          | none => exact (harm_path i).reverse
          | some j =>
              have hij : K4Graph.Adj i j := by
                simpa [K4Graph, CompleteGraphOn] using
                  (show i ≠ j from by
                    intro hij
                    exact hxy.ne (by simp [hij]))
              exact D.model.edgePath_isPath hij
    no_internal_branch_vertices := True
    internally_disjoint_edge_paths := True
    no_internal_branch_vertices' := by
      intro x y hxy z hz w hzw
      cases x with
      | none =>
          cases y with
          | none => exact False.elim (hxy.ne rfl)
          | some j =>
              exact (harm_internal_no_branch j hz w) hzw
      | some i =>
          cases y with
          | none =>
              have hz_arm : z ∈ Walk.InternalVertices (arm i) := by
                simpa [Walk.internalVertices_reverse] using hz
              exact (harm_internal_no_branch i hz_arm w) hzw
          | some j =>
              have hij : K4Graph.Adj i j := by
                simpa [K4Graph, CompleteGraphOn] using
                  (show i ≠ j from by
                    intro hij
                    exact hxy.ne (by simp [hij]))
              cases w with
              | none =>
                  exact hcore_internal_no_apex hij hz hzw
              | some k =>
                  exact D.model.no_internal_branch_vertices' hij hz k hzw
    internally_disjoint_edge_paths' := by
      intro x y x' y' hxy hx'y' hne
      rw [Set.disjoint_left]
      intro z hz hz'
      cases x with
      | none =>
          cases y with
          | none => exact False.elim (hxy.ne rfl)
          | some i =>
              cases x' with
              | none =>
                  cases y' with
                  | none => exact False.elim (hx'y'.ne rfl)
                  | some j =>
                      by_cases hij : i = j
                      · subst j
                        exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                      · exact
                          Set.disjoint_left.mp (harm_internal_disjoint hij) hz hz'
              | some j =>
                  cases y' with
                  | none =>
                      have hz'_arm : z ∈ Walk.InternalVertices (arm j) := by
                        simpa [Walk.internalVertices_reverse] using hz'
                      by_cases hij : i = j
                      · subst j
                        exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                      · exact
                          Set.disjoint_left.mp (harm_internal_disjoint hij) hz hz'_arm
                  | some k =>
                      have hjk : K4Graph.Adj j k := by
                        simpa [K4Graph, CompleteGraphOn] using
                          (show j ≠ k from by
                            intro hjk
                            exact hx'y'.ne (by simp [hjk]))
                      exact Set.disjoint_left.mp (harm_core_disjoint (i := i) hjk) hz hz'
      | some i =>
          cases y with
          | none =>
              have hz_arm : z ∈ Walk.InternalVertices (arm i) := by
                simpa [Walk.internalVertices_reverse] using hz
              cases x' with
              | none =>
                  cases y' with
                  | none => exact False.elim (hx'y'.ne rfl)
                  | some j =>
                      by_cases hij : i = j
                      · subst j
                        exact False.elim (hne (Or.inr ⟨rfl, rfl⟩))
                      · exact
                          Set.disjoint_left.mp (harm_internal_disjoint hij) hz_arm hz'
              | some j =>
                  cases y' with
                  | none =>
                      have hz'_arm : z ∈ Walk.InternalVertices (arm j) := by
                        simpa [Walk.internalVertices_reverse] using hz'
                      by_cases hij : i = j
                      · subst j
                        exact False.elim (hne (Or.inl ⟨rfl, rfl⟩))
                      · exact
                          Set.disjoint_left.mp (harm_internal_disjoint hij) hz_arm hz'_arm
                  | some k =>
                      have hjk : K4Graph.Adj j k := by
                        simpa [K4Graph, CompleteGraphOn] using
                          (show j ≠ k from by
                            intro hjk
                            exact hx'y'.ne (by simp [hjk]))
                      exact Set.disjoint_left.mp (harm_core_disjoint (i := i) hjk)
                        hz_arm hz'
          | some j =>
              have hij : K4Graph.Adj i j := by
                simpa [K4Graph, CompleteGraphOn] using
                  (show i ≠ j from by
                    intro hij
                    exact hxy.ne (by simp [hij]))
              cases x' with
              | none =>
                  cases y' with
                  | none => exact False.elim (hx'y'.ne rfl)
                  | some k =>
                      exact Set.disjoint_left.mp
                        (Disjoint.symm (harm_core_disjoint (i := k) hij)) hz hz'
              | some k =>
                  cases y' with
                  | none =>
                      have hz'_arm : z ∈ Walk.InternalVertices (arm k) := by
                        simpa [Walk.internalVertices_reverse] using hz'
                      exact Set.disjoint_left.mp
                        (Disjoint.symm (harm_core_disjoint (i := k) hij)) hz hz'_arm
                  | some l =>
                      have hkl : K4Graph.Adj k l := by
                        simpa [K4Graph, CompleteGraphOn] using
                          (show k ≠ l from by
                            intro hkl
                            exact hx'y'.ne (by simp [hkl]))
                      have hne' :
                          ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) := by
                        intro hsame
                        apply hne
                        rcases hsame with hsame | hsame
                        · exact Or.inl ⟨by simp [hsame.1], by simp [hsame.2]⟩
                        · exact Or.inr ⟨by simp [hsame.1], by simp [hsame.2]⟩
                      exact
                        Set.disjoint_left.mp
                          (D.model.internally_disjoint_edge_paths' hij hkl hne')
                          hz hz'
  }
  let e : Fin 5 ↪ Option (Fin 4) := fin5K4CoreOrApex
  let h_adj :
      forall {x y : Fin 5}, K5Graph.Adj x y -> H.Adj (e x) (e y) := by
    intro x y hxy
    exact fun h => hxy.ne (e.injective h)
  let MK5 : StrictSubdivisionModel K5Graph G := M.domainRestrict e h_adj
  exact Or.inl ⟨{
    model := MK5
    edge₁_unsplit := by
      let h01 : K5Graph.Adj (0 : Fin 5) (1 : Fin 5) := by decide
      change (M.domainRestrict e h_adj).EdgeUnsplit h01
      rw [StrictSubdivisionModel.domainRestrict_edgeUnsplit]
      simpa [M, e, h_adj, fin5K4CoreOrApex, StrictSubdivisionModel.EdgeUnsplit]
        using D.edge₁_unsplit
    edge₂_unsplit := by
      let h02 : K5Graph.Adj (0 : Fin 5) (2 : Fin 5) := by decide
      change (M.domainRestrict e h_adj).EdgeUnsplit h02
      rw [StrictSubdivisionModel.domainRestrict_edgeUnsplit]
      simpa [M, e, h_adj, fin5K4CoreOrApex, StrictSubdivisionModel.EdgeUnsplit]
        using D.edge₂_unsplit
  }⟩

theorem K4UnsplitSubdivisionData.cone_apex_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (apex : V)
    (hapex_not_branch : forall i : Fin 4, apex ≠ D.model.branchVertex i)
    (hapex_not_internal :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ apex)
    (hadj : forall i : Fin 4, G.Adj apex (D.model.branchVertex i)) :
    NearHajosStrengtheningConclusion G := by
  refine
    D.cone_paths_near_hajos_with_two_incident_unsplit_edges
      apex hapex_not_branch (fun i => (hadj i).toWalk) ?_ ?_
      hapex_not_internal ?_ ?_
  · intro i
    exact SimpleGraph.Walk.IsPath.of_adj (hadj i)
  · intro i z hz w hzw
    exact (Walk.not_mem_internalVertices_toWalk (hadj i) hz).elim
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hz _hz'
    exact (Walk.not_mem_internalVertices_toWalk (hadj i) hz).elim
  · intro i j k hjk
    rw [Set.disjoint_left]
    intro z hz _hz'
    exact (Walk.not_mem_internalVertices_toWalk (hadj i) hz).elim

theorem K4UnsplitSubdivisionData.carrier_rooted_attachment_paths_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (C : Set V)
    {apex : V}
    (hapex_mem : apex ∈ C)
    (hbranch_not_carrier :
      forall i : Fin 4, D.model.branchVertex i ∉ C)
    (hcore_internal_not_carrier :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ C)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ C ∧ G.Adj (attach i) (D.model.branchVertex i))
    (stem : forall i : Fin 4, G.Walk apex (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_carrier :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support -> z ∈ C)
    (hstem_punctured_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stem i).support ∧ z ≠ apex}
          {z : V | z ∈ (stem j).support ∧ z ≠ apex}) :
    NearHajosStrengtheningConclusion G := by
  classical
  let arm : forall i : Fin 4, G.Walk apex (D.model.branchVertex i) :=
    fun i => (stem i).concat (hattach i).2
  have hapex_not_branch :
      forall i : Fin 4, apex ≠ D.model.branchVertex i := by
    intro i h
    exact hbranch_not_carrier i (by simpa [h] using hapex_mem)
  have hbranch_not_stem_support :
      forall i : Fin 4, D.model.branchVertex i ∉ (stem i).support := by
    intro i hsupport
    exact hbranch_not_carrier i (hstem_support_carrier i hsupport)
  refine
    D.cone_paths_near_hajos_with_two_incident_unsplit_edges
      apex hapex_not_branch arm ?_ ?_ ?_ ?_ ?_
  · intro i
    change ((stem i).concat (hattach i).2).IsPath
    exact (hstem_path i).concat (hbranch_not_stem_support i) (hattach i).2
  · intro i z hz w hzw
    cases w with
    | none =>
        exact hz.2.1 hzw
    | some j =>
        exact hbranch_not_carrier j (by
          have hz_stem :
              z ∈ (stem i).support :=
            Walk.mem_support_of_mem_internalVertices_concat
              (stem i) (hattach i).2 hz
          simpa [hzw] using hstem_support_carrier i hz_stem)
  · intro i j hij z hz h
    exact hcore_internal_not_carrier hij hz (by simpa [h] using hapex_mem)
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzi_stem :
        z ∈ (stem i).support ∧ z ≠ apex :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hzi
    have hzj_stem :
        z ∈ (stem j).support ∧ z ≠ apex :=
      Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
        (stem j) (hattach j).2 hzj
    exact Set.disjoint_left.mp (hstem_punctured_disjoint hij)
      hzi_stem hzj_stem
  · intro i j k hjk
    rw [Set.disjoint_left]
    intro z hz_arm hz_core
    have hz_stem :
        z ∈ (stem i).support :=
      Walk.mem_support_of_mem_internalVertices_concat
        (stem i) (hattach i).2 hz_arm
    exact hcore_internal_not_carrier hjk hz_core
      (hstem_support_carrier i hz_stem)

theorem K4UnsplitSubdivisionData.carrier_rooted_attachment_subgraph_tree_paths_through_root_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (B : G.Subgraph)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    (apexB : B.verts)
    (attachB : Fin 4 -> B.verts)
    [DecidableEq B.verts]
    (TB : B.coe.Subgraph)
    [DecidableEq TB.verts]
    (hTB_tree : TB.coe.IsTree)
    (hroot_T : apexB ∈ TB.verts)
    (hterminal_T : forall i : Fin 4, attachB i ∈ TB.verts)
    (hattach_adj :
      forall i : Fin 4, G.Adj (attachB i : V) (D.model.branchVertex i))
    (stemB :
      forall i : Fin 4,
        B.coe.Walk apexB (attachB i))
    (hstemB_path : forall i : Fin 4, (stemB i).IsPath)
    (hstemB_le : forall i : Fin 4, (stemB i).toSubgraph ≤ TB)
    (hpair_path_through_root :
      forall {i j : Fin 4}, i ≠ j ->
        Exists fun p : B.coe.Walk (attachB i) (attachB j) =>
          p.toSubgraph ≤ TB ∧ p.IsPath ∧ apexB ∈ p.support) :
    NearHajosStrengtheningConclusion G := by
  classical
  let apex : V := apexB
  let attach : Fin 4 -> V := fun i => attachB i
  let stemG : forall i : Fin 4, G.Walk apex (attach i) :=
    fun i => (stemB i).map B.hom
  let rootT : TB.verts := ⟨apexB, hroot_T⟩
  let terminalT : Fin 4 -> TB.verts := fun i => ⟨attachB i, hterminal_T i⟩
  have hpair_path_through_root_T :
      forall {i j : Fin 4}, i ≠ j ->
        Exists fun p :
          B.coe.Walk (terminalT i : B.verts) (terminalT j : B.verts) =>
          p.toSubgraph ≤ TB ∧ p.IsPath ∧ (rootT : B.verts) ∈ p.support := by
    intro i j hij
    obtain ⟨p, hp_le, hp_path, hroot⟩ := hpair_path_through_root hij
    exact ⟨p.copy (Subtype.ext rfl) (Subtype.ext rfl), by
      simpa using hp_le, by
      simpa using hp_path, by
      simpa [rootT] using hroot⟩
  have hstemG_path : forall i : Fin 4, (stemG i).IsPath := by
    intro i
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective (hstemB_path i)
  have hstemG_support :
      forall i : Fin 4, forall {z : V},
        z ∈ (stemG i).support -> z ∈ B.verts := by
    intro i z hz
    exact Walk.support_map_subgraph_hom_subset (H := B) (stemB i)
      (by simpa [stemG] using hz)
  have hstemB_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : B.verts | z ∈ (stemB i).support ∧ z ≠ apexB}
          {z : B.verts | z ∈ (stemB j).support ∧ z ≠ apexB} := by
    have hraw :
        forall {i j : Fin 4}, i ≠ j ->
          Disjoint
            {z : B.verts | z ∈ (stemB i).support ∧ z ≠ (rootT : B.verts)}
            {z : B.verts | z ∈ (stemB j).support ∧ z ≠ (rootT : B.verts)} :=
      Subgraph.tree_rooted_paths_punctured_supports_disjoint_of_pair_paths_through_root_allow_eq
        (G := B.coe) (T := TB) hTB_tree
        (root := rootT) (terminal := terminalT)
        stemB hstemB_le hstemB_path hpair_path_through_root_T
    intro i j hij
    simpa [rootT] using hraw hij
  have hstemG_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stemG i).support ∧ z ≠ apex}
          {z : V | z ∈ (stemG j).support ∧ z ≠ apex} := by
    intro i j hij
    simpa [stemG, apex] using
      (Subgraph.walk_family_mapped_punctured_supports_disjoint
        (G := G) (B := B) stemB hstemB_disjoint hij)
  exact
    D.carrier_rooted_attachment_paths_near_hajos_with_two_incident_unsplit_edges
      B.verts (by exact apexB.2) hbranch_not_B hcore_internal_not_B
      attach
      (by
        intro i
        exact ⟨(attachB i).2, hattach_adj i⟩)
      stemG hstemG_path hstemG_support hstemG_disjoint

theorem K4UnsplitSubdivisionData.carrier_rooted_attachment_spanning_tree_all_pairs_through_root_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (B : G.Subgraph)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    (attach : Fin 4 -> V)
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    [DecidableEq B.verts]
    (TB : B.coe.Subgraph)
    [DecidableEq TB.verts]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning)
    (apexB : B.verts)
    (hattach_adj :
      forall i : Fin 4, G.Adj (attach i) (D.model.branchVertex i))
    (hpair_path_through_root :
      forall {i j : Fin 4}, i ≠ j ->
        Exists fun p :
          B.coe.Walk
            (⟨attach i, hB_terminal i⟩ : B.verts)
            (⟨attach j, hB_terminal j⟩ : B.verts) =>
          p.toSubgraph ≤ TB ∧ p.IsPath ∧ apexB ∈ p.support) :
    NearHajosStrengtheningConclusion G := by
  classical
  let attachB : Fin 4 -> B.verts := fun i => ⟨attach i, hB_terminal i⟩
  have hroot_T : apexB ∈ TB.verts := hTB_spanning apexB
  have hterminal_T : forall i : Fin 4, attachB i ∈ TB.verts := by
    intro i
    exact hTB_spanning (attachB i)
  obtain ⟨stemB, hstemB_path, hstemB_le⟩ :=
    Subgraph.Connected.exists_coe_rooted_paths_in_spanning_coe_subgraph
      (B := B) (T := TB) hTB_tree.connected hTB_spanning
      apexB.2 attach hB_terminal
  exact
    D.carrier_rooted_attachment_subgraph_tree_paths_through_root_near_hajos_with_two_incident_unsplit_edges
      B hbranch_not_B hcore_internal_not_B apexB attachB TB hTB_tree
      hroot_T hterminal_T
      (by
        intro i
        simpa [attachB] using hattach_adj i)
      (fun i => by
        simpa [attachB] using stemB i)
      (by
        intro i
        simpa [attachB] using hstemB_path i)
      (by
        intro i
        simpa [attachB] using hstemB_le i)
      (by
        intro i j hij
        simpa [attachB] using hpair_path_through_root hij)

theorem K4UnsplitSubdivisionData.carrier_rooted_attachment_paths_permute_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    (C : Set V)
    {apex : V}
    (hapex_mem : apex ∈ C)
    (hbranch_not_carrier :
      forall i : Fin 4, D.model.branchVertex i ∉ C)
    (hcore_internal_not_carrier :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ C)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ C ∧ G.Adj (attach i) (D.model.branchVertex (σ i)))
    (stem : forall i : Fin 4, G.Walk apex (attach i))
    (hstem_path : forall i : Fin 4, (stem i).IsPath)
    (hstem_support_carrier :
      forall i : Fin 4, forall {z : V},
        z ∈ (stem i).support -> z ∈ C)
    (hstem_punctured_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stem i).support ∧ z ≠ apex}
          {z : V | z ∈ (stem j).support ∧ z ≠ apex}) :
    NearHajosStrengtheningConclusion G := by
  classical
  have hsurj : Function.Surjective σ :=
    Finite.surjective_of_injective σ.injective
  let pre : Fin 4 -> Fin 4 := fun i => Classical.choose (hsurj i)
  have hpre : forall i : Fin 4, σ (pre i) = i := by
    intro i
    simpa [pre] using Classical.choose_spec (hsurj i)
  have hpre_ne : forall {i j : Fin 4}, i ≠ j -> pre i ≠ pre j := by
    intro i j hij h
    exact hij (by
      calc
        i = σ (pre i) := (hpre i).symm
        _ = σ (pre j) := by rw [h]
        _ = j := hpre j)
  let attach' : Fin 4 -> V := fun i => attach (pre i)
  let stem' : forall i : Fin 4, G.Walk apex (attach' i) := fun i => stem (pre i)
  exact
    D.carrier_rooted_attachment_paths_near_hajos_with_two_incident_unsplit_edges
      C hapex_mem hbranch_not_carrier hcore_internal_not_carrier
      attach'
      (by
        intro i
        refine ⟨(hattach (pre i)).1, ?_⟩
        simpa [attach', hpre i] using (hattach (pre i)).2)
      stem'
      (by
        intro i
        simpa [stem'] using hstem_path (pre i))
      (by
        intro i z hz
        exact hstem_support_carrier (pre i) (by simpa [stem'] using hz))
      (by
        intro i j hij
        simpa [stem'] using hstem_punctured_disjoint (hpre_ne hij))

theorem K4UnsplitSubdivisionData.carrier_rooted_attachment_subgraph_paths_permute_meet_only_root_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (σ : Fin 4 ↪ Fin 4)
    (B : G.Subgraph)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    (apexB : B.verts)
    (attachB : Fin 4 -> B.verts)
    (hattach_adj :
      forall i : Fin 4,
        G.Adj (attachB i : V) (D.model.branchVertex (σ i)))
    (stemB : forall i : Fin 4, B.coe.Walk apexB (attachB i))
    (hstemB_path : forall i : Fin 4, (stemB i).IsPath)
    (hstemB_meet_only_root :
      forall {i j : Fin 4}, i ≠ j ->
        forall {z : B.verts},
          z ∈ (stemB i).support ->
            z ∈ (stemB j).support ->
              z = apexB) :
    NearHajosStrengtheningConclusion G := by
  classical
  let apex : V := apexB
  let attach : Fin 4 -> V := fun i => attachB i
  let stemG : forall i : Fin 4, G.Walk apex (attach i) :=
    fun i => (stemB i).map B.hom
  have hstemG_path : forall i : Fin 4, (stemG i).IsPath := by
    intro i
    exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective (hstemB_path i)
  have hstemG_support :
      forall i : Fin 4, forall {z : V},
        z ∈ (stemG i).support -> z ∈ B.verts := by
    intro i z hz
    exact Walk.support_map_subgraph_hom_subset (H := B) (stemB i)
      (by simpa [stemG] using hz)
  have hstemB_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : B.verts | z ∈ (stemB i).support ∧ z ≠ apexB}
          {z : B.verts | z ∈ (stemB j).support ∧ z ≠ apexB} := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact hzi.2 (hstemB_meet_only_root hij hzi.1 hzj.1)
  have hstemG_disjoint :
      forall {i j : Fin 4}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (stemG i).support ∧ z ≠ apex}
          {z : V | z ∈ (stemG j).support ∧ z ≠ apex} := by
    intro i j hij
    simpa [stemG, apex] using
      (Subgraph.walk_family_mapped_punctured_supports_disjoint
        (G := G) (B := B) stemB hstemB_disjoint hij)
  exact
    D.carrier_rooted_attachment_paths_permute_near_hajos_with_two_incident_unsplit_edges
      σ B.verts (by exact apexB.2) hbranch_not_B hcore_internal_not_B
      attach
      (by
        intro i
        exact ⟨(attachB i).2, hattach_adj i⟩)
      stemG hstemG_path hstemG_support hstemG_disjoint

theorem K4UnsplitSubdivisionData.carrier_common_attachment_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (C : Set V)
    {apex : V}
    (hapex_mem : apex ∈ C)
    (hbranch_not_carrier :
      forall i : Fin 4, D.model.branchVertex i ∉ C)
    (hcore_internal_not_carrier :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ C)
    (hadj : forall i : Fin 4, G.Adj apex (D.model.branchVertex i)) :
    NearHajosStrengtheningConclusion G := by
  classical
  have hapex_not_branch : forall i : Fin 4, apex ≠ D.model.branchVertex i := by
    intro i h
    exact hbranch_not_carrier i (by simpa [h] using hapex_mem)
  have hcore_internal_not_apex :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ apex := by
    intro i j hij z hz h
    exact hcore_internal_not_carrier hij hz (by simpa [h] using hapex_mem)
  exact
    D.cone_apex_near_hajos_with_two_incident_unsplit_edges
      apex hapex_not_branch hcore_internal_not_apex hadj

theorem K4UnsplitSubdivisionData.carrier_three_one_attachment_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (B : G.Subgraph)
    (hB_connected : B.coe.Connected)
    {apex tip : V}
    (hapex_mem : apex ∈ B.verts)
    (htip_mem : tip ∈ B.verts)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    (hapex0 : G.Adj apex (D.model.branchVertex (0 : Fin 4)))
    (hapex1 : G.Adj apex (D.model.branchVertex (1 : Fin 4)))
    (hapex2 : G.Adj apex (D.model.branchVertex (2 : Fin 4)))
    (htip3 : G.Adj tip (D.model.branchVertex (3 : Fin 4))) :
    NearHajosStrengtheningConclusion G := by
  classical
  have hapex_not_branch : forall i : Fin 4, apex ≠ D.model.branchVertex i := by
    intro i h
    exact hbranch_not_B i (by simpa [h] using hapex_mem)
  have hcore_internal_no_apex :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ apex := by
    intro i j hij z hz h
    exact hcore_internal_not_B hij hz (by simpa [h] using hapex_mem)
  obtain ⟨q, hq_path, hq_le⟩ :=
    Subgraph.Connected.exists_path_between hB_connected hapex_mem htip_mem
  have hbranch3_not_q_support :
      D.model.branchVertex (3 : Fin 4) ∉ q.support := by
    intro hsupport
    exact hbranch_not_B 3
      (hq_le.left (by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        exact hsupport))
  let arm : forall i : Fin 4, G.Walk apex (D.model.branchVertex i)
    | 0 => hapex0.toWalk
    | 1 => hapex1.toWalk
    | 2 => hapex2.toWalk
    | 3 => q.concat htip3
  have harm_path : forall i : Fin 4, (arm i).IsPath := by
    intro i
    fin_cases i <;> simp [arm]
    · exact hapex0.ne
    · exact hapex1.ne
    · exact hapex2.ne
    · exact hq_path.concat hbranch3_not_q_support htip3
  refine
    D.cone_paths_near_hajos_with_two_incident_unsplit_edges
      apex hapex_not_branch arm harm_path ?_ hcore_internal_no_apex ?_ ?_
  · intro i z hz w hzw
    fin_cases i <;> simp [arm] at hz
    · exact (Walk.not_mem_internalVertices_toWalk hapex0 hz).elim
    · exact (Walk.not_mem_internalVertices_toWalk hapex1 hz).elim
    · exact (Walk.not_mem_internalVertices_toWalk hapex2 hz).elim
    · cases w with
      | none =>
          exact hz.2.1 hzw
      | some j =>
          have hz_q : z ∈ q.support :=
            Walk.mem_support_of_mem_internalVertices_concat q htip3 hz
          have hzB : z ∈ B.verts :=
            hq_le.left (by
              rw [SimpleGraph.Walk.mem_verts_toSubgraph]
              exact hz_q)
          exact hbranch_not_B j
            (by simpa [hzw] using hzB)
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    fin_cases i <;> fin_cases j <;> simp [arm] at hzi hzj
    all_goals first
      | exact (Walk.not_mem_internalVertices_toWalk hapex0 hzi).elim
      | exact (Walk.not_mem_internalVertices_toWalk hapex1 hzi).elim
      | exact (Walk.not_mem_internalVertices_toWalk hapex2 hzi).elim
      | exact (Walk.not_mem_internalVertices_toWalk hapex0 hzj).elim
      | exact (Walk.not_mem_internalVertices_toWalk hapex1 hzj).elim
      | exact (Walk.not_mem_internalVertices_toWalk hapex2 hzj).elim
      | exact False.elim (hij rfl)
  · intro i j k hjk
    rw [Set.disjoint_left]
    intro z hzi hz_core
    fin_cases i <;> simp [arm] at hzi
    · exact (Walk.not_mem_internalVertices_toWalk hapex0 hzi).elim
    · exact (Walk.not_mem_internalVertices_toWalk hapex1 hzi).elim
    · exact (Walk.not_mem_internalVertices_toWalk hapex2 hzi).elim
    · have hz_q : z ∈ q.support :=
        Walk.mem_support_of_mem_internalVertices_concat q htip3 hzi
      have hzB : z ∈ B.verts :=
        hq_le.left (by
          rw [SimpleGraph.Walk.mem_verts_toSubgraph]
          exact hz_q)
      exact hcore_internal_not_B hjk hz_core hzB

theorem K4UnsplitSubdivisionData.carrier_one_long_arm_cone_near_hajos_with_two_incident_unsplit_edges
    {V : Type u} {G : SimpleGraph V}
    (D : K4UnsplitSubdivisionData G)
    (B : G.Subgraph)
    (hB_connected : B.coe.Connected)
    (long : Fin 4)
    {apex tip : V}
    (hapex_mem : apex ∈ B.verts)
    (htip_mem : tip ∈ B.verts)
    (hbranch_not_B : forall i : Fin 4, D.model.branchVertex i ∉ B.verts)
    (hcore_internal_not_B :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ∉ B.verts)
    (hadj_apex :
      forall i : Fin 4, i ≠ long -> G.Adj apex (D.model.branchVertex i))
    (htip_long : G.Adj tip (D.model.branchVertex long)) :
    NearHajosStrengtheningConclusion G := by
  classical
  have hapex_not_branch : forall i : Fin 4, apex ≠ D.model.branchVertex i := by
    intro i h
    exact hbranch_not_B i (by simpa [h] using hapex_mem)
  have hcore_internal_no_apex :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (D.model.edgePath hij) -> z ≠ apex := by
    intro i j hij z hz h
    exact hcore_internal_not_B hij hz (by simpa [h] using hapex_mem)
  obtain ⟨q, hq_path, hq_le⟩ :=
    Subgraph.Connected.exists_path_between hB_connected hapex_mem htip_mem
  have hlong_not_q_support :
      D.model.branchVertex long ∉ q.support := by
    intro hsupport
    exact hbranch_not_B long
      (hq_le.left (by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        exact hsupport))
  let longArm : G.Walk apex (D.model.branchVertex long) := q.concat htip_long
  let arm : forall i : Fin 4, G.Walk apex (D.model.branchVertex i) := fun i =>
    if h : i = long then
      longArm.copy rfl (by simp [h])
    else
      (hadj_apex i h).toWalk
  have hlongArm_path : longArm.IsPath := by
    exact hq_path.concat hlong_not_q_support htip_long
  have harm_path : forall i : Fin 4, (arm i).IsPath := by
    intro i
    by_cases h : i = long
    · simpa [arm, h] using
        (SimpleGraph.Walk.isPath_copy longArm rfl (by simp)).mpr
          hlongArm_path
    · simpa [arm, h] using
        SimpleGraph.Walk.IsPath.of_adj (hadj_apex i h)
  refine
    D.cone_paths_near_hajos_with_two_incident_unsplit_edges
      apex hapex_not_branch arm harm_path ?_ hcore_internal_no_apex ?_ ?_
  · intro i z hz w hzw
    by_cases h : i = long
    · have hz_long : z ∈ Walk.InternalVertices longArm := by
        rcases hz with ⟨hz_support, hz_ne_start, hz_ne_end⟩
        refine ⟨?_, hz_ne_start, ?_⟩
        · simpa [arm, h] using hz_support
        · intro hz_eq
          exact hz_ne_end (by simpa [h] using hz_eq)
      cases w with
      | none =>
          exact hz_long.2.1 hzw
      | some j =>
          have hz_q : z ∈ q.support :=
            Walk.mem_support_of_mem_internalVertices_concat q htip_long hz_long
          have hzB : z ∈ B.verts :=
            hq_le.left (by
              rw [SimpleGraph.Walk.mem_verts_toSubgraph]
              exact hz_q)
          exact hbranch_not_B j
            (by simpa [hzw] using hzB)
    · have hz_edge : z ∈ Walk.InternalVertices ((hadj_apex i h).toWalk) := by
        simpa [arm, h] using hz
      exact (Walk.not_mem_internalVertices_toWalk (hadj_apex i h) hz_edge).elim
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    by_cases hi : i = long
    · by_cases hj : j = long
      · exact False.elim (hij (hi.trans hj.symm))
      · have hzj_edge :
            z ∈ Walk.InternalVertices ((hadj_apex j hj).toWalk) := by
          simpa [arm, hj] using hzj
        exact (Walk.not_mem_internalVertices_toWalk (hadj_apex j hj) hzj_edge).elim
    · have hzi_edge :
          z ∈ Walk.InternalVertices ((hadj_apex i hi).toWalk) := by
        simpa [arm, hi] using hzi
      exact (Walk.not_mem_internalVertices_toWalk (hadj_apex i hi) hzi_edge).elim
  · intro i j k hjk
    rw [Set.disjoint_left]
    intro z hzi hz_core
    by_cases hi : i = long
    · have hz_long : z ∈ Walk.InternalVertices longArm := by
        rcases hzi with ⟨hz_support, hz_ne_start, hz_ne_end⟩
        refine ⟨?_, hz_ne_start, ?_⟩
        · simpa [arm, hi] using hz_support
        · intro hz_eq
          exact hz_ne_end (by simpa [hi] using hz_eq)
      have hz_q : z ∈ q.support :=
        Walk.mem_support_of_mem_internalVertices_concat q htip_long hz_long
      have hzB : z ∈ B.verts :=
        hq_le.left (by
          rw [SimpleGraph.Walk.mem_verts_toSubgraph]
          exact hz_q)
      exact hcore_internal_not_B hjk hz_core hzB
    · have hzi_edge :
          z ∈ Walk.InternalVertices ((hadj_apex i hi).toWalk) := by
        simpa [arm, hi] using hzi
      exact (Walk.not_mem_internalVertices_toWalk (hadj_apex i hi) hzi_edge).elim

theorem dominating_K5_model_tail_all_singleton_common_first_branch_apex_near_hajos
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    {apex : V}
    (hapex_mem : apex ∈ (T.branch (0 : Fin 5)).verts)
    (hadj : forall i : Fin 4, G.Adj apex (htail i).choose) :
    NearHajosStrengtheningConclusion G := by
  classical
  let D : K4UnsplitSubdivisionData G :=
    dominating_K5_model_tail_all_singleton_k4UnsplitSubdivisionData T htail
  have htail_mem : forall i : Fin 4, (htail i).choose ∈ (T.tailK4.branch i).verts := by
    intro i
    exact (htail i).choose_mem
  refine D.cone_apex_near_hajos_with_two_incident_unsplit_edges apex ?_ ?_ ?_
  · intro i
    change apex ≠ (htail i).choose
    intro h
    exact (Set.disjoint_left.mp (T.tailK4_branch_disjoint_first i)
      (htail_mem i)) (by simpa [h] using hapex_mem)
  · intro i j hij z hz
    have hunsplit : D.model.EdgeUnsplit hij := by
      simp [D, dominating_K5_model_tail_all_singleton_k4UnsplitSubdivisionData,
        dominating_K4_model_all_singleton_k4UnsplitSubdivisionData,
        K4UnsplitSubdivisionData.ofCliqueEmbedding,
        StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit]
    exact (Walk.not_mem_internalVertices_of_length_eq_one hunsplit hz).elim
  · intro i
    change G.Adj apex (htail i).choose
    exact hadj i


end Schematic.Math.GraphTheory
