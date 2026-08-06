import DominatingFourColour.Consequences.NearHajos.PathCarrier.CommonNonrootNoCross

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

set_option maxHeartbeats 0 in
theorem commonRootCross
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (C : LargePathCarrier D) [DecidableEq C.Btail.verts]
    (N : NormalizedCommonObstruction C) :
    (N.root : C.Btail.verts) = N.last ->
    Not N.NoCross ->
      NearHajosStrengtheningConclusion G := by
  classical
  let Ktail := C.Ktail
  let attachTail := C.attachTail
  let hattachTail := C.hattachTail
  let hKtail_branch_not_first := C.hKtail_branch_not_first
  let hKtail_internal_not_first :
      forall {i j : Fin 4} (hij : K4Graph.Adj i j) {z : V},
        z ∈ Walk.InternalVertices (Ktail.model.edgePath hij) ->
          z ∉ (D.model.branch (0 : Fin 5)).verts :=
    C.hKtail_internal_not_first
  let Btail := C.Btail
  let hBtail_le := C.hBtail_le
  let hBtail_terminal := C.hBtail_terminal
  let TBtail := C.TBtail
  let hTBtail_tree := C.hTBtail_tree
  let hTBtail_spanning := C.hTBtail_spanning
  let leftT₀ := C.leftT
  let rightT₀ := C.rightT
  let pB₀ := C.bridge
  let σ₀ := C.order
  let stemLeftB₀ := C.leftStem
  let stemRightB₀ := C.rightStem
  let leftB₀ := C.left
  let rightB₀ := C.right
  let stemLeftOneB₀ := C.leftArm
  let stemRightThreeB₀ := C.rightArm
  have hpB₀ := C.bridge_isPath
  have hpB₀_le_TB := C.bridge_le
  have hstemLeftOneB₀_path := C.leftArm_isPath
  have hstemRightThreeB₀_path := C.rightArm_isPath
  have hstemLeftOneB₀_le_TB := C.leftArm_le
  have hstemRightThreeB₀_le_TB := C.rightArm_le
  letI : Fintype TBtail.verts := TBtail.verts.toFinite.fintype
  letI : DecidableEq TBtail.verts := Classical.decEq _
  letI : DecidableRel TBtail.coe.Adj := Classical.decRel _
  intro hroot_eq hcross
  rcases N.existsLastCross hcross with ⟨hlastCross⟩
  have hsupports := N.rootedFourPathSupports
  rcases N with ⟨zRootT, hz_left, hz_internal, hz_right,
    pLeft, pRight, pOne, pThree, last,
    hlast_one, hlast_one_rev, hlast_three, hfirst,
    hpLeft, hpRight, hpOne, hpThree,
    hpLeft_le, hpRight_le, hpOne_le, hpThree_le,
    hright_not_pLeft, hleft_not_pRight,
    hright_not_pOne, hleft_not_pThree,
    hone_support_stem, hthree_support_stem, hlast⟩
  change (zRootT : Btail.verts) = last at hroot_eq
  rcases hlastCross with ⟨xCross, hxCross_one, hxCross_one_rev,
    hxCross_right, hlastRightOne, hxCross_ne_root⟩
  let τCross : Fin 4 ↪ Fin 4 := {
    toFun
      | 0 => (0 : Fin 4)
      | 1 => (3 : Fin 4)
      | 2 => (2 : Fin 4)
      | 3 => (1 : Fin 4)
    inj' := by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp at h ⊢
  }
  let σCross : Fin 4 ↪ Fin 4 := τCross.trans σ₀
  let attachCrossB : Fin 4 -> Btail.verts := fun a =>
    match a with
    | 0 => C.left
    | 1 => C.three
    | 2 => C.right
    | 3 => C.one
  have hattachCross_eq (a : Fin 4) :
      attachCrossB a = C.reindexedAttachment τCross a := by
    fin_cases a
    · change C.left = C.attachment (τCross 0)
      simp [τCross]
    · rfl
    · change C.right = C.attachment (τCross 2)
      simp [τCross]
    · rfl
  let pBridge :
      Btail.coe.Walk (zRootT : Btail.verts) xCross :=
    pOne.takeUntil xCross hxCross_one
  let stemCrossB :
      forall a : Fin 4,
        Btail.coe.Walk
          (k4BridgeEndpointSubgraph Btail
            (zRootT : Btail.verts) xCross a)
          (attachCrossB a) := fun a =>
    match a with
    | 0 => pLeft
    | 1 => pThree
    | 2 => pRight.dropUntil xCross hxCross_right
    | 3 => pOne.dropUntil xCross hxCross_one
  have hroot_ne_crossV :
      ((zRootT : Btail.verts) : V) ≠ (xCross : V) := by
    intro h
    exact hxCross_ne_root (Subtype.ext h).symm
  have hpBridge : pBridge.IsPath := by
    simpa [pBridge] using hpOne.takeUntil hxCross_one
  have hpBridge_le : pBridge.toSubgraph ≤ TBtail := by
    simpa [pBridge] using
      Walk.toSubgraph_takeUntil_le_of_le
        (H := TBtail) hpOne_le hxCross_one
  have hattachCross :
      forall a : Fin 4,
        G.Adj (attachCrossB a : V)
          (Ktail.model.branchVertex (σCross a)) := by
    intro a
    rw [hattachCross_eq a]
    simpa [Ktail, σCross] using C.reindexedAttachment_adj τCross a
  have hstemCrossB_path :
      forall a : Fin 4, (stemCrossB a).IsPath := by
    intro a
    fin_cases a
    · simpa [stemCrossB] using hpLeft
    · simpa [stemCrossB] using hpThree
    · simpa [stemCrossB] using
        hpRight.dropUntil hxCross_right
    · simpa [stemCrossB] using
        hpOne.dropUntil hxCross_one
  rcases hsupports with ⟨hleft_support_prefix,
      hright_support_prefix, hone_support_suffix,
      hthree_support_suffix, hleft_support_pB_prefix,
      hright_support_pB_suffix⟩
  have hbridge_support_pOne :
      forall {x : Btail.verts},
        x ∈ pBridge.support -> x ∈ pOne.support := by
    intro x hx
    exact SimpleGraph.Walk.support_takeUntil_subset
      pOne hxCross_one (by simpa [pBridge] using hx)
  have hbridge_support_pRight_prefix :
      forall {x : Btail.verts},
        x ∈ pBridge.support ->
          x ∈ (pRight.takeUntil
            xCross hxCross_right).support := by
    intro x hx
    exact
      (Subgraph.tree_mem_support_iff_of_isPath_coe
        hTBtail_tree hpBridge_le
        (Walk.toSubgraph_takeUntil_le_of_le
          (H := TBtail) hpRight_le hxCross_right)
        hpBridge (hpRight.takeUntil hxCross_right)
        (x := x)).mp hx
  have hmem_pOne_reverse_to_root :
      forall {x : Btail.verts},
        x ∈ pOne.support ->
          x ∈ (pOne.reverse.takeUntil
            last hlast_one_rev).support := by
    intro x hx
    have hx_rev : x ∈ pOne.reverse.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hx
    have hx_prefix_root :
        x ∈ (pOne.reverse.takeUntil
          (zRootT : Btail.verts)
          (by simpa [hroot_eq] using hlast_one_rev)).support :=
      Schematic.Math.GraphTheory.Walk.IsPath.mem_support_takeUntil_end
        hpOne.reverse hx_rev
    cases hroot_eq
    simpa using hx_prefix_root
  have hstemCrossB_avoids :
      forall a : Fin 4, forall {x : Btail.verts},
        x ∈ (stemCrossB a).support ->
          x ≠ k4BridgeEndpointSubgraph Btail
            (zRootT : Btail.verts) xCross a ->
            x ≠ (zRootT : Btail.verts) ∧ x ≠ xCross := by
    intro a x hx hx_ne_start
    fin_cases a
    · refine ⟨by simpa [k4BridgeEndpointSubgraph] using hx_ne_start, ?_⟩
      intro hx_eq_cross
      have hx_left_pB := hleft_support_pB_prefix
        (by simpa [stemCrossB] using hx)
      have hx_right_support :
          x ∈ pRight.support := by
        rw [hx_eq_cross]
        exact hxCross_right
      have hx_right_pB := hright_support_pB_suffix
        hx_right_support
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpB₀ hz_internal.1 hx_left_pB hx_right_pB
      exact hxCross_ne_root (hx_eq_cross.symm.trans hx_eq_root)
    · refine ⟨by simpa [k4BridgeEndpointSubgraph] using hx_ne_start, ?_⟩
      intro hx_eq_cross
      have hx_one_support :
          x ∈ pOne.support := by
        rw [hx_eq_cross]
        exact hxCross_one
      have hx_prefix :=
        hmem_pOne_reverse_to_root
          hx_one_support
      have hx_eq_last := hlast x
        (by simpa [stemCrossB] using hx) hx_prefix
      exact hxCross_ne_root
        (hx_eq_cross.symm.trans (hx_eq_last.trans hroot_eq.symm))
    · refine ⟨?_, by simpa [k4BridgeEndpointSubgraph] using hx_ne_start⟩
      intro hx_root
      exact
        (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          hpRight hxCross_right hxCross_ne_root)
          (by simpa [stemCrossB, hx_root] using hx)
    · refine ⟨?_, by simpa [k4BridgeEndpointSubgraph] using hx_ne_start⟩
      intro hx_root
      exact
        (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          hpOne hxCross_one hxCross_ne_root)
          (by simpa [stemCrossB, hx_root] using hx)
  have hbridgeStem_meet :
      forall a : Fin 4, forall {x : Btail.verts},
        x ∈ Walk.InternalVertices pBridge ->
          x ∈ (stemCrossB a).support ->
            x ≠ k4BridgeEndpointSubgraph Btail
              (zRootT : Btail.verts) xCross a ->
              False := by
    intro a x hx_bridge hx_stem hx_ne_start
    have hx_bridge_support : x ∈ pBridge.support := hx_bridge.1
    fin_cases a
    · have hx_left_prefix := hleft_support_prefix
        (by simpa [stemCrossB] using hx_stem)
      have hx_one_suffix := hone_support_suffix
        (hbridge_support_pOne hx_bridge_support)
      exact hx_bridge.2.1
        (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemLeftOneB₀_path hz_left hx_left_prefix hx_one_suffix)
    · have hx_prefix :=
        hmem_pOne_reverse_to_root
          (hbridge_support_pOne hx_bridge_support)
      have hx_eq_last := hlast x
        (by simpa [stemCrossB] using hx_stem) hx_prefix
      exact hx_bridge.2.1 (hx_eq_last.trans hroot_eq.symm)
    · have hx_right_prefix :=
        hbridge_support_pRight_prefix hx_bridge_support
      exact hx_bridge.2.2
        (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpRight hxCross_right hx_right_prefix
          (by simpa [stemCrossB] using hx_stem))
    · exact hx_bridge.2.2
        (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpOne hxCross_one
          (by simpa [pBridge] using hx_bridge_support)
          (by simpa [stemCrossB] using hx_stem))
  have hstemStem_meet :
      forall {a b : Fin 4}, a ≠ b ->
        forall {x : Btail.verts},
          x ∈ (stemCrossB a).support ->
            x ∈ (stemCrossB b).support ->
              x ≠ k4BridgeEndpointSubgraph Btail
                (zRootT : Btail.verts) xCross a ->
                x ≠ k4BridgeEndpointSubgraph Btail
                  (zRootT : Btail.verts) xCross b ->
                  False := by
    intro a b hab x hxa hxb hxa_ne hxb_ne
    fin_cases a <;> fin_cases b
    · exact hab rfl
    · have hx_left_prefix := hleft_support_prefix
        (by simpa [stemCrossB] using hxa)
      have hx_three :
          x ∈ stemRightThreeB₀.support :=
        hthree_support_stem
          (by simpa [stemCrossB] using hxb)
      have hx_eq_root := hfirst x hx_three hx_left_prefix
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_left_pB := hleft_support_pB_prefix
        (by simpa [stemCrossB] using hxa)
      have hx_right_pB := hright_support_pB_suffix
        (SimpleGraph.Walk.support_dropUntil_subset
          pRight hxCross_right (by simpa [stemCrossB] using hxb))
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpB₀ hz_internal.1 hx_left_pB hx_right_pB
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_left_prefix := hleft_support_prefix
        (by simpa [stemCrossB] using hxa)
      have hx_one_suffix := hone_support_suffix
        (SimpleGraph.Walk.support_dropUntil_subset
          pOne hxCross_one (by simpa [stemCrossB] using hxb))
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemLeftOneB₀_path hz_left hx_left_prefix hx_one_suffix
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_left_prefix := hleft_support_prefix
        (by simpa [stemCrossB] using hxb)
      have hx_three :
          x ∈ stemRightThreeB₀.support :=
        hthree_support_stem
          (by simpa [stemCrossB] using hxa)
      have hx_eq_root := hfirst x hx_three hx_left_prefix
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · exact hab rfl
    · have hx_right_prefix := hright_support_prefix
        (SimpleGraph.Walk.support_dropUntil_subset
          pRight hxCross_right (by simpa [stemCrossB] using hxb))
      have hx_three_suffix := hthree_support_suffix
        (by simpa [stemCrossB] using hxa)
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemRightThreeB₀_path hz_right
          hx_right_prefix hx_three_suffix
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_prefix :=
        hmem_pOne_reverse_to_root
          (SimpleGraph.Walk.support_dropUntil_subset
            pOne hxCross_one (by simpa [stemCrossB] using hxb))
      have hx_eq_last := hlast x
        (by simpa [stemCrossB] using hxa) hx_prefix
      exact hxa_ne
        (by simp [k4BridgeEndpointSubgraph, hx_eq_last,
          hroot_eq])
    · have hx_left_pB := hleft_support_pB_prefix
        (by simpa [stemCrossB] using hxb)
      have hx_right_pB := hright_support_pB_suffix
        (SimpleGraph.Walk.support_dropUntil_subset
          pRight hxCross_right (by simpa [stemCrossB] using hxa))
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpB₀ hz_internal.1 hx_left_pB hx_right_pB
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_right_prefix := hright_support_prefix
        (SimpleGraph.Walk.support_dropUntil_subset
          pRight hxCross_right (by simpa [stemCrossB] using hxa))
      have hx_three_suffix := hthree_support_suffix
        (by simpa [stemCrossB] using hxb)
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemRightThreeB₀_path hz_right
          hx_right_prefix hx_three_suffix
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · exact hab rfl
    · have hx_right :
          x ∈ pRight.support :=
        SimpleGraph.Walk.support_dropUntil_subset
          pRight hxCross_right (by simpa [stemCrossB] using hxa)
      have hx_one_suffix_rev :
          x ∈ (pOne.reverse.takeUntil
            xCross hxCross_one_rev).support :=
        Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
          hpOne hxCross_one hxCross_one_rev
          (by simpa [stemCrossB] using hxb)
      have hx_eq_cross := hlastRightOne x hx_right
        hx_one_suffix_rev
      exact hxa_ne
        (by simp [k4BridgeEndpointSubgraph, hx_eq_cross])
    · have hx_left_prefix := hleft_support_prefix
        (by simpa [stemCrossB] using hxb)
      have hx_one_suffix := hone_support_suffix
        (SimpleGraph.Walk.support_dropUntil_subset
          pOne hxCross_one (by simpa [stemCrossB] using hxa))
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemLeftOneB₀_path hz_left hx_left_prefix hx_one_suffix
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_prefix :=
        hmem_pOne_reverse_to_root
          (SimpleGraph.Walk.support_dropUntil_subset
            pOne hxCross_one (by simpa [stemCrossB] using hxa))
      have hx_eq_last := hlast x
        (by simpa [stemCrossB] using hxb) hx_prefix
      exact hxb_ne
        (by simp [k4BridgeEndpointSubgraph, hx_eq_last,
          hroot_eq])
    · have hx_right :
          x ∈ pRight.support :=
        SimpleGraph.Walk.support_dropUntil_subset
          pRight hxCross_right (by simpa [stemCrossB] using hxb)
      have hx_one_suffix_rev :
          x ∈ (pOne.reverse.takeUntil
            xCross hxCross_one_rev).support :=
        Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
          hpOne hxCross_one hxCross_one_rev
          (by simpa [stemCrossB] using hxa)
      have hx_eq_cross := hlastRightOne x hx_right
        hx_one_suffix_rev
      exact hxb_ne
        (by simp [k4BridgeEndpointSubgraph, hx_eq_cross])
    · exact hab rfl
  exact
    Ktail.carrier_bridge_attachment_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
      σCross Btail
      (by
        intro i hmem
        exact hKtail_branch_not_first i (hBtail_le.left hmem))
      (by
        intro i j hij z hz hmem
        exact hKtail_internal_not_first hij hz
          (hBtail_le.left hmem))
      hroot_ne_crossV pBridge hpBridge
      attachCrossB hattachCross
      stemCrossB hstemCrossB_path
      hstemCrossB_avoids hbridgeStem_meet hstemStem_meet

end PathCarrier

end Schematic.Math.GraphTheory
