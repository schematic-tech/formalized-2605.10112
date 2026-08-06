import DominatingFourColour.Consequences.NearHajos.PathCarrier.CommonRootNoCross

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

set_option maxHeartbeats 0 in
theorem commonNonrootNoCross
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (C : LargePathCarrier D) [DecidableEq C.Btail.verts]
    (N : NormalizedCommonObstruction C) :
    (N.root : C.Btail.verts) ≠ N.last ->
    N.NoCross ->
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
  intro hroot_ne hno_cross
  have hsupports := N.rootedFourPathSupports
  rcases N with ⟨zRootT, hz_left, hz_internal, hz_right,
    pLeft, pRight, pOne, pThree, last,
    hlast_one, hlast_one_rev, hlast_three, hfirst,
    hpLeft, hpRight, hpOne, hpThree,
    hpLeft_le, hpRight_le, hpOne_le, hpThree_le,
    hright_not_pLeft, hleft_not_pRight,
    hright_not_pOne, hleft_not_pThree,
    hone_support_stem, hthree_support_stem, hlast⟩
  change (zRootT : Btail.verts) ≠ last at hroot_ne
  change (forall {x : Btail.verts},
    x ∈ pRight.support -> x ∈ pOne.support ->
      x = (zRootT : Btail.verts)) at hno_cross
  let τBridge : Fin 4 ↪ Fin 4 := {
    toFun
      | 0 => (0 : Fin 4)
      | 1 => (2 : Fin 4)
      | 2 => (1 : Fin 4)
      | 3 => (3 : Fin 4)
    inj' := by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp at h ⊢
  }
  let σBridge : Fin 4 ↪ Fin 4 := τBridge.trans σ₀
  let attachBridgeB : Fin 4 -> Btail.verts := fun a =>
    match a with
    | 0 => C.left
    | 1 => C.right
    | 2 => C.one
    | 3 => C.three
  have hattachBridge_eq (a : Fin 4) :
      attachBridgeB a = C.reindexedAttachment τBridge a := by
    fin_cases a
    · change C.left = C.attachment (τBridge 0)
      simp [τBridge]
    · change C.right = C.attachment (τBridge 1)
      simp [τBridge]
    · rfl
    · rfl
  let pBridge :
      Btail.coe.Walk (zRootT : Btail.verts) last :=
    pOne.takeUntil last hlast_one
  let stemBridgeB :
      forall a : Fin 4,
        Btail.coe.Walk
          (k4BridgeEndpointSubgraph Btail
            (zRootT : Btail.verts) last a)
          (attachBridgeB a) := fun a =>
    match a with
    | 0 => pLeft
    | 1 => pRight
    | 2 => pOne.dropUntil last hlast_one
    | 3 => pThree.dropUntil last hlast_three
  have hroot_ne_lastV :
      ((zRootT : Btail.verts) : V) ≠ (last : V) := by
    intro h
    exact hroot_ne (Subtype.ext h)
  have hpBridge : pBridge.IsPath := by
    simpa [pBridge] using hpOne.takeUntil hlast_one
  have hpBridge_le : pBridge.toSubgraph ≤ TBtail := by
    simpa [pBridge] using
      Walk.toSubgraph_takeUntil_le_of_le
        (H := TBtail) hpOne_le hlast_one
  have hattachBridge :
      forall a : Fin 4,
        G.Adj (attachBridgeB a : V)
          (Ktail.model.branchVertex (σBridge a)) := by
    intro a
    rw [hattachBridge_eq a]
    simpa [Ktail, σBridge] using C.reindexedAttachment_adj τBridge a
  have hstemBridgeB_path :
      forall a : Fin 4, (stemBridgeB a).IsPath := by
    intro a
    fin_cases a
    · simpa [stemBridgeB] using hpLeft
    · simpa [stemBridgeB] using hpRight
    · simpa [stemBridgeB] using hpOne.dropUntil hlast_one
    · simpa [stemBridgeB] using hpThree.dropUntil hlast_three
  rcases hsupports with ⟨hleft_support_prefix,
      hright_support_prefix, hone_support_suffix,
      hthree_support_suffix, hleft_support_pB_prefix,
      hright_support_pB_suffix⟩
  have hbridge_support_pOne :
      forall {x : Btail.verts},
        x ∈ pBridge.support -> x ∈ pOne.support := by
    intro x hx
    exact SimpleGraph.Walk.support_takeUntil_subset
      pOne hlast_one (by simpa [pBridge] using hx)
  have hbridge_support_pThree_prefix :
      forall {x : Btail.verts},
        x ∈ pBridge.support ->
          x ∈ (pThree.takeUntil last hlast_three).support := by
    intro x hx
    exact
      (Subgraph.tree_mem_support_iff_of_isPath_coe
        hTBtail_tree hpBridge_le
        (Walk.toSubgraph_takeUntil_le_of_le
          (H := TBtail) hpThree_le hlast_three)
        hpBridge (hpThree.takeUntil hlast_three)
        (x := x)).mp hx
  have hstemBridgeB_avoids :
      forall a : Fin 4, forall {x : Btail.verts},
        x ∈ (stemBridgeB a).support ->
          x ≠ k4BridgeEndpointSubgraph Btail
            (zRootT : Btail.verts) last a ->
            x ≠ (zRootT : Btail.verts) ∧ x ≠ last := by
    intro a x hx hx_ne_start
    fin_cases a
    · refine ⟨by simpa [k4BridgeEndpointSubgraph] using hx_ne_start, ?_⟩
      intro hx_last
      have hx_prefix :
          x ∈ (stemLeftOneB₀.takeUntil
            (zRootT : Btail.verts) hz_left).support :=
        hleft_support_prefix (by simpa [stemBridgeB] using hx)
      have hx_one : x ∈ pOne.support := by
        simpa [hx_last] using hlast_one
      have hx_suffix :
          x ∈ (stemLeftOneB₀.dropUntil
            (zRootT : Btail.verts) hz_left).support :=
        hone_support_suffix hx_one
      have hx_eq_root :
          x = (zRootT : Btail.verts) :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemLeftOneB₀_path hz_left hx_prefix hx_suffix
      exact hroot_ne (hx_eq_root.symm.trans hx_last)
    · refine ⟨by simpa [k4BridgeEndpointSubgraph] using hx_ne_start, ?_⟩
      intro hx_last
      have hx_eq_root :=
        hno_cross (by simpa [stemBridgeB] using hx)
          (by simpa [hx_last] using hlast_one)
      exact hroot_ne (hx_eq_root.symm.trans hx_last)
    · refine ⟨?_, by simpa [k4BridgeEndpointSubgraph] using hx_ne_start⟩
      intro hx_root
      exact
        (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          hpOne hlast_one hroot_ne.symm)
          (by simpa [stemBridgeB, hx_root] using hx)
    · refine ⟨?_, by simpa [k4BridgeEndpointSubgraph] using hx_ne_start⟩
      intro hx_root
      exact
        (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          hpThree hlast_three hroot_ne.symm)
          (by simpa [stemBridgeB, hx_root] using hx)
  have hbridgeStem_meet :
      forall a : Fin 4, forall {x : Btail.verts},
        x ∈ Walk.InternalVertices pBridge ->
          x ∈ (stemBridgeB a).support ->
            x ≠ k4BridgeEndpointSubgraph Btail
              (zRootT : Btail.verts) last a ->
              False := by
    intro a x hx_bridge hx_stem hx_ne_start
    have hx_bridge_support : x ∈ pBridge.support := hx_bridge.1
    fin_cases a
    · have hx_left_prefix := hleft_support_prefix
        (by simpa [stemBridgeB] using hx_stem)
      have hx_one_suffix := hone_support_suffix
        (hbridge_support_pOne hx_bridge_support)
      exact hx_bridge.2.1
        (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemLeftOneB₀_path hz_left hx_left_prefix hx_one_suffix)
    · have hx_eq_root :=
        hno_cross (by simpa [stemBridgeB] using hx_stem)
          (hbridge_support_pOne hx_bridge_support)
      exact hx_bridge.2.1 hx_eq_root
    · exact hx_bridge.2.2
        (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpOne hlast_one
          (by simpa [pBridge] using hx_bridge_support)
          (by simpa [stemBridgeB] using hx_stem))
    · have hx_three_prefix :=
        hbridge_support_pThree_prefix hx_bridge_support
      have hx_three_suffix :
          x ∈ (pThree.dropUntil last hlast_three).support := by
        simpa [stemBridgeB] using hx_stem
      exact hx_bridge.2.2
        (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpThree hlast_three hx_three_prefix hx_three_suffix)
  have hstemStem_meet :
      forall {a b : Fin 4}, a ≠ b ->
        forall {x : Btail.verts},
          x ∈ (stemBridgeB a).support ->
            x ∈ (stemBridgeB b).support ->
              x ≠ k4BridgeEndpointSubgraph Btail
                (zRootT : Btail.verts) last a ->
                x ≠ k4BridgeEndpointSubgraph Btail
                  (zRootT : Btail.verts) last b ->
                  False := by
    intro a b hab x hxa hxb hxa_ne hxb_ne
    fin_cases a <;> fin_cases b
    · exact hab rfl
    · have hx_left_prefix := hleft_support_pB_prefix
        (by simpa [stemBridgeB] using hxa)
      have hx_right_suffix := hright_support_pB_suffix
        (by simpa [stemBridgeB] using hxb)
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpB₀ hz_internal.1 hx_left_prefix hx_right_suffix
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_left_prefix := hleft_support_prefix
        (by simpa [stemBridgeB] using hxa)
      have hx_one_suffix := hone_support_suffix
        (SimpleGraph.Walk.support_dropUntil_subset
          pOne hlast_one (by simpa [stemBridgeB] using hxb))
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemLeftOneB₀_path hz_left hx_left_prefix hx_one_suffix
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_left_prefix := hleft_support_prefix
        (by simpa [stemBridgeB] using hxa)
      have hx_three :
          x ∈ stemRightThreeB₀.support :=
        hthree_support_stem
          (SimpleGraph.Walk.support_dropUntil_subset
            pThree hlast_three (by simpa [stemBridgeB] using hxb))
      have hx_eq_root := hfirst x hx_three hx_left_prefix
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_left_prefix := hleft_support_pB_prefix
        (by simpa [stemBridgeB] using hxb)
      have hx_right_suffix := hright_support_pB_suffix
        (by simpa [stemBridgeB] using hxa)
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpB₀ hz_internal.1 hx_left_prefix hx_right_suffix
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · exact hab rfl
    · have hx_eq_root :=
        hno_cross (by simpa [stemBridgeB] using hxa)
          (SimpleGraph.Walk.support_dropUntil_subset
            pOne hlast_one (by simpa [stemBridgeB] using hxb))
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_right_prefix := hright_support_prefix
        (by simpa [stemBridgeB] using hxa)
      have hx_three_suffix := hthree_support_suffix
        (SimpleGraph.Walk.support_dropUntil_subset
          pThree hlast_three (by simpa [stemBridgeB] using hxb))
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemRightThreeB₀_path hz_right
          hx_right_prefix hx_three_suffix
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_left_prefix := hleft_support_prefix
        (by simpa [stemBridgeB] using hxb)
      have hx_one_suffix := hone_support_suffix
        (SimpleGraph.Walk.support_dropUntil_subset
          pOne hlast_one (by simpa [stemBridgeB] using hxa))
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemLeftOneB₀_path hz_left hx_left_prefix hx_one_suffix
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_eq_root :=
        hno_cross (by simpa [stemBridgeB] using hxb)
          (SimpleGraph.Walk.support_dropUntil_subset
            pOne hlast_one (by simpa [stemBridgeB] using hxa))
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · exact hab rfl
    · have hx_one_rev :
          x ∈ pOne.reverse.support := by
        simpa [SimpleGraph.Walk.support_reverse] using
          SimpleGraph.Walk.support_dropUntil_subset
            pOne hlast_one (by simpa [stemBridgeB] using hxa)
      have hx_one_suffix_rev :
          x ∈ (pOne.reverse.takeUntil last
            hlast_one_rev).support :=
        Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
          hpOne hlast_one hlast_one_rev
          (by simpa [stemBridgeB] using hxa)
      have hx_three :
          x ∈ pThree.support :=
        SimpleGraph.Walk.support_dropUntil_subset
          pThree hlast_three (by simpa [stemBridgeB] using hxb)
      have hx_eq_last := hlast x hx_three hx_one_suffix_rev
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_last])
    · have hx_left_prefix := hleft_support_prefix
        (by simpa [stemBridgeB] using hxb)
      have hx_three :
          x ∈ stemRightThreeB₀.support :=
        hthree_support_stem
          (SimpleGraph.Walk.support_dropUntil_subset
            pThree hlast_three (by simpa [stemBridgeB] using hxa))
      have hx_eq_root := hfirst x hx_three hx_left_prefix
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_right_prefix := hright_support_prefix
        (by simpa [stemBridgeB] using hxb)
      have hx_three_suffix := hthree_support_suffix
        (SimpleGraph.Walk.support_dropUntil_subset
          pThree hlast_three (by simpa [stemBridgeB] using hxa))
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemRightThreeB₀_path hz_right
          hx_right_prefix hx_three_suffix
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_root])
    · have hx_one_suffix_rev :
          x ∈ (pOne.reverse.takeUntil last
            hlast_one_rev).support :=
        Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
          hpOne hlast_one hlast_one_rev
          (by simpa [stemBridgeB] using hxb)
      have hx_three :
          x ∈ pThree.support :=
        SimpleGraph.Walk.support_dropUntil_subset
          pThree hlast_three (by simpa [stemBridgeB] using hxa)
      have hx_eq_last := hlast x hx_three hx_one_suffix_rev
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_last])
    · exact hab rfl
  exact
    Ktail.carrier_bridge_attachment_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
      σBridge Btail
      (by
        intro i hmem
        exact hKtail_branch_not_first i (hBtail_le.left hmem))
      (by
        intro i j hij z hz hmem
        exact hKtail_internal_not_first hij hz
          (hBtail_le.left hmem))
      hroot_ne_lastV pBridge hpBridge
      attachBridgeB hattachBridge
      stemBridgeB hstemBridgeB_path
      hstemBridgeB_avoids hbridgeStem_meet hstemStem_meet

end PathCarrier

end Schematic.Math.GraphTheory
