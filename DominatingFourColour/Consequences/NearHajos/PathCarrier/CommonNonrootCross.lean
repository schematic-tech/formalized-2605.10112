import DominatingFourColour.Consequences.NearHajos.PathCarrier.CommonRootCross

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

set_option maxHeartbeats 0 in
theorem commonNonrootCross
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (C : LargePathCarrier D) [DecidableEq C.Btail.verts]
    (N : NormalizedCommonObstruction C) :
    (N.root : C.Btail.verts) ≠ N.last ->
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
  intro hroot_ne hcross
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
  change (zRootT : Btail.verts) ≠ last at hroot_ne
  rcases hlastCross with ⟨xCross, hxCross_one, hxCross_one_rev,
    hxCross_right, hlastRightOne, hxCross_ne_root⟩
  rcases hsupports with ⟨hleft_support_prefix,
      hright_support_prefix, hone_support_suffix,
      hthree_support_suffix, hleft_support_pB_prefix,
      hright_support_pB_suffix⟩
  have hnot_xCross_before_last :
      xCross ∉ (pOne.takeUntil last hlast_one).support := by
    intro hx_before_last
    have hpOne_last_le :
        (pOne.takeUntil last hlast_one).toSubgraph ≤
          TBtail :=
      Walk.toSubgraph_takeUntil_le_of_le
        (H := TBtail) hpOne_le hlast_one
    have hpThree_last_le :
        (pThree.takeUntil last hlast_three).toSubgraph ≤
          TBtail :=
      Walk.toSubgraph_takeUntil_le_of_le
        (H := TBtail) hpThree_le hlast_three
    have hx_three_prefix :
        xCross ∈
          (pThree.takeUntil last hlast_three).support :=
      (Subgraph.tree_mem_support_iff_of_isPath_coe
        hTBtail_tree hpOne_last_le hpThree_last_le
        (hpOne.takeUntil hlast_one)
        (hpThree.takeUntil hlast_three)
        (x := xCross)).mp hx_before_last
    have hx_three : xCross ∈ pThree.support :=
      SimpleGraph.Walk.support_takeUntil_subset
        pThree hlast_three hx_three_prefix
    have hx_right_prefix :=
      hright_support_prefix hxCross_right
    have hx_three_suffix :=
      hthree_support_suffix hx_three
    have hx_eq_root :=
      Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        hstemRightThreeB₀_path hz_right
        hx_right_prefix hx_three_suffix
    exact hxCross_ne_root hx_eq_root
  have hlast_before_cross :
      last ∈ (pOne.takeUntil xCross hxCross_one).support := by
    rcases Walk.mem_support_takeUntil_or_mem_support_takeUntil
        hxCross_one hlast_one with hx_before | hlast_before
    · exact False.elim (hnot_xCross_before_last hx_before)
    · exact hlast_before
  have hxCross_ne_last : xCross ≠ last := by
    intro hx_eq_last
    exact hnot_xCross_before_last
      (hx_eq_last ▸ (pOne.takeUntil last hlast_one).end_mem_support)
  let τBridge : Fin 4 ↪ Fin 4 := {
    toFun
      | 0 => (0 : Fin 4)
      | 1 => (3 : Fin 4)
      | 2 => (2 : Fin 4)
      | 3 => (1 : Fin 4)
    inj' := by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp at h ⊢
  }
  let σBridge : Fin 4 ↪ Fin 4 := τBridge.trans σ₀
  let attachBridgeB : Fin 4 -> Btail.verts := fun a =>
    match a with
    | 0 => C.left
    | 1 => C.three
    | 2 => C.right
    | 3 => C.one
  have hattachBridge_eq (a : Fin 4) :
      attachBridgeB a = C.reindexedAttachment τBridge a := by
    fin_cases a
    · change C.left = C.attachment (τBridge 0)
      simp [τBridge]
    · rfl
    · change C.right = C.attachment (τBridge 2)
      simp [τBridge]
    · rfl
  let pBridge : Btail.coe.Walk last xCross :=
    (pOne.takeUntil xCross hxCross_one).dropUntil
      last hlast_before_cross
  let pLeftLast : Btail.coe.Walk last leftB₀ :=
    (pOne.takeUntil last hlast_one).reverse.append pLeft
  let stemBridgeB :
      forall a : Fin 4,
        Btail.coe.Walk
          (k4BridgeEndpointSubgraph Btail last xCross a)
          (attachBridgeB a) := fun a =>
    match a with
    | 0 => pLeftLast
    | 1 => pThree.dropUntil last hlast_three
    | 2 => pRight.dropUntil xCross hxCross_right
    | 3 => pOne.dropUntil xCross hxCross_one
  have hlast_ne_crossV :
      (last : V) ≠ (xCross : V) := by
    intro h
    exact hxCross_ne_last (Subtype.ext h).symm
  have hpBridge : pBridge.IsPath := by
    simpa [pBridge] using
      (hpOne.takeUntil hxCross_one).dropUntil
        hlast_before_cross
  have hpOne_take_cross_le :
      (pOne.takeUntil xCross hxCross_one).toSubgraph ≤
        TBtail :=
    Walk.toSubgraph_takeUntil_le_of_le
      (H := TBtail) hpOne_le hxCross_one
  have hpBridge_le : pBridge.toSubgraph ≤ TBtail := by
    simpa [pBridge] using
      Walk.toSubgraph_dropUntil_le_of_le
        (H := TBtail) hpOne_take_cross_le
        hlast_before_cross
  have hpOne_take_last_le :
      (pOne.takeUntil last hlast_one).toSubgraph ≤
        TBtail :=
    Walk.toSubgraph_takeUntil_le_of_le
      (H := TBtail) hpOne_le hlast_one
  have hpLeftLast : pLeftLast.IsPath := by
    refine
      Walk.IsPath.append_of_punctured_supports_disjoint
        (hpOne.takeUntil hlast_one).reverse hpLeft ?_
    rw [Set.disjoint_left]
    rintro x ⟨hx_rev, hx_ne_root⟩ ⟨hx_left, _hx_left_ne_root⟩
    have hx_prefix :
        x ∈ (pOne.takeUntil last hlast_one).support := by
      simpa [SimpleGraph.Walk.support_reverse] using hx_rev
    have hx_one : x ∈ pOne.support :=
      SimpleGraph.Walk.support_takeUntil_subset
        pOne hlast_one hx_prefix
    have hx_left_prefix := hleft_support_prefix hx_left
    have hx_one_suffix := hone_support_suffix hx_one
    have hx_eq_root :=
      Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        hstemLeftOneB₀_path hz_left
        hx_left_prefix hx_one_suffix
    exact hx_ne_root hx_eq_root
  have hpLeftLast_le : pLeftLast.toSubgraph ≤ TBtail := by
    change
      (((pOne.takeUntil last hlast_one).reverse.append
        pLeft).toSubgraph ≤ TBtail)
    rw [SimpleGraph.Walk.toSubgraph_append,
      SimpleGraph.Walk.toSubgraph_reverse]
    exact sup_le hpOne_take_last_le hpLeft_le
  have hpLeftLast_support :
      forall {x : Btail.verts},
        x ∈ pLeftLast.support ->
          x ∈ (pOne.takeUntil last hlast_one).support ∨
            x ∈ pLeft.support := by
    intro x hx
    have hx' : x ∈
        ((pOne.takeUntil last hlast_one).reverse.append
          pLeft).support := by
      simpa [pLeftLast] using hx
    rw [SimpleGraph.Walk.mem_support_append_iff] at hx'
    rcases hx' with hx_rev | hx_left
    · left
      simpa [SimpleGraph.Walk.support_reverse] using hx_rev
    · exact Or.inr hx_left
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
    · simpa [stemBridgeB] using hpLeftLast
    · simpa [stemBridgeB] using
        hpThree.dropUntil hlast_three
    · simpa [stemBridgeB] using
        hpRight.dropUntil hxCross_right
    · simpa [stemBridgeB] using
        hpOne.dropUntil hxCross_one
  have hbridge_support_pOne_take_cross :
      forall {x : Btail.verts},
        x ∈ pBridge.support ->
          x ∈ (pOne.takeUntil xCross hxCross_one).support := by
    intro x hx
    exact SimpleGraph.Walk.support_dropUntil_subset
      (pOne.takeUntil xCross hxCross_one)
      hlast_before_cross (by simpa [pBridge] using hx)
  have hbridge_support_pOne :
      forall {x : Btail.verts},
        x ∈ pBridge.support -> x ∈ pOne.support := by
    intro x hx
    exact SimpleGraph.Walk.support_takeUntil_subset
      pOne hxCross_one
      (hbridge_support_pOne_take_cross hx)
  have hbridge_support_pOne_drop_last :
      forall {x : Btail.verts},
        x ∈ pBridge.support ->
          x ∈ (pOne.dropUntil last hlast_one).support := by
    intro x hx
    exact
      Walk.IsPath.support_dropUntil_takeUntil_subset_dropUntil
        hpOne hxCross_one hlast_before_cross
        (by simpa [pBridge] using hx)
  have hroot_not_pBridge :
      (zRootT : Btail.verts) ∉ pBridge.support := by
    have hnot :
        (zRootT : Btail.verts) ∉
          ((pOne.takeUntil xCross hxCross_one).dropUntil
            last hlast_before_cross).support :=
      Walk.IsPath.start_not_mem_dropUntil_support_of_ne
        (hpOne.takeUntil hxCross_one)
        hlast_before_cross hroot_ne.symm
    simpa [pBridge] using hnot
  have hpRight_take_cross_le :
      (pRight.takeUntil xCross hxCross_right).toSubgraph ≤
        TBtail :=
    Walk.toSubgraph_takeUntil_le_of_le
      (H := TBtail) hpRight_le hxCross_right
  have hbridge_support_pRight_prefix :
      forall {x : Btail.verts},
        x ∈ pBridge.support ->
          x ∈ (pRight.takeUntil
            xCross hxCross_right).support := by
    intro x hx
    have hx_prefix := hbridge_support_pOne_take_cross hx
    exact
      Subgraph.tree_mem_takeUntil_of_mem_takeUntil_of_isPath
        (G := Btail.coe) (T := TBtail)
        hTBtail_tree hpOne_le hpRight_le
        hpOne hpRight hxCross_one hxCross_right
        hx_prefix
  have hlast_support_pRight_prefix :
      last ∈ (pRight.takeUntil
        xCross hxCross_right).support :=
    Subgraph.tree_mem_takeUntil_of_mem_takeUntil_of_isPath
      (G := Btail.coe) (T := TBtail)
      hTBtail_tree hpOne_le hpRight_le
      hpOne hpRight hxCross_one hxCross_right
      hlast_before_cross
  have hroot_not_pRight_drop :
      (zRootT : Btail.verts) ∉
        (pRight.dropUntil xCross hxCross_right).support :=
    Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      hpRight hxCross_right hxCross_ne_root
  have hroot_not_pOne_drop :
      (zRootT : Btail.verts) ∉
        (pOne.dropUntil xCross hxCross_one).support :=
    Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      hpOne hxCross_one hxCross_ne_root
  have hroot_not_pThree_drop :
      (zRootT : Btail.verts) ∉
        (pThree.dropUntil last hlast_three).support :=
    Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      hpThree hlast_three hroot_ne.symm
  have hlast_not_pRight_drop :
      last ∉
        (pRight.dropUntil xCross hxCross_right).support :=
    Walk.IsPath.not_mem_dropUntil_of_mem_takeUntil_ne
      hpRight hxCross_right hlast_support_pRight_prefix
      hxCross_ne_last.symm
  have hlast_not_pOne_drop :
      last ∉
        (pOne.dropUntil xCross hxCross_one).support :=
    Walk.IsPath.not_mem_dropUntil_of_mem_takeUntil_ne
      hpOne hxCross_one hlast_before_cross
      hxCross_ne_last.symm
  have hprefix_last_subset_take_cross :
      forall {x : Btail.verts},
        x ∈ (pOne.takeUntil last hlast_one).support ->
          x ∈ (pOne.takeUntil xCross hxCross_one).support := by
    intro x hx
    have hx_take_take :
        x ∈
          ((pOne.takeUntil xCross hxCross_one).takeUntil
            last hlast_before_cross).support := by
      simpa [SimpleGraph.Walk.takeUntil_takeUntil] using hx
    exact SimpleGraph.Walk.support_takeUntil_subset
      (pOne.takeUntil xCross hxCross_one)
      hlast_before_cross hx_take_take
  have hstemBridgeB_avoids :
      forall a : Fin 4, forall {x : Btail.verts},
        x ∈ (stemBridgeB a).support ->
          x ≠ k4BridgeEndpointSubgraph Btail last xCross a ->
            x ≠ last ∧ x ≠ xCross := by
    intro a x hx hx_ne_start
    fin_cases a
    · refine ⟨by simpa [k4BridgeEndpointSubgraph] using hx_ne_start, ?_⟩
      intro hx_eq_cross
      rcases hpLeftLast_support (by simpa [stemBridgeB] using hx) with
        hx_prefix | hx_left
      · exact hnot_xCross_before_last
          (by simpa [hx_eq_cross] using hx_prefix)
      · have hx_left_pB := hleft_support_pB_prefix hx_left
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
      have hx_three : xCross ∈ pThree.support := by
        exact SimpleGraph.Walk.support_dropUntil_subset
          pThree hlast_three
          (by simpa [stemBridgeB, hx_eq_cross] using hx)
      have hx_right_prefix := hright_support_prefix hxCross_right
      have hx_three_suffix := hthree_support_suffix hx_three
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemRightThreeB₀_path hz_right
          hx_right_prefix hx_three_suffix
      exact hxCross_ne_root hx_eq_root
    · refine ⟨?_, by simpa [k4BridgeEndpointSubgraph] using hx_ne_start⟩
      intro hx_eq_last
      exact hlast_not_pRight_drop
        (by simpa [stemBridgeB, hx_eq_last] using hx)
    · refine ⟨?_, by simpa [k4BridgeEndpointSubgraph] using hx_ne_start⟩
      intro hx_eq_last
      exact hlast_not_pOne_drop
        (by simpa [stemBridgeB, hx_eq_last] using hx)
  have hbridgeStem_meet :
      forall a : Fin 4, forall {x : Btail.verts},
        x ∈ Walk.InternalVertices pBridge ->
          x ∈ (stemBridgeB a).support ->
            x ≠ k4BridgeEndpointSubgraph Btail last xCross a ->
              False := by
    intro a x hx_bridge hx_stem hx_ne_start
    have hx_bridge_support : x ∈ pBridge.support := hx_bridge.1
    fin_cases a
    · rcases hpLeftLast_support (by simpa [stemBridgeB] using hx_stem) with
        hx_prefix | hx_left
      · have hx_drop := hbridge_support_pOne_drop_last hx_bridge_support
        exact hx_bridge.2.1
          (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            hpOne hlast_one hx_prefix hx_drop)
      · have hx_left_prefix := hleft_support_prefix hx_left
        have hx_one_suffix := hone_support_suffix
          (hbridge_support_pOne hx_bridge_support)
        have hx_eq_root :=
          Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            hstemLeftOneB₀_path hz_left
            hx_left_prefix hx_one_suffix
        exact hroot_not_pBridge (by simpa [hx_eq_root] using hx_bridge_support)
    · have hx_three :
          x ∈ pThree.support :=
        SimpleGraph.Walk.support_dropUntil_subset
          pThree hlast_three
          (by simpa [stemBridgeB] using hx_stem)
      have hx_one_suffix_rev :
          x ∈ (pOne.reverse.takeUntil
            last hlast_one_rev).support :=
        Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
          hpOne hlast_one hlast_one_rev
          (hbridge_support_pOne_drop_last hx_bridge_support)
      have hx_eq_last := hlast x hx_three hx_one_suffix_rev
      exact hx_bridge.2.1 hx_eq_last
    · have hx_right_prefix :=
        hbridge_support_pRight_prefix hx_bridge_support
      exact hx_bridge.2.2
        (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpRight hxCross_right hx_right_prefix
          (by simpa [stemBridgeB] using hx_stem))
    · exact hx_bridge.2.2
        (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpOne hxCross_one
          (hbridge_support_pOne_take_cross hx_bridge_support)
          (by simpa [stemBridgeB] using hx_stem))
  have hstemStem_meet :
      forall {a b : Fin 4}, a ≠ b ->
        forall {x : Btail.verts},
          x ∈ (stemBridgeB a).support ->
            x ∈ (stemBridgeB b).support ->
              x ≠ k4BridgeEndpointSubgraph Btail last xCross a ->
                x ≠ k4BridgeEndpointSubgraph Btail last xCross b ->
                  False := by
    intro a b hab x hxa hxb hxa_ne hxb_ne
    fin_cases a <;> fin_cases b
    · exact hab rfl
    · rcases hpLeftLast_support (by simpa [stemBridgeB] using hxa) with
        hx_prefix | hx_left
      · have hx_three_prefix :
            x ∈ (pThree.takeUntil last hlast_three).support :=
          Subgraph.tree_mem_takeUntil_of_mem_takeUntil_of_isPath
            (G := Btail.coe) (T := TBtail)
            hTBtail_tree hpOne_le hpThree_le
            hpOne hpThree hlast_one hlast_three hx_prefix
        have hx_three_drop :
            x ∈ (pThree.dropUntil last hlast_three).support := by
          simpa [stemBridgeB] using hxb
        have hx_eq_last :=
          Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            hpThree hlast_three hx_three_prefix hx_three_drop
        exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_last])
      · have hx_left_prefix := hleft_support_prefix hx_left
        have hx_three :
            x ∈ stemRightThreeB₀.support :=
          hthree_support_stem
            (SimpleGraph.Walk.support_dropUntil_subset
              pThree hlast_three
              (by simpa [stemBridgeB] using hxb))
        have hx_eq_root := hfirst x hx_three hx_left_prefix
        exact hroot_not_pThree_drop
          (by simpa [stemBridgeB, hx_eq_root] using hxb)
    · rcases hpLeftLast_support (by simpa [stemBridgeB] using hxa) with
        hx_prefix | hx_left
      · have hx_right_prefix :
            x ∈ (pRight.takeUntil xCross hxCross_right).support :=
          Subgraph.tree_mem_takeUntil_of_mem_takeUntil_of_isPath
            (G := Btail.coe) (T := TBtail)
            hTBtail_tree hpOne_le hpRight_le
            hpOne hpRight hxCross_one hxCross_right
            (hprefix_last_subset_take_cross hx_prefix)
        exact False.elim (hnot_xCross_before_last (by
          have hx_eq_cross :=
            Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
              hpRight hxCross_right hx_right_prefix
              (by simpa [stemBridgeB] using hxb)
          simpa [hx_eq_cross] using hx_prefix))
      · have hx_left_pB := hleft_support_pB_prefix hx_left
        have hx_right_pB := hright_support_pB_suffix
          (SimpleGraph.Walk.support_dropUntil_subset
            pRight hxCross_right
            (by simpa [stemBridgeB] using hxb))
        have hx_eq_root :=
          Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            hpB₀ hz_internal.1 hx_left_pB hx_right_pB
        exact hroot_not_pRight_drop
          (by simpa [stemBridgeB, hx_eq_root] using hxb)
    · rcases hpLeftLast_support (by simpa [stemBridgeB] using hxa) with
        hx_prefix | hx_left
      · have hx_take_cross :
            x ∈ (pOne.takeUntil xCross hxCross_one).support :=
          hprefix_last_subset_take_cross hx_prefix
        have hx_eq_cross :=
          Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            hpOne hxCross_one hx_take_cross
            (by simpa [stemBridgeB] using hxb)
        exact hnot_xCross_before_last
          (by simpa [hx_eq_cross] using hx_prefix)
      · have hx_left_prefix := hleft_support_prefix hx_left
        have hx_one_suffix := hone_support_suffix
          (SimpleGraph.Walk.support_dropUntil_subset
            pOne hxCross_one
            (by simpa [stemBridgeB] using hxb))
        have hx_eq_root :=
          Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            hstemLeftOneB₀_path hz_left
            hx_left_prefix hx_one_suffix
        exact hroot_not_pOne_drop
          (by simpa [stemBridgeB, hx_eq_root] using hxb)
    · rcases hpLeftLast_support (by simpa [stemBridgeB] using hxb) with
        hx_prefix | hx_left
      · have hx_three_prefix :
            x ∈ (pThree.takeUntil last hlast_three).support :=
          Subgraph.tree_mem_takeUntil_of_mem_takeUntil_of_isPath
            (G := Btail.coe) (T := TBtail)
            hTBtail_tree hpOne_le hpThree_le
            hpOne hpThree hlast_one hlast_three hx_prefix
        have hx_three_drop :
            x ∈ (pThree.dropUntil last hlast_three).support := by
          simpa [stemBridgeB] using hxa
        have hx_eq_last :=
          Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            hpThree hlast_three hx_three_prefix hx_three_drop
        exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_last])
      · have hx_left_prefix := hleft_support_prefix hx_left
        have hx_three :
            x ∈ stemRightThreeB₀.support :=
          hthree_support_stem
            (SimpleGraph.Walk.support_dropUntil_subset
              pThree hlast_three
              (by simpa [stemBridgeB] using hxa))
        have hx_eq_root := hfirst x hx_three hx_left_prefix
        exact hroot_not_pThree_drop
          (by simpa [stemBridgeB, hx_eq_root] using hxa)
    · exact hab rfl
    · have hx_right_prefix := hright_support_prefix
        (SimpleGraph.Walk.support_dropUntil_subset
          pRight hxCross_right (by simpa [stemBridgeB] using hxb))
      have hx_three_suffix := hthree_support_suffix
        (SimpleGraph.Walk.support_dropUntil_subset
          pThree hlast_three (by simpa [stemBridgeB] using hxa))
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemRightThreeB₀_path hz_right
          hx_right_prefix hx_three_suffix
      exact hroot_not_pThree_drop
        (by simpa [stemBridgeB, hx_eq_root] using hxa)
    · have hx_three :
          x ∈ pThree.support :=
        SimpleGraph.Walk.support_dropUntil_subset
          pThree hlast_three (by simpa [stemBridgeB] using hxa)
      have hx_one_drop_last :
          x ∈ (pOne.dropUntil last hlast_one).support := by
        have hx_one :
            x ∈ pOne.support :=
          SimpleGraph.Walk.support_dropUntil_subset
            pOne hxCross_one
            (by simpa [stemBridgeB] using hxb)
        rcases Walk.mem_support_takeUntil_or_dropUntil_of_mem_support
            pOne hlast_one hx_one with hx_take | hx_drop
        · have hx_take_cross :=
            hprefix_last_subset_take_cross hx_take
          have hx_eq_cross :=
            Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
              hpOne hxCross_one hx_take_cross
              (by simpa [stemBridgeB] using hxb)
          exact False.elim
            (hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_cross]))
        · exact hx_drop
      have hx_one_suffix_rev :
          x ∈ (pOne.reverse.takeUntil
            last hlast_one_rev).support :=
        Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
          hpOne hlast_one hlast_one_rev hx_one_drop_last
      have hx_eq_last := hlast x hx_three hx_one_suffix_rev
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_last])
    · rcases hpLeftLast_support (by simpa [stemBridgeB] using hxb) with
        hx_prefix | hx_left
      · have hx_right_prefix :
            x ∈ (pRight.takeUntil xCross hxCross_right).support :=
          Subgraph.tree_mem_takeUntil_of_mem_takeUntil_of_isPath
            (G := Btail.coe) (T := TBtail)
            hTBtail_tree hpOne_le hpRight_le
            hpOne hpRight hxCross_one hxCross_right
            (hprefix_last_subset_take_cross hx_prefix)
        have hx_eq_cross :=
          Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            hpRight hxCross_right hx_right_prefix
            (by simpa [stemBridgeB] using hxa)
        exact hnot_xCross_before_last (by
          simpa [hx_eq_cross] using hx_prefix)
      · have hx_left_pB := hleft_support_pB_prefix hx_left
        have hx_right_pB := hright_support_pB_suffix
          (SimpleGraph.Walk.support_dropUntil_subset
            pRight hxCross_right
            (by simpa [stemBridgeB] using hxa))
        have hx_eq_root :=
          Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            hpB₀ hz_internal.1 hx_left_pB hx_right_pB
        exact hroot_not_pRight_drop
          (by simpa [stemBridgeB, hx_eq_root] using hxa)
    · have hx_right_prefix := hright_support_prefix
        (SimpleGraph.Walk.support_dropUntil_subset
          pRight hxCross_right (by simpa [stemBridgeB] using hxa))
      have hx_three_suffix := hthree_support_suffix
        (SimpleGraph.Walk.support_dropUntil_subset
          pThree hlast_three (by simpa [stemBridgeB] using hxb))
      have hx_eq_root :=
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemRightThreeB₀_path hz_right
          hx_right_prefix hx_three_suffix
      exact hroot_not_pThree_drop
        (by simpa [stemBridgeB, hx_eq_root] using hxb)
    · exact hab rfl
    · have hx_right :
          x ∈ pRight.support :=
        SimpleGraph.Walk.support_dropUntil_subset
          pRight hxCross_right (by simpa [stemBridgeB] using hxa)
      have hx_one_suffix_rev :
          x ∈ (pOne.reverse.takeUntil
            xCross hxCross_one_rev).support :=
        Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
          hpOne hxCross_one hxCross_one_rev
          (by simpa [stemBridgeB] using hxb)
      have hx_eq_cross := hlastRightOne x hx_right
        hx_one_suffix_rev
      exact hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_cross])
    · rcases hpLeftLast_support (by simpa [stemBridgeB] using hxb) with
        hx_prefix | hx_left
      · have hx_take_cross :
            x ∈ (pOne.takeUntil xCross hxCross_one).support :=
          hprefix_last_subset_take_cross hx_prefix
        have hx_eq_cross :=
          Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            hpOne hxCross_one hx_take_cross
            (by simpa [stemBridgeB] using hxa)
        exact hnot_xCross_before_last
          (by simpa [hx_eq_cross] using hx_prefix)
      · have hx_left_prefix := hleft_support_prefix hx_left
        have hx_one_suffix := hone_support_suffix
          (SimpleGraph.Walk.support_dropUntil_subset
            pOne hxCross_one
            (by simpa [stemBridgeB] using hxa))
        have hx_eq_root :=
          Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            hstemLeftOneB₀_path hz_left
            hx_left_prefix hx_one_suffix
        exact hroot_not_pOne_drop
          (by simpa [stemBridgeB, hx_eq_root] using hxa)
    · have hx_three :
          x ∈ pThree.support :=
        SimpleGraph.Walk.support_dropUntil_subset
          pThree hlast_three (by simpa [stemBridgeB] using hxb)
      have hx_one_drop_last :
          x ∈ (pOne.dropUntil last hlast_one).support := by
        have hx_one :
            x ∈ pOne.support :=
          SimpleGraph.Walk.support_dropUntil_subset
            pOne hxCross_one
            (by simpa [stemBridgeB] using hxa)
        rcases Walk.mem_support_takeUntil_or_dropUntil_of_mem_support
            pOne hlast_one hx_one with hx_take | hx_drop
        · have hx_take_cross :=
            hprefix_last_subset_take_cross hx_take
          have hx_eq_cross :=
            Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
              hpOne hxCross_one hx_take_cross
              (by simpa [stemBridgeB] using hxa)
          exact False.elim
            (hxa_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_cross]))
        · exact hx_drop
      have hx_one_suffix_rev :
          x ∈ (pOne.reverse.takeUntil
            last hlast_one_rev).support :=
        Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
          hpOne hlast_one hlast_one_rev hx_one_drop_last
      have hx_eq_last := hlast x hx_three hx_one_suffix_rev
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_last])
    · have hx_right :
          x ∈ pRight.support :=
        SimpleGraph.Walk.support_dropUntil_subset
          pRight hxCross_right (by simpa [stemBridgeB] using hxb)
      have hx_one_suffix_rev :
          x ∈ (pOne.reverse.takeUntil
            xCross hxCross_one_rev).support :=
        Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
          hpOne hxCross_one hxCross_one_rev
          (by simpa [stemBridgeB] using hxa)
      have hx_eq_cross := hlastRightOne x hx_right
        hx_one_suffix_rev
      exact hxb_ne (by simp [k4BridgeEndpointSubgraph, hx_eq_cross])
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
      hlast_ne_crossV pBridge hpBridge
      attachBridgeB hattachBridge
      stemBridgeB hstemBridgeB_path
      hstemBridgeB_avoids hbridgeStem_meet hstemStem_meet

end PathCarrier

end Schematic.Math.GraphTheory
