import DominatingFourColour.Consequences.NearHajos.PathCarrier.CommonData

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

set_option maxHeartbeats 0 in
theorem commonRootNoCross
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (C : LargePathCarrier D) [DecidableEq C.Btail.verts]
    (N : NormalizedCommonObstruction C) :
    (N.root : C.Btail.verts) = N.last ->
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
  intro hroot_eq hno_cross
  have hsupports := N.rootedFourPathSupports
  rcases N with ⟨zRootT, hz_left, hz_internal, hz_right,
    pLeft, pRight, pOne, pThree, last,
    hlast_one, hlast_one_rev, hlast_three, hfirst,
    hpLeft, hpRight, hpOne, hpThree,
    hpLeft_le, hpRight_le, hpOne_le, hpThree_le,
    _hright_not_pLeft, _hleft_not_pRight,
    _hright_not_pOne, _hleft_not_pThree,
    hone_support_stem, hthree_support_stem, hlast⟩
  change (zRootT : Btail.verts) = last at hroot_eq
  change (forall {x : Btail.verts},
    x ∈ pRight.support -> x ∈ pOne.support ->
      x = (zRootT : Btail.verts)) at hno_cross
  subst last
  let attachRootB : Fin 4 -> Btail.verts := fun a =>
    match a with
    | 0 => C.left
    | 1 => C.one
    | 2 => C.right
    | 3 => C.three
  have hattachRoot_eq (a : Fin 4) :
      attachRootB a = C.attachment a := by
    fin_cases a <;> simp [attachRootB]
  let stemRootB :
      forall a : Fin 4,
        Btail.coe.Walk
          (zRootT : Btail.verts)
          (attachRootB a) := fun a =>
    match a with
    | 0 => pLeft
    | 1 => pOne
    | 2 => pRight
    | 3 => pThree
  have hattachRoot :
      forall a : Fin 4,
        G.Adj (attachRootB a : V)
          (Ktail.model.branchVertex (σ₀ a)) := by
    intro a
    rw [hattachRoot_eq a]
    simpa [Ktail, σ₀] using C.attachment_adj a
  have hstemRootB_path :
      forall a : Fin 4,
        (stemRootB a).IsPath := by
    intro a
    fin_cases a
    · simpa [stemRootB] using hpLeft
    · simpa [stemRootB] using hpOne
    · simpa [stemRootB] using hpRight
    · simpa [stemRootB] using hpThree
  rcases hsupports with ⟨hleft_support_prefix,
      hright_support_prefix, hone_support_suffix,
      hthree_support_suffix, hleft_support_pB_prefix,
      hright_support_pB_suffix⟩
  have hstemRootB_meet :
      forall {a b : Fin 4}, a ≠ b ->
        forall {x : Btail.verts},
          x ∈ (stemRootB a).support ->
            x ∈ (stemRootB b).support ->
              x = (zRootT : Btail.verts) := by
    intro a b hab x hxa hxb
    fin_cases a <;> fin_cases b
    · exact False.elim (hab rfl)
    · have hx_left_prefix :=
        hleft_support_prefix
          (by simpa [stemRootB] using hxa)
      have hx_left_suffix :=
        hone_support_suffix
          (by simpa [stemRootB] using hxb)
      exact
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemLeftOneB₀_path hz_left
          hx_left_prefix hx_left_suffix
    · have hx_left_pB :=
        hleft_support_pB_prefix
          (by simpa [stemRootB] using hxa)
      have hx_right_pB :=
        hright_support_pB_suffix
          (by simpa [stemRootB] using hxb)
      exact
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpB₀ hz_internal.1
          hx_left_pB hx_right_pB
    · have hx_left_prefix :=
        hleft_support_prefix
          (by simpa [stemRootB] using hxa)
      have hx_three :
          x ∈ stemRightThreeB₀.support :=
        hthree_support_stem
          (by simpa [stemRootB] using hxb)
      exact hfirst x hx_three hx_left_prefix
    · have hx_left_prefix :=
        hleft_support_prefix
          (by simpa [stemRootB] using hxb)
      have hx_left_suffix :=
        hone_support_suffix
          (by simpa [stemRootB] using hxa)
      exact
        (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemLeftOneB₀_path hz_left
          hx_left_prefix hx_left_suffix)
    · exact False.elim (hab rfl)
    · exact hno_cross
        (by simpa [stemRootB] using hxb)
        (by simpa [stemRootB] using hxa)
    · have hx_one :
          x ∈ pOne.support := by
        simpa [stemRootB] using hxa
      have hx_three :
          x ∈ pThree.support := by
        simpa [stemRootB] using hxb
      have hx_one_rev :
          x ∈ pOne.reverse.support := by
        simpa [SimpleGraph.Walk.support_reverse] using
          hx_one
      have hx_prefix :
          x ∈ (pOne.reverse.takeUntil (zRootT : Btail.verts)
            hlast_one_rev).support :=
        Schematic.Math.GraphTheory.Walk.IsPath.mem_support_takeUntil_end
          hpOne.reverse hx_one_rev
      exact hlast x hx_three hx_prefix
    · have hx_left_pB :=
        hleft_support_pB_prefix
          (by simpa [stemRootB] using hxb)
      have hx_right_pB :=
        hright_support_pB_suffix
          (by simpa [stemRootB] using hxa)
      exact
        (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hpB₀ hz_internal.1
          hx_left_pB hx_right_pB)
    · exact hno_cross
        (by simpa [stemRootB] using hxa)
        (by simpa [stemRootB] using hxb)
    · exact False.elim (hab rfl)
    · have hx_right_prefix :=
        hright_support_prefix
          (by simpa [stemRootB] using hxa)
      have hx_right_suffix :=
        hthree_support_suffix
          (by simpa [stemRootB] using hxb)
      exact
        Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemRightThreeB₀_path hz_right
          hx_right_prefix hx_right_suffix
    · have hx_left_prefix :=
        hleft_support_prefix
          (by simpa [stemRootB] using hxb)
      have hx_three :
          x ∈ stemRightThreeB₀.support :=
        hthree_support_stem
          (by simpa [stemRootB] using hxa)
      exact hfirst x hx_three hx_left_prefix
    · have hx_one :
          x ∈ pOne.support := by
        simpa [stemRootB] using hxb
      have hx_three :
          x ∈ pThree.support := by
        simpa [stemRootB] using hxa
      have hx_one_rev :
          x ∈ pOne.reverse.support := by
        simpa [SimpleGraph.Walk.support_reverse] using
          hx_one
      have hx_prefix :
          x ∈ (pOne.reverse.takeUntil (zRootT : Btail.verts)
            hlast_one_rev).support :=
        Schematic.Math.GraphTheory.Walk.IsPath.mem_support_takeUntil_end
          hpOne.reverse hx_one_rev
      exact hlast x hx_three hx_prefix
    · have hx_right_prefix :=
        hright_support_prefix
          (by simpa [stemRootB] using hxb)
      have hx_right_suffix :=
        hthree_support_suffix
          (by simpa [stemRootB] using hxa)
      exact
        (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hstemRightThreeB₀_path hz_right
          hx_right_prefix hx_right_suffix)
    · exact False.elim (hab rfl)
  exact
    Ktail.carrier_rooted_attachment_subgraph_paths_permute_meet_only_root_near_hajos_with_two_incident_unsplit_edges
      σ₀ Btail
      (by
        intro i hmem
        exact hKtail_branch_not_first i
          (hBtail_le.left hmem))
      (by
        intro i j hij z hz hmem
        exact hKtail_internal_not_first hij hz
          (hBtail_le.left hmem))
      (zRootT : Btail.verts) attachRootB
      hattachRoot stemRootB
      hstemRootB_path hstemRootB_meet

end PathCarrier

end Schematic.Math.GraphTheory
