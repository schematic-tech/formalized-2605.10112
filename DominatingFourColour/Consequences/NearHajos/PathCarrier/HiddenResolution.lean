import DominatingFourColour.Consequences.NearHajos.PathCarrier.CommonResolution
import DominatingFourColour.Consequences.NearHajos.PathCarrier.PathSplits

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

set_option maxHeartbeats 0 in
theorem resolveHidden
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (C : LargePathCarrier D)
    (hnot_clean : Not C.Clean) :
    NearHajosStrengtheningConclusion G := by
  classical
  let C₀ := C
  rcases C with ⟨Ktail, attachTail, hattachTail,
    hKtail_branch_not_first, hKtail_internal_not_first,
    Btail, hBtail_le, hBtail_terminal, TBtail,
    hTBtail_tree, hTBtail_spanning, leftT₀, rightT₀,
    pB₀, σ₀, stemLeftB₀, stemRightB₀,
    hleft₀_ne_right₀, hpB₀, hpB₀_le_TB,
    hleft₀_eq_attachσ₀_zero, hright₀_eq_attachσ₀_two,
    hattachσ₀_one_ne_right, hattachσ₀_three_ne_left,
    hstemLeftB₀_path, hstemLeftB₀_le_TB,
    hstemRightB₀_path, hstemRightB₀_le_TB,
    hstemLeftB₀_avoids_right,
    hstemRightB₀_avoids_left⟩
  letI : DecidableEq Btail.verts := Classical.decEq _
  letI : Fintype TBtail.verts := TBtail.verts.toFinite.fintype
  letI : DecidableEq TBtail.verts := Classical.decEq _
  letI : DecidableRel TBtail.coe.Adj := Classical.decRel _
  let leftB₀ : Btail.verts :=
    (leftT₀ : Btail.verts)
  let rightB₀ : Btail.verts :=
    (rightT₀ : Btail.verts)
  let attachB₀ : Fin 4 -> Btail.verts :=
    fun a =>
      ⟨attachTail (σ₀ a),
        hBtail_terminal (σ₀ a)⟩
  have hattachB₀_adj :
      forall a : Fin 4,
        G.Adj (attachB₀ a : V)
          (Ktail.model.branchVertex (σ₀ a)) := by
    intro a
    simpa [attachB₀] using
      (hattachTail (σ₀ a)).2
  have hattachB₀_zero :
      attachB₀ (0 : Fin 4) = leftB₀ := by
    apply Subtype.ext
    exact hleft₀_eq_attachσ₀_zero.symm
  have hattachB₀_two :
      attachB₀ (2 : Fin 4) = rightB₀ := by
    apply Subtype.ext
    exact hright₀_eq_attachσ₀_two.symm
  let LeftObs : Prop :=
    Exists fun z : Btail.verts =>
      z ∈ Walk.InternalVertices pB₀ ∧
        z ∈ (stemLeftB₀ (1 : Fin 4)).support ∧
          z ≠ (leftT₀ : Btail.verts)
  let RightObs : Prop :=
    Exists fun z : Btail.verts =>
      z ∈ Walk.InternalVertices pB₀ ∧
        z ∈ (stemRightB₀ (3 : Fin 4)).support ∧
          z ≠ (rightT₀ : Btail.verts)
  let ArmsObs : Prop :=
    Exists fun z : Btail.verts =>
      z ∈ (stemLeftB₀ (1 : Fin 4)).support ∧
        z ∈ (stemRightB₀ (3 : Fin 4)).support ∧
          z ≠ (leftT₀ : Btail.verts) ∧
            z ≠ (rightT₀ : Btail.verts)
  have hoverlap : LeftObs ∨ RightObs ∨ ArmsObs := by
    by_cases hleftObs : LeftObs
    · exact Or.inl hleftObs
    · by_cases hrightObs : RightObs
      · exact Or.inr (Or.inl hrightObs)
      · by_cases harmsObs : ArmsObs
        · exact Or.inr (Or.inr harmsObs)
        · exfalso
          apply hnot_clean
          refine ⟨?_, ?_, ?_⟩
          · intro z hz_p hz_stem hz_ne_left
            exact hleftObs
              ⟨z, hz_p, hz_stem, hz_ne_left⟩
          · intro z hz_p hz_stem hz_ne_right
            exact hrightObs
              ⟨z, hz_p, hz_stem, hz_ne_right⟩
          · intro z hz_left hz_right hz_ne_left
              hz_ne_right
            exact harmsObs
              ⟨z, hz_left, hz_right, hz_ne_left,
                hz_ne_right⟩
  let attachOneT₀ : TBtail.verts :=
    ⟨attachB₀ (1 : Fin 4),
      hTBtail_spanning (attachB₀ (1 : Fin 4))⟩
  let attachThreeT₀ : TBtail.verts :=
    ⟨attachB₀ (3 : Fin 4),
      hTBtail_spanning (attachB₀ (3 : Fin 4))⟩
  have hoverlap_endpoint_or_common :
      (Exists fun r :
        Btail.coe.Walk
          (rightT₀ : Btail.verts)
          (attachB₀ (1 : Fin 4)) =>
        r.toSubgraph ≤ TBtail ∧ r.IsPath ∧
          (leftT₀ : Btail.verts) ∉ r.support) ∨
      (Exists fun r :
        Btail.coe.Walk
          (leftT₀ : Btail.verts)
          (attachB₀ (3 : Fin 4)) =>
        r.toSubgraph ≤ TBtail ∧ r.IsPath ∧
          (rightT₀ : Btail.verts) ∉ r.support) ∨
        ArmsObs := by
    rcases hoverlap with hleftOverlap | hrest
    · rcases hleftOverlap with
        ⟨z, hz_p, hz_stem, hz_ne_left⟩
      let zT : TBtail.verts :=
        ⟨z,
          Walk.support_subset_of_toSubgraph_le
            hpB₀_le_TB hz_p.1⟩
      have hright_ne_leftT :
          rightT₀ ≠ leftT₀ := by
        intro h
        exact hleft₀_ne_right₀ (by
          cases h
          rfl)
      have hz_pT :
          (zT : Btail.verts) ∈
            Walk.InternalVertices pB₀ := by
        simpa [zT] using hz_p
      have hz_stemT :
          (zT : Btail.verts) ∈
            (stemLeftB₀ (1 : Fin 4)).support := by
        simpa [zT] using hz_stem
      have hz_ne_leftT :
          (zT : Btail.verts) ≠
            (leftT₀ : Btail.verts) := by
        simpa [zT] using hz_ne_left
      exact Or.inl (by
        simpa [attachOneT₀, attachB₀] using
          (tree_bridge_internal_left_stem_yields_path_avoiding_left
            (G := G) (B := Btail)
            (TB := TBtail)
            (leftT := leftT₀)
            (rightT := rightT₀)
            (attachT := attachOneT₀)
            (p := pB₀)
            (stem := stemLeftB₀ (1 : Fin 4))
            hTBtail_tree hpB₀_le_TB
            (hstemLeftB₀_le_TB (1 : Fin 4))
            hpB₀ (hstemLeftB₀_path (1 : Fin 4))
            hright_ne_leftT hz_pT hz_stemT
            hz_ne_leftT))
    · rcases hrest with hrightOverlap | harmsOverlap
      · rcases hrightOverlap with
          ⟨z, hz_p, hz_stem, hz_ne_right⟩
        let zT : TBtail.verts :=
          ⟨z,
            Walk.support_subset_of_toSubgraph_le
              hpB₀_le_TB hz_p.1⟩
        have hleft_ne_rightT :
            leftT₀ ≠ rightT₀ := by
          intro h
          exact hleft₀_ne_right₀ (by
            cases h
            rfl)
        have hz_pT :
            (zT : Btail.verts) ∈
              Walk.InternalVertices pB₀ := by
          simpa [zT] using hz_p
        have hz_stemT :
            (zT : Btail.verts) ∈
              (stemRightB₀ (3 : Fin 4)).support := by
          simpa [zT] using hz_stem
        have hz_ne_rightT :
            (zT : Btail.verts) ≠
              (rightT₀ : Btail.verts) := by
          simpa [zT] using hz_ne_right
        exact Or.inr (Or.inl (by
          simpa [attachThreeT₀, attachB₀] using
            (tree_bridge_internal_right_stem_yields_path_avoiding_right
              (G := G) (B := Btail)
              (TB := TBtail)
              (leftT := leftT₀)
              (rightT := rightT₀)
              (attachT := attachThreeT₀)
              (p := pB₀)
              (stem := stemRightB₀ (3 : Fin 4))
              hTBtail_tree hpB₀_le_TB
              (hstemRightB₀_le_TB (3 : Fin 4))
              hpB₀ (hstemRightB₀_path (3 : Fin 4))
              hleft_ne_rightT hz_pT hz_stemT
              hz_ne_rightT)))
      · exact Or.inr (Or.inr harmsOverlap)
  let CommonObs : Prop :=
    Exists fun z : Btail.verts =>
      z ∈ Walk.InternalVertices pB₀ ∧
        z ∈ (stemLeftB₀ (1 : Fin 4)).support ∧
          z ∈ (stemRightB₀ (3 : Fin 4)).support
  have hoverlap_recovered_on_p :
      LeftObs ∨ RightObs ∨ CommonObs := by
    rcases hoverlap_endpoint_or_common with
      hleftPath | hrest
    · rcases hleftPath with
        ⟨r, hr_le, hr_path, hleft_not_r⟩
      rcases
        Subgraph.tree_exists_rooted_paths_common_nonroot_of_endpoint_path_avoids_root
          (G := Btail.coe) (T := TBtail)
          (root := leftT₀) (a := rightT₀)
          (b := attachOneT₀)
          hTBtail_tree hpB₀_le_TB
          (hstemLeftB₀_le_TB (1 : Fin 4))
          hr_le hpB₀
          (hstemLeftB₀_path (1 : Fin 4))
          hr_path hleft_not_r with
        ⟨zT, hz_p, hz_ne_left, hz_stem,
          _hz_ne_left'⟩
      have hz_ne_right :
          (zT : Btail.verts) ≠
            (rightT₀ : Btail.verts) :=
        hstemLeftB₀_avoids_right
          hz_stem hz_ne_left
      exact Or.inl
        ⟨(zT : Btail.verts),
          ⟨hz_p, hz_ne_left, hz_ne_right⟩,
          hz_stem, hz_ne_left⟩
    · rcases hrest with hrightPath | harmsOverlap
      · rcases hrightPath with
          ⟨r, hr_le, hr_path, hright_not_r⟩
        rcases
          Subgraph.tree_exists_rooted_paths_common_nonroot_of_endpoint_path_avoids_root
            (G := Btail.coe) (T := TBtail)
            (root := rightT₀) (a := leftT₀)
            (b := attachThreeT₀)
            hTBtail_tree
            (by
              simpa [SimpleGraph.Walk.toSubgraph_reverse]
                using hpB₀_le_TB)
            (hstemRightB₀_le_TB (3 : Fin 4))
            hr_le hpB₀.reverse
            (hstemRightB₀_path (3 : Fin 4))
            hr_path hright_not_r with
          ⟨zT, hz_p_rev, hz_ne_right, hz_stem,
            _hz_ne_right'⟩
        have hz_p :
            (zT : Btail.verts) ∈ pB₀.support := by
          simpa [SimpleGraph.Walk.support_reverse] using
            hz_p_rev
        have hz_ne_left :
            (zT : Btail.verts) ≠
              (leftT₀ : Btail.verts) :=
          hstemRightB₀_avoids_left
            hz_stem hz_ne_right
        exact Or.inr (Or.inl
          ⟨(zT : Btail.verts),
            ⟨hz_p, hz_ne_left, hz_ne_right⟩,
            hz_stem, hz_ne_right⟩)
      · rcases harmsOverlap with
          ⟨z₀, hz₀_left, hz₀_right,
            _hz₀_ne_left, _hz₀_ne_right⟩
        rcases
          Walk.exists_first_common_support
            (stemLeftB₀ (1 : Fin 4))
            (stemRightB₀ (3 : Fin 4))
            ⟨z₀, hz₀_left, hz₀_right⟩ with
          ⟨z, hz_left, hz_right, hfirst⟩
        have hz_p :
            z ∈ pB₀.support :=
          Subgraph.tree_common_prefix_split_mem_start_path
            (G := Btail.coe) (T := TBtail)
            (p := stemLeftB₀ (1 : Fin 4))
            (q := stemRightB₀ (3 : Fin 4))
            (r := pB₀)
            hTBtail_tree
            (hstemLeftB₀_le_TB (1 : Fin 4))
            (hstemRightB₀_le_TB (3 : Fin 4))
            hpB₀_le_TB
            (hstemLeftB₀_path (1 : Fin 4))
            (hstemRightB₀_path (3 : Fin 4))
            hpB₀ hz_left hz_right
            (Walk.first_common_takeUntil_punctured_disjoint_takeUntil
              (p := stemLeftB₀ (1 : Fin 4))
              (q := stemRightB₀ (3 : Fin 4))
              hz_left hz_right hfirst)
        have hz_ne_left :
            z ≠ (leftT₀ : Btail.verts) := by
          intro hz_eq_left
          have hz_ne_right :
              z ≠ (rightT₀ : Btail.verts) := by
            intro hz_eq_right
            exact hleft₀_ne_right₀ (by
              calc
                ((leftT₀ : Btail.verts) : V) =
                    (z : V) := by
                  simp [hz_eq_left]
                _ = ((rightT₀ : Btail.verts) : V) := by
                  simp [hz_eq_right])
          exact
            (hstemRightB₀_avoids_left
              hz_right hz_ne_right) hz_eq_left
        have hz_ne_right :
            z ≠ (rightT₀ : Btail.verts) := by
          intro hz_eq_right
          have hz_ne_left' :
              z ≠ (leftT₀ : Btail.verts) := by
            intro hz_eq_left
            exact hleft₀_ne_right₀ (by
              calc
                ((leftT₀ : Btail.verts) : V) =
                    (z : V) := by
                  simp [hz_eq_left]
                _ = ((rightT₀ : Btail.verts) : V) := by
                  simp [hz_eq_right])
          exact
            (hstemLeftB₀_avoids_right
              hz_left hz_ne_left') hz_eq_right
        exact Or.inr (Or.inr
          ⟨z, ⟨hz_p, hz_ne_left, hz_ne_right⟩,
            hz_left, hz_right⟩)
  let LeftObsT : Prop :=
    Exists fun zT : TBtail.verts =>
      (zT : Btail.verts) ∈
          Walk.InternalVertices pB₀ ∧
        (zT : Btail.verts) ∈
            (stemLeftB₀ (1 : Fin 4)).support ∧
          (zT : Btail.verts) ≠ leftB₀
  let RightObsT : Prop :=
    Exists fun zT : TBtail.verts =>
      (zT : Btail.verts) ∈
          Walk.InternalVertices pB₀ ∧
        (zT : Btail.verts) ∈
            (stemRightB₀ (3 : Fin 4)).support ∧
          (zT : Btail.verts) ≠ rightB₀
  let CommonObsT : Prop :=
    Exists fun zT : TBtail.verts =>
      (zT : Btail.verts) ∈
          Walk.InternalVertices pB₀ ∧
        (zT : Btail.verts) ∈
            (stemLeftB₀ (1 : Fin 4)).support ∧
          (zT : Btail.verts) ∈
            (stemRightB₀ (3 : Fin 4)).support
  have hoverlap_recovered_on_p_T :
      LeftObsT ∨ RightObsT ∨ CommonObsT := by
    rcases hoverlap_recovered_on_p with
      hleft | hrest
    · rcases hleft with
        ⟨z, hz_internal, hz_left, hz_ne_left⟩
      let zT : TBtail.verts :=
        ⟨z,
          Walk.support_subset_of_toSubgraph_le
            hpB₀_le_TB hz_internal.1⟩
      exact Or.inl
        ⟨zT,
          by simpa [zT] using hz_internal,
          by simpa [zT] using hz_left,
          by simpa [zT, leftB₀] using
            hz_ne_left⟩
    · rcases hrest with hright | hcommon
      · rcases hright with
          ⟨z, hz_internal, hz_right,
            hz_ne_right⟩
        let zT : TBtail.verts :=
          ⟨z,
            Walk.support_subset_of_toSubgraph_le
              hpB₀_le_TB hz_internal.1⟩
        exact Or.inr (Or.inl
          ⟨zT,
            by simpa [zT] using hz_internal,
            by simpa [zT] using hz_right,
            by simpa [zT, rightB₀] using
              hz_ne_right⟩)
      · rcases hcommon with
          ⟨z, hz_internal, hz_left, hz_right⟩
        let zT : TBtail.verts :=
          ⟨z,
            Walk.support_subset_of_toSubgraph_le
              hpB₀_le_TB hz_internal.1⟩
        exact Or.inr (Or.inr
          ⟨zT,
            by simpa [zT] using hz_internal,
            by simpa [zT] using hz_left,
            by simpa [zT] using hz_right⟩)
  let attachOneB₀ : Btail.verts :=
    attachB₀ (1 : Fin 4)
  let attachThreeB₀ : Btail.verts :=
    attachB₀ (3 : Fin 4)
  let stemLeftOneB₀ :
      Btail.coe.Walk leftB₀ attachOneB₀ :=
    stemLeftB₀ (1 : Fin 4)
  let stemRightThreeB₀ :
      Btail.coe.Walk rightB₀ attachThreeB₀ :=
    stemRightB₀ (3 : Fin 4)
  have hleftB₀_eq_leftT₀ :
      leftB₀ = (leftT₀ : Btail.verts) := rfl
  have hrightB₀_eq_rightT₀ :
      rightB₀ = (rightT₀ : Btail.verts) := rfl
  have hleftT₀_ne_rightT₀ :
      leftT₀ ≠ rightT₀ := by
    intro h
    exact hleft₀_ne_right₀ (by
      cases h
      rfl)
  have hstemLeftOneB₀_path :
      stemLeftOneB₀.IsPath := by
    simpa [stemLeftOneB₀] using
      hstemLeftB₀_path (1 : Fin 4)
  have hstemRightThreeB₀_path :
      stemRightThreeB₀.IsPath := by
    simpa [stemRightThreeB₀] using
      hstemRightB₀_path (3 : Fin 4)
  have hstemLeftOneB₀_le_TB :
      stemLeftOneB₀.toSubgraph ≤ TBtail := by
    simpa [stemLeftOneB₀] using
      hstemLeftB₀_le_TB (1 : Fin 4)
  have hstemRightThreeB₀_le_TB :
      stemRightThreeB₀.toSubgraph ≤ TBtail := by
    simpa [stemRightThreeB₀] using
      hstemRightB₀_le_TB (3 : Fin 4)
  have hrightT₀_on_left_stem_one_endpoint :
      (rightT₀ : Btail.verts) ∈
          stemLeftOneB₀.support ->
        (rightT₀ : Btail.verts) = leftB₀ ∨
          (rightT₀ : Btail.verts) = attachOneB₀ := by
    intro hright
    exact False.elim
      (hstemLeftB₀_avoids_right
        (by simpa [stemLeftOneB₀] using hright)
        (by
          intro h
          exact hleftT₀_ne_rightT₀.symm (by
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg
              (fun x : Btail.verts => (x : V)) h))
        rfl)
  have hleftT₀_on_right_stem_three_endpoint :
      (leftT₀ : Btail.verts) ∈
          stemRightThreeB₀.support ->
        (leftT₀ : Btail.verts) = rightB₀ ∨
          (leftT₀ : Btail.verts) = attachThreeB₀ := by
    intro hleft
    exact False.elim
      (hstemRightB₀_avoids_left
        (by simpa [stemRightThreeB₀] using hleft)
        (by
          intro h
          exact hleftT₀_ne_rightT₀ (by
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg
              (fun x : Btail.verts => (x : V)) h))
        rfl)
  have hrightB₀_not_stemLeftOne :
      rightB₀ ∉ stemLeftOneB₀.support := by
    intro hright
    exact hstemLeftB₀_avoids_right
      (by
        simpa [stemLeftOneB₀, rightB₀] using
          hright)
      (by
        intro h
        exact hleftT₀_ne_rightT₀.symm
          (Subtype.ext h))
      rfl
  have hleftB₀_not_stemRightThree :
      leftB₀ ∉ stemRightThreeB₀.support := by
    intro hleft
    exact hstemRightB₀_avoids_left
      (by
        simpa [stemRightThreeB₀, leftB₀] using
          hleft)
      (by
        intro h
        exact hleftT₀_ne_rightT₀
          (Subtype.ext h))
      rfl
  have hleft_first_common_split :
      LeftObsT ->
        Exists fun zT : TBtail.verts =>
          Exists fun pBridge :
            Btail.coe.Walk
              (zT : Btail.verts) rightB₀ =>
          Exists fun pLeft :
            Btail.coe.Walk
              (zT : Btail.verts) leftB₀ =>
          Exists fun pOne :
            Btail.coe.Walk
              (zT : Btail.verts) attachOneB₀ =>
          pBridge.IsPath ∧ pLeft.IsPath ∧
            pOne.IsPath ∧
              pBridge.toSubgraph ≤ TBtail ∧
                pLeft.toSubgraph ≤ TBtail ∧
                  pOne.toSubgraph ≤ TBtail ∧
                    (zT : Btail.verts) ∈
                      stemLeftOneB₀.support ∧
                    (zT : Btail.verts) ∈
                      Walk.InternalVertices pB₀ ∧
                    (forall {x : Btail.verts},
                      x ∈ pBridge.support ->
                        x ∈ pB₀.support) ∧
                    (forall {x : Btail.verts},
                      x ∈ pLeft.support ->
                        x ∈ stemLeftOneB₀.support) ∧
                    (forall {x : Btail.verts},
                      x ∈ pOne.support ->
                        x ∈ stemLeftOneB₀.support) ∧
                    rightB₀ ∉ pLeft.support ∧
                      rightB₀ ∉ pOne.support ∧
                        Disjoint
                          (Walk.InternalVertices pBridge)
                          {x : Btail.verts |
                            x ∈ pLeft.support ∧
                              x ≠ (zT : Btail.verts)} ∧
                        Disjoint
                          (Walk.InternalVertices pBridge)
                          {x : Btail.verts |
                            x ∈ pOne.support ∧
                              x ≠ (zT : Btail.verts)} ∧
                          Disjoint
                            {x : Btail.verts |
                              x ∈ pLeft.support ∧
                                x ≠ (zT : Btail.verts)}
                            {x : Btail.verts |
                              x ∈ pOne.support ∧
                                x ≠ (zT : Btail.verts)} := by
    intro hleft
    simpa [LeftObsT, stemLeftOneB₀] using
      (Subgraph.exists_left_first_common_split
        (T := TBtail) (p := pB₀)
        (q := stemLeftOneB₀)
        hpB₀ hstemLeftOneB₀_path hpB₀_le_TB
        hstemLeftOneB₀_le_TB
        hrightB₀_not_stemLeftOne
        (by
          simpa [LeftObsT, stemLeftOneB₀]
            using hleft))
  have hright_first_common_split :
      RightObsT ->
        Exists fun zT : TBtail.verts =>
          Exists fun pBridge :
            Btail.coe.Walk leftB₀
              (zT : Btail.verts) =>
          Exists fun pRight :
            Btail.coe.Walk
              (zT : Btail.verts) rightB₀ =>
          Exists fun pThree :
            Btail.coe.Walk
              (zT : Btail.verts) attachThreeB₀ =>
          pBridge.IsPath ∧ pRight.IsPath ∧
            pThree.IsPath ∧
              pBridge.toSubgraph ≤ TBtail ∧
                pRight.toSubgraph ≤ TBtail ∧
                  pThree.toSubgraph ≤ TBtail ∧
                    (zT : Btail.verts) ∈
                      stemRightThreeB₀.support ∧
                    (zT : Btail.verts) ∈
                      Walk.InternalVertices pB₀ ∧
                    (forall {x : Btail.verts},
                      x ∈ pBridge.support ->
                        x ∈ pB₀.support) ∧
                    (forall {x : Btail.verts},
                      x ∈ pRight.support ->
                        x ∈ stemRightThreeB₀.support) ∧
                    (forall {x : Btail.verts},
                      x ∈ pThree.support ->
                        x ∈ stemRightThreeB₀.support) ∧
                    leftB₀ ∉ pRight.support ∧
                      leftB₀ ∉ pThree.support ∧
                        Disjoint
                          (Walk.InternalVertices pBridge)
                          {x : Btail.verts |
                            x ∈ pRight.support ∧
                              x ≠ (zT : Btail.verts)} ∧
                        Disjoint
                          (Walk.InternalVertices pBridge)
                          {x : Btail.verts |
                            x ∈ pThree.support ∧
                              x ≠ (zT : Btail.verts)} ∧
                          Disjoint
                            {x : Btail.verts |
                              x ∈ pRight.support ∧
                                x ≠ (zT : Btail.verts)}
                            {x : Btail.verts |
                              x ∈ pThree.support ∧
                                x ≠ (zT : Btail.verts)} := by
    intro hright
    simpa [RightObsT, stemRightThreeB₀] using
      (Subgraph.exists_right_first_common_split
        (T := TBtail) (p := pB₀)
        (q := stemRightThreeB₀)
        hpB₀ hstemRightThreeB₀_path hpB₀_le_TB
        hstemRightThreeB₀_le_TB
        hleftB₀_not_stemRightThree
        (by
          simpa [RightObsT, stemRightThreeB₀]
            using hright))
  have hcommon_obstruction_recovered_on_p_T :
      (Exists fun zT : TBtail.verts =>
        (zT : Btail.verts) ∈
            stemLeftOneB₀.support ∧
          (zT : Btail.verts) ≠ leftB₀ ∧
            (zT : Btail.verts) ∈
              stemRightThreeB₀.support ∧
              (zT : Btail.verts) ≠ rightB₀) ->
        CommonObsT := by
    intro hcommon
    rcases hcommon with
      ⟨zT₀, hz_left₀, _hz_ne_left₀,
        hz_right₀, _hz_ne_right₀⟩
    rcases
      Walk.exists_first_common_support
        stemLeftOneB₀ stemRightThreeB₀
        ⟨(zT₀ : Btail.verts), hz_left₀,
          hz_right₀⟩ with
      ⟨z, hz_left, hz_right, hfirst⟩
    have hz_p :
        z ∈ pB₀.support :=
      Subgraph.tree_common_prefix_split_mem_start_path
        (G := Btail.coe) (T := TBtail)
        (p := stemLeftOneB₀)
        (q := stemRightThreeB₀)
        (r := pB₀)
        hTBtail_tree hstemLeftOneB₀_le_TB
        hstemRightThreeB₀_le_TB
        hpB₀_le_TB hstemLeftOneB₀_path
        hstemRightThreeB₀_path hpB₀
        hz_left hz_right
        (Walk.first_common_takeUntil_punctured_disjoint_takeUntil
          (p := stemLeftOneB₀)
          (q := stemRightThreeB₀)
          hz_left hz_right hfirst)
    have hz_ne_left :
        z ≠ (leftT₀ : Btail.verts) := by
      intro hz_eq_left
      have hleft_support :
          (leftT₀ : Btail.verts) ∈
            stemRightThreeB₀.support := by
        simpa [hz_eq_left] using hz_right
      rcases hleftT₀_on_right_stem_three_endpoint
          hleft_support with
        hleft_eq_right | hleft_eq_attach
      · exact hleftT₀_ne_rightT₀
          (Subtype.ext
            (hleft_eq_right.trans
              hrightB₀_eq_rightT₀))
      · exact hattachσ₀_three_ne_left
          (by
            have hval :=
              congrArg
                (fun x : Btail.verts => (x : V))
                hleft_eq_attach
            simpa [attachThreeB₀, attachB₀] using
              hval.symm)
    have hz_ne_right :
        z ≠ (rightT₀ : Btail.verts) := by
      intro hz_eq_right
      have hright_support :
          (rightT₀ : Btail.verts) ∈
            stemLeftOneB₀.support := by
        simpa [hz_eq_right] using hz_left
      rcases hrightT₀_on_left_stem_one_endpoint
          hright_support with
        hright_eq_left | hright_eq_attach
      · exact hleftT₀_ne_rightT₀.symm
          (Subtype.ext
            (hright_eq_left.trans
              hleftB₀_eq_leftT₀))
      · exact hattachσ₀_one_ne_right
          (by
            have hval :=
              congrArg
                (fun x : Btail.verts => (x : V))
                hright_eq_attach
            simpa [attachOneB₀, attachB₀] using
              hval.symm)
    have hzT_mem : z ∈ TBtail.verts :=
      Walk.support_subset_of_toSubgraph_le
        hpB₀_le_TB hz_p
    exact ⟨⟨z, hzT_mem⟩,
      ⟨by simpa using hz_p,
        by simpa [leftB₀] using hz_ne_left,
        by simpa [rightB₀] using hz_ne_right⟩,
      by
        simpa [CommonObsT, stemLeftOneB₀] using
          hz_left,
      by
        simpa [CommonObsT, stemRightThreeB₀] using
          hz_right⟩
  have hleft_first_common_bridge_conclusion :
      LeftObsT ->
      Not RightObsT ->
      Not CommonObsT ->
        NearHajosStrengtheningConclusion G := by
    intro hleft hno_right hno_common
    rcases hleft_first_common_split hleft with
      ⟨zT, pBridge, pLeft, pOne,
        hpBridge, hpLeft, hpOne,
        hpBridge_le, _hpLeft_le, _hpOne_le,
        hz_left_stem, _hz_left_internal,
        hbridge_support_pB,
        hleft_support_stem, hone_support_stem,
        hright_not_pLeft, hright_not_pOne,
        hbridge_left_disjoint,
        hbridge_one_disjoint,
        hleft_one_disjoint⟩
    have hz_ne_rightB :
        (zT : Btail.verts) ≠ rightB₀ := by
      intro hz_eq
      exact hright_not_pLeft (by
        simpa [hz_eq] using pLeft.start_mem_support)
    have hz_ne_rightV :
        ((zT : Btail.verts) : V) ≠
          (rightB₀ : V) := by
      intro h
      exact hz_ne_rightB (Subtype.ext h)
    let attachBridgeB : Fin 4 -> Btail.verts
      | 0 => leftB₀
      | 1 => attachOneB₀
      | 2 => rightB₀
      | 3 => attachThreeB₀
    let stemBridgeB :
        forall a : Fin 4,
          Btail.coe.Walk
            (k4BridgeEndpointSubgraph Btail
              (zT : Btail.verts) rightB₀ a)
            (attachBridgeB a)
      | 0 => pLeft
      | 1 => pOne
      | 2 => SimpleGraph.Walk.nil
      | 3 => stemRightThreeB₀
    have hattachBridge :
        forall a : Fin 4,
          G.Adj (attachBridgeB a : V)
            (Ktail.model.branchVertex (σ₀ a)) := by
      intro a
      fin_cases a
      · simpa [attachBridgeB, hattachB₀_zero] using
          hattachB₀_adj (0 : Fin 4)
      · simpa [attachBridgeB, attachOneB₀] using
          hattachB₀_adj (1 : Fin 4)
      · simpa [attachBridgeB, hattachB₀_two] using
          hattachB₀_adj (2 : Fin 4)
      · simpa [attachBridgeB, attachThreeB₀] using
          hattachB₀_adj (3 : Fin 4)
    have hstemBridgeB_path :
        forall a : Fin 4,
          (stemBridgeB a).IsPath := by
      intro a
      fin_cases a
      · simpa [stemBridgeB] using hpLeft
      · simpa [stemBridgeB] using hpOne
      · change
          (SimpleGraph.Walk.nil :
            Btail.coe.Walk rightB₀ rightB₀).IsPath
        exact SimpleGraph.Walk.IsPath.mk' (by simp)
      · simpa [stemBridgeB] using
          hstemRightThreeB₀_path
    have hmem_nil_right_eq :
        forall {x : Btail.verts},
          x ∈
              (SimpleGraph.Walk.nil :
                Btail.coe.Walk rightB₀ rightB₀).support ->
            x = rightB₀ := by
      intro x hx
      exact SimpleGraph.Walk.mem_support_nil_iff.mp hx
    have hrightStem_ne_left :
        forall {x : Btail.verts},
          x ∈ stemRightThreeB₀.support ->
            x ≠ leftB₀ := by
      intro x hx hxl
      exact hleftB₀_not_stemRightThree
        (by simpa [hxl] using hx)
    have hleftRightStem_common_false :
        forall {x : Btail.verts},
          x ∈ stemLeftOneB₀.support ->
            x ∈ stemRightThreeB₀.support ->
              x ≠ rightB₀ -> False := by
      intro x hx_left hx_right hx_ne_right
      have hx_ne_left : x ≠ leftB₀ :=
        hrightStem_ne_left hx_right
      have hxT_mem : x ∈ TBtail.verts :=
        Walk.support_subset_of_toSubgraph_le
          hstemRightThreeB₀_le_TB hx_right
      exact hno_common
        (hcommon_obstruction_recovered_on_p_T
          ⟨⟨x, hxT_mem⟩,
            hx_left, hx_ne_left,
            hx_right, hx_ne_right⟩)
    have hrightStem_bridge_false :
        forall {x : Btail.verts},
          x ∈ Walk.InternalVertices pBridge ->
            x ∈ stemRightThreeB₀.support ->
              x ≠ rightB₀ -> False := by
      intro x hx_bridge hx_right hx_ne_right
      have hx_p : x ∈ pB₀.support :=
        hbridge_support_pB hx_bridge.1
      have hx_ne_leftB : x ≠ leftB₀ :=
        hrightStem_ne_left hx_right
      have hx_ne_leftT :
          x ≠ (leftT₀ : Btail.verts) := by
        intro h
        exact hx_ne_leftB
          (h.trans hleftB₀_eq_leftT₀.symm)
      have hx_ne_rightT :
          x ≠ (rightT₀ : Btail.verts) := by
        intro h
        exact hx_ne_right
          (h.trans hrightB₀_eq_rightT₀.symm)
      have hxT_mem : x ∈ TBtail.verts :=
        Walk.support_subset_of_toSubgraph_le
          hpB₀_le_TB hx_p
      exact hno_right
        ⟨⟨x, hxT_mem⟩,
          ⟨hx_p, hx_ne_leftT, hx_ne_rightT⟩,
          by
            simpa [RightObsT, stemRightThreeB₀] using
              hx_right,
          by
            simpa [rightB₀] using hx_ne_right⟩
    have hstemBridgeB_avoids :
        forall a : Fin 4, forall {x : Btail.verts},
          x ∈ (stemBridgeB a).support ->
            x ≠ k4BridgeEndpointSubgraph Btail
              (zT : Btail.verts) rightB₀ a ->
              x ≠ (zT : Btail.verts) ∧
                x ≠ rightB₀ := by
      intro a x hx hx_ne_start
      fin_cases a
      · refine ⟨?_, ?_⟩
        · exact hx_ne_start
        · intro hxr
          exact hright_not_pLeft (by
            simpa [stemBridgeB, hxr] using hx)
      · refine ⟨?_, ?_⟩
        · exact hx_ne_start
        · intro hxr
          exact hright_not_pOne (by
            simpa [stemBridgeB, hxr] using hx)
      · have hx_eq : x = rightB₀ := by
          exact hmem_nil_right_eq
            (by simpa only [stemBridgeB] using hx)
        exact False.elim
          (hx_ne_start (by
            simp [k4BridgeEndpointSubgraph, hx_eq]))
      · refine ⟨?_, ?_⟩
        · intro hxz
          have hz_right :
              (zT : Btail.verts) ∈
                stemRightThreeB₀.support := by
            simpa [stemBridgeB, hxz] using hx
          exact hleftRightStem_common_false
            hz_left_stem hz_right hz_ne_rightB
        · exact hx_ne_start
    have hbridgeStem_meet :
        forall a : Fin 4, forall {x : Btail.verts},
          x ∈ Walk.InternalVertices pBridge ->
            x ∈ (stemBridgeB a).support ->
              x ≠ k4BridgeEndpointSubgraph Btail
                (zT : Btail.verts) rightB₀ a ->
                False := by
      intro a x hx_bridge hx_stem hx_ne
      fin_cases a
      · exact Set.disjoint_left.mp
          hbridge_left_disjoint hx_bridge
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hx_stem hx_ne)
      · exact Set.disjoint_left.mp
          hbridge_one_disjoint hx_bridge
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hx_stem hx_ne)
      · have hx_eq : x = rightB₀ := by
          exact hmem_nil_right_eq
            (by simpa only [stemBridgeB] using hx_stem)
        exact hx_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · have hx_right :
            x ∈ stemRightThreeB₀.support := by
          simpa [stemBridgeB] using hx_stem
        have hx_ne_right : x ≠ rightB₀ := by
          simpa [k4BridgeEndpointSubgraph] using hx_ne
        exact hrightStem_bridge_false
          hx_bridge hx_right hx_ne_right
    have hstemStem_meet :
        forall {a b : Fin 4}, a ≠ b ->
          forall {x : Btail.verts},
            x ∈ (stemBridgeB a).support ->
              x ∈ (stemBridgeB b).support ->
                x ≠ k4BridgeEndpointSubgraph Btail
                  (zT : Btail.verts) rightB₀ a ->
                  x ≠ k4BridgeEndpointSubgraph Btail
                    (zT : Btail.verts) rightB₀ b ->
                    False := by
      intro a b hab x hxa hxb hxa_ne hxb_ne
      fin_cases a <;> fin_cases b
      · exact hab rfl
      · exact Set.disjoint_left.mp hleft_one_disjoint
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hxa hxa_ne)
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hxb hxb_ne)
      · have hx_eq : x = rightB₀ := by
          exact hmem_nil_right_eq
            (by simpa only [stemBridgeB] using hxb)
        exact hxb_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · have hx_left :
            x ∈ stemLeftOneB₀.support :=
          hleft_support_stem
            (by simpa [stemBridgeB] using hxa)
        have hx_right :
            x ∈ stemRightThreeB₀.support := by
          simpa [stemBridgeB] using hxb
        have hx_ne_right : x ≠ rightB₀ := by
          simpa [k4BridgeEndpointSubgraph] using hxb_ne
        exact hleftRightStem_common_false
          hx_left hx_right hx_ne_right
      · exact Set.disjoint_left.mp
          (Disjoint.symm hleft_one_disjoint)
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hxa hxa_ne)
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hxb hxb_ne)
      · exact hab rfl
      · have hx_eq : x = rightB₀ := by
          exact hmem_nil_right_eq
            (by simpa only [stemBridgeB] using hxb)
        exact hxb_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · have hx_left :
            x ∈ stemLeftOneB₀.support :=
          hone_support_stem
            (by simpa [stemBridgeB] using hxa)
        have hx_right :
            x ∈ stemRightThreeB₀.support := by
          simpa [stemBridgeB] using hxb
        have hx_ne_right : x ≠ rightB₀ := by
          simpa [k4BridgeEndpointSubgraph] using hxb_ne
        exact hleftRightStem_common_false
          hx_left hx_right hx_ne_right
      · have hx_eq : x = rightB₀ := by
          exact hmem_nil_right_eq
            (by simpa only [stemBridgeB] using hxa)
        exact hxa_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · have hx_eq : x = rightB₀ := by
          exact hmem_nil_right_eq
            (by simpa only [stemBridgeB] using hxa)
        exact hxa_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · exact hab rfl
      · have hx_eq : x = rightB₀ := by
          exact hmem_nil_right_eq
            (by simpa only [stemBridgeB] using hxa)
        exact hxa_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · have hx_right :
            x ∈ stemRightThreeB₀.support := by
          simpa [stemBridgeB] using hxa
        have hx_left :
            x ∈ stemLeftOneB₀.support :=
          hleft_support_stem
            (by simpa [stemBridgeB] using hxb)
        have hx_ne_right : x ≠ rightB₀ := by
          simpa [k4BridgeEndpointSubgraph] using hxa_ne
        exact hleftRightStem_common_false
          hx_left hx_right hx_ne_right
      · have hx_right :
            x ∈ stemRightThreeB₀.support := by
          simpa [stemBridgeB] using hxa
        have hx_left :
            x ∈ stemLeftOneB₀.support :=
          hone_support_stem
            (by simpa [stemBridgeB] using hxb)
        have hx_ne_right : x ≠ rightB₀ := by
          simpa [k4BridgeEndpointSubgraph] using hxa_ne
        exact hleftRightStem_common_false
          hx_left hx_right hx_ne_right
      · have hx_eq : x = rightB₀ := by
          exact hmem_nil_right_eq
            (by simpa only [stemBridgeB] using hxb)
        exact hxb_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · exact hab rfl
    exact
      Ktail.carrier_bridge_attachment_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
        σ₀ Btail
        (by
          intro i hmem
          exact hKtail_branch_not_first i
            (hBtail_le.left hmem))
        (by
          intro i j hij z hz hmem
          exact hKtail_internal_not_first hij hz
            (hBtail_le.left hmem))
        hz_ne_rightV pBridge hpBridge
        attachBridgeB hattachBridge
        stemBridgeB hstemBridgeB_path
        hstemBridgeB_avoids hbridgeStem_meet
        hstemStem_meet
  have hright_first_common_bridge_conclusion :
      RightObsT ->
      Not LeftObsT ->
      Not CommonObsT ->
        NearHajosStrengtheningConclusion G := by
    intro hright hno_left hno_common
    rcases hright_first_common_split hright with
      ⟨zT, pBridge, pRight, pThree,
        hpBridge, hpRight, hpThree,
        hpBridge_le, _hpRight_le, _hpThree_le,
        hz_right_stem, _hz_right_internal,
        hbridge_support_pB,
        hright_support_stem, hthree_support_stem,
        hleft_not_pRight, hleft_not_pThree,
        hbridge_right_disjoint,
        hbridge_three_disjoint,
        hright_three_disjoint⟩
    have hleft_ne_zB :
        leftB₀ ≠ (zT : Btail.verts) := by
      intro hz_eq
      exact hleft_not_pRight
        (hz_eq.symm ▸ pRight.start_mem_support)
    have hleft_ne_zV :
        (leftB₀ : V) ≠
          ((zT : Btail.verts) : V) := by
      intro h
      exact hleft_ne_zB (Subtype.ext h)
    let attachBridgeB : Fin 4 -> Btail.verts
      | 0 => leftB₀
      | 1 => attachOneB₀
      | 2 => rightB₀
      | 3 => attachThreeB₀
    let stemBridgeB :
        forall a : Fin 4,
          Btail.coe.Walk
            (k4BridgeEndpointSubgraph Btail
              leftB₀ (zT : Btail.verts) a)
            (attachBridgeB a)
      | 0 => SimpleGraph.Walk.nil
      | 1 => stemLeftOneB₀
      | 2 => pRight
      | 3 => pThree
    have hattachBridge :
        forall a : Fin 4,
          G.Adj (attachBridgeB a : V)
            (Ktail.model.branchVertex (σ₀ a)) := by
      intro a
      fin_cases a
      · simpa [attachBridgeB, hattachB₀_zero] using
          hattachB₀_adj (0 : Fin 4)
      · simpa [attachBridgeB, attachOneB₀] using
          hattachB₀_adj (1 : Fin 4)
      · simpa [attachBridgeB, hattachB₀_two] using
          hattachB₀_adj (2 : Fin 4)
      · simpa [attachBridgeB, attachThreeB₀] using
          hattachB₀_adj (3 : Fin 4)
    have hstemBridgeB_path :
        forall a : Fin 4,
          (stemBridgeB a).IsPath := by
      intro a
      fin_cases a
      · change
          (SimpleGraph.Walk.nil :
            Btail.coe.Walk leftB₀ leftB₀).IsPath
        exact SimpleGraph.Walk.IsPath.mk' (by simp)
      · simpa [stemBridgeB] using
          hstemLeftOneB₀_path
      · simpa [stemBridgeB] using hpRight
      · simpa [stemBridgeB] using hpThree
    have hmem_nil_left_eq :
        forall {x : Btail.verts},
          x ∈
              (SimpleGraph.Walk.nil :
                Btail.coe.Walk leftB₀ leftB₀).support ->
            x = leftB₀ := by
      intro x hx
      exact SimpleGraph.Walk.mem_support_nil_iff.mp hx
    have hleftStem_ne_right :
        forall {x : Btail.verts},
          x ∈ stemLeftOneB₀.support ->
            x ≠ rightB₀ := by
      intro x hx hxr
      exact hrightB₀_not_stemLeftOne
        (by simpa [hxr] using hx)
    have hleftRightStem_common_false :
        forall {x : Btail.verts},
          x ∈ stemLeftOneB₀.support ->
            x ∈ stemRightThreeB₀.support ->
              x ≠ leftB₀ -> False := by
      intro x hx_left hx_right hx_ne_left
      have hx_ne_right : x ≠ rightB₀ :=
        hleftStem_ne_right hx_left
      have hxT_mem : x ∈ TBtail.verts :=
        Walk.support_subset_of_toSubgraph_le
          hstemLeftOneB₀_le_TB hx_left
      exact hno_common
        (hcommon_obstruction_recovered_on_p_T
          ⟨⟨x, hxT_mem⟩,
            hx_left, hx_ne_left,
            hx_right, hx_ne_right⟩)
    have hleftStem_bridge_false :
        forall {x : Btail.verts},
          x ∈ Walk.InternalVertices pBridge ->
            x ∈ stemLeftOneB₀.support ->
              x ≠ leftB₀ -> False := by
      intro x hx_bridge hx_left hx_ne_left
      have hx_p : x ∈ pB₀.support :=
        hbridge_support_pB hx_bridge.1
      have hx_ne_leftT :
          x ≠ (leftT₀ : Btail.verts) := by
        intro h
        exact hx_ne_left
          (h.trans hleftB₀_eq_leftT₀.symm)
      have hx_ne_rightB : x ≠ rightB₀ :=
        hleftStem_ne_right hx_left
      have hx_ne_rightT :
          x ≠ (rightT₀ : Btail.verts) := by
        intro h
        exact hx_ne_rightB
          (h.trans hrightB₀_eq_rightT₀.symm)
      have hxT_mem : x ∈ TBtail.verts :=
        Walk.support_subset_of_toSubgraph_le
          hpB₀_le_TB hx_p
      exact hno_left
        ⟨⟨x, hxT_mem⟩,
          ⟨hx_p, hx_ne_leftT, hx_ne_rightT⟩,
          by
            simpa [LeftObsT, stemLeftOneB₀] using
              hx_left,
          by
            simpa [leftB₀] using hx_ne_left⟩
    have hstemBridgeB_avoids :
        forall a : Fin 4, forall {x : Btail.verts},
          x ∈ (stemBridgeB a).support ->
            x ≠ k4BridgeEndpointSubgraph Btail
              leftB₀ (zT : Btail.verts) a ->
              x ≠ leftB₀ ∧
                x ≠ (zT : Btail.verts) := by
      intro a x hx hx_ne_start
      fin_cases a
      · have hx_eq : x = leftB₀ := by
          exact hmem_nil_left_eq
            (by simpa only [stemBridgeB] using hx)
        exact False.elim
          (hx_ne_start (by
            simp [k4BridgeEndpointSubgraph, hx_eq]))
      · refine ⟨?_, ?_⟩
        · exact hx_ne_start
        · intro hxz
          have hz_left :
              (zT : Btail.verts) ∈
                stemLeftOneB₀.support := by
            simpa [stemBridgeB, hxz] using hx
          exact hleftRightStem_common_false
            hz_left hz_right_stem hleft_ne_zB.symm
      · refine ⟨?_, ?_⟩
        · intro hxl
          exact hleft_not_pRight (by
            simpa [stemBridgeB, hxl] using hx)
        · exact hx_ne_start
      · refine ⟨?_, ?_⟩
        · intro hxl
          exact hleft_not_pThree (by
            simpa [stemBridgeB, hxl] using hx)
        · exact hx_ne_start
    have hbridgeStem_meet :
        forall a : Fin 4, forall {x : Btail.verts},
          x ∈ Walk.InternalVertices pBridge ->
            x ∈ (stemBridgeB a).support ->
              x ≠ k4BridgeEndpointSubgraph Btail
                leftB₀ (zT : Btail.verts) a ->
                False := by
      intro a x hx_bridge hx_stem hx_ne
      fin_cases a
      · have hx_eq : x = leftB₀ := by
          exact hmem_nil_left_eq
            (by simpa only [stemBridgeB] using hx_stem)
        exact hx_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · have hx_left :
            x ∈ stemLeftOneB₀.support := by
          simpa [stemBridgeB] using hx_stem
        have hx_ne_left : x ≠ leftB₀ := by
          simpa [k4BridgeEndpointSubgraph] using hx_ne
        exact hleftStem_bridge_false
          hx_bridge hx_left hx_ne_left
      · exact Set.disjoint_left.mp
          hbridge_right_disjoint hx_bridge
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hx_stem hx_ne)
      · exact Set.disjoint_left.mp
          hbridge_three_disjoint hx_bridge
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hx_stem hx_ne)
    have hstemStem_meet :
        forall {a b : Fin 4}, a ≠ b ->
          forall {x : Btail.verts},
            x ∈ (stemBridgeB a).support ->
              x ∈ (stemBridgeB b).support ->
                x ≠ k4BridgeEndpointSubgraph Btail
                  leftB₀ (zT : Btail.verts) a ->
                  x ≠ k4BridgeEndpointSubgraph Btail
                    leftB₀ (zT : Btail.verts) b ->
                    False := by
      intro a b hab x hxa hxb hxa_ne hxb_ne
      fin_cases a <;> fin_cases b
      · exact hab rfl
      · have hx_eq : x = leftB₀ := by
          exact hmem_nil_left_eq
            (by simpa only [stemBridgeB] using hxa)
        exact hxa_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · have hx_eq : x = leftB₀ := by
          exact hmem_nil_left_eq
            (by simpa only [stemBridgeB] using hxa)
        exact hxa_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · have hx_eq : x = leftB₀ := by
          exact hmem_nil_left_eq
            (by simpa only [stemBridgeB] using hxa)
        exact hxa_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · have hx_eq : x = leftB₀ := by
          exact hmem_nil_left_eq
            (by simpa only [stemBridgeB] using hxb)
        exact hxb_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · exact hab rfl
      · have hx_left :
            x ∈ stemLeftOneB₀.support := by
          simpa [stemBridgeB] using hxa
        have hx_right :
            x ∈ stemRightThreeB₀.support :=
          hright_support_stem
            (by simpa [stemBridgeB] using hxb)
        have hx_ne_left : x ≠ leftB₀ := by
          simpa [k4BridgeEndpointSubgraph] using hxa_ne
        exact hleftRightStem_common_false
          hx_left hx_right hx_ne_left
      · have hx_left :
            x ∈ stemLeftOneB₀.support := by
          simpa [stemBridgeB] using hxa
        have hx_right :
            x ∈ stemRightThreeB₀.support :=
          hthree_support_stem
            (by simpa [stemBridgeB] using hxb)
        have hx_ne_left : x ≠ leftB₀ := by
          simpa [k4BridgeEndpointSubgraph] using hxa_ne
        exact hleftRightStem_common_false
          hx_left hx_right hx_ne_left
      · have hx_eq : x = leftB₀ := by
          exact hmem_nil_left_eq
            (by simpa only [stemBridgeB] using hxb)
        exact hxb_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · have hx_right :
            x ∈ stemRightThreeB₀.support :=
          hright_support_stem
            (by simpa [stemBridgeB] using hxa)
        have hx_left :
            x ∈ stemLeftOneB₀.support := by
          simpa [stemBridgeB] using hxb
        have hx_ne_left : x ≠ leftB₀ := by
          simpa [k4BridgeEndpointSubgraph] using hxb_ne
        exact hleftRightStem_common_false
          hx_left hx_right hx_ne_left
      · exact hab rfl
      · exact Set.disjoint_left.mp hright_three_disjoint
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hxa hxa_ne)
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hxb hxb_ne)
      · have hx_eq : x = leftB₀ := by
          exact hmem_nil_left_eq
            (by simpa only [stemBridgeB] using hxb)
        exact hxb_ne (by
          simp [k4BridgeEndpointSubgraph, hx_eq])
      · have hx_right :
            x ∈ stemRightThreeB₀.support :=
          hthree_support_stem
            (by simpa [stemBridgeB] using hxa)
        have hx_left :
            x ∈ stemLeftOneB₀.support := by
          simpa [stemBridgeB] using hxb
        have hx_ne_left : x ≠ leftB₀ := by
          simpa [k4BridgeEndpointSubgraph] using hxb_ne
        exact hleftRightStem_common_false
          hx_left hx_right hx_ne_left
      · exact Set.disjoint_left.mp
          (Disjoint.symm hright_three_disjoint)
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hxa hxa_ne)
          (by
            simpa [stemBridgeB,
              k4BridgeEndpointSubgraph] using
              And.intro hxb hxb_ne)
      · exact hab rfl
    exact
      Ktail.carrier_bridge_attachment_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
        σ₀ Btail
        (by
          intro i hmem
          exact hKtail_branch_not_first i
            (hBtail_le.left hmem))
        (by
          intro i j hij z hz hmem
          exact hKtail_internal_not_first hij hz
            (hBtail_le.left hmem))
        hleft_ne_zV pBridge hpBridge
        attachBridgeB hattachBridge
        stemBridgeB hstemBridgeB_path
        hstemBridgeB_avoids hbridgeStem_meet
        hstemStem_meet
  have hsimultaneous_equal_gives_common :
      forall {zLeftT zRightT : TBtail.verts},
        (zLeftT : Btail.verts) ∈
            Walk.InternalVertices pB₀ ->
          (zLeftT : Btail.verts) ∈
              stemLeftOneB₀.support ->
            (zRightT : Btail.verts) ∈
                stemRightThreeB₀.support ->
              (zLeftT : Btail.verts) =
                  (zRightT : Btail.verts) ->
                CommonObsT := by
    intro zLeftT zRightT hzLeft_internal
      hzLeft_stem hzRight_stem heq
    exact ⟨zLeftT, hzLeft_internal,
      by
        simpa [CommonObsT, stemLeftOneB₀] using
          hzLeft_stem,
      by
        simpa [CommonObsT, stemRightThreeB₀, heq]
          using hzRight_stem⟩
  have hcrossed_simultaneous_obstruction_gives_common :
      forall {zLeftT zRightT : TBtail.verts},
        forall (hzLeft_internal :
          (zLeftT : Btail.verts) ∈
            Walk.InternalVertices pB₀),
          (zLeftT : Btail.verts) ∈
              stemLeftOneB₀.support ->
            forall (hzRight_internal :
              (zRightT : Btail.verts) ∈
                Walk.InternalVertices pB₀),
              (zRightT : Btail.verts) ∈
                  stemRightThreeB₀.support ->
                (zRightT : Btail.verts) ∈
                  (pB₀.takeUntil
                    (zLeftT : Btail.verts)
                    hzLeft_internal.1).support ->
                  CommonObsT := by
    intro zLeftT zRightT hzLeft_internal
      hzLeft_stem hzRight_internal hzRight_stem
      hright_before
    have hzRight_left_prefix :
        (zRightT : Btail.verts) ∈
          (stemLeftOneB₀.takeUntil
            (zLeftT : Btail.verts)
            hzLeft_stem).support :=
      Subgraph.tree_mem_takeUntil_of_mem_takeUntil_of_isPath
        (G := Btail.coe) (T := TBtail)
        (p := pB₀) (q := stemLeftOneB₀)
        hTBtail_tree hpB₀_le_TB
        hstemLeftOneB₀_le_TB hpB₀
        hstemLeftOneB₀_path
        hzLeft_internal.1 hzLeft_stem
        hright_before
    have hzRight_left_stem :
        (zRightT : Btail.verts) ∈
          stemLeftOneB₀.support :=
      SimpleGraph.Walk.support_takeUntil_subset
        stemLeftOneB₀ hzLeft_stem
        hzRight_left_prefix
    exact ⟨zRightT, hzRight_internal,
      by
        simpa [CommonObsT, stemLeftOneB₀] using
          hzRight_left_stem,
      by
        simpa [CommonObsT, stemRightThreeB₀] using
          hzRight_stem⟩
  have hselected_simultaneous_ordered_or_common :
      LeftObsT ->
      RightObsT ->
        (Exists fun zLeftT : TBtail.verts =>
          Exists fun zRightT : TBtail.verts =>
            Exists fun hzLeft_internal :
              (zLeftT : Btail.verts) ∈
                Walk.InternalVertices pB₀ =>
            Exists fun hzRight_internal :
              (zRightT : Btail.verts) ∈
                Walk.InternalVertices pB₀ =>
              (zLeftT : Btail.verts) ∈
                  stemLeftOneB₀.support ∧
                (zLeftT : Btail.verts) ≠ leftB₀ ∧
                  (zRightT : Btail.verts) ∈
                    stemRightThreeB₀.support ∧
                    (zRightT : Btail.verts) ≠
                      rightB₀ ∧
                      (zLeftT : Btail.verts) ≠
                        (zRightT : Btail.verts) ∧
                        (zLeftT : Btail.verts) ∈
                          (pB₀.takeUntil
                            (zRightT : Btail.verts)
                            hzRight_internal.1).support) ∨
          CommonObsT := by
    intro hleft hright
    rcases hleft_first_common_split hleft with
      ⟨zLeftT, _pBridgeLeft, _pLeft, _pOne,
        _hpBridgeLeft, _hpLeft, _hpOne,
        _hpBridgeLeft_le, _hpLeft_le, _hpOne_le,
        hzLeft_stem, hzLeft_internal,
        _hbridgeLeft_support_pB,
        _hleft_support_stem, _hone_support_stem,
        _hright_not_pLeft, _hright_not_pOne,
        _hbridge_left_disjoint,
        _hbridge_one_disjoint,
        _hleft_one_disjoint⟩
    rcases hright_first_common_split hright with
      ⟨zRightT, _pBridgeRight, _pRight, _pThree,
        _hpBridgeRight, _hpRight, _hpThree,
        _hpBridgeRight_le, _hpRight_le, _hpThree_le,
        hzRight_stem, hzRight_internal,
        _hbridgeRight_support_pB,
        _hright_support_stem, _hthree_support_stem,
        _hleft_not_pRight, _hleft_not_pThree,
        _hbridge_right_disjoint,
        _hbridge_three_disjoint,
        _hright_three_disjoint⟩
    have hzLeft_ne_left :
        (zLeftT : Btail.verts) ≠ leftB₀ := by
      intro h
      exact hzLeft_internal.2.1
        (h.trans hleftB₀_eq_leftT₀)
    have hzRight_ne_right :
        (zRightT : Btail.verts) ≠ rightB₀ := by
      intro h
      exact hzRight_internal.2.2
        (h.trans hrightB₀_eq_rightT₀)
    by_cases heq :
        (zLeftT : Btail.verts) =
          (zRightT : Btail.verts)
    · exact Or.inr
        (hsimultaneous_equal_gives_common
          hzLeft_internal hzLeft_stem
          hzRight_stem heq)
    · rcases
        Walk.mem_support_takeUntil_or_mem_support_takeUntil
          hzLeft_internal.1 hzRight_internal.1 with
        hleft_before | hright_before
      · exact Or.inl
          ⟨zLeftT, zRightT,
            hzLeft_internal, hzRight_internal,
            hzLeft_stem, hzLeft_ne_left,
            hzRight_stem, hzRight_ne_right,
            heq, hleft_before⟩
      · exact Or.inr
          (hcrossed_simultaneous_obstruction_gives_common
            hzLeft_internal hzLeft_stem
            hzRight_internal hzRight_stem
            hright_before)
  have hno_common_forbids_side_stem_overlap :
      Not CommonObsT ->
        forall {x : Btail.verts},
          x ∈ stemLeftOneB₀.support ->
            x ≠ leftB₀ ->
              x ∈ stemRightThreeB₀.support ->
                x ≠ rightB₀ ->
                  False := by
    intro hno_common x hx_left hx_ne_left
      hx_right hx_ne_right
    have hxT_mem : x ∈ TBtail.verts :=
      Walk.support_subset_of_toSubgraph_le
        hstemLeftOneB₀_le_TB hx_left
    exact hno_common
      (hcommon_obstruction_recovered_on_p_T
        ⟨⟨x, hxT_mem⟩,
          hx_left, hx_ne_left,
          hx_right, hx_ne_right⟩)
  have hpB_internal_split_paths :
      forall zT : TBtail.verts,
        (zT : Btail.verts) ∈
            Walk.InternalVertices pB₀ ->
          Exists fun pLeft :
            Btail.coe.Walk
              (zT : Btail.verts) leftB₀ =>
          Exists fun pRight :
            Btail.coe.Walk
              (zT : Btail.verts) rightB₀ =>
          pLeft.IsPath ∧ pRight.IsPath ∧
            pLeft.toSubgraph ≤ TBtail ∧
              pRight.toSubgraph ≤ TBtail ∧
                (forall {x : Btail.verts},
                  x ∈ pLeft.support ->
                    x ∈ pB₀.support) ∧
                  (forall {x : Btail.verts},
                    x ∈ pRight.support ->
                      x ∈ pB₀.support) ∧
                    rightB₀ ∉ pLeft.support ∧
                      leftB₀ ∉ pRight.support := by
    intro zT hz_internal
    let S := internalSplit hpB₀ hpB₀_le_TB zT hz_internal
    exact ⟨S.left, S.right, S.left_isPath, S.right_isPath,
      S.left_le, S.right_le, S.left_support, S.right_support,
      S.right_not_left, S.left_not_right⟩
  have hstemLeftOne_suffix_paths :
      forall zT : TBtail.verts,
        (zT : Btail.verts) ∈
            stemLeftOneB₀.support ->
          Exists fun pOne :
            Btail.coe.Walk
              (zT : Btail.verts) attachOneB₀ =>
          pOne.IsPath ∧ pOne.toSubgraph ≤ TBtail ∧
            (forall {x : Btail.verts},
              x ∈ pOne.support ->
                x ∈ stemLeftOneB₀.support) ∧
              rightB₀ ∉ pOne.support := by
    intro zT hz
    let S := suffix hstemLeftOneB₀_path hstemLeftOneB₀_le_TB zT hz
    exact ⟨S.path, S.isPath, S.le, S.support,
      fun h => hrightB₀_not_stemLeftOne (S.support h)⟩
  have hstemRightThree_suffix_paths :
      forall zT : TBtail.verts,
        (zT : Btail.verts) ∈
            stemRightThreeB₀.support ->
          Exists fun pThree :
            Btail.coe.Walk
              (zT : Btail.verts) attachThreeB₀ =>
          pThree.IsPath ∧ pThree.toSubgraph ≤ TBtail ∧
            (forall {x : Btail.verts},
              x ∈ pThree.support ->
                x ∈ stemRightThreeB₀.support) ∧
              leftB₀ ∉ pThree.support := by
    intro zT hz
    let S := suffix hstemRightThreeB₀_path hstemRightThreeB₀_le_TB zT hz
    exact ⟨S.path, S.isPath, S.le, S.support,
      fun h => hleftB₀_not_stemRightThree (S.support h)⟩
  have hordered_simultaneous_split :
      forall {zLeftT zRightT : TBtail.verts},
        forall (hzLeft_internal :
          (zLeftT : Btail.verts) ∈
            Walk.InternalVertices pB₀),
          (zLeftT : Btail.verts) ∈
              stemLeftOneB₀.support ->
            forall (hzRight_internal :
              (zRightT : Btail.verts) ∈
                Walk.InternalVertices pB₀),
              (zRightT : Btail.verts) ∈
                  stemRightThreeB₀.support ->
                (zLeftT : Btail.verts) ∈
                  (pB₀.takeUntil
                    (zRightT : Btail.verts)
                    hzRight_internal.1).support ->
                  Exists fun pBridge :
                    Btail.coe.Walk
                      (zLeftT : Btail.verts)
                      (zRightT : Btail.verts) =>
                  Exists fun pLeft :
                    Btail.coe.Walk
                      (zLeftT : Btail.verts)
                      leftB₀ =>
                  Exists fun pOne :
                    Btail.coe.Walk
                      (zLeftT : Btail.verts)
                      attachOneB₀ =>
                  Exists fun pRight :
                    Btail.coe.Walk
                      (zRightT : Btail.verts)
                      rightB₀ =>
                  Exists fun pThree :
                    Btail.coe.Walk
                      (zRightT : Btail.verts)
                      attachThreeB₀ =>
                    pBridge.IsPath ∧
                      pLeft.IsPath ∧ pOne.IsPath ∧
                        pRight.IsPath ∧ pThree.IsPath ∧
                          pBridge.toSubgraph ≤ TBtail ∧
                            pLeft.toSubgraph ≤ TBtail ∧
                              pOne.toSubgraph ≤ TBtail ∧
                                pRight.toSubgraph ≤ TBtail ∧
                                  pThree.toSubgraph ≤ TBtail ∧
                                    (forall {x : Btail.verts},
                                      x ∈ pBridge.support ->
                                        x ∈ pB₀.support) ∧
                                      (forall {x : Btail.verts},
                                        x ∈ pLeft.support ->
                                          x ∈ pB₀.support) ∧
                                        (forall {x : Btail.verts},
                                          x ∈ pOne.support ->
                                            x ∈ stemLeftOneB₀.support) ∧
                                          (forall {x : Btail.verts},
                                            x ∈ pRight.support ->
                                              x ∈ pB₀.support) ∧
                                            (forall {x : Btail.verts},
                                              x ∈ pThree.support ->
                                                x ∈ stemRightThreeB₀.support) ∧
                                              rightB₀ ∉ pLeft.support ∧
                                                rightB₀ ∉ pOne.support ∧
                                                  leftB₀ ∉ pRight.support ∧
                                                    leftB₀ ∉ pThree.support := by
    intro zLeftT zRightT hzLeft_internal
      hzLeft_stem hzRight_internal hzRight_stem
      hzLeft_before_right
    let pBridge :
        Btail.coe.Walk
          (zLeftT : Btail.verts)
          (zRightT : Btail.verts) :=
      (pB₀.takeUntil (zRightT : Btail.verts)
        hzRight_internal.1).dropUntil
          (zLeftT : Btail.verts)
          hzLeft_before_right
    have hpBridge : pBridge.IsPath := by
      simpa [pBridge] using
        (hpB₀.takeUntil
          hzRight_internal.1).dropUntil
          hzLeft_before_right
    have hpBridge_le :
        pBridge.toSubgraph ≤ TBtail := by
      simpa [pBridge] using
        Walk.toSubgraph_dropUntil_le_of_le
          (H := TBtail)
          (Walk.toSubgraph_takeUntil_le_of_le
            hpB₀_le_TB hzRight_internal.1)
          hzLeft_before_right
    have hbridge_support_pB :
        forall {x : Btail.verts},
          x ∈ pBridge.support ->
            x ∈ pB₀.support := by
      intro x hx
      have hx_prefix :
          x ∈
            (pB₀.takeUntil
              (zRightT : Btail.verts)
              hzRight_internal.1).support :=
        SimpleGraph.Walk.support_dropUntil_subset
          (pB₀.takeUntil
            (zRightT : Btail.verts)
            hzRight_internal.1)
          hzLeft_before_right
          (by simpa [pBridge] using hx)
      exact SimpleGraph.Walk.support_takeUntil_subset
        pB₀ hzRight_internal.1 hx_prefix
    rcases hpB_internal_split_paths zLeftT
        hzLeft_internal with
      ⟨pLeft, _pRightFromLeft, hpLeft,
        _hpRightFromLeft, hpLeft_le,
        _hpRightFromLeft_le, hleft_support_pB,
        _hrightFromLeft_support_pB,
        hright_not_pLeft,
        _hleft_not_pRightFromLeft⟩
    rcases hstemLeftOne_suffix_paths zLeftT
        hzLeft_stem with
      ⟨pOne, hpOne, hpOne_le,
        hone_support_stem, hright_not_pOne⟩
    rcases hpB_internal_split_paths zRightT
        hzRight_internal with
      ⟨_pLeftFromRight, pRight,
        _hpLeftFromRight, hpRight,
        _hpLeftFromRight_le, hpRight_le,
        _hleftFromRight_support_pB,
        hright_support_pB,
        _hright_not_pLeftFromRight,
        hleft_not_pRight⟩
    rcases hstemRightThree_suffix_paths zRightT
        hzRight_stem with
      ⟨pThree, hpThree, hpThree_le,
        hthree_support_stem, hleft_not_pThree⟩
    exact ⟨pBridge, pLeft, pOne, pRight, pThree,
      hpBridge, hpLeft, hpOne, hpRight, hpThree,
      hpBridge_le, hpLeft_le, hpOne_le,
      hpRight_le, hpThree_le, hbridge_support_pB,
      hleft_support_pB, hone_support_stem,
      hright_support_pB, hthree_support_stem,
      hright_not_pLeft, hright_not_pOne,
      hleft_not_pRight, hleft_not_pThree⟩
  have hsimultaneous_bridge_conclusion :
      LeftObsT ->
      RightObsT ->
      Not CommonObsT ->
        NearHajosStrengtheningConclusion G := by
    intro hleft hright hno_common
    rcases hleft_first_common_split hleft with
      ⟨zLeftT, pBridgeLeft, pLeft, pOne,
        hpBridgeLeft, hpLeft, hpOne,
        hpBridgeLeft_le, _hpLeft_le, _hpOne_le,
        hzLeft_stem, hzLeft_internal,
        _hbridgeLeft_support_pB,
        hleft_support_stem, hone_support_stem,
        hright_not_pLeft, hright_not_pOne,
        hbridge_left_disjoint,
        hbridge_one_disjoint,
        hleft_one_disjoint⟩
    rcases hright_first_common_split hright with
      ⟨zRightT, pBridgeRight, pRight, pThree,
        hpBridgeRight, hpRight, hpThree,
        hpBridgeRight_le, _hpRight_le,
        _hpThree_le, hzRight_stem,
        hzRight_internal,
        _hbridgeRight_support_pB,
        hright_support_stem, hthree_support_stem,
        hleft_not_pRight, hleft_not_pThree,
        hbridge_right_disjoint,
        hbridge_three_disjoint,
        hright_three_disjoint⟩
    have hzLeft_ne_leftB :
        (zLeftT : Btail.verts) ≠ leftB₀ := by
      intro h
      exact hzLeft_internal.2.1
        (h.trans hleftB₀_eq_leftT₀)
    have hzLeft_ne_rightB :
        (zLeftT : Btail.verts) ≠ rightB₀ := by
      intro h
      exact hzLeft_internal.2.2
        (h.trans hrightB₀_eq_rightT₀)
    have hzRight_ne_leftB :
        (zRightT : Btail.verts) ≠ leftB₀ := by
      intro h
      exact hzRight_internal.2.1
        (h.trans hleftB₀_eq_leftT₀)
    have hzRight_ne_rightB :
        (zRightT : Btail.verts) ≠ rightB₀ := by
      intro h
      exact hzRight_internal.2.2
        (h.trans hrightB₀_eq_rightT₀)
    have hleftRightStem_common_false :
        forall {x : Btail.verts},
          x ∈ stemLeftOneB₀.support ->
            x ≠ leftB₀ ->
              x ∈ stemRightThreeB₀.support ->
                x ≠ rightB₀ ->
                  False := by
      intro x hx_left hx_ne_left
        hx_right hx_ne_right
      exact hno_common_forbids_side_stem_overlap
        hno_common hx_left hx_ne_left
        hx_right hx_ne_right
    by_cases heq :
        (zLeftT : Btail.verts) =
          (zRightT : Btail.verts)
    · exact False.elim
        (hno_common
          (hsimultaneous_equal_gives_common
            hzLeft_internal hzLeft_stem
            hzRight_stem heq))
    · rcases
        Walk.mem_support_takeUntil_or_mem_support_takeUntil
          hzLeft_internal.1 hzRight_internal.1 with
        hleft_before | hright_before
      · let pBridge :
          Btail.coe.Walk
            (zLeftT : Btail.verts)
            (zRightT : Btail.verts) :=
          (pB₀.takeUntil
            (zRightT : Btail.verts)
            hzRight_internal.1).dropUntil
              (zLeftT : Btail.verts)
              hleft_before
        have hpBridge : pBridge.IsPath := by
          simpa [pBridge] using
            (hpB₀.takeUntil
              hzRight_internal.1).dropUntil
              hleft_before
        let pSuffix :
            Btail.coe.Walk
              (zLeftT : Btail.verts) rightB₀ :=
          (pB₀.dropUntil
            (zLeftT : Btail.verts)
            hzLeft_internal.1).copy rfl
              hrightB₀_eq_rightT₀.symm
        have hpSuffix : pSuffix.IsPath := by
          simpa [pSuffix] using
            (SimpleGraph.Walk.isPath_copy
              (pB₀.dropUntil
                (zLeftT : Btail.verts)
                hzLeft_internal.1)
              rfl hrightB₀_eq_rightT₀.symm).mpr
              (hpB₀.dropUntil
                hzLeft_internal.1)
        have hpSuffix_le :
            pSuffix.toSubgraph ≤ TBtail := by
          simpa [pSuffix] using
            Walk.toSubgraph_dropUntil_le_of_le
              (H := TBtail) hpB₀_le_TB
              hzLeft_internal.1
        let pPrefix :
            Btail.coe.Walk leftB₀
              (zRightT : Btail.verts) :=
          (pB₀.takeUntil
            (zRightT : Btail.verts)
            hzRight_internal.1).copy
              hleftB₀_eq_leftT₀.symm rfl
        have hpPrefix : pPrefix.IsPath := by
          simpa [pPrefix] using
            (SimpleGraph.Walk.isPath_copy
              (pB₀.takeUntil
                (zRightT : Btail.verts)
                hzRight_internal.1)
              hleftB₀_eq_leftT₀.symm rfl).mpr
              (hpB₀.takeUntil
                hzRight_internal.1)
        have hpPrefix_le :
            pPrefix.toSubgraph ≤ TBtail := by
          simpa [pPrefix] using
            Walk.toSubgraph_takeUntil_le_of_le
              (H := TBtail) hpB₀_le_TB
              hzRight_internal.1
        have hbridge_internal_left :
            Walk.InternalVertices pBridge ⊆
              Walk.InternalVertices pBridgeLeft := by
          intro x hx_bridge
          have hx_middle :
              x ∈ Walk.InternalVertices
                ((pB₀.takeUntil
                  (zRightT : Btail.verts)
                  hzRight_internal.1).dropUntil
                    (zLeftT : Btail.verts)
                    hleft_before) := by
            simpa [pBridge] using hx_bridge
          have hx_suffix_internal :
              x ∈ Walk.InternalVertices
                (pB₀.dropUntil
                  (zLeftT : Btail.verts)
                  hzLeft_internal.1) :=
            Walk.IsPath.internalVertices_dropUntil_takeUntil_subset_dropUntil
              hpB₀ hzRight_internal hleft_before
              hx_middle
          have hx_bridgeLeft_support :
              x ∈ pBridgeLeft.support := by
            exact
              (Subgraph.tree_mem_support_iff_of_isPath_coe
                hTBtail_tree hpBridgeLeft_le hpSuffix_le
                hpBridgeLeft hpSuffix (x := x)).mpr
              (by simpa [pSuffix] using
                hx_suffix_internal.1)
          refine ⟨hx_bridgeLeft_support, ?_, ?_⟩
          · exact hx_suffix_internal.2.1
          · intro hx_eq_right
            exact hx_suffix_internal.2.2
              (hx_eq_right.trans
                hrightB₀_eq_rightT₀)
        have hbridge_internal_right :
            Walk.InternalVertices pBridge ⊆
              Walk.InternalVertices pBridgeRight := by
          intro x hx_bridge
          have hx_middle :
              x ∈ Walk.InternalVertices
                ((pB₀.takeUntil
                  (zRightT : Btail.verts)
                  hzRight_internal.1).dropUntil
                    (zLeftT : Btail.verts)
                    hleft_before) := by
            simpa [pBridge] using hx_bridge
          have hx_prefix_internal :
              x ∈ Walk.InternalVertices
                (pB₀.takeUntil
                  (zRightT : Btail.verts)
                  hzRight_internal.1) :=
            Walk.IsPath.internalVertices_dropUntil_takeUntil_subset_takeUntil
              hpB₀ hzLeft_internal
              hzRight_internal.1
              hleft_before hx_middle
          have hx_bridgeRight_support :
              x ∈ pBridgeRight.support := by
            exact
              (Subgraph.tree_mem_support_iff_of_isPath_coe
                hTBtail_tree hpBridgeRight_le hpPrefix_le
                hpBridgeRight hpPrefix (x := x)).mpr
              (by simpa [pPrefix] using
                hx_prefix_internal.1)
          refine ⟨hx_bridgeRight_support, ?_, ?_⟩
          · intro hx_eq_left
            exact hx_prefix_internal.2.1
              (hx_eq_left.trans
                hleftB₀_eq_leftT₀)
          · exact hx_prefix_internal.2.2
        have hleft_ne_rightV :
            ((zLeftT : Btail.verts) : V) ≠
              ((zRightT : Btail.verts) : V) := by
          intro h
          exact heq (Subtype.ext h)
        let attachBridgeB : Fin 4 -> Btail.verts
          | 0 => leftB₀
          | 1 => attachOneB₀
          | 2 => rightB₀
          | 3 => attachThreeB₀
        let stemBridgeB :
            forall a : Fin 4,
              Btail.coe.Walk
                (k4BridgeEndpointSubgraph Btail
                  (zLeftT : Btail.verts)
                  (zRightT : Btail.verts) a)
                (attachBridgeB a)
          | 0 => pLeft
          | 1 => pOne
          | 2 => pRight
          | 3 => pThree
        have hattachBridge :
            forall a : Fin 4,
              G.Adj (attachBridgeB a : V)
                (Ktail.model.branchVertex
                  (σ₀ a)) := by
          intro a
          fin_cases a
          · simpa [attachBridgeB, hattachB₀_zero] using
              hattachB₀_adj (0 : Fin 4)
          · simpa [attachBridgeB, attachOneB₀] using
              hattachB₀_adj (1 : Fin 4)
          · simpa [attachBridgeB, hattachB₀_two] using
              hattachB₀_adj (2 : Fin 4)
          · simpa [attachBridgeB, attachThreeB₀] using
              hattachB₀_adj (3 : Fin 4)
        have hstemBridgeB_path :
            forall a : Fin 4,
              (stemBridgeB a).IsPath := by
          intro a
          fin_cases a
          · simpa [stemBridgeB] using hpLeft
          · simpa [stemBridgeB] using hpOne
          · simpa [stemBridgeB] using hpRight
          · simpa [stemBridgeB] using hpThree
        have hstemBridgeB_avoids :
            forall a : Fin 4, forall {x : Btail.verts},
              x ∈ (stemBridgeB a).support ->
                x ≠ k4BridgeEndpointSubgraph Btail
                  (zLeftT : Btail.verts)
                  (zRightT : Btail.verts) a ->
                  x ≠ (zLeftT : Btail.verts) ∧
                    x ≠ (zRightT : Btail.verts) := by
          intro a x hx hx_ne_start
          fin_cases a
          · refine ⟨?_, ?_⟩
            · simpa [k4BridgeEndpointSubgraph] using
                hx_ne_start
            · intro hxz
              have hx_left :
                  x ∈ stemLeftOneB₀.support :=
                hleft_support_stem
                  (by simpa [stemBridgeB] using hx)
              have hzRight_left :
                  (zRightT : Btail.verts) ∈
                    stemLeftOneB₀.support := by
                simpa [hxz] using hx_left
              exact hleftRightStem_common_false
                hzRight_left hzRight_ne_leftB
                hzRight_stem hzRight_ne_rightB
          · refine ⟨?_, ?_⟩
            · simpa [k4BridgeEndpointSubgraph] using
                hx_ne_start
            · intro hxz
              have hx_left :
                  x ∈ stemLeftOneB₀.support :=
                hone_support_stem
                  (by simpa [stemBridgeB] using hx)
              have hzRight_left :
                  (zRightT : Btail.verts) ∈
                    stemLeftOneB₀.support := by
                simpa [hxz] using hx_left
              exact hleftRightStem_common_false
                hzRight_left hzRight_ne_leftB
                hzRight_stem hzRight_ne_rightB
          · refine ⟨?_, ?_⟩
            · intro hxz
              have hx_right :
                  x ∈ stemRightThreeB₀.support :=
                hright_support_stem
                  (by simpa [stemBridgeB] using hx)
              have hzLeft_right :
                  (zLeftT : Btail.verts) ∈
                    stemRightThreeB₀.support := by
                simpa [hxz] using hx_right
              exact hleftRightStem_common_false
                hzLeft_stem hzLeft_ne_leftB
                hzLeft_right hzLeft_ne_rightB
            · simpa [k4BridgeEndpointSubgraph] using
                hx_ne_start
          · refine ⟨?_, ?_⟩
            · intro hxz
              have hx_right :
                  x ∈ stemRightThreeB₀.support :=
                hthree_support_stem
                  (by simpa [stemBridgeB] using hx)
              have hzLeft_right :
                  (zLeftT : Btail.verts) ∈
                    stemRightThreeB₀.support := by
                simpa [hxz] using hx_right
              exact hleftRightStem_common_false
                hzLeft_stem hzLeft_ne_leftB
                hzLeft_right hzLeft_ne_rightB
            · simpa [k4BridgeEndpointSubgraph] using
                hx_ne_start
        have hbridgeStem_meet :
            forall a : Fin 4, forall {x : Btail.verts},
              x ∈ Walk.InternalVertices pBridge ->
                x ∈ (stemBridgeB a).support ->
                  x ≠ k4BridgeEndpointSubgraph Btail
                    (zLeftT : Btail.verts)
                    (zRightT : Btail.verts) a ->
                    False := by
          intro a x hx_bridge hx_stem hx_ne
          fin_cases a
          · exact Set.disjoint_left.mp
              hbridge_left_disjoint
              (hbridge_internal_left hx_bridge)
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hx_stem hx_ne)
          · exact Set.disjoint_left.mp
              hbridge_one_disjoint
              (hbridge_internal_left hx_bridge)
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hx_stem hx_ne)
          · exact Set.disjoint_left.mp
              hbridge_right_disjoint
              (hbridge_internal_right hx_bridge)
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hx_stem hx_ne)
          · exact Set.disjoint_left.mp
              hbridge_three_disjoint
              (hbridge_internal_right hx_bridge)
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hx_stem hx_ne)
        have hstemStem_meet :
            forall {a b : Fin 4}, a ≠ b ->
              forall {x : Btail.verts},
                x ∈ (stemBridgeB a).support ->
                  x ∈ (stemBridgeB b).support ->
                    x ≠ k4BridgeEndpointSubgraph Btail
                      (zLeftT : Btail.verts)
                      (zRightT : Btail.verts) a ->
                      x ≠ k4BridgeEndpointSubgraph Btail
                        (zLeftT : Btail.verts)
                        (zRightT : Btail.verts) b ->
                        False := by
          intro a b hab x hxa hxb hxa_ne hxb_ne
          fin_cases a <;> fin_cases b
          · exact hab rfl
          · exact Set.disjoint_left.mp
              hleft_one_disjoint
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hxa hxa_ne)
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hxb hxb_ne)
          · have hx_left :
                x ∈ stemLeftOneB₀.support :=
              hleft_support_stem
                (by simpa [stemBridgeB] using hxa)
            have hx_right :
                x ∈ stemRightThreeB₀.support :=
              hright_support_stem
                (by simpa [stemBridgeB] using hxb)
            have hx_ne_left : x ≠ leftB₀ := by
              intro hx_eq
              exact hleft_not_pRight (by
                simpa [stemBridgeB, hx_eq] using hxb)
            have hx_ne_right : x ≠ rightB₀ := by
              intro hx_eq
              exact hright_not_pLeft (by
                simpa [stemBridgeB, hx_eq] using hxa)
            exact hleftRightStem_common_false
              hx_left hx_ne_left hx_right hx_ne_right
          · have hx_left :
                x ∈ stemLeftOneB₀.support :=
              hleft_support_stem
                (by simpa [stemBridgeB] using hxa)
            have hx_right :
                x ∈ stemRightThreeB₀.support :=
              hthree_support_stem
                (by simpa [stemBridgeB] using hxb)
            have hx_ne_left : x ≠ leftB₀ := by
              intro hx_eq
              exact hleft_not_pThree (by
                simpa [stemBridgeB, hx_eq] using hxb)
            have hx_ne_right : x ≠ rightB₀ := by
              intro hx_eq
              exact hright_not_pLeft (by
                simpa [stemBridgeB, hx_eq] using hxa)
            exact hleftRightStem_common_false
              hx_left hx_ne_left hx_right hx_ne_right
          · exact Set.disjoint_left.mp
              (Disjoint.symm hleft_one_disjoint)
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hxa hxa_ne)
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hxb hxb_ne)
          · exact hab rfl
          · have hx_left :
                x ∈ stemLeftOneB₀.support :=
              hone_support_stem
                (by simpa [stemBridgeB] using hxa)
            have hx_right :
                x ∈ stemRightThreeB₀.support :=
              hright_support_stem
                (by simpa [stemBridgeB] using hxb)
            have hx_ne_left : x ≠ leftB₀ := by
              intro hx_eq
              exact hleft_not_pRight (by
                simpa [stemBridgeB, hx_eq] using hxb)
            have hx_ne_right : x ≠ rightB₀ := by
              intro hx_eq
              exact hright_not_pOne (by
                simpa [stemBridgeB, hx_eq] using hxa)
            exact hleftRightStem_common_false
              hx_left hx_ne_left hx_right hx_ne_right
          · have hx_left :
                x ∈ stemLeftOneB₀.support :=
              hone_support_stem
                (by simpa [stemBridgeB] using hxa)
            have hx_right :
                x ∈ stemRightThreeB₀.support :=
              hthree_support_stem
                (by simpa [stemBridgeB] using hxb)
            have hx_ne_left : x ≠ leftB₀ := by
              intro hx_eq
              exact hleft_not_pThree (by
                simpa [stemBridgeB, hx_eq] using hxb)
            have hx_ne_right : x ≠ rightB₀ := by
              intro hx_eq
              exact hright_not_pOne (by
                simpa [stemBridgeB, hx_eq] using hxa)
            exact hleftRightStem_common_false
              hx_left hx_ne_left hx_right hx_ne_right
          · have hx_left :
                x ∈ stemLeftOneB₀.support :=
              hleft_support_stem
                (by simpa [stemBridgeB] using hxb)
            have hx_right :
                x ∈ stemRightThreeB₀.support :=
              hright_support_stem
                (by simpa [stemBridgeB] using hxa)
            have hx_ne_left : x ≠ leftB₀ := by
              intro hx_eq
              exact hleft_not_pRight (by
                simpa [stemBridgeB, hx_eq] using hxa)
            have hx_ne_right : x ≠ rightB₀ := by
              intro hx_eq
              exact hright_not_pLeft (by
                simpa [stemBridgeB, hx_eq] using hxb)
            exact hleftRightStem_common_false
              hx_left hx_ne_left hx_right hx_ne_right
          · have hx_left :
                x ∈ stemLeftOneB₀.support :=
              hone_support_stem
                (by simpa [stemBridgeB] using hxb)
            have hx_right :
                x ∈ stemRightThreeB₀.support :=
              hright_support_stem
                (by simpa [stemBridgeB] using hxa)
            have hx_ne_left : x ≠ leftB₀ := by
              intro hx_eq
              exact hleft_not_pRight (by
                simpa [stemBridgeB, hx_eq] using hxa)
            have hx_ne_right : x ≠ rightB₀ := by
              intro hx_eq
              exact hright_not_pOne (by
                simpa [stemBridgeB, hx_eq] using hxb)
            exact hleftRightStem_common_false
              hx_left hx_ne_left hx_right hx_ne_right
          · exact hab rfl
          · exact Set.disjoint_left.mp
              hright_three_disjoint
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hxa hxa_ne)
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hxb hxb_ne)
          · have hx_left :
                x ∈ stemLeftOneB₀.support :=
              hleft_support_stem
                (by simpa [stemBridgeB] using hxb)
            have hx_right :
                x ∈ stemRightThreeB₀.support :=
              hthree_support_stem
                (by simpa [stemBridgeB] using hxa)
            have hx_ne_left : x ≠ leftB₀ := by
              intro hx_eq
              exact hleft_not_pThree (by
                simpa [stemBridgeB, hx_eq] using hxa)
            have hx_ne_right : x ≠ rightB₀ := by
              intro hx_eq
              exact hright_not_pLeft (by
                simpa [stemBridgeB, hx_eq] using hxb)
            exact hleftRightStem_common_false
              hx_left hx_ne_left hx_right hx_ne_right
          · have hx_left :
                x ∈ stemLeftOneB₀.support :=
              hone_support_stem
                (by simpa [stemBridgeB] using hxb)
            have hx_right :
                x ∈ stemRightThreeB₀.support :=
              hthree_support_stem
                (by simpa [stemBridgeB] using hxa)
            have hx_ne_left : x ≠ leftB₀ := by
              intro hx_eq
              exact hleft_not_pThree (by
                simpa [stemBridgeB, hx_eq] using hxa)
            have hx_ne_right : x ≠ rightB₀ := by
              intro hx_eq
              exact hright_not_pOne (by
                simpa [stemBridgeB, hx_eq] using hxb)
            exact hleftRightStem_common_false
              hx_left hx_ne_left hx_right hx_ne_right
          · exact Set.disjoint_left.mp
              (Disjoint.symm hright_three_disjoint)
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hxa hxa_ne)
              (by
                simpa [stemBridgeB,
                  k4BridgeEndpointSubgraph] using
                  And.intro hxb hxb_ne)
          · exact hab rfl
        exact
          Ktail.carrier_bridge_attachment_subgraph_paths_permute_meet_only_endpoints_near_hajos_with_two_incident_unsplit_edges
            σ₀ Btail
            (by
              intro i hmem
              exact hKtail_branch_not_first i
                (hBtail_le.left hmem))
            (by
              intro i j hij z hz hmem
              exact hKtail_internal_not_first hij hz
                (hBtail_le.left hmem))
            hleft_ne_rightV pBridge hpBridge
            attachBridgeB hattachBridge
            stemBridgeB hstemBridgeB_path
            hstemBridgeB_avoids hbridgeStem_meet
            hstemStem_meet
      · exact False.elim
          (hno_common
            (hcrossed_simultaneous_obstruction_gives_common
              hzLeft_internal hzLeft_stem
              hzRight_internal hzRight_stem
              hright_before))
  have hcommon_obstruction_first_common_on_p :
      CommonObsT ->
        Exists fun zRootT : TBtail.verts =>
          Exists fun hz_left :
            (zRootT : Btail.verts) ∈
              stemLeftOneB₀.support =>
            (zRootT : Btail.verts) ∈
                Walk.InternalVertices pB₀ ∧
              (zRootT : Btail.verts) ∈
                stemRightThreeB₀.support ∧
                forall t : Btail.verts,
                  t ∈ stemRightThreeB₀.support ->
                    t ∈ (stemLeftOneB₀.takeUntil
                      (zRootT : Btail.verts)
                      hz_left).support ->
                      t =
                        (zRootT : Btail.verts) := by
    intro hcommon
    rcases hcommon with
      ⟨zT₀, _hz_internal₀,
        hz_left₀, hz_right₀⟩
    rcases
      Walk.exists_first_common_support
        stemLeftOneB₀ stemRightThreeB₀
        ⟨(zT₀ : Btail.verts),
          hz_left₀, hz_right₀⟩ with
      ⟨zB, hz_left, hz_right, hfirst⟩
    have hz_p :
        zB ∈ pB₀.support :=
      Subgraph.tree_common_prefix_split_mem_start_path
        (G := Btail.coe) (T := TBtail)
        (p := stemLeftOneB₀)
        (q := stemRightThreeB₀)
        (r := pB₀)
        hTBtail_tree hstemLeftOneB₀_le_TB
        hstemRightThreeB₀_le_TB
        hpB₀_le_TB hstemLeftOneB₀_path
        hstemRightThreeB₀_path hpB₀
        hz_left hz_right
        (Walk.first_common_takeUntil_punctured_disjoint_takeUntil
          (p := stemLeftOneB₀)
          (q := stemRightThreeB₀)
          hz_left hz_right hfirst)
    have hz_ne_leftT :
        zB ≠ (leftT₀ : Btail.verts) := by
      intro hz_eq_left
      have hleft_support :
          (leftT₀ : Btail.verts) ∈
            stemRightThreeB₀.support := by
        simpa [hz_eq_left] using hz_right
      rcases hleftT₀_on_right_stem_three_endpoint
          hleft_support with
        hleft_eq_right | hleft_eq_attach
      · exact hleftT₀_ne_rightT₀
          (Subtype.ext
            (hleft_eq_right.trans
              hrightB₀_eq_rightT₀))
      · exact hattachσ₀_three_ne_left
          (by
            have hval :=
              congrArg
                (fun x : Btail.verts => (x : V))
                hleft_eq_attach
            simpa [attachThreeB₀, attachB₀] using
              hval.symm)
    have hz_ne_rightT :
        zB ≠ (rightT₀ : Btail.verts) := by
      intro hz_eq_right
      have hright_support :
          (rightT₀ : Btail.verts) ∈
            stemLeftOneB₀.support := by
        simpa [hz_eq_right] using hz_left
      rcases hrightT₀_on_left_stem_one_endpoint
          hright_support with
        hright_eq_left | hright_eq_attach
      · exact hleftT₀_ne_rightT₀.symm
          (Subtype.ext
            (hright_eq_left.trans
              hleftB₀_eq_leftT₀))
      · exact hattachσ₀_one_ne_right
          (by
            have hval :=
              congrArg
                (fun x : Btail.verts => (x : V))
                hright_eq_attach
            simpa [attachOneB₀, attachB₀] using
              hval.symm)
    have hzT_mem : zB ∈ TBtail.verts :=
      Walk.support_subset_of_toSubgraph_le
        hpB₀_le_TB hz_p
    refine ⟨⟨zB, hzT_mem⟩, ?_, ?_, ?_⟩
    · simpa using hz_left
    · exact ⟨hz_p, hz_ne_leftT, hz_ne_rightT⟩
    · exact ⟨by simpa using hz_right, by
        intro t ht_right ht_left
        simpa using hfirst t ht_right ht_left⟩
  have hcommon_obstruction_normalized_last_common_split :
      CommonObsT -> Nonempty (NormalizedCommonObstruction C₀) := by
    intro hcommon
    rcases hcommon_obstruction_first_common_on_p
        hcommon with
      ⟨zRootT, hz_left, hz_internal,
        hz_right, hfirst⟩
    rcases hpB_internal_split_paths zRootT
        hz_internal with
      ⟨pLeft, pRight, hpLeft, hpRight,
        hpLeft_le, hpRight_le,
        _hleft_support_pB,
        _hright_support_pB,
        hright_not_pLeft,
        hleft_not_pRight⟩
    rcases hstemLeftOne_suffix_paths zRootT
        hz_left with
      ⟨pOne, hpOne, hpOne_le,
        hone_support_stem,
        hright_not_pOne⟩
    rcases hstemRightThree_suffix_paths zRootT
        hz_right with
      ⟨pThree, hpThree, hpThree_le,
        hthree_support_stem,
        hleft_not_pThree⟩
    have hcommon_suffix :
        Exists fun z : Btail.verts =>
          z ∈ pOne.support ∧
            z ∈ pThree.support := by
      exact ⟨(zRootT : Btail.verts),
        pOne.start_mem_support,
        pThree.start_mem_support⟩
    rcases Walk.exists_last_common_support
        pOne pThree hcommon_suffix with
      ⟨last, hlast_one, hlast_one_rev,
        hlast_three, hlast⟩
    exact ⟨{
      root := zRootT
      root_left := hz_left
      root_internal := hz_internal
      root_right := hz_right
      leftPath := pLeft
      rightPath := pRight
      onePath := pOne
      threePath := pThree
      last := last
      last_one := hlast_one
      last_one_reverse := hlast_one_rev
      last_three := hlast_three
      first_common := hfirst
      leftPath_isPath := hpLeft
      rightPath_isPath := hpRight
      onePath_isPath := hpOne
      threePath_isPath := hpThree
      leftPath_le := hpLeft_le
      rightPath_le := hpRight_le
      onePath_le := hpOne_le
      threePath_le := hpThree_le
      right_not_leftPath := hright_not_pLeft
      left_not_rightPath := hleft_not_pRight
      right_not_onePath := hright_not_pOne
      left_not_threePath := hleft_not_pThree
      onePath_support := hone_support_stem
      threePath_support := hthree_support_stem
      last_common := hlast
    }⟩
  have hcommon_conclusion (hcommon : CommonObsT) :
      NearHajosStrengtheningConclusion G := by
    rcases hcommon_obstruction_normalized_last_common_split
        hcommon with ⟨N⟩
    exact resolveCommon D C₀ N
  have hendpoint_hard_case_or_conclusion :
      NearHajosStrengtheningConclusion G ∨
        (LeftObsT ∧ RightObsT) ∨ CommonObsT := by
    rcases hoverlap_recovered_on_p_T with
      hleft | hrest
    · by_cases hright : RightObsT
      · exact Or.inr (Or.inl ⟨hleft, hright⟩)
      · by_cases hcommon : CommonObsT
        · exact Or.inr (Or.inr hcommon)
        · exact Or.inl
            (hleft_first_common_bridge_conclusion
              hleft hright hcommon)
    · rcases hrest with hright | hcommon
      · by_cases hleft : LeftObsT
        · exact Or.inr (Or.inl ⟨hleft, hright⟩)
        · by_cases hcommon' : CommonObsT
          · exact Or.inr (Or.inr hcommon')
          · exact Or.inl
              (hright_first_common_bridge_conclusion
                hright hleft hcommon')
      · exact Or.inr (Or.inr hcommon)
  rcases hendpoint_hard_case_or_conclusion with
    hdone | hhard
  · exact hdone
  · rcases hhard with hsimultaneous | hcommon
    · by_cases hcommon' : CommonObsT
      · exact hcommon_conclusion hcommon'
      · exact
          hsimultaneous_bridge_conclusion
            hsimultaneous.1 hsimultaneous.2 hcommon'
    · exact hcommon_conclusion hcommon

end PathCarrier

end Schematic.Math.GraphTheory
