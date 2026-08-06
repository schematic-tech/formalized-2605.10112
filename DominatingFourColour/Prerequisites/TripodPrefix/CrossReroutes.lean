import DominatingFourColour.Prerequisites.TripodPrefix.CrossRimDisjointness

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
theorem Tripod.exists_legLengthSum_lt_of_cross_prefix_clean_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j k : Fin 3}
    (hji : j ≠ i)
    (hki : k ≠ i)
    (hjk : j ≠ k)
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hx_ne_attach : x ≠ H.attach j)
    (hidx :
      (H.rim j).support.idxOf x <
        (H.rim j).support.idxOf (H.attach j))
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_rims :
      forall l : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim l).support -> v = x) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  let posRim : G.Walk x H.right :=
    (p.append (H.leg i).reverse).append
      ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)
  let splitRim : G.Walk x H.right :=
    (H.rim j).dropUntil x hxj.1
  let thirdRim : G.Walk x H.right :=
    ((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k)
  let newRim : Fin 3 -> G.Walk x H.right := fun l =>
    if hli : l = i then posRim
    else if hlj : l = j then splitRim
    else thirdRim
  let newAttach : Fin 3 -> V := Function.update H.attach i (feet i)
  let newLeg : forall l : Fin 3, G.Walk (newAttach l) (feet l) := fun l =>
    if hli : l = i then
      (SimpleGraph.Walk.nil : G.Walk (feet i) (feet i)).copy
        (by simp [newAttach, hli]) (by simp [hli])
    else
      (H.leg l).copy (by simp [newAttach, hli]) rfl
  have hkj : k ≠ j := fun h => hjk h.symm
  let H' : Tripod G feet := {
    left := x
    right := H.right
    left_ne_right := hxj.2.2
    left_not_foot := by
      intro l
      exact H.crossContact_ne_foot_of_ne_attach hxj hx_ne_attach l
    right_not_foot := H.right_not_foot
    rim := newRim
    rim_isPath := by
      intro l
      by_cases hli : l = i
      · subst l
        simpa [newRim, posRim] using
          H.crossPrefixPositiveRim_isPath_of_trim_clean
            hji hpos hxj p hp hp_clean hp_meets_rims
      · by_cases hlj : l = j
        · subst l
          simpa [newRim, hji, splitRim] using
            (SimpleGraph.Walk.isPath_of_isSubwalk
              (SimpleGraph.Walk.isSubwalk_dropUntil (H.rim j) hxj.1)
              (H.rim_isPath j))
        · simpa [newRim, hli, hlj, thirdRim] using
            H.crossPrefixThirdRim_isPath hjk hxj
    attach := newAttach
    attach_mem_rim := by
      intro l
      by_cases hli : l = i
      · subst l
        simpa [newRim, newAttach, posRim] using
          H.crossPrefix_positive_foot_mem_internal hxj hx_ne_attach p
      · by_cases hlj : l = j
        · subst l
          simpa [newRim, newAttach, hli, splitRim] using
            H.crossPrefix_attach_mem_split_rim hxj hidx
        · have hlk : l = k := by
            exact fin3_eq_of_ne_ne
              (fun hij : i = j => hji hij.symm)
              (fun hik : i = k => hki hik.symm)
              hjk hli hlj
          subst l
          simpa [newRim, newAttach, hki, hkj, thirdRim] using
            H.crossPrefix_third_attach_mem_internal hjk hxj
    rim_internals_disjoint := by
      intro a b hab
      by_cases hai : a = i
      · subst a
        by_cases hbi : b = i
        · exact False.elim (hab hbi.symm)
        · by_cases hbj : b = j
          · subst b
            simpa [newRim, hji, posRim, splitRim] using
              H.crossPrefixPositiveRim_internal_disjoint_splitRim
                hji hxj p hp_meets_rims
          · have hbk : b = k := by
              exact fin3_eq_of_ne_ne
                (fun hij : i = j => hji hij.symm)
                (fun hik : i = k => hki hik.symm)
                hjk hbi hbj
            subst b
            simpa [newRim, hki, hkj, posRim, thirdRim] using
              H.crossPrefixPositiveRim_internal_disjoint_thirdRim
                hji hki hxj p hp_meets_rims
      · by_cases haj : a = j
        · subst a
          by_cases hbi : b = i
          · subst b
            simpa [newRim, hji, posRim, splitRim] using
              (H.crossPrefixPositiveRim_internal_disjoint_splitRim
                hji hxj p hp_meets_rims).symm
          · by_cases hbj : b = j
            · exact False.elim (hab hbj.symm)
            · have hbk : b = k := by
                exact fin3_eq_of_ne_ne
                  (fun hij : i = j => hji hij.symm)
                  (fun hik : i = k => hki hik.symm)
                  hjk hbi hbj
              subst b
              simpa [newRim, hki, hkj, hji, splitRim, thirdRim] using
                H.crossPrefixSplitRim_internal_disjoint_thirdRim hjk hxj
        · have hak : a = k := by
            exact fin3_eq_of_ne_ne
              (fun hij : i = j => hji hij.symm)
              (fun hik : i = k => hki hik.symm)
              hjk hai haj
          subst a
          by_cases hbi : b = i
          · subst b
            simpa [newRim, hki, hkj, posRim, thirdRim] using
              (H.crossPrefixPositiveRim_internal_disjoint_thirdRim
                hji hki hxj p hp_meets_rims).symm
          · by_cases hbj : b = j
            · subst b
              simpa [newRim, hki, hkj, hji, splitRim, thirdRim] using
                (H.crossPrefixSplitRim_internal_disjoint_thirdRim hjk hxj).symm
            · have hbk : b = k := by
                exact fin3_eq_of_ne_ne
                  (fun hij : i = j => hji hij.symm)
                  (fun hik : i = k => hki hik.symm)
                  hjk hbi hbj
              exact False.elim (hab hbk.symm)
    leg := newLeg
    leg_isPath := by
      intro l
      by_cases hli : l = i
      · subst l
        simp [newLeg]
      · simpa [newLeg, hli] using H.leg_isPath l
    legs_disjoint := by
      intro a b hab
      by_cases hai : a = i
      · subst a
        by_cases hbi : b = i
        · exact False.elim (hab hbi.symm)
        · rw [Set.disjoint_left]
          intro v hvnil hvold
          have hv_eq : v = feet i := by
            simpa [newLeg] using hvnil
          have hvold' : v ∈ (H.leg b).support := by
            simpa [newLeg, hbi] using hvold
          exact Set.disjoint_left.mp
            (H.legs_disjoint i b (fun hib => hbi hib.symm))
            (by simp [hv_eq])
            hvold'
      · by_cases hbi : b = i
        · subst b
          rw [Set.disjoint_left]
          intro v hvold hvnil
          have hv_eq : v = feet i := by
            simpa [newLeg] using hvnil
          have hvold' : v ∈ (H.leg a).support := by
            simpa [newLeg, hai] using hvold
          exact Set.disjoint_left.mp
            (H.legs_disjoint a i hai)
            hvold'
            (by simp [hv_eq])
        · simpa [newLeg, hai, hbi] using H.legs_disjoint a b hab
    leg_meets_rims_only_at_attach := by
      intro a b v hvleg hvrim
      by_cases hai : a = i
      · subst a
        have hv_eq : v = feet i := by
          simpa [newLeg] using hvleg
        simp [newAttach, hv_eq]
      · have hvleg_old : v ∈ (H.leg a).support := by
          simpa [newLeg, hai] using hvleg
        by_cases hbi : b = i
        · subst b
          have hvrim_pos : v ∈ posRim.support := by
            simpa [newRim] using hvrim
          have hv_attach :
              v = H.attach a :=
            H.crossPrefixPositiveRim_oldLeg_meets_only_at_attach_of_trim_clean
              hpos p hp_clean a hai v hvleg_old (by simpa [posRim] using hvrim_pos)
          simpa [newAttach, hai] using hv_attach
        · by_cases hbj : b = j
          · subst b
            have hvrim_split : v ∈ splitRim.support := by
              simpa [newRim, hbi, splitRim] using hvrim
            have hv_attach :
                v = H.attach a :=
              H.crossPrefixSplitRim_oldLeg_meets_only_at_attach hxj
                hvleg_old (by simpa [splitRim] using hvrim_split)
            simpa [newAttach, hai] using hv_attach
          · have hbk : b = k := by
              exact fin3_eq_of_ne_ne
                (fun hij : i = j => hji hij.symm)
                (fun hik : i = k => hki hik.symm)
                hjk hbi hbj
            subst b
            have hvrim_third : v ∈ thirdRim.support := by
              simpa [newRim, hki, hkj, hji, thirdRim] using hvrim
            have hv_attach :
                v = H.attach a :=
              H.crossPrefixThirdRim_oldLeg_meets_only_at_attach hxj
                hvleg_old (by simpa [thirdRim] using hvrim_third)
            simpa [newAttach, hai] using hv_attach
  }
  refine ⟨H', ?_⟩
  fin_cases i
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hpos
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hpos
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hpos

theorem Tripod.exists_legLengthSum_lt_of_cross_suffix_clean_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j k : Fin 3}
    (hji : j ≠ i)
    (hki : k ≠ i)
    (hjk : j ≠ k)
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hx_ne_attach : x ≠ H.attach j)
    (hidx :
      (H.rim j).support.idxOf (H.attach j) <
        (H.rim j).support.idxOf x)
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_rims :
      forall l : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim l).support -> v = x) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  let posRim : G.Walk H.left x :=
    (((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
      (H.leg i)).append p.reverse
  let splitRim : G.Walk H.left x :=
    (H.rim j).takeUntil x hxj.1
  let thirdRim : G.Walk H.left x :=
    (H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse
  let newRim : Fin 3 -> G.Walk H.left x := fun l =>
    if hli : l = i then posRim
    else if hlj : l = j then splitRim
    else thirdRim
  let newAttach : Fin 3 -> V := Function.update H.attach i (feet i)
  let newLeg : forall l : Fin 3, G.Walk (newAttach l) (feet l) := fun l =>
    if hli : l = i then
      (SimpleGraph.Walk.nil : G.Walk (feet i) (feet i)).copy
        (by simp [newAttach, hli]) (by simp [hli])
    else
      (H.leg l).copy (by simp [newAttach, hli]) rfl
  have hkj : k ≠ j := fun h => hjk h.symm
  let H' : Tripod G feet := {
    left := H.left
    right := x
    left_ne_right := fun h => hxj.2.1 h.symm
    left_not_foot := H.left_not_foot
    right_not_foot := by
      intro l
      exact H.crossContact_ne_foot_of_ne_attach hxj hx_ne_attach l
    rim := newRim
    rim_isPath := by
      intro l
      by_cases hli : l = i
      · subst l
        simpa [newRim, posRim] using
          H.crossSuffixPositiveRim_isPath_of_trim_clean
            hji hpos hxj p hp hp_clean hp_meets_rims
      · by_cases hlj : l = j
        · subst l
          simpa [newRim, hji, splitRim] using
            (SimpleGraph.Walk.isPath_of_isSubwalk
              (SimpleGraph.Walk.isSubwalk_takeUntil (H.rim j) hxj.1)
              (H.rim_isPath j))
        · simpa [newRim, hli, hlj, thirdRim] using
            H.crossSuffixThirdRim_isPath hkj hxj
    attach := newAttach
    attach_mem_rim := by
      intro l
      by_cases hli : l = i
      · subst l
        simpa [newRim, newAttach, posRim] using
          H.crossSuffix_positive_foot_mem_internal hxj hx_ne_attach p
      · by_cases hlj : l = j
        · subst l
          simpa [newRim, newAttach, hli, splitRim] using
            H.crossSuffix_attach_mem_split_rim hxj hidx
        · have hlk : l = k := by
            exact fin3_eq_of_ne_ne
              (fun hij : i = j => hji hij.symm)
              (fun hik : i = k => hki hik.symm)
              hjk hli hlj
          subst l
          simpa [newRim, newAttach, hki, hkj, thirdRim] using
            H.crossSuffix_third_attach_mem_internal hkj hxj
    rim_internals_disjoint := by
      intro a b hab
      by_cases hai : a = i
      · subst a
        by_cases hbi : b = i
        · exact False.elim (hab hbi.symm)
        · by_cases hbj : b = j
          · subst b
            simpa [newRim, hji, posRim, splitRim] using
              H.crossSuffixPositiveRim_internal_disjoint_splitRim
                hji hxj p hp_meets_rims
          · have hbk : b = k := by
              exact fin3_eq_of_ne_ne
                (fun hij : i = j => hji hij.symm)
                (fun hik : i = k => hki hik.symm)
                hjk hbi hbj
            subst b
            simpa [newRim, hki, hkj, posRim, thirdRim] using
              H.crossSuffixPositiveRim_internal_disjoint_thirdRim
                hji hki hxj p hp_meets_rims
      · by_cases haj : a = j
        · subst a
          by_cases hbi : b = i
          · subst b
            simpa [newRim, hji, posRim, splitRim] using
              (H.crossSuffixPositiveRim_internal_disjoint_splitRim
                hji hxj p hp_meets_rims).symm
          · by_cases hbj : b = j
            · exact False.elim (hab hbj.symm)
            · have hbk : b = k := by
                exact fin3_eq_of_ne_ne
                  (fun hij : i = j => hji hij.symm)
                  (fun hik : i = k => hki hik.symm)
                  hjk hbi hbj
              subst b
              simpa [newRim, hki, hkj, hji, splitRim, thirdRim] using
                H.crossSuffixSplitRim_internal_disjoint_thirdRim hjk hxj
        · have hak : a = k := by
            exact fin3_eq_of_ne_ne
              (fun hij : i = j => hji hij.symm)
              (fun hik : i = k => hki hik.symm)
              hjk hai haj
          subst a
          by_cases hbi : b = i
          · subst b
            simpa [newRim, hki, hkj, posRim, thirdRim] using
              (H.crossSuffixPositiveRim_internal_disjoint_thirdRim
                hji hki hxj p hp_meets_rims).symm
          · by_cases hbj : b = j
            · subst b
              simpa [newRim, hki, hkj, hji, splitRim, thirdRim] using
                (H.crossSuffixSplitRim_internal_disjoint_thirdRim hjk hxj).symm
            · have hbk : b = k := by
                exact fin3_eq_of_ne_ne
                  (fun hij : i = j => hji hij.symm)
                  (fun hik : i = k => hki hik.symm)
                  hjk hbi hbj
              exact False.elim (hab hbk.symm)
    leg := newLeg
    leg_isPath := by
      intro l
      by_cases hli : l = i
      · subst l
        simp [newLeg]
      · simpa [newLeg, hli] using H.leg_isPath l
    legs_disjoint := by
      intro a b hab
      by_cases hai : a = i
      · subst a
        by_cases hbi : b = i
        · exact False.elim (hab hbi.symm)
        · rw [Set.disjoint_left]
          intro v hvnil hvold
          have hv_eq : v = feet i := by
            simpa [newLeg] using hvnil
          have hvold' : v ∈ (H.leg b).support := by
            simpa [newLeg, hbi] using hvold
          exact Set.disjoint_left.mp
            (H.legs_disjoint i b (fun hib => hbi hib.symm))
            (by simp [hv_eq])
            hvold'
      · by_cases hbi : b = i
        · subst b
          rw [Set.disjoint_left]
          intro v hvold hvnil
          have hv_eq : v = feet i := by
            simpa [newLeg] using hvnil
          have hvold' : v ∈ (H.leg a).support := by
            simpa [newLeg, hai] using hvold
          exact Set.disjoint_left.mp
            (H.legs_disjoint a i hai)
            hvold'
            (by simp [hv_eq])
        · simpa [newLeg, hai, hbi] using H.legs_disjoint a b hab
    leg_meets_rims_only_at_attach := by
      intro a b v hvleg hvrim
      by_cases hai : a = i
      · subst a
        have hv_eq : v = feet i := by
          simpa [newLeg] using hvleg
        simp [newAttach, hv_eq]
      · have hvleg_old : v ∈ (H.leg a).support := by
          simpa [newLeg, hai] using hvleg
        by_cases hbi : b = i
        · subst b
          have hvrim_pos : v ∈ posRim.support := by
            simpa [newRim] using hvrim
          have hv_attach :
              v = H.attach a :=
            H.crossSuffixPositiveRim_oldLeg_meets_only_at_attach_of_trim_clean
              hpos p hp_clean a hai v hvleg_old (by simpa [posRim] using hvrim_pos)
          simpa [newAttach, hai] using hv_attach
        · by_cases hbj : b = j
          · subst b
            have hvrim_split : v ∈ splitRim.support := by
              simpa [newRim, hbi, splitRim] using hvrim
            have hv_attach :
                v = H.attach a :=
              H.crossSuffixSplitRim_oldLeg_meets_only_at_attach hxj
                hvleg_old (by simpa [splitRim] using hvrim_split)
            simpa [newAttach, hai] using hv_attach
          · have hbk : b = k := by
              exact fin3_eq_of_ne_ne
                (fun hij : i = j => hji hij.symm)
                (fun hik : i = k => hki hik.symm)
                hjk hbi hbj
            subst b
            have hvrim_third : v ∈ thirdRim.support := by
              simpa [newRim, hki, hkj, hji, thirdRim] using hvrim
            have hv_attach :
                v = H.attach a :=
              H.crossSuffixThirdRim_oldLeg_meets_only_at_attach hxj
                hvleg_old (by simpa [thirdRim] using hvrim_third)
            simpa [newAttach, hai] using hv_attach
  }
  refine ⟨H', ?_⟩
  fin_cases i
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hpos
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hpos
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hpos

theorem Tripod.exists_legLengthSum_lt_of_cross_prefix_leg_hit_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j k : Fin 3}
    (hji : j ≠ i)
    (hki : k ≠ i)
    (hjk : j ≠ k)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hx_ne_attach : x ≠ H.attach j)
    (hidx :
      (H.rim j).support.idxOf x <
        (H.rim j).support.idxOf (H.attach j))
    (hy : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hp_old_leg :
      forall l : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg l).support -> v = y)
    (hp_meets_rims :
      forall l : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim l).support -> v = x)
    (hlt : ((H.leg i).dropUntil y hy).length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  let hitRim : G.Walk x H.right :=
    (p.append ((H.leg i).takeUntil y hy).reverse).append
      ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)
  let splitRim : G.Walk x H.right :=
    (H.rim j).dropUntil x hxj.1
  let thirdRim : G.Walk x H.right :=
    ((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k)
  let newRim : Fin 3 -> G.Walk x H.right := fun l =>
    if hli : l = i then hitRim
    else if hlj : l = j then splitRim
    else thirdRim
  let newAttach : Fin 3 -> V := Function.update H.attach i y
  let newLeg : forall l : Fin 3, G.Walk (newAttach l) (feet l) := fun l =>
    if hli : l = i then
      ((H.leg i).dropUntil y hy).copy
        (by simp [newAttach, hli]) (by simp [hli])
    else
      (H.leg l).copy (by simp [newAttach, hli]) rfl
  have hkj : k ≠ j := fun h => hjk h.symm
  have hattach_not_newLeg :
      H.attach i ∉ ((H.leg i).dropUntil y hy).support :=
    Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      (H.leg_isPath i) hy hy_ne_attach
  let H' : Tripod G feet := {
    left := x
    right := H.right
    left_ne_right := hxj.2.2
    left_not_foot := by
      intro l
      exact H.crossContact_ne_foot_of_ne_attach hxj hx_ne_attach l
    right_not_foot := H.right_not_foot
    rim := newRim
    rim_isPath := by
      intro l
      by_cases hli : l = i
      · subst l
        simpa [newRim, hitRim] using
          H.crossPrefixHitRim_isPath hji hxj hy p hp
            (hp_old_leg i) hp_meets_rims
      · by_cases hlj : l = j
        · subst l
          simpa [newRim, hji, splitRim] using
            (SimpleGraph.Walk.isPath_of_isSubwalk
              (SimpleGraph.Walk.isSubwalk_dropUntil (H.rim j) hxj.1)
              (H.rim_isPath j))
        · simpa [newRim, hli, hlj, thirdRim] using
            H.crossPrefixThirdRim_isPath hjk hxj
    attach := newAttach
    attach_mem_rim := by
      intro l
      by_cases hli : l = i
      · subst l
        simpa [newRim, newAttach, hitRim] using
          H.crossPrefix_hit_attach_mem_internal hxj hy hy_ne_attach p
      · by_cases hlj : l = j
        · subst l
          simpa [newRim, newAttach, hli, splitRim] using
            H.crossPrefix_attach_mem_split_rim hxj hidx
        · have hlk : l = k := by
            exact fin3_eq_of_ne_ne
              (fun hij : i = j => hji hij.symm)
              (fun hik : i = k => hki hik.symm)
              hjk hli hlj
          subst l
          simpa [newRim, newAttach, hki, hkj, thirdRim] using
            H.crossPrefix_third_attach_mem_internal hjk hxj
    rim_internals_disjoint := by
      intro a b hab
      by_cases hai : a = i
      · subst a
        by_cases hbi : b = i
        · exact False.elim (hab hbi.symm)
        · by_cases hbj : b = j
          · subst b
            simpa [newRim, hji, hitRim, splitRim] using
              H.crossPrefixHitRim_internal_disjoint_splitRim
                hji hxj hy p hp_meets_rims
          · have hbk : b = k := by
              exact fin3_eq_of_ne_ne
                (fun hij : i = j => hji hij.symm)
                (fun hik : i = k => hki hik.symm)
                hjk hbi hbj
            subst b
            simpa [newRim, hki, hkj, hitRim, thirdRim] using
              H.crossPrefixHitRim_internal_disjoint_thirdRim
                hji hki hxj hy p hp_meets_rims
      · by_cases haj : a = j
        · subst a
          by_cases hbi : b = i
          · subst b
            simpa [newRim, hji, hitRim, splitRim] using
              (H.crossPrefixHitRim_internal_disjoint_splitRim
                hji hxj hy p hp_meets_rims).symm
          · by_cases hbj : b = j
            · exact False.elim (hab hbj.symm)
            · have hbk : b = k := by
                exact fin3_eq_of_ne_ne
                  (fun hij : i = j => hji hij.symm)
                  (fun hik : i = k => hki hik.symm)
                  hjk hbi hbj
              subst b
              simpa [newRim, hki, hkj, hji, splitRim, thirdRim] using
                H.crossPrefixSplitRim_internal_disjoint_thirdRim hjk hxj
        · have hak : a = k := by
            exact fin3_eq_of_ne_ne
              (fun hij : i = j => hji hij.symm)
              (fun hik : i = k => hki hik.symm)
              hjk hai haj
          subst a
          by_cases hbi : b = i
          · subst b
            simpa [newRim, hki, hkj, hitRim, thirdRim] using
              (H.crossPrefixHitRim_internal_disjoint_thirdRim
                hji hki hxj hy p hp_meets_rims).symm
          · by_cases hbj : b = j
            · subst b
              simpa [newRim, hki, hkj, hji, splitRim, thirdRim] using
                (H.crossPrefixSplitRim_internal_disjoint_thirdRim hjk hxj).symm
            · have hbk : b = k := by
                exact fin3_eq_of_ne_ne
                  (fun hij : i = j => hji hij.symm)
                  (fun hik : i = k => hki hik.symm)
                  hjk hbi hbj
              exact False.elim (hab hbk.symm)
    leg := newLeg
    leg_isPath := by
      intro l
      by_cases hli : l = i
      · subst l
        simpa [newLeg] using
          SimpleGraph.Walk.isPath_of_isSubwalk
            (SimpleGraph.Walk.isSubwalk_dropUntil (H.leg i) hy)
            (H.leg_isPath i)
      · simpa [newLeg, hli] using H.leg_isPath l
    legs_disjoint := by
      intro a b hab
      by_cases hai : a = i
      · subst a
        by_cases hbi : b = i
        · exact False.elim (hab hbi.symm)
        · rw [Set.disjoint_left]
          intro v hvnew hvold
          have hvnew_old : v ∈ (H.leg i).support :=
            SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy
              (by simpa [newLeg] using hvnew)
          have hvold' : v ∈ (H.leg b).support := by
            simpa [newLeg, hbi] using hvold
          exact Set.disjoint_left.mp
            (H.legs_disjoint i b (fun hib => hbi hib.symm))
            hvnew_old hvold'
      · by_cases hbi : b = i
        · subst b
          rw [Set.disjoint_left]
          intro v hvold hvnew
          have hvold' : v ∈ (H.leg a).support := by
            simpa [newLeg, hai] using hvold
          have hvnew_old : v ∈ (H.leg i).support :=
            SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy
              (by simpa [newLeg] using hvnew)
          exact Set.disjoint_left.mp
            (H.legs_disjoint a i hai) hvold' hvnew_old
        · simpa [newLeg, hai, hbi] using H.legs_disjoint a b hab
    leg_meets_rims_only_at_attach := by
      intro a b v hvleg hvrim
      by_cases hai : a = i
      · subst a
        have hvleg_new : v ∈ ((H.leg i).dropUntil y hy).support := by
          simpa [newLeg] using hvleg
        have hvleg_old : v ∈ (H.leg i).support :=
          SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy hvleg_new
        by_cases hbi : b = i
        · subst b
          have hvrim_hit : v ∈ hitRim.support := by
            simpa [newRim] using hvrim
          have hv_y :
              v = y :=
            H.crossPrefixHitRim_newLeg_meets_hitRim hy hy_ne_attach p
              hp_old_leg v hvleg_new (by simpa [hitRim] using hvrim_hit)
          simp [newAttach, hv_y]
        · by_cases hbj : b = j
          · subst b
            have hvrim_split : v ∈ splitRim.support := by
              simpa [newRim, hbi, splitRim] using hvrim
            have hvrim_old : v ∈ (H.rim j).support :=
              SimpleGraph.Walk.support_dropUntil_subset (H.rim j) hxj.1 hvrim_split
            have hv_attach :
                v = H.attach i :=
              H.leg_meets_rims_only_at_attach i j v hvleg_old hvrim_old
            exact False.elim
              (hattach_not_newLeg (by simpa [hv_attach] using hvleg_new))
          · have hbk : b = k := by
              exact fin3_eq_of_ne_ne
                (fun hij : i = j => hji hij.symm)
                (fun hik : i = k => hki hik.symm)
                hjk hbi hbj
            subst b
            have hvrim_third : v ∈ thirdRim.support := by
              simpa [newRim, hki, hkj, hji, thirdRim] using hvrim
            rcases H.crossPrefixThirdRim_support_cases hxj hvrim_third with hvj | hvk
            · have hv_attach :
                  v = H.attach i :=
                H.leg_meets_rims_only_at_attach i j v hvleg_old hvj
              exact False.elim
                (hattach_not_newLeg (by simpa [hv_attach] using hvleg_new))
            · have hv_attach :
                  v = H.attach i :=
                H.leg_meets_rims_only_at_attach i k v hvleg_old hvk
              exact False.elim
                (hattach_not_newLeg (by simpa [hv_attach] using hvleg_new))
      · have hvleg_old : v ∈ (H.leg a).support := by
          simpa [newLeg, hai] using hvleg
        by_cases hbi : b = i
        · subst b
          have hvrim_hit : v ∈ hitRim.support := by
            simpa [newRim] using hvrim
          have hv_attach :
              v = H.attach a :=
            H.crossPrefixHitRim_oldLeg_meets_only_at_attach hy p hp_old_leg
              a hai v hvleg_old (by simpa [hitRim] using hvrim_hit)
          simpa [newAttach, hai] using hv_attach
        · by_cases hbj : b = j
          · subst b
            have hvrim_split : v ∈ splitRim.support := by
              simpa [newRim, hbi, splitRim] using hvrim
            have hv_attach :
                v = H.attach a :=
              H.crossPrefixSplitRim_oldLeg_meets_only_at_attach hxj
                hvleg_old (by simpa [splitRim] using hvrim_split)
            simpa [newAttach, hai] using hv_attach
          · have hbk : b = k := by
              exact fin3_eq_of_ne_ne
                (fun hij : i = j => hji hij.symm)
                (fun hik : i = k => hki hik.symm)
                hjk hbi hbj
            subst b
            have hvrim_third : v ∈ thirdRim.support := by
              simpa [newRim, hki, hkj, hji, thirdRim] using hvrim
            have hv_attach :
                v = H.attach a :=
              H.crossPrefixThirdRim_oldLeg_meets_only_at_attach hxj
                hvleg_old (by simpa [thirdRim] using hvrim_third)
            simpa [newAttach, hai] using hv_attach
  }
  refine ⟨H', ?_⟩
  fin_cases i
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hlt
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hlt
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hlt

theorem Tripod.exists_legLengthSum_lt_of_cross_suffix_leg_hit_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j k : Fin 3}
    (hji : j ≠ i)
    (hki : k ≠ i)
    (hjk : j ≠ k)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hx_ne_attach : x ≠ H.attach j)
    (hidx :
      (H.rim j).support.idxOf (H.attach j) <
        (H.rim j).support.idxOf x)
    (hy : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hp_old_leg :
      forall l : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg l).support -> v = y)
    (hp_meets_rims :
      forall l : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim l).support -> v = x)
    (hlt : ((H.leg i).dropUntil y hy).length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  let hitRim : G.Walk H.left x :=
    (((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
      ((H.leg i).takeUntil y hy)).append p.reverse
  let splitRim : G.Walk H.left x :=
    (H.rim j).takeUntil x hxj.1
  let thirdRim : G.Walk H.left x :=
    (H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse
  let newRim : Fin 3 -> G.Walk H.left x := fun l =>
    if hli : l = i then hitRim
    else if hlj : l = j then splitRim
    else thirdRim
  let newAttach : Fin 3 -> V := Function.update H.attach i y
  let newLeg : forall l : Fin 3, G.Walk (newAttach l) (feet l) := fun l =>
    if hli : l = i then
      ((H.leg i).dropUntil y hy).copy
        (by simp [newAttach, hli]) (by simp [hli])
    else
      (H.leg l).copy (by simp [newAttach, hli]) rfl
  have hkj : k ≠ j := fun h => hjk h.symm
  have hattach_not_newLeg :
      H.attach i ∉ ((H.leg i).dropUntil y hy).support :=
    Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      (H.leg_isPath i) hy hy_ne_attach
  let H' : Tripod G feet := {
    left := H.left
    right := x
    left_ne_right := fun h => hxj.2.1 h.symm
    left_not_foot := H.left_not_foot
    right_not_foot := by
      intro l
      exact H.crossContact_ne_foot_of_ne_attach hxj hx_ne_attach l
    rim := newRim
    rim_isPath := by
      intro l
      by_cases hli : l = i
      · subst l
        simpa [newRim, hitRim] using
          H.crossSuffixHitRim_isPath hji hxj hy p hp
            (hp_old_leg i) hp_meets_rims
      · by_cases hlj : l = j
        · subst l
          simpa [newRim, hji, splitRim] using
            (SimpleGraph.Walk.isPath_of_isSubwalk
              (SimpleGraph.Walk.isSubwalk_takeUntil (H.rim j) hxj.1)
              (H.rim_isPath j))
        · simpa [newRim, hli, hlj, thirdRim] using
            H.crossSuffixThirdRim_isPath hkj hxj
    attach := newAttach
    attach_mem_rim := by
      intro l
      by_cases hli : l = i
      · subst l
        simpa [newRim, newAttach, hitRim] using
          H.crossSuffix_hit_attach_mem_internal hxj hy hy_ne_attach p
      · by_cases hlj : l = j
        · subst l
          simpa [newRim, newAttach, hli, splitRim] using
            H.crossSuffix_attach_mem_split_rim hxj hidx
        · have hlk : l = k := by
            exact fin3_eq_of_ne_ne
              (fun hij : i = j => hji hij.symm)
              (fun hik : i = k => hki hik.symm)
              hjk hli hlj
          subst l
          simpa [newRim, newAttach, hki, hkj, thirdRim] using
            H.crossSuffix_third_attach_mem_internal hkj hxj
    rim_internals_disjoint := by
      intro a b hab
      by_cases hai : a = i
      · subst a
        by_cases hbi : b = i
        · exact False.elim (hab hbi.symm)
        · by_cases hbj : b = j
          · subst b
            simpa [newRim, hji, hitRim, splitRim] using
              H.crossSuffixHitRim_internal_disjoint_splitRim
                hji hxj hy p hp_meets_rims
          · have hbk : b = k := by
              exact fin3_eq_of_ne_ne
                (fun hij : i = j => hji hij.symm)
                (fun hik : i = k => hki hik.symm)
                hjk hbi hbj
            subst b
            simpa [newRim, hki, hkj, hitRim, thirdRim] using
              H.crossSuffixHitRim_internal_disjoint_thirdRim
                hji hki hxj hy p hp_meets_rims
      · by_cases haj : a = j
        · subst a
          by_cases hbi : b = i
          · subst b
            simpa [newRim, hji, hitRim, splitRim] using
              (H.crossSuffixHitRim_internal_disjoint_splitRim
                hji hxj hy p hp_meets_rims).symm
          · by_cases hbj : b = j
            · exact False.elim (hab hbj.symm)
            · have hbk : b = k := by
                exact fin3_eq_of_ne_ne
                  (fun hij : i = j => hji hij.symm)
                  (fun hik : i = k => hki hik.symm)
                  hjk hbi hbj
              subst b
              simpa [newRim, hki, hkj, hji, splitRim, thirdRim] using
                H.crossSuffixSplitRim_internal_disjoint_thirdRim hjk hxj
        · have hak : a = k := by
            exact fin3_eq_of_ne_ne
              (fun hij : i = j => hji hij.symm)
              (fun hik : i = k => hki hik.symm)
              hjk hai haj
          subst a
          by_cases hbi : b = i
          · subst b
            simpa [newRim, hki, hkj, hitRim, thirdRim] using
              (H.crossSuffixHitRim_internal_disjoint_thirdRim
                hji hki hxj hy p hp_meets_rims).symm
          · by_cases hbj : b = j
            · subst b
              simpa [newRim, hki, hkj, hji, splitRim, thirdRim] using
                (H.crossSuffixSplitRim_internal_disjoint_thirdRim hjk hxj).symm
            · have hbk : b = k := by
                exact fin3_eq_of_ne_ne
                  (fun hij : i = j => hji hij.symm)
                  (fun hik : i = k => hki hik.symm)
                  hjk hbi hbj
              exact False.elim (hab hbk.symm)
    leg := newLeg
    leg_isPath := by
      intro l
      by_cases hli : l = i
      · subst l
        simpa [newLeg] using
          SimpleGraph.Walk.isPath_of_isSubwalk
            (SimpleGraph.Walk.isSubwalk_dropUntil (H.leg i) hy)
            (H.leg_isPath i)
      · simpa [newLeg, hli] using H.leg_isPath l
    legs_disjoint := by
      intro a b hab
      by_cases hai : a = i
      · subst a
        by_cases hbi : b = i
        · exact False.elim (hab hbi.symm)
        · rw [Set.disjoint_left]
          intro v hvnew hvold
          have hvnew_old : v ∈ (H.leg i).support :=
            SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy
              (by simpa [newLeg] using hvnew)
          have hvold' : v ∈ (H.leg b).support := by
            simpa [newLeg, hbi] using hvold
          exact Set.disjoint_left.mp
            (H.legs_disjoint i b (fun hib => hbi hib.symm))
            hvnew_old hvold'
      · by_cases hbi : b = i
        · subst b
          rw [Set.disjoint_left]
          intro v hvold hvnew
          have hvold' : v ∈ (H.leg a).support := by
            simpa [newLeg, hai] using hvold
          have hvnew_old : v ∈ (H.leg i).support :=
            SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy
              (by simpa [newLeg] using hvnew)
          exact Set.disjoint_left.mp
            (H.legs_disjoint a i hai) hvold' hvnew_old
        · simpa [newLeg, hai, hbi] using H.legs_disjoint a b hab
    leg_meets_rims_only_at_attach := by
      intro a b v hvleg hvrim
      by_cases hai : a = i
      · subst a
        have hvleg_new : v ∈ ((H.leg i).dropUntil y hy).support := by
          simpa [newLeg] using hvleg
        have hvleg_old : v ∈ (H.leg i).support :=
          SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy hvleg_new
        by_cases hbi : b = i
        · subst b
          have hvrim_hit : v ∈ hitRim.support := by
            simpa [newRim] using hvrim
          have hv_y :
              v = y :=
            H.crossSuffixHitRim_newLeg_meets_hitRim hy hy_ne_attach p
              hp_old_leg v hvleg_new (by simpa [hitRim] using hvrim_hit)
          simp [newAttach, hv_y]
        · by_cases hbj : b = j
          · subst b
            have hvrim_split : v ∈ splitRim.support := by
              simpa [newRim, hbi, splitRim] using hvrim
            have hvrim_old : v ∈ (H.rim j).support :=
              SimpleGraph.Walk.support_takeUntil_subset (H.rim j) hxj.1 hvrim_split
            have hv_attach :
                v = H.attach i :=
              H.leg_meets_rims_only_at_attach i j v hvleg_old hvrim_old
            exact False.elim
              (hattach_not_newLeg (by simpa [hv_attach] using hvleg_new))
          · have hbk : b = k := by
              exact fin3_eq_of_ne_ne
                (fun hij : i = j => hji hij.symm)
                (fun hik : i = k => hki hik.symm)
                hjk hbi hbj
            subst b
            have hvrim_third : v ∈ thirdRim.support := by
              simpa [newRim, hki, hkj, hji, thirdRim] using hvrim
            rcases H.crossSuffixThirdRim_support_cases hxj hvrim_third with hvk | hvj
            · have hv_attach :
                  v = H.attach i :=
                H.leg_meets_rims_only_at_attach i k v hvleg_old hvk
              exact False.elim
                (hattach_not_newLeg (by simpa [hv_attach] using hvleg_new))
            · have hv_attach :
                  v = H.attach i :=
                H.leg_meets_rims_only_at_attach i j v hvleg_old hvj
              exact False.elim
                (hattach_not_newLeg (by simpa [hv_attach] using hvleg_new))
      · have hvleg_old : v ∈ (H.leg a).support := by
          simpa [newLeg, hai] using hvleg
        by_cases hbi : b = i
        · subst b
          have hvrim_hit : v ∈ hitRim.support := by
            simpa [newRim] using hvrim
          have hv_attach :
              v = H.attach a :=
            H.crossSuffixHitRim_oldLeg_meets_only_at_attach hy p hp_old_leg
              a hai v hvleg_old (by simpa [hitRim] using hvrim_hit)
          simpa [newAttach, hai] using hv_attach
        · by_cases hbj : b = j
          · subst b
            have hvrim_split : v ∈ splitRim.support := by
              simpa [newRim, hbi, splitRim] using hvrim
            have hv_attach :
                v = H.attach a :=
              H.crossSuffixSplitRim_oldLeg_meets_only_at_attach hxj
                hvleg_old (by simpa [splitRim] using hvrim_split)
            simpa [newAttach, hai] using hv_attach
          · have hbk : b = k := by
              exact fin3_eq_of_ne_ne
                (fun hij : i = j => hji hij.symm)
                (fun hik : i = k => hki hik.symm)
                hjk hbi hbj
            subst b
            have hvrim_third : v ∈ thirdRim.support := by
              simpa [newRim, hki, hkj, hji, thirdRim] using hvrim
            have hv_attach :
                v = H.attach a :=
              H.crossSuffixThirdRim_oldLeg_meets_only_at_attach hxj
                hvleg_old (by simpa [thirdRim] using hvrim_third)
            simpa [newAttach, hai] using hv_attach
  }
  refine ⟨H', ?_⟩
  fin_cases i
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hlt
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hlt
  · dsimp [H', Tripod.legLengthSum, newLeg]
    simp
    simpa using hlt

theorem Tripod.exists_legLengthSum_lt_of_cross_rim_leg_hit_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hx_ne_attach : x ≠ H.attach j)
    (hy : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hp_old_leg :
      forall l : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg l).support -> v = y)
    (hp_meets_rims :
      forall l : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim l).support -> v = x)
    (hlt : ((H.leg i).dropUntil y hy).length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  obtain ⟨k, hik, hjk⟩ :=
    fin3_exists_ne_ne (i := i) (j := j) (fun hij : i = j => hji hij.symm)
  have hki : k ≠ i := fun h => hik h.symm
  rcases lt_trichotomy
      ((H.rim j).support.idxOf x)
      ((H.rim j).support.idxOf (H.attach j)) with hlt_idx | heq | hgt_idx
  · exact H.exists_legLengthSum_lt_of_cross_prefix_leg_hit_reroute
      hji hki hjk hxj hx_ne_attach hlt_idx hy hy_ne_attach p hp
      hp_old_leg hp_meets_rims hlt
  · have hx_attach : x = H.attach j :=
      (List.idxOf_inj hxj.1).mp heq
    exact False.elim (hx_ne_attach hx_attach)
  · exact H.exists_legLengthSum_lt_of_cross_suffix_leg_hit_reroute
      hji hki hjk hxj hx_ne_attach hgt_idx hy hy_ne_attach p hp
      hp_old_leg hp_meets_rims hlt

theorem Tripod.exists_legLengthSum_lt_of_cross_rim_clean_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hx_ne_attach : x ≠ H.attach j)
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_rims :
      forall l : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim l).support -> v = x) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  obtain ⟨k, hik, hjk⟩ :=
    fin3_exists_ne_ne (i := i) (j := j) (fun hij : i = j => hji hij.symm)
  have hki : k ≠ i := fun h => hik h.symm
  rcases lt_trichotomy
      ((H.rim j).support.idxOf x)
      ((H.rim j).support.idxOf (H.attach j)) with hlt | heq | hgt
  · exact H.exists_legLengthSum_lt_of_cross_prefix_clean_reroute
      hji hki hjk hpos hxj hx_ne_attach hlt p hp hp_clean hp_meets_rims
  · have hx_attach : x = H.attach j :=
      (List.idxOf_inj hxj.1).mp heq
    exact False.elim (hx_ne_attach hx_attach)
  · exact H.exists_legLengthSum_lt_of_cross_suffix_clean_reroute
      hji hki hjk hpos hxj hx_ne_attach hgt p hp hp_clean hp_meets_rims

theorem Tripod.exists_legLengthSum_lt_of_prefix_foot_reroute_of_trim_clean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx_rim : x ∈ (H.rim i).support)
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_rim :
      forall v : V, v ∈ p.support -> v ∈ (H.rim i).support -> v = x)
    (hidx :
      (H.rim i).support.idxOf x <
        (H.rim i).support.idxOf (H.attach i))
    (hrim_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint
          (Walk.InternalVertices (H.prefixFootRerouteRim i hx_rim p))
          (Walk.InternalVertices (H.rim j)))
    (holdLeg_meets_newRim :
      forall j : Fin 3, j ≠ i ->
        forall v : V, v ∈ (H.leg j).support ->
          v ∈ (H.prefixFootRerouteRim i hx_rim p).support ->
            v = H.attach j) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum :=
  H.exists_legLengthSum_lt_of_prefix_foot_reroute hpos hx_rim p
    (H.prefixFootRerouteRim_isPath_of_trim_clean
      hpos hx_rim p hp hp_clean hp_meets_rim hidx)
    hrim_disjoint holdLeg_meets_newRim

theorem Tripod.exists_legLengthSum_lt_of_suffix_foot_reroute_of_trim_clean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx_rim : x ∈ (H.rim i).support)
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_rim :
      forall v : V, v ∈ p.support -> v ∈ (H.rim i).support -> v = x)
    (hidx :
      (H.rim i).support.idxOf (H.attach i) <
        (H.rim i).support.idxOf x)
    (hrim_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint
          (Walk.InternalVertices (H.suffixFootRerouteRim i hx_rim p))
          (Walk.InternalVertices (H.rim j)))
    (holdLeg_meets_newRim :
      forall j : Fin 3, j ≠ i ->
        forall v : V, v ∈ (H.leg j).support ->
          v ∈ (H.suffixFootRerouteRim i hx_rim p).support ->
            v = H.attach j) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum :=
  H.exists_legLengthSum_lt_of_suffix_foot_reroute hpos hx_rim p
    (H.suffixFootRerouteRim_isPath_of_trim_clean
      hpos hx_rim p hp hp_clean hp_meets_rim hidx)
    hrim_disjoint holdLeg_meets_newRim


end Schematic.Math.GraphTheory
