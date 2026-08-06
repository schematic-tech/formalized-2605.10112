import DominatingFourColour.Prerequisites.TripodPrefix.LegMinimality
import Schematic.Math.GraphTheory.PathsTrees.Foundations.PathIntervals

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
theorem Tripod.crossPrefixHitRim_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hy : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hp_meets_leg_only_at_y :
      forall v : V, v ∈ p.support -> v ∈ (H.leg i).support -> v = y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    ((p.append ((H.leg i).takeUntil y hy).reverse).append
      ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)).IsPath := by
  have hp_no_rim_i :
      forall v : V, v ∈ p.support -> v ∈ (H.rim i).support -> False := by
    intro v hvp hvrim
    have hvx : v = x := hp_meets_rims i v hvp hvrim
    have hxrim : x ∈ (H.rim i).support := by
      simpa [hvx] using hvrim
    have hxi : x ∈ Walk.InternalVertices (H.rim i) := by
      exact ⟨hxrim, hxj.2.1, hxj.2.2⟩
    exact Set.disjoint_left.mp
      (H.rim_internals_disjoint j i hji) hxj hxi
  let legPref : G.Walk (H.attach i) y := (H.leg i).takeUntil y hy
  have hlegPref : legPref.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil (H.leg i) hy)
      (H.leg_isPath i)
  have hp_leg : (p.append legPref.reverse).IsPath := by
    refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
      hp hlegPref.reverse ?_
    intro z hzp hzlegrev
    rw [SimpleGraph.Walk.support_reverse] at hzlegrev
    have hzleg : z ∈ (H.leg i).support :=
      SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy
        (List.mem_reverse.mp hzlegrev)
    exact hp_meets_leg_only_at_y z hzp hzleg
  refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint hp_leg ?_ ?_
  · exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_dropUntil (H.rim i) (H.attach_mem_rim i).1)
      (H.rim_isPath i)
  · intro z hzleft hzsuff
    have hzrim : z ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hzsuff
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzleft
    rcases hzleft with hzp | hzlegrev
    · exact False.elim (hp_no_rim_i z hzp hzrim)
    · rw [SimpleGraph.Walk.support_reverse] at hzlegrev
      have hzleg : z ∈ (H.leg i).support :=
        SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy
          (List.mem_reverse.mp hzlegrev)
      exact H.leg_meets_rims_only_at_attach i i z hzleg hzrim

theorem Tripod.crossSuffixHitRim_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hy : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hp_meets_leg_only_at_y :
      forall v : V, v ∈ p.support -> v ∈ (H.leg i).support -> v = y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
      ((H.leg i).takeUntil y hy)).append p.reverse).IsPath := by
  have hp_no_rim_i :
      forall v : V, v ∈ p.support -> v ∈ (H.rim i).support -> False := by
    intro v hvp hvrim
    have hvx : v = x := hp_meets_rims i v hvp hvrim
    have hxrim : x ∈ (H.rim i).support := by
      simpa [hvx] using hvrim
    have hxi : x ∈ Walk.InternalVertices (H.rim i) := by
      exact ⟨hxrim, hxj.2.1, hxj.2.2⟩
    exact Set.disjoint_left.mp
      (H.rim_internals_disjoint j i hji) hxj hxi
  let pref : G.Walk H.left (H.attach i) :=
    (H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1
  let legPref : G.Walk (H.attach i) y := (H.leg i).takeUntil y hy
  have hpref : pref.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil (H.rim i)
        (H.attach_mem_rim i).1)
      (H.rim_isPath i)
  have hlegPref : legPref.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil (H.leg i) hy)
      (H.leg_isPath i)
  have hpref_leg : (pref.append legPref).IsPath := by
    refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
      hpref hlegPref ?_
    intro z hzpref hzleg
    have hzrim : z ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 (by simpa [pref] using hzpref)
    have hzleg_old : z ∈ (H.leg i).support :=
      SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy
        (by simpa [legPref] using hzleg)
    exact H.leg_meets_rims_only_at_attach i i z hzleg_old hzrim
  refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
    hpref_leg hp.reverse ?_
  intro z hzleft hzprev
  rw [SimpleGraph.Walk.support_reverse] at hzprev
  have hzp : z ∈ p.support := List.mem_reverse.mp hzprev
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzleft
  rcases hzleft with hzpref | hzleg
  · have hzrim : z ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 (by simpa [pref] using hzpref)
    exact False.elim (hp_no_rim_i z hzp hzrim)
  · have hzleg_old : z ∈ (H.leg i).support :=
      SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy
        (by simpa [legPref] using hzleg)
    exact hp_meets_leg_only_at_y z hzp hzleg_old

theorem Tripod.crossPrefixHitRim_support_cases
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y v : V}
    (hy : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hv :
      v ∈
        ((p.append ((H.leg i).takeUntil y hy).reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)).support) :
    v ∈ p.support ∨ v ∈ (H.leg i).support ∨ v ∈ (H.rim i).support := by
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hvleft | hvsuff
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvp | hvlegrev
    · exact Or.inl hvp
    · rw [SimpleGraph.Walk.support_reverse] at hvlegrev
      exact Or.inr (Or.inl
        (SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy
          (List.mem_reverse.mp hvlegrev)))
  · exact Or.inr (Or.inr
      (SimpleGraph.Walk.support_dropUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvsuff))

theorem Tripod.crossSuffixHitRim_support_cases
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y v : V}
    (hy : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hv :
      v ∈
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
          ((H.leg i).takeUntil y hy)).append p.reverse).support) :
    v ∈ (H.rim i).support ∨ v ∈ (H.leg i).support ∨ v ∈ p.support := by
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hvleft | hvprev
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvpref | hvleg
    · exact Or.inl
        (SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
          (H.attach_mem_rim i).1 hvpref)
    · exact Or.inr (Or.inl
        (SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy hvleg))
  · rw [SimpleGraph.Walk.support_reverse] at hvprev
    exact Or.inr (Or.inr (List.mem_reverse.mp hvprev))

theorem Tripod.crossPrefixHitRim_newLeg_meets_hitRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hy : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hp_old_leg :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y) :
    forall v : V,
      v ∈ ((H.leg i).dropUntil y hy).support ->
        v ∈
          ((p.append ((H.leg i).takeUntil y hy).reverse).append
            ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)).support ->
          v = y := by
  intro v hvnew hvRim
  let legSuff : G.Walk y (feet i) := (H.leg i).dropUntil y hy
  have hvold : v ∈ (H.leg i).support :=
    SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy hvnew
  have hattach_not_new :
      H.attach i ∉ legSuff.support :=
    Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      (H.leg_isPath i) hy hy_ne_attach
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvRim
  rcases hvRim with hvleft | hvsuff
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvp | hvlegrev
    · exact hp_old_leg i v hvp hvold
    · rw [SimpleGraph.Walk.support_reverse] at hvlegrev
      exact Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        (H.leg_isPath i) hy (List.mem_reverse.mp hvlegrev) hvnew
  · have hvrim : v ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvsuff
    have hv_attach : v = H.attach i :=
      H.leg_meets_rims_only_at_attach i i v hvold hvrim
    exact False.elim
      (hattach_not_new (by simpa [legSuff, hv_attach] using hvnew))

theorem Tripod.crossSuffixHitRim_newLeg_meets_hitRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hy : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hp_old_leg :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y) :
    forall v : V,
      v ∈ ((H.leg i).dropUntil y hy).support ->
        v ∈
          ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
            ((H.leg i).takeUntil y hy)).append p.reverse).support ->
          v = y := by
  intro v hvnew hvRim
  let legSuff : G.Walk y (feet i) := (H.leg i).dropUntil y hy
  have hvold : v ∈ (H.leg i).support :=
    SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy hvnew
  have hattach_not_new :
      H.attach i ∉ legSuff.support :=
    Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      (H.leg_isPath i) hy hy_ne_attach
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvRim
  rcases hvRim with hvleft | hvprev
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvpref | hvlegpref
    · have hvrim : v ∈ (H.rim i).support :=
        SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
          (H.attach_mem_rim i).1 hvpref
      have hv_attach : v = H.attach i :=
        H.leg_meets_rims_only_at_attach i i v hvold hvrim
      exact False.elim
        (hattach_not_new (by simpa [legSuff, hv_attach] using hvnew))
    · exact Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        (H.leg_isPath i) hy hvlegpref hvnew
  · rw [SimpleGraph.Walk.support_reverse] at hvprev
    exact hp_old_leg i v (List.mem_reverse.mp hvprev) hvold

theorem Tripod.crossPrefixHitRim_oldLeg_meets_only_at_attach
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hy : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_old_leg :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y) :
    forall j : Fin 3, j ≠ i ->
      forall v : V, v ∈ (H.leg j).support ->
        v ∈
          ((p.append ((H.leg i).takeUntil y hy).reverse).append
            ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)).support ->
          v = H.attach j := by
  intro j hji v hvleg hvnew
  rcases H.crossPrefixHitRim_support_cases hy p hvnew with hvp | hvleg_or_rim
  · have hv_y : v = y := hp_old_leg j v hvp hvleg
    exact False.elim
      (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg
        (by simpa [hv_y] using hy))
  · rcases hvleg_or_rim with hvi | hvrim
    · exact False.elim
        (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg hvi)
    · exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim

theorem Tripod.crossSuffixHitRim_oldLeg_meets_only_at_attach
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hy : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_old_leg :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y) :
    forall j : Fin 3, j ≠ i ->
      forall v : V, v ∈ (H.leg j).support ->
        v ∈
          ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
            ((H.leg i).takeUntil y hy)).append p.reverse).support ->
          v = H.attach j := by
  intro j hji v hvleg hvnew
  rcases H.crossSuffixHitRim_support_cases hy p hvnew with hvrim | hvleg_or_p
  · exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim
  · rcases hvleg_or_p with hvi | hvp
    · exact False.elim
        (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg hvi)
    · have hv_y : v = y := hp_old_leg j v hvp hvleg
      exact False.elim
        (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg
          (by simpa [hv_y] using hy))

theorem Tripod.crossPrefix_hit_attach_mem_internal
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hy : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y) :
    y ∈
      Walk.InternalVertices
        ((p.append ((H.leg i).takeUntil y hy).reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)) := by
  have hy_ne_x : y ≠ x := by
    intro hyx
    have hy_attach : y = H.attach i :=
      H.leg_meets_rims_only_at_attach i j y hy (by
        simpa [hyx] using hxj.1)
    exact hy_ne_attach hy_attach
  refine ⟨?_, hy_ne_x, H.leg_support_ne_right hy⟩
  rw [SimpleGraph.Walk.mem_support_append_iff]
  left
  rw [SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl p.end_mem_support

theorem Tripod.crossSuffix_hit_attach_mem_internal
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hy : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y) :
    y ∈
      Walk.InternalVertices
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
          ((H.leg i).takeUntil y hy)).append p.reverse) := by
  have hy_ne_x : y ≠ x := by
    intro hyx
    have hy_attach : y = H.attach i :=
      H.leg_meets_rims_only_at_attach i j y hy (by
        simpa [hyx] using hxj.1)
    exact hy_ne_attach hy_attach
  refine ⟨?_, H.leg_support_ne_left hy, hy_ne_x⟩
  rw [SimpleGraph.Walk.mem_support_append_iff]
  left
  rw [SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inr ((H.leg i).takeUntil y hy).end_mem_support

theorem Tripod.crossPrefixThirdRim_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j k : Fin 3}
    (hjk : j ≠ k)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j)) :
    (((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k)).IsPath := by
  have hprefix : ((H.rim j).takeUntil x hxj.1).reverse.IsPath := by
    exact (SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil (H.rim j) hxj.1)
      (H.rim_isPath j)).reverse
  refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
    hprefix (H.rim_isPath k) ?_
  intro z hzpref_rev hzk
  rw [SimpleGraph.Walk.support_reverse] at hzpref_rev
  have hzpref : z ∈ ((H.rim j).takeUntil x hxj.1).support :=
    List.mem_reverse.mp hzpref_rev
  by_cases hz_left : z = H.left
  · exact hz_left
  · have hzj : z ∈ (H.rim j).support :=
      SimpleGraph.Walk.support_takeUntil_subset (H.rim j) hxj.1 hzpref
    by_cases hz_right : z = H.right
    · have hle :
          (H.rim j).support.idxOf H.right <=
            (H.rim j).support.idxOf x :=
        Schematic.Math.GraphTheory.Walk.idxOf_le_of_mem_takeUntil
          (p := H.rim j) (x := x) (z := H.right) hxj.1 (by
            simpa [hz_right] using hzpref)
      have hlt :
          (H.rim j).support.idxOf x <
            (H.rim j).support.idxOf H.right :=
        Schematic.Math.GraphTheory.Walk.IsPath.idxOf_lt_end_of_mem_support_ne_end
          (H.rim_isPath j) hxj.1 hxj.2.2
      omega
    · exact False.elim
        (Set.disjoint_left.mp (H.rim_internals_disjoint j k hjk)
          ⟨hzj, hz_left, hz_right⟩ ⟨hzk, hz_left, hz_right⟩)

theorem Tripod.crossSuffixThirdRim_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j k : Fin 3}
    (hkj : k ≠ j)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j)) :
    ((H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse).IsPath := by
  have hsuffix : ((H.rim j).dropUntil x hxj.1).reverse.IsPath := by
    exact (SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_dropUntil (H.rim j) hxj.1)
      (H.rim_isPath j)).reverse
  refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
    (H.rim_isPath k) hsuffix ?_
  intro z hzk hzsuff_rev
  rw [SimpleGraph.Walk.support_reverse] at hzsuff_rev
  have hzsuff : z ∈ ((H.rim j).dropUntil x hxj.1).support :=
    List.mem_reverse.mp hzsuff_rev
  by_cases hz_right : z = H.right
  · exact hz_right
  · have hzj : z ∈ (H.rim j).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim j) hxj.1 hzsuff
    by_cases hz_left : z = H.left
    · have hle :
          (H.rim j).support.idxOf x <=
            (H.rim j).support.idxOf H.left :=
        Schematic.Math.GraphTheory.Walk.idxOf_le_of_mem_dropUntil
          (p := H.rim j) (H.rim_isPath j) hxj.1 (by
            simpa [hz_left] using hzsuff)
      have hleft_idx :
          (H.rim j).support.idxOf H.left = 0 :=
        Schematic.Math.GraphTheory.Walk.idxOf_start_support (H.rim j)
      have hx_pos :
          0 < (H.rim j).support.idxOf x :=
        Schematic.Math.GraphTheory.Walk.idxOf_pos_of_mem_support_ne_start
          hxj.1 hxj.2.1
      omega
    · exact False.elim
        (Set.disjoint_left.mp (H.rim_internals_disjoint k j hkj)
          ⟨hzk, hz_left, hz_right⟩ ⟨hzj, hz_left, hz_right⟩)

theorem Tripod.crossContact_ne_foot_of_ne_attach
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j : Fin 3}
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hx_ne_attach : x ≠ H.attach j)
    (l : Fin 3) :
    x ≠ feet l := by
  intro hxfoot
  have hfoot_rim_j : feet l ∈ (H.rim j).support := by
    simpa [hxfoot] using hxj.1
  have hfoot_attach :
      feet l = H.attach l :=
    H.leg_meets_rims_only_at_attach l j (feet l)
      (H.leg l).end_mem_support hfoot_rim_j
  have hx_attach_l : x = H.attach l := hxfoot.trans hfoot_attach
  by_cases hlj : l = j
  · subst l
    exact hx_ne_attach hx_attach_l
  · have hxl : x ∈ Walk.InternalVertices (H.rim l) := by
      simpa [← hx_attach_l] using H.attach_mem_rim l
    exact Set.disjoint_left.mp
      (H.rim_internals_disjoint j l (fun hjl => hlj hjl.symm))
      hxj hxl

theorem Tripod.crossPrefix_attach_mem_split_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j : Fin 3}
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hidx :
      (H.rim j).support.idxOf x <
        (H.rim j).support.idxOf (H.attach j)) :
    H.attach j ∈
      Walk.InternalVertices ((H.rim j).dropUntil x hxj.1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Schematic.Math.GraphTheory.Walk.mem_support_dropUntil_of_idxOf_le
      (p := H.rim j) hxj.1 (H.attach_mem_rim j).1 (by omega)
  · intro hattach_x
    have hidx_eq :
        (H.rim j).support.idxOf x =
          (H.rim j).support.idxOf (H.attach j) := by
      rw [hattach_x]
    omega
  · exact H.attach_ne_right j

theorem Tripod.crossSuffix_attach_mem_split_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j : Fin 3}
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hidx :
      (H.rim j).support.idxOf (H.attach j) <
        (H.rim j).support.idxOf x) :
    H.attach j ∈
      Walk.InternalVertices ((H.rim j).takeUntil x hxj.1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Schematic.Math.GraphTheory.Walk.mem_support_takeUntil_of_idxOf_le
      (p := H.rim j) hxj.1 (H.attach_mem_rim j).1 (by omega)
  · exact H.attach_ne_left j
  · intro hattach_x
    have hidx_eq :
        (H.rim j).support.idxOf (H.attach j) =
          (H.rim j).support.idxOf x := by
      rw [hattach_x]
    omega

theorem Tripod.crossPrefix_positive_foot_mem_internal
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hx_ne_attach : x ≠ H.attach j)
    (p : G.Walk x (feet i)) :
    feet i ∈
      Walk.InternalVertices
        ((p.append (H.leg i).reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl p.end_mem_support
  · intro hfoot_x
    exact (H.crossContact_ne_foot_of_ne_attach hxj hx_ne_attach i) hfoot_x.symm
  · exact (H.right_not_foot i).symm

theorem Tripod.crossSuffix_positive_foot_mem_internal
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hx_ne_attach : x ≠ H.attach j)
    (p : G.Walk x (feet i)) :
    feet i ∈
      Walk.InternalVertices
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
          (H.leg i)).append p.reverse) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr (H.leg i).end_mem_support
  · exact (H.left_not_foot i).symm
  · intro hfoot_x
    exact (H.crossContact_ne_foot_of_ne_attach hxj hx_ne_attach i) hfoot_x.symm

theorem Tripod.crossPrefix_third_attach_mem_internal
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j k : Fin 3}
    (hjk : j ≠ k)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j)) :
    H.attach k ∈
      Walk.InternalVertices
        (((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr (H.attach_mem_rim k).1
  · intro hattach_x
    have hxk : x ∈ Walk.InternalVertices (H.rim k) := by
      simpa [hattach_x] using H.attach_mem_rim k
    exact Set.disjoint_left.mp (H.rim_internals_disjoint j k hjk)
      hxj hxk
  · exact H.attach_ne_right k

theorem Tripod.crossSuffix_third_attach_mem_internal
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j k : Fin 3}
    (hkj : k ≠ j)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j)) :
    H.attach k ∈
      Walk.InternalVertices
        ((H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (H.attach_mem_rim k).1
  · exact H.attach_ne_left k
  · intro hattach_x
    have hxk : x ∈ Walk.InternalVertices (H.rim k) := by
      simpa [hattach_x] using H.attach_mem_rim k
    exact Set.disjoint_left.mp (H.rim_internals_disjoint k j hkj)
      hxk hxj

theorem Tripod.crossPrefixPositiveRim_support_cases
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x v : V}
    (p : G.Walk x (feet i))
    (hv :
      v ∈
        ((p.append (H.leg i).reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)).support) :
    v ∈ p.support ∨ v ∈ (H.leg i).support ∨ v ∈ (H.rim i).support := by
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hvleft | hvsuff
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvp | hvlegrev
    · exact Or.inl hvp
    · rw [SimpleGraph.Walk.support_reverse] at hvlegrev
      exact Or.inr (Or.inl (List.mem_reverse.mp hvlegrev))
  · exact Or.inr (Or.inr
      (SimpleGraph.Walk.support_dropUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvsuff))

theorem Tripod.crossSuffixPositiveRim_support_cases
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x v : V}
    (p : G.Walk x (feet i))
    (hv :
      v ∈
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
          (H.leg i)).append p.reverse).support) :
    v ∈ (H.rim i).support ∨ v ∈ (H.leg i).support ∨ v ∈ p.support := by
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hvleft | hvprev
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvpref | hvleg
    · exact Or.inl
        (SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
          (H.attach_mem_rim i).1 hvpref)
    · exact Or.inr (Or.inl hvleg)
  · rw [SimpleGraph.Walk.support_reverse] at hvprev
    exact Or.inr (Or.inr (List.mem_reverse.mp hvprev))

theorem Tripod.crossPrefixThirdRim_support_cases
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j k : Fin 3}
    {x v : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hv :
      v ∈ (((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k)).support) :
    v ∈ (H.rim j).support ∨ v ∈ (H.rim k).support := by
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hvprefrev | hvk
  · rw [SimpleGraph.Walk.support_reverse] at hvprefrev
    exact Or.inl
      (SimpleGraph.Walk.support_takeUntil_subset (H.rim j) hxj.1
        (List.mem_reverse.mp hvprefrev))
  · exact Or.inr hvk

theorem Tripod.crossSuffixThirdRim_support_cases
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j k : Fin 3}
    {x v : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hv :
      v ∈ ((H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse).support) :
    v ∈ (H.rim k).support ∨ v ∈ (H.rim j).support := by
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hvk | hvsuffrev
  · exact Or.inl hvk
  · rw [SimpleGraph.Walk.support_reverse] at hvsuffrev
    exact Or.inr
      (SimpleGraph.Walk.support_dropUntil_subset (H.rim j) hxj.1
        (List.mem_reverse.mp hvsuffrev))

theorem Tripod.crossPrefixPositiveRim_oldLeg_meets_only_at_attach_of_trim_clean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (p : G.Walk x (feet i))
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet) :
    forall j : Fin 3, j ≠ i ->
      forall v : V, v ∈ (H.leg j).support ->
        v ∈
          ((p.append (H.leg i).reverse).append
            ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)).support ->
          v = H.attach j := by
  intro j hji v hvleg hvnew
  rcases H.crossPrefixPositiveRim_support_cases p hvnew with hvp | hvleg_or_rim
  · exact False.elim
      (hp_clean v hvp ⟨j, by
        simpa [Tripod.trimPositiveLeg, Tripod.trimPositiveLegLeg, hji] using hvleg⟩)
  · rcases hvleg_or_rim with hvi | hvrim
    · exact False.elim
        (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg hvi)
    · exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim

theorem Tripod.crossSuffixPositiveRim_oldLeg_meets_only_at_attach_of_trim_clean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (p : G.Walk x (feet i))
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet) :
    forall j : Fin 3, j ≠ i ->
      forall v : V, v ∈ (H.leg j).support ->
        v ∈
          ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
            (H.leg i)).append p.reverse).support ->
          v = H.attach j := by
  intro j hji v hvleg hvnew
  rcases H.crossSuffixPositiveRim_support_cases p hvnew with hvrim | hvleg_or_p
  · exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim
  · rcases hvleg_or_p with hvi | hvp
    · exact False.elim
        (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg hvi)
    · exact False.elim
        (hp_clean v hvp ⟨j, by
          simpa [Tripod.trimPositiveLeg, Tripod.trimPositiveLegLeg, hji] using hvleg⟩)

theorem Tripod.crossPrefixSplitRim_oldLeg_meets_only_at_attach
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j l : Fin 3}
    {x v : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hvleg : v ∈ (H.leg l).support)
    (hvrim : v ∈ ((H.rim j).dropUntil x hxj.1).support) :
    v = H.attach l :=
  H.leg_meets_rims_only_at_attach l j v hvleg
    (SimpleGraph.Walk.support_dropUntil_subset (H.rim j) hxj.1 hvrim)

theorem Tripod.crossSuffixSplitRim_oldLeg_meets_only_at_attach
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j l : Fin 3}
    {x v : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hvleg : v ∈ (H.leg l).support)
    (hvrim : v ∈ ((H.rim j).takeUntil x hxj.1).support) :
    v = H.attach l :=
  H.leg_meets_rims_only_at_attach l j v hvleg
    (SimpleGraph.Walk.support_takeUntil_subset (H.rim j) hxj.1 hvrim)

theorem Tripod.crossPrefixThirdRim_oldLeg_meets_only_at_attach
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j k l : Fin 3}
    {x v : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hvleg : v ∈ (H.leg l).support)
    (hvrim :
      v ∈ (((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k)).support) :
    v = H.attach l := by
  rcases H.crossPrefixThirdRim_support_cases hxj hvrim with hvj | hvk
  · exact H.leg_meets_rims_only_at_attach l j v hvleg hvj
  · exact H.leg_meets_rims_only_at_attach l k v hvleg hvk

theorem Tripod.crossSuffixThirdRim_oldLeg_meets_only_at_attach
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j k l : Fin 3}
    {x v : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hvleg : v ∈ (H.leg l).support)
    (hvrim :
      v ∈ ((H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse).support) :
    v = H.attach l := by
  rcases H.crossSuffixThirdRim_support_cases hxj hvrim with hvk | hvj
  · exact H.leg_meets_rims_only_at_attach l k v hvleg hvk
  · exact H.leg_meets_rims_only_at_attach l j v hvleg hvj


end Schematic.Math.GraphTheory
