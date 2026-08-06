import DominatingFourColour.Prerequisites.TripodPrefix.CrossRimPaths

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
theorem Tripod.crossPrefixSplitRim_internal_disjoint_thirdRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j k : Fin 3}
    (hjk : j ≠ k)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j)) :
    Disjoint
      (Walk.InternalVertices ((H.rim j).dropUntil x hxj.1))
      (Walk.InternalVertices
        (((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k))) := by
  rw [Set.disjoint_left]
  intro v hvdrop hvthird
  have hvthird_support : v ∈
      (((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k)).support :=
    hvthird.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvthird_support
  rcases hvthird_support with hvprefrev | hvk
  · rw [SimpleGraph.Walk.support_reverse] at hvprefrev
    have hvpref :
        v ∈ ((H.rim j).takeUntil x hxj.1).support :=
      List.mem_reverse.mp hvprefrev
    have hvx :
        v = x :=
      Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        (H.rim_isPath j) hxj.1 hvpref hvdrop.1
    exact hvdrop.2.1 hvx
  · have hvj : v ∈ (H.rim j).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim j) hxj.1 hvdrop.1
    have hv_ne_left : v ≠ H.left := by
      intro hvleft
      have hleft_not_drop :
          H.left ∉ ((H.rim j).dropUntil x hxj.1).support :=
        Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          (H.rim_isPath j) hxj.1 hxj.2.1
      exact hleft_not_drop (hvleft ▸ hvdrop.1)
    have hvj_internal : v ∈ Walk.InternalVertices (H.rim j) :=
      ⟨hvj, hv_ne_left, hvdrop.2.2⟩
    have hvk_internal : v ∈ Walk.InternalVertices (H.rim k) :=
      ⟨hvk, hv_ne_left, hvthird.2.2⟩
    exact Set.disjoint_left.mp (H.rim_internals_disjoint j k hjk)
      hvj_internal hvk_internal

theorem Tripod.crossSuffixSplitRim_internal_disjoint_thirdRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {j k : Fin 3}
    (hjk : j ≠ k)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j)) :
    Disjoint
      (Walk.InternalVertices ((H.rim j).takeUntil x hxj.1))
      (Walk.InternalVertices
        ((H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse)) := by
  rw [Set.disjoint_left]
  intro v hvtake hvthird
  have hvthird_support : v ∈
      ((H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse).support :=
    hvthird.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvthird_support
  rcases hvthird_support with hvk | hvsuffrev
  · have hvj : v ∈ (H.rim j).support :=
      SimpleGraph.Walk.support_takeUntil_subset (H.rim j) hxj.1 hvtake.1
    have hv_ne_right : v ≠ H.right := by
      intro hvright
      have hright_not_take :
          H.right ∉ ((H.rim j).takeUntil x hxj.1).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (H.rim_isPath j) hxj.1 hxj.2.2.symm
      exact hright_not_take (hvright ▸ hvtake.1)
    have hvj_internal : v ∈ Walk.InternalVertices (H.rim j) :=
      ⟨hvj, hvtake.2.1, hv_ne_right⟩
    have hvk_internal : v ∈ Walk.InternalVertices (H.rim k) :=
      ⟨hvk, hvthird.2.1, hv_ne_right⟩
    exact Set.disjoint_left.mp (H.rim_internals_disjoint j k hjk)
      hvj_internal hvk_internal
  · rw [SimpleGraph.Walk.support_reverse] at hvsuffrev
    have hvsuff :
        v ∈ ((H.rim j).dropUntil x hxj.1).support :=
      List.mem_reverse.mp hvsuffrev
    have hvx :
        v = x :=
      Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        (H.rim_isPath j) hxj.1 hvtake.1 hvsuff
    exact hvtake.2.2 hvx

private theorem Tripod.crossPrefixSegmentRim_internal_disjoint_splitRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (q : G.Walk (H.attach i) y)
    (hq_leg : forall v : V, v ∈ q.support -> v ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((p.append q.reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)))
      (Walk.InternalVertices ((H.rim j).dropUntil x hxj.1)) := by
  rw [Set.disjoint_left]
  intro v hvpos hvsplit
  have hvsplit_rim : v ∈ (H.rim j).support :=
    SimpleGraph.Walk.support_dropUntil_subset (H.rim j) hxj.1 hvsplit.1
  have hvsplit_ne_left : v ≠ H.left := by
    intro hvleft
    have hleft_not_drop :
        H.left ∉ ((H.rim j).dropUntil x hxj.1).support :=
      Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
        (H.rim_isPath j) hxj.1 hxj.2.1
    exact hleft_not_drop (hvleft ▸ hvsplit.1)
  have hvsplit_internal : v ∈ Walk.InternalVertices (H.rim j) :=
    ⟨hvsplit_rim, hvsplit_ne_left, hvsplit.2.2⟩
  have hvpos_support :
      v ∈
        ((p.append q.reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)).support :=
    hvpos.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvpos_support
  rcases hvpos_support with hvleft | hvsuff
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvp | hvqrev
    · have hvx : v = x := hp_meets_rims j v hvp hvsplit_rim
      exact hvpos.2.1 hvx
    · rw [SimpleGraph.Walk.support_reverse] at hvqrev
      have hvleg : v ∈ (H.leg i).support :=
        hq_leg v (List.mem_reverse.mp hvqrev)
      have hv_attach : v = H.attach i :=
        H.leg_meets_rims_only_at_attach i j v hvleg hvsplit_rim
      have hvi_internal : v ∈ Walk.InternalVertices (H.rim i) := by
        simpa [← hv_attach] using H.attach_mem_rim i
      exact Set.disjoint_left.mp
        (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
        hvi_internal hvsplit_internal
  · have hvi_support : v ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvsuff
    have hv_ne_left : v ≠ H.left := by
      intro hvleft
      have hleft_not_suff :
          H.left ∉
            ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1).support :=
        Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          (H.rim_isPath i) (H.attach_mem_rim i).1 (H.attach_ne_left i)
      exact hleft_not_suff (hvleft ▸ hvsuff)
    have hvi_internal : v ∈ Walk.InternalVertices (H.rim i) :=
      ⟨hvi_support, hv_ne_left, hvpos.2.2⟩
    exact Set.disjoint_left.mp
      (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
      hvi_internal hvsplit_internal

private theorem Tripod.crossSuffixSegmentRim_internal_disjoint_splitRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (q : G.Walk (H.attach i) y)
    (hq_leg : forall v : V, v ∈ q.support -> v ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append q).append
          p.reverse))
      (Walk.InternalVertices ((H.rim j).takeUntil x hxj.1)) := by
  rw [Set.disjoint_left]
  intro v hvpos hvsplit
  have hvsplit_rim : v ∈ (H.rim j).support :=
    SimpleGraph.Walk.support_takeUntil_subset (H.rim j) hxj.1 hvsplit.1
  have hvsplit_ne_right : v ≠ H.right := by
    intro hvright
    have hright_not_take :
        H.right ∉ ((H.rim j).takeUntil x hxj.1).support :=
      SimpleGraph.Walk.endpoint_notMem_support_takeUntil
        (H.rim_isPath j) hxj.1 hxj.2.2.symm
    exact hright_not_take (hvright ▸ hvsplit.1)
  have hvsplit_internal : v ∈ Walk.InternalVertices (H.rim j) :=
    ⟨hvsplit_rim, hvsplit.2.1, hvsplit_ne_right⟩
  have hvpos_support :
      v ∈
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append q).append
          p.reverse).support :=
    hvpos.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvpos_support
  rcases hvpos_support with hvleft | hvprev
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvpref | hvq
    · have hvi_support : v ∈ (H.rim i).support :=
        SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
          (H.attach_mem_rim i).1 hvpref
      have hv_ne_right : v ≠ H.right := by
        intro hvright
        have hright_not_pref :
            H.right ∉
              ((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).support :=
          SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            (H.rim_isPath i) (H.attach_mem_rim i).1 (H.attach_ne_right i).symm
        exact hright_not_pref (hvright ▸ hvpref)
      have hvi_internal : v ∈ Walk.InternalVertices (H.rim i) :=
        ⟨hvi_support, hvpos.2.1, hv_ne_right⟩
      exact Set.disjoint_left.mp
        (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
        hvi_internal hvsplit_internal
    · have hvleg : v ∈ (H.leg i).support := hq_leg v hvq
      have hv_attach : v = H.attach i :=
        H.leg_meets_rims_only_at_attach i j v hvleg hvsplit_rim
      have hvi_internal : v ∈ Walk.InternalVertices (H.rim i) := by
        simpa [← hv_attach] using H.attach_mem_rim i
      exact Set.disjoint_left.mp
        (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
        hvi_internal hvsplit_internal
  · rw [SimpleGraph.Walk.support_reverse] at hvprev
    have hvp : v ∈ p.support := List.mem_reverse.mp hvprev
    have hvx : v = x := hp_meets_rims j v hvp hvsplit_rim
    exact hvpos.2.2 hvx

theorem Tripod.crossPrefixPositiveRim_internal_disjoint_splitRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (p : G.Walk x (feet i))
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((p.append (H.leg i).reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)))
      (Walk.InternalVertices ((H.rim j).dropUntil x hxj.1)) := by
  exact H.crossPrefixSegmentRim_internal_disjoint_splitRim hji hxj
    (H.leg i) (fun _ hv => hv) p hp_meets_rims

theorem Tripod.crossSuffixPositiveRim_internal_disjoint_splitRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (p : G.Walk x (feet i))
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
          (H.leg i)).append p.reverse))
      (Walk.InternalVertices ((H.rim j).takeUntil x hxj.1)) := by
  exact H.crossSuffixSegmentRim_internal_disjoint_splitRim hji hxj
    (H.leg i) (fun _ hv => hv) p hp_meets_rims

private theorem Tripod.crossPrefixSegmentRim_internal_disjoint_thirdRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j k : Fin 3}
    (hji : j ≠ i)
    (hki : k ≠ i)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (q : G.Walk (H.attach i) y)
    (hq_leg : forall v : V, v ∈ q.support -> v ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((p.append q.reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)))
      (Walk.InternalVertices
        (((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k))) := by
  rw [Set.disjoint_left]
  intro v hvpos hvthird
  have hvpos_support :
      v ∈
        ((p.append q.reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)).support :=
    hvpos.1
  have hvthird_support :
      v ∈ (((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k)).support :=
    hvthird.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvthird_support
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvpos_support
  rcases hvpos_support with hvleft | hvsuff
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvp | hvqrev
    · rcases hvthird_support with hvprefrev | hvk
      · rw [SimpleGraph.Walk.support_reverse] at hvprefrev
        have hvj : v ∈ (H.rim j).support :=
          SimpleGraph.Walk.support_takeUntil_subset (H.rim j) hxj.1
            (List.mem_reverse.mp hvprefrev)
        have hvx : v = x := hp_meets_rims j v hvp hvj
        exact hvpos.2.1 hvx
      · have hvx : v = x := hp_meets_rims k v hvp hvk
        exact hvpos.2.1 hvx
    · rw [SimpleGraph.Walk.support_reverse] at hvqrev
      have hvleg : v ∈ (H.leg i).support :=
        hq_leg v (List.mem_reverse.mp hvqrev)
      rcases hvthird_support with hvprefrev | hvk
      · rw [SimpleGraph.Walk.support_reverse] at hvprefrev
        have hvj : v ∈ (H.rim j).support :=
          SimpleGraph.Walk.support_takeUntil_subset (H.rim j) hxj.1
            (List.mem_reverse.mp hvprefrev)
        have hv_attach : v = H.attach i :=
          H.leg_meets_rims_only_at_attach i j v hvleg hvj
        have hvi_internal : v ∈ Walk.InternalVertices (H.rim i) := by
          simpa [← hv_attach] using H.attach_mem_rim i
        have hvj_internal : v ∈ Walk.InternalVertices (H.rim j) := by
          refine ⟨hvj, ?_, ?_⟩
          · intro hv_left
            exact H.attach_ne_left i (hv_attach.symm.trans hv_left)
          · intro hv_right
            exact H.attach_ne_right i (hv_attach.symm.trans hv_right)
        exact Set.disjoint_left.mp
          (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
          hvi_internal hvj_internal
      · have hv_attach : v = H.attach i :=
          H.leg_meets_rims_only_at_attach i k v hvleg hvk
        have hvi_internal : v ∈ Walk.InternalVertices (H.rim i) := by
          simpa [← hv_attach] using H.attach_mem_rim i
        have hvk_internal : v ∈ Walk.InternalVertices (H.rim k) := by
          refine ⟨hvk, ?_, ?_⟩
          · intro hv_left
            exact H.attach_ne_left i (hv_attach.symm.trans hv_left)
          · intro hv_right
            exact H.attach_ne_right i (hv_attach.symm.trans hv_right)
        exact Set.disjoint_left.mp
          (H.rim_internals_disjoint i k (fun hik => hki hik.symm))
          hvi_internal hvk_internal
  · have hvi_support : v ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvsuff
    have hv_ne_left : v ≠ H.left := by
      intro hvleft
      have hleft_not_suff :
          H.left ∉
            ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1).support :=
        Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          (H.rim_isPath i) (H.attach_mem_rim i).1 (H.attach_ne_left i)
      exact hleft_not_suff (hvleft ▸ hvsuff)
    have hvi_internal : v ∈ Walk.InternalVertices (H.rim i) :=
      ⟨hvi_support, hv_ne_left, hvpos.2.2⟩
    rcases hvthird_support with hvprefrev | hvk
    · rw [SimpleGraph.Walk.support_reverse] at hvprefrev
      have hvj : v ∈ (H.rim j).support :=
        SimpleGraph.Walk.support_takeUntil_subset (H.rim j) hxj.1
          (List.mem_reverse.mp hvprefrev)
      by_cases hv_left : v = H.left
      · exact hv_ne_left hv_left
      · have hvj_internal : v ∈ Walk.InternalVertices (H.rim j) :=
          ⟨hvj, hv_left, hvthird.2.2⟩
        exact Set.disjoint_left.mp
          (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
          hvi_internal hvj_internal
    · have hvk_internal : v ∈ Walk.InternalVertices (H.rim k) :=
        ⟨hvk, hv_ne_left, hvthird.2.2⟩
      exact Set.disjoint_left.mp
        (H.rim_internals_disjoint i k (fun hik => hki hik.symm))
        hvi_internal hvk_internal

private theorem Tripod.crossSuffixSegmentRim_internal_disjoint_thirdRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j k : Fin 3}
    (hji : j ≠ i)
    (hki : k ≠ i)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (q : G.Walk (H.attach i) y)
    (hq_leg : forall v : V, v ∈ q.support -> v ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append q).append
          p.reverse))
      (Walk.InternalVertices
        ((H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse)) := by
  rw [Set.disjoint_left]
  intro v hvpos hvthird
  have hvpos_support :
      v ∈
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append q).append
          p.reverse).support :=
    hvpos.1
  have hvthird_support :
      v ∈ ((H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse).support :=
    hvthird.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvthird_support
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvpos_support
  rcases hvpos_support with hvleft | hvprev
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvpref | hvq
    · have hvi_support : v ∈ (H.rim i).support :=
        SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
          (H.attach_mem_rim i).1 hvpref
      have hv_ne_right : v ≠ H.right := by
        intro hvright
        have hright_not_pref :
            H.right ∉
              ((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).support :=
          SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            (H.rim_isPath i) (H.attach_mem_rim i).1 (H.attach_ne_right i).symm
        exact hright_not_pref (hvright ▸ hvpref)
      have hvi_internal : v ∈ Walk.InternalVertices (H.rim i) :=
        ⟨hvi_support, hvpos.2.1, hv_ne_right⟩
      rcases hvthird_support with hvk | hvsuffrev
      · have hvk_internal : v ∈ Walk.InternalVertices (H.rim k) :=
          ⟨hvk, hvthird.2.1, hv_ne_right⟩
        exact Set.disjoint_left.mp
          (H.rim_internals_disjoint i k (fun hik => hki hik.symm))
          hvi_internal hvk_internal
      · rw [SimpleGraph.Walk.support_reverse] at hvsuffrev
        have hvsuff :
            v ∈ ((H.rim j).dropUntil x hxj.1).support :=
          List.mem_reverse.mp hvsuffrev
        have hvj : v ∈ (H.rim j).support :=
          SimpleGraph.Walk.support_dropUntil_subset (H.rim j) hxj.1 hvsuff
        have hv_ne_left : v ≠ H.left := by
          intro hvleft
          have hleft_not_drop :
              H.left ∉ ((H.rim j).dropUntil x hxj.1).support :=
            Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
              (H.rim_isPath j) hxj.1 hxj.2.1
          exact hleft_not_drop (hvleft ▸ hvsuff)
        have hvj_internal : v ∈ Walk.InternalVertices (H.rim j) :=
          ⟨hvj, hv_ne_left, hv_ne_right⟩
        exact Set.disjoint_left.mp
          (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
          hvi_internal hvj_internal
    · have hvleg : v ∈ (H.leg i).support := hq_leg v hvq
      rcases hvthird_support with hvk | hvsuffrev
      · have hv_attach : v = H.attach i :=
          H.leg_meets_rims_only_at_attach i k v hvleg hvk
        have hvi_internal : v ∈ Walk.InternalVertices (H.rim i) := by
          simpa [← hv_attach] using H.attach_mem_rim i
        have hvk_internal : v ∈ Walk.InternalVertices (H.rim k) := by
          refine ⟨hvk, ?_, ?_⟩
          · intro hv_left
            exact H.attach_ne_left i (hv_attach.symm.trans hv_left)
          · intro hv_right
            exact H.attach_ne_right i (hv_attach.symm.trans hv_right)
        exact Set.disjoint_left.mp
          (H.rim_internals_disjoint i k (fun hik => hki hik.symm))
          hvi_internal hvk_internal
      · rw [SimpleGraph.Walk.support_reverse] at hvsuffrev
        have hvsuff :
            v ∈ ((H.rim j).dropUntil x hxj.1).support :=
          List.mem_reverse.mp hvsuffrev
        have hvj : v ∈ (H.rim j).support :=
          SimpleGraph.Walk.support_dropUntil_subset (H.rim j) hxj.1 hvsuff
        have hv_attach : v = H.attach i :=
          H.leg_meets_rims_only_at_attach i j v hvleg hvj
        have hvi_internal : v ∈ Walk.InternalVertices (H.rim i) := by
          simpa [← hv_attach] using H.attach_mem_rim i
        have hvj_internal : v ∈ Walk.InternalVertices (H.rim j) := by
          refine ⟨hvj, ?_, ?_⟩
          · intro hv_left
            exact H.attach_ne_left i (hv_attach.symm.trans hv_left)
          · intro hv_right
            exact H.attach_ne_right i (hv_attach.symm.trans hv_right)
        exact Set.disjoint_left.mp
          (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
          hvi_internal hvj_internal
  · rw [SimpleGraph.Walk.support_reverse] at hvprev
    have hvp : v ∈ p.support := List.mem_reverse.mp hvprev
    rcases hvthird_support with hvk | hvsuffrev
    · have hvx : v = x := hp_meets_rims k v hvp hvk
      exact hvpos.2.2 hvx
    · rw [SimpleGraph.Walk.support_reverse] at hvsuffrev
      have hvsuff :
          v ∈ ((H.rim j).dropUntil x hxj.1).support :=
        List.mem_reverse.mp hvsuffrev
      have hvj : v ∈ (H.rim j).support :=
        SimpleGraph.Walk.support_dropUntil_subset (H.rim j) hxj.1 hvsuff
      have hvx : v = x := hp_meets_rims j v hvp hvj
      exact hvpos.2.2 hvx

theorem Tripod.crossPrefixPositiveRim_internal_disjoint_thirdRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j k : Fin 3}
    (hji : j ≠ i)
    (hki : k ≠ i)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (p : G.Walk x (feet i))
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((p.append (H.leg i).reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)))
      (Walk.InternalVertices
        (((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k))) := by
  exact H.crossPrefixSegmentRim_internal_disjoint_thirdRim hji hki hxj
    (H.leg i) (fun _ hv => hv) p hp_meets_rims

theorem Tripod.crossSuffixPositiveRim_internal_disjoint_thirdRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j k : Fin 3}
    (hji : j ≠ i)
    (hki : k ≠ i)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (p : G.Walk x (feet i))
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
          (H.leg i)).append p.reverse))
      (Walk.InternalVertices
        ((H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse)) := by
  exact H.crossSuffixSegmentRim_internal_disjoint_thirdRim hji hki hxj
    (H.leg i) (fun _ hv => hv) p hp_meets_rims

theorem Tripod.crossPrefixHitRim_internal_disjoint_splitRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hy : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((p.append ((H.leg i).takeUntil y hy).reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)))
      (Walk.InternalVertices ((H.rim j).dropUntil x hxj.1)) := by
  exact H.crossPrefixSegmentRim_internal_disjoint_splitRim hji hxj
    ((H.leg i).takeUntil y hy)
    (fun _ hv => SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy hv)
    p hp_meets_rims

theorem Tripod.crossSuffixHitRim_internal_disjoint_splitRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hy : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
          ((H.leg i).takeUntil y hy)).append p.reverse))
      (Walk.InternalVertices ((H.rim j).takeUntil x hxj.1)) := by
  exact H.crossSuffixSegmentRim_internal_disjoint_splitRim hji hxj
    ((H.leg i).takeUntil y hy)
    (fun _ hv => SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy hv)
    p hp_meets_rims

theorem Tripod.crossPrefixHitRim_internal_disjoint_thirdRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j k : Fin 3}
    (hji : j ≠ i)
    (hki : k ≠ i)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hy : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((p.append ((H.leg i).takeUntil y hy).reverse).append
          ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)))
      (Walk.InternalVertices
        (((H.rim j).takeUntil x hxj.1).reverse.append (H.rim k))) := by
  exact H.crossPrefixSegmentRim_internal_disjoint_thirdRim hji hki hxj
    ((H.leg i).takeUntil y hy)
    (fun _ hv => SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy hv)
    p hp_meets_rims

theorem Tripod.crossSuffixHitRim_internal_disjoint_thirdRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j k : Fin 3}
    (hji : j ≠ i)
    (hki : k ≠ i)
    {x y : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hy : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Disjoint
      (Walk.InternalVertices
        ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
          ((H.leg i).takeUntil y hy)).append p.reverse))
      (Walk.InternalVertices
        ((H.rim k).append ((H.rim j).dropUntil x hxj.1).reverse)) := by
  exact H.crossSuffixSegmentRim_internal_disjoint_thirdRim hji hki hxj
    ((H.leg i).takeUntil y hy)
    (fun _ hv => SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy hv)
    p hp_meets_rims


end Schematic.Math.GraphTheory
