import DominatingFourColour.Prerequisites.Triad.TripodReplacement

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

def Tripod.prefixFootRerouteRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    {x : V}
    (hx_rim : x ∈ (H.rim i).support)
    (p : G.Walk x (feet i)) :
    G.Walk H.left H.right :=
  ((((H.rim i).takeUntil x hx_rim).append p).append
    (H.leg i).reverse).append
      ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)

theorem Tripod.prefixFootRerouteRim_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x : V}
    (hx_rim : x ∈ (H.rim i).support)
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_meets_leg_only_at_foot :
      forall v : V, v ∈ p.support -> v ∈ (H.leg i).support ->
        v = feet i)
    (hp_meets_rim :
      forall v : V, v ∈ p.support -> v ∈ (H.rim i).support -> v = x)
    (hidx :
      (H.rim i).support.idxOf x <
        (H.rim i).support.idxOf (H.attach i)) :
    (H.prefixFootRerouteRim i hx_rim p).IsPath := by
  let r : G.Walk H.left H.right := H.rim i
  let pref : G.Walk H.left x := r.takeUntil x (by simpa [r] using hx_rim)
  let suff : G.Walk (H.attach i) H.right :=
    r.dropUntil (H.attach i) (by simpa [r] using (H.attach_mem_rim i).1)
  have hpref : pref.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil r (by simpa [r] using hx_rim))
      (by simpa [r] using H.rim_isPath i)
  have hsuff : suff.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_dropUntil r
        (by simpa [r] using (H.attach_mem_rim i).1))
      (by simpa [r] using H.rim_isPath i)
  have hprefp : (pref.append p).IsPath := by
    refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint hpref hp ?_
    intro z hzpref hzp
    have hzrim : z ∈ (H.rim i).support := by
      have hzrim' : z ∈ r.support :=
        SimpleGraph.Walk.support_takeUntil_subset r
          (by simpa [r] using hx_rim) (by simpa [pref] using hzpref)
      simpa [r] using hzrim'
    exact hp_meets_rim z hzp hzrim
  have hlegrev : (H.leg i).reverse.IsPath := (H.leg_isPath i).reverse
  have hprefp_leg : ((pref.append p).append (H.leg i).reverse).IsPath := by
    refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint hprefp hlegrev ?_
    intro z hzprefp hzlegrev
    rw [SimpleGraph.Walk.support_reverse] at hzlegrev
    have hzleg : z ∈ (H.leg i).support := List.mem_reverse.mp hzlegrev
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzprefp
    rcases hzprefp with hzpref | hzp
    · exfalso
      have hzrim : z ∈ (H.rim i).support := by
        have hzrim' : z ∈ r.support :=
          SimpleGraph.Walk.support_takeUntil_subset r
            (by simpa [r] using hx_rim) (by simpa [pref] using hzpref)
        simpa [r] using hzrim'
      have hz_attach : z = H.attach i :=
        H.leg_meets_rims_only_at_attach i i z hzleg hzrim
      have hattach_pref : H.attach i ∈ pref.support := by
        simpa [hz_attach] using hzpref
      have hle :
          (H.rim i).support.idxOf (H.attach i) <=
            (H.rim i).support.idxOf x := by
        have hle' :=
          Schematic.Math.GraphTheory.Walk.idxOf_le_of_mem_takeUntil
            (p := r) (x := x) (z := H.attach i)
            (by simpa [r] using hx_rim) (by simpa [pref] using hattach_pref)
        simpa [r] using hle'
      omega
    · by_cases hzfoot : z = feet i
      · exact hzfoot
      · exact hp_meets_leg_only_at_foot z hzp hzleg
  refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
    hprefp_leg hsuff ?_
  intro z hzleft hzsuff
  have hzrim_suff : z ∈ (H.rim i).support := by
    have hzrim' : z ∈ r.support :=
      SimpleGraph.Walk.support_dropUntil_subset r
        (by simpa [r] using (H.attach_mem_rim i).1)
        (by simpa [suff] using hzsuff)
    simpa [r] using hzrim'
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzleft
  rcases hzleft with hzprefp | hzlegrev
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzprefp
    rcases hzprefp with hzpref | hzp
    · exfalso
      have hdis :
          Disjoint
            {z : V | z ∈ (r.takeUntil x (by simpa [r] using hx_rim)).support}
            {z : V |
              z ∈ (r.dropUntil (H.attach i)
                (by simpa [r] using (H.attach_mem_rim i).1)).support} := by
        exact Schematic.Math.GraphTheory.Walk.IsPath.takeUntil_support_disjoint_dropUntil_support_of_idx_lt
          (p := r)
          (by simpa [r] using H.rim_isPath i)
          (by simpa [r] using hx_rim)
          (by simpa [r] using (H.attach_mem_rim i).1)
          (by simpa [r] using hidx)
      exact Set.disjoint_left.mp hdis (by simpa [pref] using hzpref)
        (by simpa [suff] using hzsuff)
    · exfalso
      have hz_eq_x : z = x := hp_meets_rim z hzp hzrim_suff
      subst z
      have hle :
          (H.rim i).support.idxOf (H.attach i) <=
            (H.rim i).support.idxOf x := by
        have hle' :=
          Schematic.Math.GraphTheory.Walk.idxOf_le_of_mem_dropUntil
            (p := r)
            (by simpa [r] using H.rim_isPath i)
            (by simpa [r] using (H.attach_mem_rim i).1)
            (by simpa [suff] using hzsuff)
        simpa [r] using hle'
      omega
  · rw [SimpleGraph.Walk.support_reverse] at hzlegrev
    have hzleg : z ∈ (H.leg i).support := List.mem_reverse.mp hzlegrev
    exact H.leg_meets_rims_only_at_attach i i z hzleg hzrim_suff

end Schematic.Math.GraphTheory

