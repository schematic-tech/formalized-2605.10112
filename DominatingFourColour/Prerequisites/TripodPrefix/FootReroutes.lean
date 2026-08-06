import DominatingFourColour.Prerequisites.Triad.PrefixFootRerouting
import Schematic.Math.GraphTheory.PathsTrees.Foundations.PathIntervals

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
theorem Tripod.exists_legLengthSum_lt_of_prefix_foot_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx_rim : x ∈ (H.rim i).support)
    (p : G.Walk x (feet i))
    (hnewRim_path : (H.prefixFootRerouteRim i hx_rim p).IsPath)
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
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  let newRim : G.Walk H.left H.right := H.prefixFootRerouteRim i hx_rim p
  have hfoot_support : feet i ∈ newRim.support := by
    dsimp [newRim, Tripod.prefixFootRerouteRim]
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr p.end_mem_support
  have hfoot_internal : feet i ∈ Walk.InternalVertices newRim := by
    exact ⟨hfoot_support, (H.left_not_foot i).symm,
      (H.right_not_foot i).symm⟩
  exact H.exists_legLengthSum_lt_of_replaceRim_attach_foot
    hpos newRim hfoot_internal (by simpa [newRim] using hnewRim_path)
    (by simpa [newRim] using hrim_disjoint)
    (by simpa [newRim] using holdLeg_meets_newRim)

def Tripod.suffixFootRerouteRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    {x : V}
    (hx_rim : x ∈ (H.rim i).support)
    (p : G.Walk x (feet i)) :
    G.Walk H.left H.right :=
  ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
    (H.leg i)).append p.reverse).append
      ((H.rim i).dropUntil x hx_rim)

theorem Tripod.suffixFootRerouteRim_isPath
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
      (H.rim i).support.idxOf (H.attach i) <
        (H.rim i).support.idxOf x) :
    (H.suffixFootRerouteRim i hx_rim p).IsPath := by
  let r : G.Walk H.left H.right := H.rim i
  let pref : G.Walk H.left (H.attach i) :=
    r.takeUntil (H.attach i) (by simpa [r] using (H.attach_mem_rim i).1)
  let suff : G.Walk x H.right := r.dropUntil x (by simpa [r] using hx_rim)
  have hpref : pref.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil r
        (by simpa [r] using (H.attach_mem_rim i).1))
      (by simpa [r] using H.rim_isPath i)
  have hsuff : suff.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_dropUntil r (by simpa [r] using hx_rim))
      (by simpa [r] using H.rim_isPath i)
  have hpref_leg : (pref.append (H.leg i)).IsPath := by
    refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
      hpref (H.leg_isPath i) ?_
    intro z hzpref hzleg
    have hzrim : z ∈ (H.rim i).support := by
      have hzrim' : z ∈ r.support :=
        SimpleGraph.Walk.support_takeUntil_subset r
          (by simpa [r] using (H.attach_mem_rim i).1)
          (by simpa [pref] using hzpref)
      simpa [r] using hzrim'
    exact H.leg_meets_rims_only_at_attach i i z hzleg hzrim
  have hrev : p.reverse.IsPath := hp.reverse
  have hpref_leg_rev : ((pref.append (H.leg i)).append p.reverse).IsPath := by
    refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
      hpref_leg hrev ?_
    intro z hzleft hzrev
    rw [SimpleGraph.Walk.support_reverse] at hzrev
    have hzp : z ∈ p.support := List.mem_reverse.mp hzrev
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzleft
    rcases hzleft with hzpref | hzleg
    · exfalso
      have hzrim : z ∈ (H.rim i).support := by
        have hzrim' : z ∈ r.support :=
          SimpleGraph.Walk.support_takeUntil_subset r
            (by simpa [r] using (H.attach_mem_rim i).1)
            (by simpa [pref] using hzpref)
        simpa [r] using hzrim'
      have hz_eq_x : z = x := hp_meets_rim z hzp hzrim
      have hx_pref : x ∈ pref.support := by
        simpa [hz_eq_x] using hzpref
      have hle :
          (H.rim i).support.idxOf x <=
            (H.rim i).support.idxOf (H.attach i) := by
        have hle' :=
          Schematic.Math.GraphTheory.Walk.idxOf_le_of_mem_takeUntil
            (p := r) (x := H.attach i) (z := x)
            (by simpa [r] using (H.attach_mem_rim i).1)
            (by simpa [pref] using hx_pref)
        simpa [r] using hle'
      omega
    · exact hp_meets_leg_only_at_foot z hzp hzleg
  refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
    hpref_leg_rev hsuff ?_
  intro z hzleft hzsuff
  have hzrim_suff : z ∈ (H.rim i).support := by
    have hzrim' : z ∈ r.support :=
      SimpleGraph.Walk.support_dropUntil_subset r
        (by simpa [r] using hx_rim) (by simpa [suff] using hzsuff)
    simpa [r] using hzrim'
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzleft
  rcases hzleft with hzpref_leg | hzrev
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzpref_leg
    rcases hzpref_leg with hzpref | hzleg
    · exfalso
      have hdis :
          Disjoint
            {z : V |
              z ∈ (r.takeUntil (H.attach i)
                (by simpa [r] using (H.attach_mem_rim i).1)).support}
            {z : V | z ∈ (r.dropUntil x (by simpa [r] using hx_rim)).support} := by
        exact Schematic.Math.GraphTheory.Walk.IsPath.takeUntil_support_disjoint_dropUntil_support_of_idx_lt
          (p := r)
          (by simpa [r] using H.rim_isPath i)
          (by simpa [r] using (H.attach_mem_rim i).1)
          (by simpa [r] using hx_rim)
          (by simpa [r] using hidx)
      exact Set.disjoint_left.mp hdis (by simpa [pref] using hzpref)
        (by simpa [suff] using hzsuff)
    · exfalso
      have hz_attach : z = H.attach i :=
        H.leg_meets_rims_only_at_attach i i z hzleg hzrim_suff
      subst z
      have hle :
          (H.rim i).support.idxOf x <=
            (H.rim i).support.idxOf (H.attach i) := by
        have hle' :=
          Schematic.Math.GraphTheory.Walk.idxOf_le_of_mem_dropUntil
            (p := r)
            (by simpa [r] using H.rim_isPath i)
            (by simpa [r] using hx_rim)
            (by simpa [suff] using hzsuff)
        simpa [r] using hle'
      omega
  · rw [SimpleGraph.Walk.support_reverse] at hzrev
    have hzp : z ∈ p.support := List.mem_reverse.mp hzrev
    exact hp_meets_rim z hzp hzrim_suff

def Tripod.prefixLegHitRerouteRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk x y) :
    G.Walk H.left H.right :=
  ((((H.rim i).takeUntil x hx_rim).append p).append
    ((H.leg i).takeUntil y hy_leg).reverse).append
      ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1)

def Tripod.suffixLegHitRerouteRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk x y) :
    G.Walk H.left H.right :=
  ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
    ((H.leg i).takeUntil y hy_leg)).append p.reverse).append
      ((H.rim i).dropUntil x hx_rim)

theorem Tripod.prefixLegHitRerouteRim_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hp_meets_leg_only_at_y :
      forall v : V, v ∈ p.support -> v ∈ (H.leg i).support -> v = y)
    (hp_meets_rim :
      forall v : V, v ∈ p.support -> v ∈ (H.rim i).support -> v = x)
    (hidx :
      (H.rim i).support.idxOf x <
        (H.rim i).support.idxOf (H.attach i)) :
    (H.prefixLegHitRerouteRim i hx_rim hy_leg p).IsPath := by
  let r : G.Walk H.left H.right := H.rim i
  let l : G.Walk (H.attach i) (feet i) := H.leg i
  let pref : G.Walk H.left x := r.takeUntil x (by simpa [r] using hx_rim)
  let legPref : G.Walk (H.attach i) y := l.takeUntil y (by simpa [l] using hy_leg)
  let suff : G.Walk (H.attach i) H.right :=
    r.dropUntil (H.attach i) (by simpa [r] using (H.attach_mem_rim i).1)
  have hpref : pref.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil r (by simpa [r] using hx_rim))
      (by simpa [r] using H.rim_isPath i)
  have hlegPref : legPref.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil l (by simpa [l] using hy_leg))
      (by simpa [l] using H.leg_isPath i)
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
  have hlegPrefRev : legPref.reverse.IsPath := hlegPref.reverse
  have hprefp_leg :
      ((pref.append p).append legPref.reverse).IsPath := by
    refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
      hprefp hlegPrefRev ?_
    intro z hzprefp hzlegrev
    rw [SimpleGraph.Walk.support_reverse] at hzlegrev
    have hzlegPref : z ∈ legPref.support := List.mem_reverse.mp hzlegrev
    have hzleg : z ∈ (H.leg i).support := by
      have hzleg' : z ∈ l.support :=
        SimpleGraph.Walk.support_takeUntil_subset l
          (by simpa [l] using hy_leg) (by simpa [legPref] using hzlegPref)
      simpa [l] using hzleg'
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
    · exact hp_meets_leg_only_at_y z hzp hzleg
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
    have hzlegPref : z ∈ legPref.support := List.mem_reverse.mp hzlegrev
    have hzleg : z ∈ (H.leg i).support := by
      have hzleg' : z ∈ l.support :=
        SimpleGraph.Walk.support_takeUntil_subset l
          (by simpa [l] using hy_leg) (by simpa [legPref] using hzlegPref)
      simpa [l] using hzleg'
    exact H.leg_meets_rims_only_at_attach i i z hzleg hzrim_suff

theorem Tripod.suffixLegHitRerouteRim_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hp_meets_leg_only_at_y :
      forall v : V, v ∈ p.support -> v ∈ (H.leg i).support -> v = y)
    (hp_meets_rim :
      forall v : V, v ∈ p.support -> v ∈ (H.rim i).support -> v = x)
    (hidx :
      (H.rim i).support.idxOf (H.attach i) <
        (H.rim i).support.idxOf x) :
    (H.suffixLegHitRerouteRim i hx_rim hy_leg p).IsPath := by
  let r : G.Walk H.left H.right := H.rim i
  let l : G.Walk (H.attach i) (feet i) := H.leg i
  let pref : G.Walk H.left (H.attach i) :=
    r.takeUntil (H.attach i) (by simpa [r] using (H.attach_mem_rim i).1)
  let legPref : G.Walk (H.attach i) y := l.takeUntil y (by simpa [l] using hy_leg)
  let suff : G.Walk x H.right := r.dropUntil x (by simpa [r] using hx_rim)
  have hpref : pref.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil r
        (by simpa [r] using (H.attach_mem_rim i).1))
      (by simpa [r] using H.rim_isPath i)
  have hlegPref : legPref.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil l (by simpa [l] using hy_leg))
      (by simpa [l] using H.leg_isPath i)
  have hsuff : suff.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_dropUntil r (by simpa [r] using hx_rim))
      (by simpa [r] using H.rim_isPath i)
  have hpref_legPref : (pref.append legPref).IsPath := by
    refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
      hpref hlegPref ?_
    intro z hzpref hzleg
    have hzrim : z ∈ (H.rim i).support := by
      have hzrim' : z ∈ r.support :=
        SimpleGraph.Walk.support_takeUntil_subset r
          (by simpa [r] using (H.attach_mem_rim i).1)
          (by simpa [pref] using hzpref)
      simpa [r] using hzrim'
    have hzleg_old : z ∈ (H.leg i).support := by
      have hzleg' : z ∈ l.support :=
        SimpleGraph.Walk.support_takeUntil_subset l
          (by simpa [l] using hy_leg) (by simpa [legPref] using hzleg)
      simpa [l] using hzleg'
    exact H.leg_meets_rims_only_at_attach i i z hzleg_old hzrim
  have hrev : p.reverse.IsPath := hp.reverse
  have hpref_leg_rev : ((pref.append legPref).append p.reverse).IsPath := by
    refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
      hpref_legPref hrev ?_
    intro z hzleft hzrev
    rw [SimpleGraph.Walk.support_reverse] at hzrev
    have hzp : z ∈ p.support := List.mem_reverse.mp hzrev
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzleft
    rcases hzleft with hzpref | hzleg
    · exfalso
      have hzrim : z ∈ (H.rim i).support := by
        have hzrim' : z ∈ r.support :=
          SimpleGraph.Walk.support_takeUntil_subset r
            (by simpa [r] using (H.attach_mem_rim i).1)
            (by simpa [pref] using hzpref)
        simpa [r] using hzrim'
      have hz_eq_x : z = x := hp_meets_rim z hzp hzrim
      have hx_pref : x ∈ pref.support := by
        simpa [hz_eq_x] using hzpref
      have hle :
          (H.rim i).support.idxOf x <=
            (H.rim i).support.idxOf (H.attach i) := by
        have hle' :=
          Schematic.Math.GraphTheory.Walk.idxOf_le_of_mem_takeUntil
            (p := r) (x := H.attach i) (z := x)
            (by simpa [r] using (H.attach_mem_rim i).1)
            (by simpa [pref] using hx_pref)
        simpa [r] using hle'
      omega
    · have hzleg_old : z ∈ (H.leg i).support := by
        have hzleg' : z ∈ l.support :=
          SimpleGraph.Walk.support_takeUntil_subset l
            (by simpa [l] using hy_leg) (by simpa [legPref] using hzleg)
        simpa [l] using hzleg'
      exact hp_meets_leg_only_at_y z hzp hzleg_old
  refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
    hpref_leg_rev hsuff ?_
  intro z hzleft hzsuff
  have hzrim_suff : z ∈ (H.rim i).support := by
    have hzrim' : z ∈ r.support :=
      SimpleGraph.Walk.support_dropUntil_subset r
        (by simpa [r] using hx_rim) (by simpa [suff] using hzsuff)
    simpa [r] using hzrim'
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzleft
  rcases hzleft with hzpref_leg | hzrev
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzpref_leg
    rcases hzpref_leg with hzpref | hzleg
    · exfalso
      have hdis :
          Disjoint
            {z : V |
              z ∈ (r.takeUntil (H.attach i)
                (by simpa [r] using (H.attach_mem_rim i).1)).support}
            {z : V | z ∈ (r.dropUntil x (by simpa [r] using hx_rim)).support} := by
        exact Schematic.Math.GraphTheory.Walk.IsPath.takeUntil_support_disjoint_dropUntil_support_of_idx_lt
          (p := r)
          (by simpa [r] using H.rim_isPath i)
          (by simpa [r] using (H.attach_mem_rim i).1)
          (by simpa [r] using hx_rim)
          (by simpa [r] using hidx)
      exact Set.disjoint_left.mp hdis (by simpa [pref] using hzpref)
        (by simpa [suff] using hzsuff)
    · exfalso
      have hzleg_old : z ∈ (H.leg i).support := by
        have hzleg' : z ∈ l.support :=
          SimpleGraph.Walk.support_takeUntil_subset l
            (by simpa [l] using hy_leg) (by simpa [legPref] using hzleg)
        simpa [l] using hzleg'
      have hz_attach : z = H.attach i :=
        H.leg_meets_rims_only_at_attach i i z hzleg_old hzrim_suff
      subst z
      have hle :
          (H.rim i).support.idxOf x <=
            (H.rim i).support.idxOf (H.attach i) := by
        have hle' :=
          Schematic.Math.GraphTheory.Walk.idxOf_le_of_mem_dropUntil
            (p := r)
            (by simpa [r] using H.rim_isPath i)
            (by simpa [r] using hx_rim)
            (by simpa [suff] using hzsuff)
        simpa [r] using hle'
      omega
  · rw [SimpleGraph.Walk.support_reverse] at hzrev
    have hzp : z ∈ p.support := List.mem_reverse.mp hzrev
    exact hp_meets_rim z hzp hzrim_suff

theorem Tripod.exists_legLengthSum_lt_of_prefix_leg_hit_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hnewRim_path : (H.prefixLegHitRerouteRim i hx_rim hy_leg p).IsPath)
    (hnewLeg_meets_newRim :
      forall v : V,
        v ∈ ((H.leg i).dropUntil y hy_leg).support ->
          v ∈ (H.prefixLegHitRerouteRim i hx_rim hy_leg p).support ->
            v = y)
    (hrim_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint
          (Walk.InternalVertices (H.prefixLegHitRerouteRim i hx_rim hy_leg p))
          (Walk.InternalVertices (H.rim j)))
    (holdLeg_meets_newRim :
      forall j : Fin 3, j ≠ i ->
        forall v : V, v ∈ (H.leg j).support ->
          v ∈ (H.prefixLegHitRerouteRim i hx_rim hy_leg p).support ->
            v = H.attach j)
    (hlt : ((H.leg i).dropUntil y hy_leg).length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  let newRim : G.Walk H.left H.right := H.prefixLegHitRerouteRim i hx_rim hy_leg p
  let newLeg : G.Walk y (feet i) := (H.leg i).dropUntil y hy_leg
  have hy_support : y ∈ newRim.support := by
    dsimp [newRim, Tripod.prefixLegHitRerouteRim]
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr p.end_mem_support
  have hy_internal : y ∈ Walk.InternalVertices newRim := by
    exact ⟨hy_support, H.leg_support_ne_left hy_leg, H.leg_support_ne_right hy_leg⟩
  have hnewLeg_path : newLeg.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_dropUntil (H.leg i) hy_leg)
      (H.leg_isPath i)
  have hattach_not_newLeg : H.attach i ∉ newLeg.support :=
    Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      (H.leg_isPath i) hy_leg hy_ne_attach
  refine H.exists_legLengthSum_lt_of_replaceRimAndLeg
    i newRim y hy_internal newLeg hnewRim_path hnewLeg_path
    (by simpa [newRim] using hrim_disjoint) ?_ ?_ ?_
    (by simpa [newRim] using holdLeg_meets_newRim) ?_
  · intro j hji
    rw [Set.disjoint_left]
    intro v hvnew hvj
    have hvold : v ∈ (H.leg i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy_leg
        (by simpa [newLeg] using hvnew)
    exact Set.disjoint_left.mp (H.legs_disjoint i j (fun hij => hji hij.symm))
      hvold hvj
  · intro v hvnew hvRim
    exact hnewLeg_meets_newRim v (by simpa [newLeg] using hvnew)
      (by simpa [newRim] using hvRim)
  · intro j _hji v hvnew hvrim
    have hvold : v ∈ (H.leg i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy_leg
        (by simpa [newLeg] using hvnew)
    have hv_attach : v = H.attach i :=
      H.leg_meets_rims_only_at_attach i j v hvold hvrim
    exact False.elim (hattach_not_newLeg (by simpa [newLeg, hv_attach] using hvnew))
  · simpa [newLeg] using hlt

theorem Tripod.exists_legLengthSum_lt_of_suffix_leg_hit_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hnewRim_path : (H.suffixLegHitRerouteRim i hx_rim hy_leg p).IsPath)
    (hnewLeg_meets_newRim :
      forall v : V,
        v ∈ ((H.leg i).dropUntil y hy_leg).support ->
          v ∈ (H.suffixLegHitRerouteRim i hx_rim hy_leg p).support ->
            v = y)
    (hrim_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint
          (Walk.InternalVertices (H.suffixLegHitRerouteRim i hx_rim hy_leg p))
          (Walk.InternalVertices (H.rim j)))
    (holdLeg_meets_newRim :
      forall j : Fin 3, j ≠ i ->
        forall v : V, v ∈ (H.leg j).support ->
          v ∈ (H.suffixLegHitRerouteRim i hx_rim hy_leg p).support ->
            v = H.attach j)
    (hlt : ((H.leg i).dropUntil y hy_leg).length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  let newRim : G.Walk H.left H.right := H.suffixLegHitRerouteRim i hx_rim hy_leg p
  let newLeg : G.Walk y (feet i) := (H.leg i).dropUntil y hy_leg
  have hy_support : y ∈ newRim.support := by
    dsimp [newRim, Tripod.suffixLegHitRerouteRim]
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr ((H.leg i).takeUntil y hy_leg).end_mem_support
  have hy_internal : y ∈ Walk.InternalVertices newRim := by
    exact ⟨hy_support, H.leg_support_ne_left hy_leg, H.leg_support_ne_right hy_leg⟩
  have hnewLeg_path : newLeg.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_dropUntil (H.leg i) hy_leg)
      (H.leg_isPath i)
  have hattach_not_newLeg : H.attach i ∉ newLeg.support :=
    Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      (H.leg_isPath i) hy_leg hy_ne_attach
  refine H.exists_legLengthSum_lt_of_replaceRimAndLeg
    i newRim y hy_internal newLeg hnewRim_path hnewLeg_path
    (by simpa [newRim] using hrim_disjoint) ?_ ?_ ?_
    (by simpa [newRim] using holdLeg_meets_newRim) ?_
  · intro j hji
    rw [Set.disjoint_left]
    intro v hvnew hvj
    have hvold : v ∈ (H.leg i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy_leg
        (by simpa [newLeg] using hvnew)
    exact Set.disjoint_left.mp (H.legs_disjoint i j (fun hij => hji hij.symm))
      hvold hvj
  · intro v hvnew hvRim
    exact hnewLeg_meets_newRim v (by simpa [newLeg] using hvnew)
      (by simpa [newRim] using hvRim)
  · intro j _hji v hvnew hvrim
    have hvold : v ∈ (H.leg i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy_leg
        (by simpa [newLeg] using hvnew)
    have hv_attach : v = H.attach i :=
      H.leg_meets_rims_only_at_attach i j v hvold hvrim
    exact False.elim (hattach_not_newLeg (by simpa [newLeg, hv_attach] using hvnew))
  · simpa [newLeg] using hlt

theorem Tripod.prefixLegHitReroute_newLeg_meets_newRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hp_meets_leg_only_at_y :
      forall v : V, v ∈ p.support -> v ∈ (H.leg i).support -> v = y) :
    forall v : V,
      v ∈ ((H.leg i).dropUntil y hy_leg).support ->
        v ∈ (H.prefixLegHitRerouteRim i hx_rim hy_leg p).support ->
          v = y := by
  intro v hvnew hvRim
  let legSuff : G.Walk y (feet i) := (H.leg i).dropUntil y hy_leg
  have hvold : v ∈ (H.leg i).support :=
    SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy_leg hvnew
  have hattach_not_new :
      H.attach i ∉ legSuff.support :=
    Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      (H.leg_isPath i) hy_leg hy_ne_attach
  dsimp [Tripod.prefixLegHitRerouteRim] at hvRim
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvRim
  rcases hvRim with hvleft | hvsuff
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvprefp | hvlegrev
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hvprefp
      rcases hvprefp with hvpref | hvp
      · have hvrim : v ∈ (H.rim i).support :=
          SimpleGraph.Walk.support_takeUntil_subset (H.rim i) hx_rim hvpref
        have hv_attach : v = H.attach i :=
          H.leg_meets_rims_only_at_attach i i v hvold hvrim
        exact False.elim (hattach_not_new (by simpa [legSuff, hv_attach] using hvnew))
      · exact hp_meets_leg_only_at_y v hvp hvold
    · rw [SimpleGraph.Walk.support_reverse] at hvlegrev
      have hvpref :
          v ∈ ((H.leg i).takeUntil y hy_leg).support :=
        List.mem_reverse.mp hvlegrev
      exact Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        (H.leg_isPath i) hy_leg hvpref hvnew
  · have hvrim : v ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvsuff
    have hv_attach : v = H.attach i :=
      H.leg_meets_rims_only_at_attach i i v hvold hvrim
    exact False.elim (hattach_not_new (by simpa [legSuff, hv_attach] using hvnew))

theorem Tripod.suffixLegHitReroute_newLeg_meets_newRim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hp_meets_leg_only_at_y :
      forall v : V, v ∈ p.support -> v ∈ (H.leg i).support -> v = y) :
    forall v : V,
      v ∈ ((H.leg i).dropUntil y hy_leg).support ->
        v ∈ (H.suffixLegHitRerouteRim i hx_rim hy_leg p).support ->
          v = y := by
  intro v hvnew hvRim
  let legSuff : G.Walk y (feet i) := (H.leg i).dropUntil y hy_leg
  have hvold : v ∈ (H.leg i).support :=
    SimpleGraph.Walk.support_dropUntil_subset (H.leg i) hy_leg hvnew
  have hattach_not_new :
      H.attach i ∉ legSuff.support :=
    Schematic.Math.GraphTheory.Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      (H.leg_isPath i) hy_leg hy_ne_attach
  dsimp [Tripod.suffixLegHitRerouteRim] at hvRim
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvRim
  rcases hvRim with hvleft | hvsuff
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvprefleg | hvprev
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hvprefleg
      rcases hvprefleg with hvpref | hvlegpref
      · have hvrim : v ∈ (H.rim i).support :=
          SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
            (H.attach_mem_rim i).1 hvpref
        have hv_attach : v = H.attach i :=
          H.leg_meets_rims_only_at_attach i i v hvold hvrim
        exact False.elim (hattach_not_new (by simpa [legSuff, hv_attach] using hvnew))
      · exact Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          (H.leg_isPath i) hy_leg hvlegpref hvnew
    · rw [SimpleGraph.Walk.support_reverse] at hvprev
      have hvp : v ∈ p.support := List.mem_reverse.mp hvprev
      exact hp_meets_leg_only_at_y v hvp hvold
  · have hvrim : v ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim i) hx_rim hvsuff
    have hv_attach : v = H.attach i :=
      H.leg_meets_rims_only_at_attach i i v hvold hvrim
    exact False.elim (hattach_not_new (by simpa [legSuff, hv_attach] using hvnew))

theorem Tripod.prefixLegHitReroute_oldLeg_meets_only_at_attach
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_old_leg_only_at_y :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y) :
    forall j : Fin 3, j ≠ i ->
      forall v : V, v ∈ (H.leg j).support ->
        v ∈ (H.prefixLegHitRerouteRim i hx_rim hy_leg p).support ->
          v = H.attach j := by
  intro j hji v hvleg hvnew
  dsimp [Tripod.prefixLegHitRerouteRim] at hvnew
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvnew
  rcases hvnew with hvleft | hvsuff
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvprefp | hvlegrev
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hvprefp
      rcases hvprefp with hvpref | hvp
      · have hvrim : v ∈ (H.rim i).support :=
          SimpleGraph.Walk.support_takeUntil_subset (H.rim i) hx_rim hvpref
        exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim
      · have hv_y : v = y := hp_meets_old_leg_only_at_y j v hvp hvleg
        exact False.elim
          (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg
            (by simpa [hv_y] using hy_leg))
    · rw [SimpleGraph.Walk.support_reverse] at hvlegrev
      have hvi : v ∈ (H.leg i).support := by
        exact SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy_leg
          (List.mem_reverse.mp hvlegrev)
      exact False.elim
        (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg hvi)
  · have hvrim : v ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvsuff
    exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim

theorem Tripod.suffixLegHitReroute_oldLeg_meets_only_at_attach
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_old_leg_only_at_y :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y) :
    forall j : Fin 3, j ≠ i ->
      forall v : V, v ∈ (H.leg j).support ->
        v ∈ (H.suffixLegHitRerouteRim i hx_rim hy_leg p).support ->
          v = H.attach j := by
  intro j hji v hvleg hvnew
  dsimp [Tripod.suffixLegHitRerouteRim] at hvnew
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvnew
  rcases hvnew with hvleft | hvsuff
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvprefleg | hvprev
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hvprefleg
      rcases hvprefleg with hvpref | hvi
      · have hvrim : v ∈ (H.rim i).support :=
          SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
            (H.attach_mem_rim i).1 hvpref
        exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim
      · have hvi_old : v ∈ (H.leg i).support :=
          SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy_leg hvi
        exact False.elim
          (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg hvi_old)
    · rw [SimpleGraph.Walk.support_reverse] at hvprev
      have hvp : v ∈ p.support := List.mem_reverse.mp hvprev
      have hv_y : v = y := hp_meets_old_leg_only_at_y j v hvp hvleg
      exact False.elim
        (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg
          (by simpa [hv_y] using hy_leg))
  · have hvrim : v ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim i) hx_rim hvsuff
    exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim

theorem Tripod.prefixFootRerouteRim_support_subset
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x : V}
    (hx_rim : x ∈ (H.rim i).support)
    (p : G.Walk x (feet i)) :
    forall v : V, v ∈ (H.prefixFootRerouteRim i hx_rim p).support ->
      v ∈ (H.rim i).support ∨
        v ∈ p.support ∨ v ∈ (H.leg i).support := by
  intro v hvnew
  dsimp [Tripod.prefixFootRerouteRim] at hvnew
  simp only [SimpleGraph.Walk.mem_support_append_iff] at hvnew
  rcases hvnew with ((hvpref | hvp) | hvlegrev) | hvsuff
  · exact Or.inl
      (SimpleGraph.Walk.support_takeUntil_subset (H.rim i) hx_rim hvpref)
  · exact Or.inr (Or.inl hvp)
  · exact Or.inr (Or.inr (List.mem_reverse.mp
      (by simpa [SimpleGraph.Walk.support_reverse] using hvlegrev)))
  · exact Or.inl
      (SimpleGraph.Walk.support_dropUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvsuff)

theorem Tripod.suffixFootRerouteRim_support_subset
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x : V}
    (hx_rim : x ∈ (H.rim i).support)
    (p : G.Walk x (feet i)) :
    forall v : V, v ∈ (H.suffixFootRerouteRim i hx_rim p).support ->
      v ∈ (H.rim i).support ∨
        v ∈ p.support ∨ v ∈ (H.leg i).support := by
  intro v hvnew
  dsimp [Tripod.suffixFootRerouteRim] at hvnew
  simp only [SimpleGraph.Walk.mem_support_append_iff] at hvnew
  rcases hvnew with ((hvpref | hvleg) | hvprev) | hvsuff
  · exact Or.inl
      (SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvpref)
  · exact Or.inr (Or.inr hvleg)
  · exact Or.inr (Or.inl (List.mem_reverse.mp
      (by simpa [SimpleGraph.Walk.support_reverse] using hvprev)))
  · exact Or.inl
      (SimpleGraph.Walk.support_dropUntil_subset (H.rim i) hx_rim hvsuff)

theorem Tripod.prefixLegHitRerouteRim_support_subset
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk x y) :
    forall v : V, v ∈ (H.prefixLegHitRerouteRim i hx_rim hy_leg p).support ->
      v ∈ (H.rim i).support ∨
        v ∈ p.support ∨ v ∈ (H.leg i).support := by
  intro v hvnew
  dsimp [Tripod.prefixLegHitRerouteRim] at hvnew
  simp only [SimpleGraph.Walk.mem_support_append_iff] at hvnew
  rcases hvnew with ((hvpref | hvp) | hvlegrev) | hvsuff
  · exact Or.inl
      (SimpleGraph.Walk.support_takeUntil_subset (H.rim i) hx_rim hvpref)
  · exact Or.inr (Or.inl hvp)
  · exact Or.inr (Or.inr
      (SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy_leg
        (List.mem_reverse.mp
          (by simpa [SimpleGraph.Walk.support_reverse] using hvlegrev))))
  · exact Or.inl
      (SimpleGraph.Walk.support_dropUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvsuff)

theorem Tripod.suffixLegHitRerouteRim_support_subset
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_rim : x ∈ (H.rim i).support)
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk x y) :
    forall v : V, v ∈ (H.suffixLegHitRerouteRim i hx_rim hy_leg p).support ->
      v ∈ (H.rim i).support ∨
        v ∈ p.support ∨ v ∈ (H.leg i).support := by
  intro v hvnew
  dsimp [Tripod.suffixLegHitRerouteRim] at hvnew
  simp only [SimpleGraph.Walk.mem_support_append_iff] at hvnew
  rcases hvnew with ((hvpref | hvleg) | hvprev) | hvsuff
  · exact Or.inl
      (SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvpref)
  · exact Or.inr (Or.inr
      (SimpleGraph.Walk.support_takeUntil_subset (H.leg i) hy_leg hvleg))
  · exact Or.inr (Or.inl (List.mem_reverse.mp
      (by simpa [SimpleGraph.Walk.support_reverse] using hvprev)))
  · exact Or.inl
      (SimpleGraph.Walk.support_dropUntil_subset (H.rim i) hx_rim hvsuff)

theorem Tripod.rerouteRim_internal_disjoint_of_support
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (p : G.Walk x y)
    (hx_avoids_other_rims :
      forall j : Fin 3, j ≠ i ->
        x ∉ Walk.InternalVertices (H.rim j))
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x)
    {a b : V}
    (q : G.Walk a b)
    (hq_support :
      forall v : V, v ∈ q.support ->
        v ∈ (H.rim i).support ∨
          v ∈ p.support ∨ v ∈ (H.leg i).support) :
    forall j : Fin 3, j ≠ i ->
      Disjoint
        (Walk.InternalVertices q)
        (Walk.InternalVertices (H.rim j)) := by
  intro j hji
  rw [Set.disjoint_left]
  intro v hvq hvj
  rcases hq_support v hvq.1 with hvrim | hvp | hvleg
  · exact Set.disjoint_left.mp
      (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
      ⟨hvrim, hvj.2.1, hvj.2.2⟩ hvj
  · have hvx : x ∈ Walk.InternalVertices (H.rim j) := by
      simpa [hp_meets_rims j v hvp hvj.1] using hvj
    exact hx_avoids_other_rims j hji hvx
  · have hv_attach : v = H.attach i :=
      H.leg_meets_rims_only_at_attach i j v hvleg hvj.1
    have hattach_j : H.attach i ∈ Walk.InternalVertices (H.rim j) := by
      simpa [hv_attach] using hvj
    exact Set.disjoint_left.mp
      (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
      (H.attach_mem_rim i) hattach_j

theorem Tripod.prefixLegHitReroute_internal_disjoint_of_last_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_internal : x ∈ Walk.InternalVertices (H.rim i))
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    forall j : Fin 3, j ≠ i ->
      Disjoint
        (Walk.InternalVertices
          (H.prefixLegHitRerouteRim i hx_internal.1 hy_leg p))
        (Walk.InternalVertices (H.rim j)) := by
  refine H.rerouteRim_internal_disjoint_of_support p ?_ hp_meets_rims
    (H.prefixLegHitRerouteRim i hx_internal.1 hy_leg p) ?_
  · intro j hji hxj
    exact Set.disjoint_left.mp
      (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
      hx_internal hxj
  · exact H.prefixLegHitRerouteRim_support_subset hx_internal.1 hy_leg p

theorem Tripod.suffixLegHitReroute_internal_disjoint_of_last_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_internal : x ∈ Walk.InternalVertices (H.rim i))
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk x y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    forall j : Fin 3, j ≠ i ->
      Disjoint
        (Walk.InternalVertices
          (H.suffixLegHitRerouteRim i hx_internal.1 hy_leg p))
        (Walk.InternalVertices (H.rim j)) := by
  refine H.rerouteRim_internal_disjoint_of_support p ?_ hp_meets_rims
    (H.suffixLegHitRerouteRim i hx_internal.1 hy_leg p) ?_
  · intro j hji hxj
    exact Set.disjoint_left.mp
      (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
      hx_internal hxj
  · exact H.suffixLegHitRerouteRim_support_subset hx_internal.1 hy_leg p

theorem Tripod.prefixLegHitReroute_internal_disjoint_of_left_endpoint
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {y : V}
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk H.left y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = H.left) :
    forall j : Fin 3, j ≠ i ->
      Disjoint
        (Walk.InternalVertices
          (H.prefixLegHitRerouteRim i (H.rim i).start_mem_support hy_leg p))
        (Walk.InternalVertices (H.rim j)) := by
  refine H.rerouteRim_internal_disjoint_of_support p ?_ hp_meets_rims
    (H.prefixLegHitRerouteRim i (H.rim i).start_mem_support hy_leg p) ?_
  · intro j hji hxj
    exact hxj.2.1 rfl
  · exact H.prefixLegHitRerouteRim_support_subset
      (H.rim i).start_mem_support hy_leg p

theorem Tripod.suffixLegHitReroute_internal_disjoint_of_right_endpoint
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {y : V}
    (hy_leg : y ∈ (H.leg i).support)
    (p : G.Walk H.right y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = H.right) :
    forall j : Fin 3, j ≠ i ->
      Disjoint
        (Walk.InternalVertices
          (H.suffixLegHitRerouteRim i (H.rim i).end_mem_support hy_leg p))
        (Walk.InternalVertices (H.rim j)) := by
  refine H.rerouteRim_internal_disjoint_of_support p ?_ hp_meets_rims
    (H.suffixLegHitRerouteRim i (H.rim i).end_mem_support hy_leg p) ?_
  · intro j hji hxj
    exact hxj.2.2 rfl
  · exact H.suffixLegHitRerouteRim_support_subset
      (H.rim i).end_mem_support hy_leg p

theorem Tripod.exists_legLengthSum_lt_of_prefix_same_rim_leg_hit_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_internal : x ∈ Walk.InternalVertices (H.rim i))
    (hy_leg : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hp_meets_old_leg_only_at_y :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x)
    (hidx :
      (H.rim i).support.idxOf x <
        (H.rim i).support.idxOf (H.attach i))
    (hlt : ((H.leg i).dropUntil y hy_leg).length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum :=
  H.exists_legLengthSum_lt_of_prefix_leg_hit_reroute
    hx_internal.1 hy_leg hy_ne_attach p
    (H.prefixLegHitRerouteRim_isPath hx_internal.1 hy_leg p hp
      (hp_meets_old_leg_only_at_y i) (hp_meets_rims i) hidx)
    (H.prefixLegHitReroute_newLeg_meets_newRim
      hx_internal.1 hy_leg hy_ne_attach p (hp_meets_old_leg_only_at_y i))
    (H.prefixLegHitReroute_internal_disjoint_of_last_rim
      hx_internal hy_leg p hp_meets_rims)
    (H.prefixLegHitReroute_oldLeg_meets_only_at_attach
      hx_internal.1 hy_leg p hp_meets_old_leg_only_at_y)
    hlt

theorem Tripod.exists_legLengthSum_lt_of_suffix_same_rim_leg_hit_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_internal : x ∈ Walk.InternalVertices (H.rim i))
    (hy_leg : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hp_meets_old_leg_only_at_y :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x)
    (hidx :
      (H.rim i).support.idxOf (H.attach i) <
        (H.rim i).support.idxOf x)
    (hlt : ((H.leg i).dropUntil y hy_leg).length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum :=
  H.exists_legLengthSum_lt_of_suffix_leg_hit_reroute
    hx_internal.1 hy_leg hy_ne_attach p
    (H.suffixLegHitRerouteRim_isPath hx_internal.1 hy_leg p hp
      (hp_meets_old_leg_only_at_y i) (hp_meets_rims i) hidx)
    (H.suffixLegHitReroute_newLeg_meets_newRim
      hx_internal.1 hy_leg hy_ne_attach p (hp_meets_old_leg_only_at_y i))
    (H.suffixLegHitReroute_internal_disjoint_of_last_rim
      hx_internal hy_leg p hp_meets_rims)
    (H.suffixLegHitReroute_oldLeg_meets_only_at_attach
      hx_internal.1 hy_leg p hp_meets_old_leg_only_at_y)
    hlt

theorem Tripod.exists_legLengthSum_lt_of_same_rim_leg_hit_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x y : V}
    (hx_internal : x ∈ Walk.InternalVertices (H.rim i))
    (hy_leg : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hp_meets_old_leg_only_at_y :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x)
    (hx_ne_attach : x ≠ H.attach i)
    (hlt : ((H.leg i).dropUntil y hy_leg).length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  rcases lt_trichotomy
      ((H.rim i).support.idxOf x)
      ((H.rim i).support.idxOf (H.attach i)) with hlt_idx | heq_idx | hgt_idx
  · exact H.exists_legLengthSum_lt_of_prefix_same_rim_leg_hit_reroute
      hx_internal hy_leg hy_ne_attach p hp hp_meets_old_leg_only_at_y
      hp_meets_rims hlt_idx hlt
  · have hx_attach : x = H.attach i :=
      (List.idxOf_inj hx_internal.1).mp heq_idx
    exact False.elim (hx_ne_attach hx_attach)
  · exact H.exists_legLengthSum_lt_of_suffix_same_rim_leg_hit_reroute
      hx_internal hy_leg hy_ne_attach p hp hp_meets_old_leg_only_at_y
      hp_meets_rims hgt_idx hlt

theorem Tripod.exists_legLengthSum_lt_of_left_endpoint_leg_hit_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {y : V}
    (hy_leg : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk H.left y)
    (hp : p.IsPath)
    (hp_meets_old_leg_only_at_y :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = H.left)
    (hlt : ((H.leg i).dropUntil y hy_leg).length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  have hidx :
      (H.rim i).support.idxOf H.left <
        (H.rim i).support.idxOf (H.attach i) := by
    rw [Schematic.Math.GraphTheory.Walk.idxOf_start_support (H.rim i)]
    exact Schematic.Math.GraphTheory.Walk.idxOf_pos_of_mem_support_ne_start
      (H.attach_mem_rim i).1 (H.attach_ne_left i)
  exact H.exists_legLengthSum_lt_of_prefix_leg_hit_reroute
    (H.rim i).start_mem_support hy_leg hy_ne_attach p
    (H.prefixLegHitRerouteRim_isPath (H.rim i).start_mem_support hy_leg p hp
      (hp_meets_old_leg_only_at_y i) (hp_meets_rims i) hidx)
    (H.prefixLegHitReroute_newLeg_meets_newRim
      (H.rim i).start_mem_support hy_leg hy_ne_attach p
      (hp_meets_old_leg_only_at_y i))
    (H.prefixLegHitReroute_internal_disjoint_of_left_endpoint
      hy_leg p hp_meets_rims)
    (H.prefixLegHitReroute_oldLeg_meets_only_at_attach
      (H.rim i).start_mem_support hy_leg p hp_meets_old_leg_only_at_y)
    hlt

theorem Tripod.exists_legLengthSum_lt_of_right_endpoint_leg_hit_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {y : V}
    (hy_leg : y ∈ (H.leg i).support)
    (hy_ne_attach : y ≠ H.attach i)
    (p : G.Walk H.right y)
    (hp : p.IsPath)
    (hp_meets_old_leg_only_at_y :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = H.right)
    (hlt : ((H.leg i).dropUntil y hy_leg).length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  simpa using
    H.flip.exists_legLengthSum_lt_of_left_endpoint_leg_hit_reroute
      hy_leg hy_ne_attach p hp hp_meets_old_leg_only_at_y
      (by
        intro k v hvp hvrim
        exact hp_meets_rims k v hvp (by simpa using hvrim))
      hlt

theorem Tripod.exists_legLengthSum_lt_of_suffix_foot_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx_rim : x ∈ (H.rim i).support)
    (p : G.Walk x (feet i))
    (hnewRim_path : (H.suffixFootRerouteRim i hx_rim p).IsPath)
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
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  let newRim : G.Walk H.left H.right := H.suffixFootRerouteRim i hx_rim p
  have hfoot_support : feet i ∈ newRim.support := by
    dsimp [newRim, Tripod.suffixFootRerouteRim]
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr (H.leg i).end_mem_support
  have hfoot_internal : feet i ∈ Walk.InternalVertices newRim := by
    exact ⟨hfoot_support, (H.left_not_foot i).symm,
      (H.right_not_foot i).symm⟩
  exact H.exists_legLengthSum_lt_of_replaceRim_attach_foot
    hpos newRim hfoot_internal (by simpa [newRim] using hnewRim_path)
    (by simpa [newRim] using hrim_disjoint)
    (by simpa [newRim] using holdLeg_meets_newRim)

theorem Tripod.exists_legLengthSum_lt_of_leg_chord_idx_gap
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    {x y : V}
    (hx : x ∈ (H.leg i).support)
    (hy : y ∈ (H.leg i).support)
    (hxy : G.Adj x y)
    (hidx : (H.leg i).support.idxOf x + 1 < (H.leg i).support.idxOf y) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  let r : G.Walk (H.attach i) (feet i) :=
    Walk.chordShortcut (H.leg i) hx hy hxy
  let q : G.Walk (H.attach i) (feet i) := r.bypass
  have hq_path : q.IsPath := by
    exact SimpleGraph.Walk.bypass_isPath r
  have hq_subset :
      forall z : V, z ∈ q.support -> z ∈ (H.leg i).support := by
    intro z hz
    exact Walk.chordShortcut_bypass_support_subset (H.leg i) hx hy hxy hz
  have hq_len_le : q.length <= r.length := by
    exact SimpleGraph.Walk.length_bypass_le r
  have hr_short : r.length < (H.leg i).length := by
    exact Walk.chordShortcut_length_lt_of_idx_gap (H.leg i) hx hy hxy hidx
  exact H.exists_legLengthSum_lt_of_shorter_same_attach_subpath
    i q hq_path hq_subset (lt_of_le_of_lt hq_len_le hr_short)


end Schematic.Math.GraphTheory
