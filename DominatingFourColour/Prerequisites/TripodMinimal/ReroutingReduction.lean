import DominatingFourColour.Prerequisites.TripodPrefix.CrossReroutes
import Schematic.Math.GraphTheory.PathsTrees.Foundations.PathIntervals

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
theorem Tripod.prefixFootRerouteRim_oldLeg_meets_only_at_attach_of_trim_clean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx_rim : x ∈ (H.rim i).support)
    (p : G.Walk x (feet i))
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet) :
    forall j : Fin 3, j ≠ i ->
      forall v : V, v ∈ (H.leg j).support ->
        v ∈ (H.prefixFootRerouteRim i hx_rim p).support ->
          v = H.attach j := by
  intro j hji v hvleg hvnew
  dsimp [Tripod.prefixFootRerouteRim] at hvnew
  rw [SimpleGraph.Walk.mem_support_append_iff] at hvnew
  rcases hvnew with hvleft | hvsuff
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hvleft
    rcases hvleft with hvprefp | hvlegrev
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hvprefp
      rcases hvprefp with hvpref | hvp
      · have hvrim : v ∈ (H.rim i).support :=
          SimpleGraph.Walk.support_takeUntil_subset (H.rim i) hx_rim hvpref
        exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim
      · exfalso
        exact hp_clean v hvp ⟨j, by
          simpa [Tripod.trimPositiveLeg, Tripod.trimPositiveLegLeg, hji] using hvleg⟩
    · rw [SimpleGraph.Walk.support_reverse] at hvlegrev
      have hvi : v ∈ (H.leg i).support := List.mem_reverse.mp hvlegrev
      exact False.elim
        (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg hvi)
  · have hvrim : v ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvsuff
    exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim

theorem Tripod.suffixFootRerouteRim_oldLeg_meets_only_at_attach_of_trim_clean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx_rim : x ∈ (H.rim i).support)
    (p : G.Walk x (feet i))
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet) :
    forall j : Fin 3, j ≠ i ->
      forall v : V, v ∈ (H.leg j).support ->
        v ∈ (H.suffixFootRerouteRim i hx_rim p).support ->
          v = H.attach j := by
  intro j hji v hvleg hvnew
  dsimp [Tripod.suffixFootRerouteRim] at hvnew
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
      · exact False.elim
          (Set.disjoint_left.mp (H.legs_disjoint j i hji) hvleg hvi)
    · rw [SimpleGraph.Walk.support_reverse] at hvprev
      have hvp : v ∈ p.support := List.mem_reverse.mp hvprev
      exfalso
      exact hp_clean v hvp ⟨j, by
        simpa [Tripod.trimPositiveLeg, Tripod.trimPositiveLegLeg, hji] using hvleg⟩
  · have hvrim : v ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim i) hx_rim hvsuff
    exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim

theorem Tripod.prefixFootRerouteRim_internal_disjoint_of_last_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x : V}
    (hx_internal : x ∈ Walk.InternalVertices (H.rim i))
    (p : G.Walk x (feet i))
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    forall j : Fin 3, j ≠ i ->
      Disjoint
        (Walk.InternalVertices (H.prefixFootRerouteRim i hx_internal.1 p))
        (Walk.InternalVertices (H.rim j)) := by
  refine H.rerouteRim_internal_disjoint_of_support p ?_ hp_meets_rims
    (H.prefixFootRerouteRim i hx_internal.1 p) ?_
  · intro j hji hxj
    exact Set.disjoint_left.mp
      (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
      hx_internal hxj
  · exact H.prefixFootRerouteRim_support_subset hx_internal.1 p

theorem Tripod.suffixFootRerouteRim_internal_disjoint_of_last_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {x : V}
    (hx_internal : x ∈ Walk.InternalVertices (H.rim i))
    (p : G.Walk x (feet i))
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    forall j : Fin 3, j ≠ i ->
      Disjoint
        (Walk.InternalVertices (H.suffixFootRerouteRim i hx_internal.1 p))
        (Walk.InternalVertices (H.rim j)) := by
  refine H.rerouteRim_internal_disjoint_of_support p ?_ hp_meets_rims
    (H.suffixFootRerouteRim i hx_internal.1 p) ?_
  · intro j hji hxj
    exact Set.disjoint_left.mp
      (H.rim_internals_disjoint i j (fun hij => hji hij.symm))
      hx_internal hxj
  · exact H.suffixFootRerouteRim_support_subset hx_internal.1 p

theorem Tripod.prefixFootRerouteRim_internal_disjoint_of_left_endpoint
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (p : G.Walk H.left (feet i))
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = H.left) :
    forall j : Fin 3, j ≠ i ->
      Disjoint
        (Walk.InternalVertices
          (H.prefixFootRerouteRim i (H.rim i).start_mem_support p))
        (Walk.InternalVertices (H.rim j)) := by
  refine H.rerouteRim_internal_disjoint_of_support p ?_ hp_meets_rims
    (H.prefixFootRerouteRim i (H.rim i).start_mem_support p) ?_
  · intro j hji hxj
    exact hxj.2.1 rfl
  · exact H.prefixFootRerouteRim_support_subset
      (H.rim i).start_mem_support p

theorem Tripod.suffixFootRerouteRim_internal_disjoint_of_right_endpoint
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (p : G.Walk H.right (feet i))
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = H.right) :
    forall j : Fin 3, j ≠ i ->
      Disjoint
        (Walk.InternalVertices
          (H.suffixFootRerouteRim i (H.rim i).end_mem_support p))
        (Walk.InternalVertices (H.rim j)) := by
  refine H.rerouteRim_internal_disjoint_of_support p ?_ hp_meets_rims
    (H.suffixFootRerouteRim i (H.rim i).end_mem_support p) ?_
  · intro j hji hxj
    exact hxj.2.2 rfl
  · exact H.suffixFootRerouteRim_support_subset
      (H.rim i).end_mem_support p

theorem Tripod.exists_legLengthSum_lt_of_prefix_same_rim_clean_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx_internal : x ∈ Walk.InternalVertices (H.rim i))
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x)
    (hidx :
      (H.rim i).support.idxOf x <
        (H.rim i).support.idxOf (H.attach i)) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum :=
  H.exists_legLengthSum_lt_of_prefix_foot_reroute_of_trim_clean
    hpos hx_internal.1 p hp hp_clean (hp_meets_rims i) hidx
    (H.prefixFootRerouteRim_internal_disjoint_of_last_rim
      hx_internal p hp_meets_rims)
    (H.prefixFootRerouteRim_oldLeg_meets_only_at_attach_of_trim_clean
      hpos hx_internal.1 p hp_clean)

theorem Tripod.exists_legLengthSum_lt_of_suffix_same_rim_clean_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx_internal : x ∈ Walk.InternalVertices (H.rim i))
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x)
    (hidx :
      (H.rim i).support.idxOf (H.attach i) <
        (H.rim i).support.idxOf x) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum :=
  H.exists_legLengthSum_lt_of_suffix_foot_reroute_of_trim_clean
    hpos hx_internal.1 p hp hp_clean (hp_meets_rims i) hidx
    (H.suffixFootRerouteRim_internal_disjoint_of_last_rim
      hx_internal p hp_meets_rims)
    (H.suffixFootRerouteRim_oldLeg_meets_only_at_attach_of_trim_clean
      hpos hx_internal.1 p hp_clean)

theorem Tripod.exists_legLengthSum_lt_of_left_endpoint_trim_clean_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    (p : G.Walk H.left (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_trimmed_rims :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = H.left) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  have hidx :
      (H.rim i).support.idxOf H.left <
        (H.rim i).support.idxOf (H.attach i) := by
    have hpos_idx :
        0 < (H.rim i).support.idxOf (H.attach i) :=
      Schematic.Math.GraphTheory.Walk.idxOf_pos_of_mem_support_ne_start
        (H.attach_mem_rim i).1 (H.attach_ne_left i)
    rw [Schematic.Math.GraphTheory.Walk.idxOf_start_support]
    exact hpos_idx
  refine H.exists_legLengthSum_lt_of_prefix_foot_reroute_of_trim_clean
    hpos (H.rim i).start_mem_support p hp hp_clean ?_ hidx ?_ ?_
  · intro v hvp hvrim
    exact hp_meets_trimmed_rims v hvp ⟨i, by
      simpa [Tripod.trimPositiveLeg] using hvrim⟩
  · exact H.prefixFootRerouteRim_internal_disjoint_of_left_endpoint p (by
      intro k v hvp hvrim
      exact hp_meets_trimmed_rims v hvp ⟨k, by
        simpa [Tripod.trimPositiveLeg] using hvrim⟩)
  · exact H.prefixFootRerouteRim_oldLeg_meets_only_at_attach_of_trim_clean
      hpos (H.rim i).start_mem_support p hp_clean

theorem Tripod.exists_legLengthSum_lt_of_right_endpoint_trim_clean_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    (p : G.Walk H.right (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_trimmed_rims :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = H.right) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  simpa using
    H.flip.exists_legLengthSum_lt_of_left_endpoint_trim_clean_reroute
      hpos p hp
      (by
        intro v hvp
        simpa [Tripod.trimPositiveLeg] using hp_clean v hvp)
      (by
        intro v hvp hvrim
        exact hp_meets_trimmed_rims v hvp (by
          simpa [Tripod.trimPositiveLeg, Tripod.rimVertexSet,
            SimpleGraph.Walk.support_reverse] using hvrim))

theorem Tripod.exists_legLengthSum_lt_of_same_rim_clean_reroute
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx_internal : x ∈ Walk.InternalVertices (H.rim i))
    (hx_ne_attach : x ≠ H.attach i)
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  rcases lt_trichotomy
      ((H.rim i).support.idxOf x)
      ((H.rim i).support.idxOf (H.attach i)) with hlt | heq | hgt
  · exact H.exists_legLengthSum_lt_of_prefix_same_rim_clean_reroute
      hpos hx_internal p hp hp_clean hp_meets_rims hlt
  · have hx_attach : x = H.attach i :=
      (List.idxOf_inj hx_internal.1).mp heq
    exact False.elim (hx_ne_attach hx_attach)
  · exact H.exists_legLengthSum_lt_of_suffix_same_rim_clean_reroute
      hpos hx_internal p hp hp_clean hp_meets_rims hgt

theorem Tripod.exists_legLengthSum_lt_of_normalized_trim_clean_same_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx :
      x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
        (H.trimPositiveLeg i hpos).legVertexSet)
    (hx_internal : x ∈ Walk.InternalVertices (H.rim i))
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_trimmed_rims :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = x) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  have hx_ne_attach : x ≠ H.attach i := by
    intro hx_attach
    exact hx.2 (by
      have hmem :
          H.attach i ∈ (H.trimPositiveLeg i hpos).legVertexSet := by
        simpa [Tripod.trimPositiveLeg] using
          (H.trimPositiveLeg i hpos).attach_mem_legVertexSet i
      simpa [hx_attach] using hmem)
  refine H.exists_legLengthSum_lt_of_same_rim_clean_reroute
    hpos hx_internal hx_ne_attach p hp hp_clean ?_
  intro k v hvp hvrim
  exact hp_meets_trimmed_rims v hvp ⟨k, by
    simpa [Tripod.trimPositiveLeg] using hvrim⟩

theorem Tripod.exists_legLengthSum_lt_of_normalized_trim_clean_endpoint_or_same_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx :
      x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
        (H.trimPositiveLeg i hpos).legVertexSet)
    (hx_case :
      x = H.left ∨ x = H.right ∨ x ∈ Walk.InternalVertices (H.rim i))
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_trimmed_rims :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = x) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  rcases hx_case with hx_left | hx_right_or_same
  · subst x
    exact H.exists_legLengthSum_lt_of_left_endpoint_trim_clean_reroute
      hpos p hp hp_clean hp_meets_trimmed_rims
  · rcases hx_right_or_same with hx_right | hx_internal
    · subst x
      exact H.exists_legLengthSum_lt_of_right_endpoint_trim_clean_reroute
        hpos p hp hp_clean hp_meets_trimmed_rims
    · exact H.exists_legLengthSum_lt_of_normalized_trim_clean_same_rim
        hpos hx hx_internal p hp hp_clean hp_meets_trimmed_rims

theorem Tripod.exists_legLengthSum_lt_or_cross_rim_of_normalized_trim_clean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx :
      x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
        (H.trimPositiveLeg i hpos).legVertexSet)
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_trimmed_rims :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = x) :
    (Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum) ∨
      Exists fun j : Fin 3 => j ≠ i ∧ x ∈ Walk.InternalVertices (H.rim j) := by
  rcases (H.trimPositiveLeg i hpos).eq_endpoint_or_exists_rim_internal_of_mem_rimVertexSet_diff_legVertexSet
      hx with hx_left | hx_right_or_internal
  · exact Or.inl
      (H.exists_legLengthSum_lt_of_normalized_trim_clean_endpoint_or_same_rim
        hpos hx (Or.inl hx_left) p hp hp_clean hp_meets_trimmed_rims)
  · rcases hx_right_or_internal with hx_right | hx_internal_trim
    · exact Or.inl
        (H.exists_legLengthSum_lt_of_normalized_trim_clean_endpoint_or_same_rim
          hpos hx (Or.inr (Or.inl hx_right)) p hp hp_clean
          hp_meets_trimmed_rims)
    · rcases hx_internal_trim with ⟨j, hxj_trim⟩
      have hxj : x ∈ Walk.InternalVertices (H.rim j) := by
        simpa [Tripod.trimPositiveLeg] using hxj_trim
      by_cases hji : j = i
      · subst j
        exact Or.inl
          (H.exists_legLengthSum_lt_of_normalized_trim_clean_endpoint_or_same_rim
            hpos hx (Or.inr (Or.inr hxj)) p hp hp_clean
            hp_meets_trimmed_rims)
      · exact Or.inr ⟨j, hji, hxj⟩

theorem Tripod.exists_legLengthSum_lt_of_normalized_trim_clean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx :
      x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
        (H.trimPositiveLeg i hpos).legVertexSet)
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_trimmed_rims :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = x) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  rcases H.exists_legLengthSum_lt_or_cross_rim_of_normalized_trim_clean
      hpos hx p hp hp_clean hp_meets_trimmed_rims with hdone | hcross
  · exact hdone
  · rcases hcross with ⟨j, hji, hxj⟩
    have hx_ne_attach : x ≠ H.attach j := by
      intro hx_attach
      exact hx.2 (by
        have hmem :
            H.attach j ∈ (H.trimPositiveLeg i hpos).legVertexSet := by
          simpa [Tripod.trimPositiveLeg] using
            (H.trimPositiveLeg i hpos).attach_mem_legVertexSet j
        simpa [hx_attach] using hmem)
    refine H.exists_legLengthSum_lt_of_cross_rim_clean_reroute
      hji hpos hxj hx_ne_attach p hp hp_clean ?_
    intro l v hvp hvrim
    exact hp_meets_trimmed_rims v hvp ⟨l, by
      simpa [Tripod.trimPositiveLeg] using hvrim⟩

theorem Tripod.trimPositiveLeg_vertexSet_subset
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (hpos : 0 < (H.leg i).length) :
    (H.trimPositiveLeg i hpos).vertexSet ⊆ H.vertexSet := by
  intro v hv
  rcases hv with hrim | hleg
  · exact Or.inl (H.trimPositiveLeg_rimVertexSet_subset i hpos hrim)
  · exact Or.inr (H.trimPositiveLeg_legVertexSet_subset i hpos hleg)

theorem Tripod.trimPositiveLeg_vertexSet_subset_delete_old_foot
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (hpos : 0 < (H.leg i).length) :
    (H.trimPositiveLeg i hpos).vertexSet ⊆ H.vertexSet \ {feet i} := by
  intro v hv
  exact ⟨H.trimPositiveLeg_vertexSet_subset i hpos hv, by
    intro hvfoot
    have hv_eq : v = feet i := Set.mem_singleton_iff.mp hvfoot
    exact H.foot_not_mem_trimPositiveLeg_vertexSet hpos (by
      simpa [hv_eq] using hv)⟩

theorem Tripod.trimPositiveLeg_new_foot_adj_old_foot
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    G.Adj ((H.feetWithPenultimate i) i) (feet i) := by
  simpa using H.positive_leg_penultimate_adj_foot hpos

theorem Tripod.trimPositiveLeg_noOtherVertexIn_oldFoot_insert_newFeet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (hpos : 0 < (H.leg i).length) :
    (H.trimPositiveLeg i hpos).NoOtherVertexIn
      (insert (feet i) (Set.range (H.feetWithPenultimate i))) := by
  intro v hv
  rcases hv with ⟨hvH, hvZ⟩
  simp only [Set.mem_insert_iff] at hvZ
  rcases hvZ with hv_old | hv_new
  · exfalso
    exact H.foot_not_mem_trimPositiveLeg_vertexSet hpos (by
      simpa [hv_old] using hvH)
  · exact hv_new

theorem Tripod.trimPositiveLeg_newFeet_subset_oldFoot_insert_newFeet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    forall j : Fin 3,
      (H.feetWithPenultimate i) j ∈
        insert (feet i) (Set.range (H.feetWithPenultimate i)) := by
  intro j
  exact Set.mem_insert_of_mem (feet i) ⟨j, rfl⟩

theorem Tripod.trimPositiveLeg_oldFoot_mem_oldFoot_insert_newFeet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    feet i ∈ insert (feet i) (Set.range (H.feetWithPenultimate i)) :=
  Set.mem_insert _ _

theorem Tripod.trimPositiveLeg_legLengthSum_lt
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (hpos : 0 < (H.leg i).length) :
    (H.trimPositiveLeg i hpos).legLengthSum < H.legLengthSum := by
  fin_cases i
  · have hdrop : (H.leg 0).dropLast.length < (H.leg 0).length := by
      rw [SimpleGraph.Walk.length_dropLast]
      exact Nat.sub_one_lt (Nat.ne_of_gt hpos)
    change
      (H.trimPositiveLegLeg 0 0).length +
          (H.trimPositiveLegLeg 0 1).length +
            (H.trimPositiveLegLeg 0 2).length <
        (H.leg 0).length + (H.leg 1).length + (H.leg 2).length
    rw [H.trimPositiveLegLeg_length_self 0,
      H.trimPositiveLegLeg_length_ne (show (1 : Fin 3) ≠ 0 by decide),
      H.trimPositiveLegLeg_length_ne (show (2 : Fin 3) ≠ 0 by decide)]
    omega
  · have hdrop : (H.leg 1).dropLast.length < (H.leg 1).length := by
      rw [SimpleGraph.Walk.length_dropLast]
      exact Nat.sub_one_lt (Nat.ne_of_gt hpos)
    change
      (H.trimPositiveLegLeg 1 0).length +
          (H.trimPositiveLegLeg 1 1).length +
            (H.trimPositiveLegLeg 1 2).length <
        (H.leg 0).length + (H.leg 1).length + (H.leg 2).length
    rw [H.trimPositiveLegLeg_length_ne (show (0 : Fin 3) ≠ 1 by decide),
      H.trimPositiveLegLeg_length_self 1,
      H.trimPositiveLegLeg_length_ne (show (2 : Fin 3) ≠ 1 by decide)]
    omega
  · have hdrop : (H.leg 2).dropLast.length < (H.leg 2).length := by
      rw [SimpleGraph.Walk.length_dropLast]
      exact Nat.sub_one_lt (Nat.ne_of_gt hpos)
    change
      (H.trimPositiveLegLeg 2 0).length +
          (H.trimPositiveLegLeg 2 1).length +
            (H.trimPositiveLegLeg 2 2).length <
        (H.leg 0).length + (H.leg 1).length + (H.leg 2).length
    rw [H.trimPositiveLegLeg_length_ne (show (0 : Fin 3) ≠ 2 by decide),
      H.trimPositiveLegLeg_length_ne (show (1 : Fin 3) ≠ 2 by decide),
      H.trimPositiveLegLeg_length_self 2]
    omega

theorem Tripod.exists_legLengthSum_lt_of_trim_clean_same_rim_path
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx : x ∈ Walk.InternalVertices ((H.trimPositiveLeg i hpos).rim i))
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_rims :
      forall j : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim j).support -> v = x)
    (hlt : p.length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  refine H.exists_legLengthSum_lt_of_shorter_same_rim_path i ?_ p hp ?_
    hp_meets_rims hlt
  · simpa [Tripod.trimPositiveLeg] using hx
  · intro j hji
    rw [Set.disjoint_left]
    intro v hvp hvj
    exact hp_clean v hvp ⟨j, by
      simpa [Tripod.trimPositiveLeg, Tripod.trimPositiveLegLeg, hji] using hvj⟩

theorem Tripod.trimPositiveLeg_clean_path_suffix_from_last_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx :
      x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
        (H.trimPositiveLeg i hpos).legVertexSet)
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet) :
    Exists fun y : V =>
      Exists fun hy : y ∈ p.reverse.support =>
        y ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
          (H.trimPositiveLeg i hpos).legVertexSet ∧
          let q : G.Walk y (feet i) := (p.reverse.takeUntil y hy).reverse
          q.IsPath ∧
            (forall v : V, v ∈ q.support ->
              v ∉ (H.trimPositiveLeg i hpos).legVertexSet) ∧
              (forall v : V, v ∈ q.support ->
                v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = y) ∧
                forall v : V, v ∈ q.support -> v ∈ p.support := by
  classical
  obtain ⟨y, hy, hyrim, hq_path, hq_last_rim, hq_subset⟩ :=
    Schematic.Math.GraphTheory.Walk.IsPath.exists_suffix_from_last_mem
      (G := G) (p := p) hp
      ((H.trimPositiveLeg i hpos).rimVertexSet) hx.1
  have hy_support : y ∈ p.support := by
    rw [SimpleGraph.Walk.support_reverse] at hy
    exact List.mem_reverse.mp hy
  refine ⟨y, hy, ⟨hyrim, ?_⟩, hq_path, ?_, hq_last_rim, hq_subset⟩
  · exact hp_clean y hy_support
  · intro v hv
    exact hp_clean v (hq_subset v hv)

theorem Tripod.trimPositiveLeg_clean_walk_suffix_from_last_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hx :
      x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
        (H.trimPositiveLeg i hpos).legVertexSet)
    (p : G.Walk x (feet i))
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet) :
    Exists fun y : V =>
      Exists fun hy : y ∈ ((p.toPath : G.Walk x (feet i)).reverse).support =>
        y ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
          (H.trimPositiveLeg i hpos).legVertexSet ∧
          let q : G.Walk y (feet i) :=
            (((p.toPath : G.Walk x (feet i)).reverse).takeUntil y hy).reverse
          q.IsPath ∧
            (forall v : V, v ∈ q.support ->
              v ∉ (H.trimPositiveLeg i hpos).legVertexSet) ∧
              (forall v : V, v ∈ q.support ->
                v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = y) ∧
                forall v : V, v ∈ q.support -> v ∈ p.support := by
  classical
  let q0 : G.Walk x (feet i) := p.toPath
  have hq0_path : q0.IsPath := p.toPath.property
  have hq0_clean :
      forall v : V, v ∈ q0.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet := by
    intro v hv
    exact hp_clean v (SimpleGraph.Walk.support_toPath_subset p hv)
  obtain ⟨y, hy, hydata, hq_path, hq_clean, hq_last_rim, hq_subset_q0⟩ :=
    H.trimPositiveLeg_clean_path_suffix_from_last_rim
      hpos hx q0 hq0_path hq0_clean
  refine ⟨y, hy, hydata, hq_path, hq_clean, hq_last_rim, ?_⟩
  intro v hv
  exact SimpleGraph.Walk.support_toPath_subset p (hq_subset_q0 v hv)

theorem Tripod.exists_legLengthSum_lt_of_trim_clean_path_to_old_foot
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    (hpath :
      Exists fun x : V =>
        x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
            (H.trimPositiveLeg i hpos).legVertexSet ∧
          Exists fun p : G.Walk x (feet i) =>
            forall v : V, v ∈ p.support ->
              v ∉ (H.trimPositiveLeg i hpos).legVertexSet) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  rcases hpath with ⟨x, hx, p, hp_clean⟩
  obtain ⟨y, hy, hydata, hq_path, hq_clean, hq_last_rim, _hq_subset⟩ :=
    H.trimPositiveLeg_clean_walk_suffix_from_last_rim hpos hx p hp_clean
  let q : G.Walk y (feet i) :=
    (((p.toPath : G.Walk x (feet i)).reverse).takeUntil y hy).reverse
  exact H.exists_legLengthSum_lt_of_normalized_trim_clean
    hpos hydata q hq_path hq_clean hq_last_rim

theorem Tripod.trimPositiveLeg_leg_hit_suffix_from_last_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x y : V}
    (hx :
      x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
        (H.trimPositiveLeg i hpos).legVertexSet)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hfirst_leg :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).legVertexSet -> v = y)
    (hfirst_Z :
      forall v : V, v ∈ p.support ->
        v ∈ insert (feet i) (Set.range (H.feetWithPenultimate i)) -> v = y)
    (hp_attach :
      forall v : V, v ∈ p.support ->
        v ∉ Set.range (H.trimPositiveLeg i hpos).attach) :
    Exists fun z : V =>
      Exists fun hz : z ∈ p.reverse.support =>
        z ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
          (H.trimPositiveLeg i hpos).legVertexSet ∧
          let q : G.Walk z y := (p.reverse.takeUntil z hz).reverse
          q.IsPath ∧
            (forall v : V, v ∈ q.support ->
              v ∈ (H.trimPositiveLeg i hpos).legVertexSet -> v = y) ∧
              (forall v : V, v ∈ q.support ->
                v ∈ insert (feet i) (Set.range (H.feetWithPenultimate i)) -> v = y) ∧
                (forall v : V, v ∈ q.support ->
                  v ∉ Set.range (H.trimPositiveLeg i hpos).attach) ∧
                  (forall v : V, v ∈ q.support ->
                    v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = z) ∧
                    forall v : V, v ∈ q.support -> v ∈ p.support := by
  classical
  obtain ⟨z, hz, hzrim, hq_path, hq_last_rim, hq_subset⟩ :=
    Schematic.Math.GraphTheory.Walk.IsPath.exists_suffix_from_last_mem
      (G := G) (p := p) hp
      ((H.trimPositiveLeg i hpos).rimVertexSet) hx.1
  have hz_support : z ∈ p.support := by
    rw [SimpleGraph.Walk.support_reverse] at hz
    exact List.mem_reverse.mp hz
  have hz_not_leg :
      z ∉ (H.trimPositiveLeg i hpos).legVertexSet :=
    (H.trimPositiveLeg i hpos).not_mem_legVertexSet_of_mem_rimVertexSet_of_not_attach
      hzrim (hp_attach z hz_support)
  refine ⟨z, hz, ⟨hzrim, hz_not_leg⟩, hq_path, ?_, ?_, ?_, hq_last_rim, hq_subset⟩
  · intro v hv hvleg
    exact hfirst_leg v (hq_subset v hv) hvleg
  · intro v hv hvZ
    exact hfirst_Z v (hq_subset v hv) hvZ
  · intro v hv
    exact hp_attach v (hq_subset v hv)

theorem Tripod.exists_legLengthSum_lt_of_normalized_trim_leg_hit_same_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x y : V}
    (hx :
      x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
        (H.trimPositiveLeg i hpos).legVertexSet)
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (hyj : y ∈ (H.leg j).support)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hfirst_leg :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).legVertexSet -> v = y)
    (hfirst_Z :
      forall v : V, v ∈ p.support ->
        v ∈ insert (feet i) (Set.range (H.feetWithPenultimate i)) -> v = y)
    (hp_attach :
      forall v : V, v ∈ p.support ->
        v ∉ Set.range (H.trimPositiveLeg i hpos).attach)
    (hp_meets_trimmed_rims :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = x)
    (hlt : ((H.leg j).dropUntil y hyj).length < (H.leg j).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  have hp_old_leg :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y :=
    H.trimPositiveLeg_path_meets_old_leg_only_at_hit hpos p
      hfirst_leg hfirst_Z
  have hp_old_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x := by
    intro k v hvp hvk
    exact hp_meets_trimmed_rims v hvp ⟨k, by
      simpa [Tripod.trimPositiveLeg] using hvk⟩
  have hy_ne_attach : y ≠ H.attach j := by
    intro hy_attach
    exact hp_attach y p.end_mem_support ⟨j, by
      simp [Tripod.trimPositiveLeg, hy_attach]⟩
  have hx_ne_attach : x ≠ H.attach j := by
    intro hx_attach
    exact hx.2 (by
      have hmem :
          H.attach j ∈ (H.trimPositiveLeg i hpos).legVertexSet := by
        simpa [Tripod.trimPositiveLeg] using
          (H.trimPositiveLeg i hpos).attach_mem_legVertexSet j
      simpa [hx_attach] using hmem)
  exact H.exists_legLengthSum_lt_of_same_rim_leg_hit_reroute
    hxj hyj hy_ne_attach p hp hp_old_leg hp_old_rims hx_ne_attach hlt

theorem Tripod.exists_legLengthSum_lt_of_normalized_trim_leg_hit_same_rim_support
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x y : V}
    (hx :
      x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
        (H.trimPositiveLeg i hpos).legVertexSet)
    (hxj_support : x ∈ (H.rim j).support)
    (hyj : y ∈ (H.leg j).support)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hfirst_leg :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).legVertexSet -> v = y)
    (hfirst_Z :
      forall v : V, v ∈ p.support ->
        v ∈ insert (feet i) (Set.range (H.feetWithPenultimate i)) -> v = y)
    (hp_attach :
      forall v : V, v ∈ p.support ->
        v ∉ Set.range (H.trimPositiveLeg i hpos).attach)
    (hp_meets_trimmed_rims :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = x)
    (hlt : ((H.leg j).dropUntil y hyj).length < (H.leg j).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  have hp_old_leg :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y :=
    H.trimPositiveLeg_path_meets_old_leg_only_at_hit hpos p
      hfirst_leg hfirst_Z
  have hp_old_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x := by
    intro k v hvp hvk
    exact hp_meets_trimmed_rims v hvp ⟨k, by
      simpa [Tripod.trimPositiveLeg] using hvk⟩
  have hy_ne_attach : y ≠ H.attach j := by
    intro hy_attach
    exact hp_attach y p.end_mem_support ⟨j, by
      simp [Tripod.trimPositiveLeg, hy_attach]⟩
  by_cases hx_left : x = H.left
  · subst x
    exact H.exists_legLengthSum_lt_of_left_endpoint_leg_hit_reroute
      hyj hy_ne_attach p hp hp_old_leg hp_old_rims hlt
  · by_cases hx_right : x = H.right
    · subst x
      exact H.exists_legLengthSum_lt_of_right_endpoint_leg_hit_reroute
        hyj hy_ne_attach p hp hp_old_leg hp_old_rims hlt
    · have hx_internal : x ∈ Walk.InternalVertices (H.rim j) :=
        ⟨hxj_support, hx_left, hx_right⟩
      exact H.exists_legLengthSum_lt_of_normalized_trim_leg_hit_same_rim
        hpos hx hx_internal hyj p hp hfirst_leg hfirst_Z hp_attach
        hp_meets_trimmed_rims hlt

theorem Tripod.exists_legLengthSum_lt_of_normalized_trim_leg_hit
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x y : V}
    (hx :
      x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
        (H.trimPositiveLeg i hpos).legVertexSet)
    (hyj : y ∈ (H.leg j).support)
    (p : G.Walk x y)
    (hp : p.IsPath)
    (hfirst_leg :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).legVertexSet -> v = y)
    (hfirst_Z :
      forall v : V, v ∈ p.support ->
        v ∈ insert (feet i) (Set.range (H.feetWithPenultimate i)) -> v = y)
    (hp_attach :
      forall v : V, v ∈ p.support ->
        v ∉ Set.range (H.trimPositiveLeg i hpos).attach)
    (hp_meets_trimmed_rims :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).rimVertexSet -> v = x)
    (hlt : ((H.leg j).dropUntil y hyj).length < (H.leg j).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  have hp_old_leg :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.leg k).support -> v = y :=
    H.trimPositiveLeg_path_meets_old_leg_only_at_hit hpos p
      hfirst_leg hfirst_Z
  have hp_old_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x := by
    intro k v hvp hvk
    exact hp_meets_trimmed_rims v hvp ⟨k, by
      simpa [Tripod.trimPositiveLeg] using hvk⟩
  have hy_ne_attach : y ≠ H.attach j := by
    intro hy_attach
    exact hp_attach y p.end_mem_support ⟨j, by
      simp [Tripod.trimPositiveLeg, hy_attach]⟩
  rcases (H.trimPositiveLeg i hpos).eq_endpoint_or_exists_rim_internal_of_mem_rimVertexSet_diff_legVertexSet
      hx with hx_left | hx_right_or_internal
  · subst x
    exact H.exists_legLengthSum_lt_of_left_endpoint_leg_hit_reroute
      hyj hy_ne_attach p hp hp_old_leg hp_old_rims hlt
  · rcases hx_right_or_internal with hx_right | hx_internal_trim
    · subst x
      exact H.exists_legLengthSum_lt_of_right_endpoint_leg_hit_reroute
        hyj hy_ne_attach p hp hp_old_leg hp_old_rims hlt
    · rcases hx_internal_trim with ⟨l, hxl_trim⟩
      have hxl : x ∈ Walk.InternalVertices (H.rim l) := by
        simpa [Tripod.trimPositiveLeg] using hxl_trim
      by_cases hlj : l = j
      · subst l
        exact H.exists_legLengthSum_lt_of_normalized_trim_leg_hit_same_rim
          hpos hx hxl hyj p hp hfirst_leg hfirst_Z hp_attach
          hp_meets_trimmed_rims hlt
      · have hx_ne_attach : x ≠ H.attach l := by
          intro hx_attach
          exact hx.2 (by
            have hmem :
                H.attach l ∈ (H.trimPositiveLeg i hpos).legVertexSet := by
              simpa [Tripod.trimPositiveLeg] using
                (H.trimPositiveLeg i hpos).attach_mem_legVertexSet l
            simpa [hx_attach] using hmem)
        exact H.exists_legLengthSum_lt_of_cross_rim_leg_hit_reroute
          (i := j) (j := l) hlj hxl hx_ne_attach hyj hy_ne_attach
          p hp hp_old_leg hp_old_rims hlt


end Schematic.Math.GraphTheory
