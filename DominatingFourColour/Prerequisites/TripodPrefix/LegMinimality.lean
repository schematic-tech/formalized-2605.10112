import DominatingFourColour.Prerequisites.TripodPrefix.FootReroutes

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
def Tripod.LegLengthMinimal {feet : Fin 3 -> V} (H : Tripod G feet) : Prop :=
  forall H' : Tripod G feet, H.legLengthSum <= H'.legLengthSum

theorem Tripod.not_adj_of_legLengthMinimal_leg_idx_gap
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hmin : H.LegLengthMinimal)
    (i : Fin 3)
    {x y : V}
    (hx : x ∈ (H.leg i).support)
    (hy : y ∈ (H.leg i).support)
    (hidx : (H.leg i).support.idxOf x + 1 < (H.leg i).support.idxOf y) :
    ¬ G.Adj x y := by
  intro hxy
  rcases H.exists_legLengthSum_lt_of_leg_chord_idx_gap i hx hy hxy hidx with
    ⟨H', hlt⟩
  exact Nat.not_lt_of_ge (hmin H') hlt

theorem Tripod.leg_isChordless_of_legLengthMinimal
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hmin : H.LegLengthMinimal)
    (i : Fin 3) :
    (H.leg i).IsChordless := by
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
  intro x y hx hy hxy
  rcases Walk.toSubgraph_adj_or_idx_gap_of_support_adj
      (H.leg i) hx hy hxy with hsub | hgap
  · exact (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).mp hsub
  · rcases hgap with hgap | hgap
    · exact False.elim
        ((H.not_adj_of_legLengthMinimal_leg_idx_gap hmin i hx hy hgap) hxy)
    · exact False.elim
        ((H.not_adj_of_legLengthMinimal_leg_idx_gap hmin i hy hx hgap) hxy.symm)

theorem Tripod.leg_length_pos_iff_attach_ne_foot
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    0 < (H.leg i).length ↔ H.attach i ≠ feet i := by
  constructor
  · intro hpos hattach
    have hpath :
        ((H.leg i).copy hattach rfl).IsPath := by
      exact (SimpleGraph.Walk.isPath_copy (H.leg i) hattach rfl).mpr
        (H.leg_isPath i)
    have hnil :
        (H.leg i).copy hattach rfl =
          (SimpleGraph.Walk.nil : G.Walk (feet i) (feet i)) :=
      (SimpleGraph.Walk.isPath_iff_eq_nil _).mp hpath
    have hlen := congrArg SimpleGraph.Walk.length hnil
    have hzero : (H.leg i).length = 0 := by
      simpa [SimpleGraph.Walk.length_copy] using hlen
    omega
  · intro hne
    by_contra hnot
    have hzero : (H.leg i).length = 0 := by omega
    exact hne (SimpleGraph.Walk.eq_of_length_eq_zero hzero)

theorem Tripod.leg_length_eq_zero_of_legLengthSum_eq_zero
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hzero : H.legLengthSum = 0)
    (i : Fin 3) :
    (H.leg i).length = 0 := by
  fin_cases i <;> dsimp [Tripod.legLengthSum] at hzero ⊢ <;> omega

theorem Tripod.legless_of_legLengthSum_eq_zero
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hzero : H.legLengthSum = 0) :
    H.Legless := by
  intro i
  exact SimpleGraph.Walk.eq_of_length_eq_zero
    (H.leg_length_eq_zero_of_legLengthSum_eq_zero hzero i)

theorem Tripod.legLengthSum_eq_zero_of_legless
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless) :
    H.legLengthSum = 0 := by
  have h0 : (H.leg 0).length = 0 := by
    have hpath :
        ((H.leg 0).copy (hH 0) rfl).IsPath := by
      exact (SimpleGraph.Walk.isPath_copy (H.leg 0) (hH 0) rfl).mpr
        (H.leg_isPath 0)
    have hnil :
        (H.leg 0).copy (hH 0) rfl =
          (SimpleGraph.Walk.nil : G.Walk (feet 0) (feet 0)) :=
      (SimpleGraph.Walk.isPath_iff_eq_nil _).mp hpath
    have hlen := congrArg SimpleGraph.Walk.length hnil
    simpa [SimpleGraph.Walk.length_copy] using hlen
  have h1 : (H.leg 1).length = 0 := by
    have hpath :
        ((H.leg 1).copy (hH 1) rfl).IsPath := by
      exact (SimpleGraph.Walk.isPath_copy (H.leg 1) (hH 1) rfl).mpr
        (H.leg_isPath 1)
    have hnil :
        (H.leg 1).copy (hH 1) rfl =
          (SimpleGraph.Walk.nil : G.Walk (feet 1) (feet 1)) :=
      (SimpleGraph.Walk.isPath_iff_eq_nil _).mp hpath
    have hlen := congrArg SimpleGraph.Walk.length hnil
    simpa [SimpleGraph.Walk.length_copy] using hlen
  have h2 : (H.leg 2).length = 0 := by
    have hpath :
        ((H.leg 2).copy (hH 2) rfl).IsPath := by
      exact (SimpleGraph.Walk.isPath_copy (H.leg 2) (hH 2) rfl).mpr
        (H.leg_isPath 2)
    have hnil :
        (H.leg 2).copy (hH 2) rfl =
          (SimpleGraph.Walk.nil : G.Walk (feet 2) (feet 2)) :=
      (SimpleGraph.Walk.isPath_iff_eq_nil _).mp hpath
    have hlen := congrArg SimpleGraph.Walk.length hnil
    simpa [SimpleGraph.Walk.length_copy] using hlen
  dsimp [Tripod.legLengthSum]
  omega

theorem Tripod.legless_iff_legLengthSum_eq_zero
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.Legless ↔ H.legLengthSum = 0 := by
  exact ⟨H.legLengthSum_eq_zero_of_legless,
    H.legless_of_legLengthSum_eq_zero⟩

theorem Tripod.exists_positive_leg_of_not_legless
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hnot : Not H.Legless) :
    Exists fun i : Fin 3 => 0 < (H.leg i).length := by
  by_contra hnone
  push Not at hnone
  have hzero : H.legLengthSum = 0 := by
    dsimp [Tripod.legLengthSum]
    have h0 := hnone 0
    have h1 := hnone 1
    have h2 := hnone 2
    omega
  exact hnot (H.legless_of_legLengthSum_eq_zero hzero)

theorem Tripod.attach_ne_foot_of_positive_leg
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    H.attach i ≠ feet i :=
  (H.leg_length_pos_iff_attach_ne_foot i).mp hpos

theorem Tripod.leg_dropUntil_length_lt_of_mem_support_ne_attach
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {y : V}
    (hy : y ∈ (H.leg i).support)
    (hy_attach : y ≠ H.attach i) :
    ((H.leg i).dropUntil y hy).length < (H.leg i).length :=
  Walk.length_dropUntil_lt_of_mem_support_ne_start
    (G := G) hy hy_attach

theorem Tripod.exists_leg_dropUntil_length_lt_of_legVertexSet_not_attach
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {y : V}
    (hy_leg : y ∈ H.legVertexSet)
    (hy_attach : y ∉ Set.range H.attach) :
    Exists fun i : Fin 3 =>
      Exists fun hy : y ∈ (H.leg i).support =>
        ((H.leg i).dropUntil y hy).length < (H.leg i).length := by
  rcases hy_leg with ⟨i, hyi⟩
  refine ⟨i, hyi, H.leg_dropUntil_length_lt_of_mem_support_ne_attach hyi ?_⟩
  intro hy_eq_attach
  exact hy_attach ⟨i, hy_eq_attach.symm⟩

theorem Tripod.foot_not_mem_attach_range_of_attach_ne_foot
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hne : H.attach i ≠ feet i) :
    feet i ∉ Set.range H.attach := by
  rintro ⟨j, hj⟩
  have hleg : feet i ∈ (H.leg i).support :=
    (H.leg i).end_mem_support
  have hrim : feet i ∈ (H.rim j).support := by
    simpa [hj] using (H.attach_mem_rim j).1
  have hfoot_eq_attach :
      feet i = H.attach i :=
    H.leg_meets_rims_only_at_attach i j (feet i) hleg hrim
  exact hne hfoot_eq_attach.symm

theorem Tripod.foot_not_mem_attach_range_of_positive_leg
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    feet i ∉ Set.range H.attach :=
  H.foot_not_mem_attach_range_of_attach_ne_foot
    (H.attach_ne_foot_of_positive_leg hpos)

theorem Tripod.foot_not_mem_rim_support_of_attach_ne_foot
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hne : H.attach i ≠ feet i)
    (j : Fin 3) :
    feet i ∉ (H.rim j).support := by
  intro hrim
  have hleg : feet i ∈ (H.leg i).support :=
    (H.leg i).end_mem_support
  have hfoot_eq_attach :
      feet i = H.attach i :=
    H.leg_meets_rims_only_at_attach i j (feet i) hleg hrim
  exact hne hfoot_eq_attach.symm

theorem Tripod.foot_not_mem_rim_support_of_positive_leg
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    (j : Fin 3) :
    feet i ∉ (H.rim j).support :=
  H.foot_not_mem_rim_support_of_attach_ne_foot
    (H.attach_ne_foot_of_positive_leg hpos) j

theorem Tripod.foot_not_mem_rimVertexSet_of_positive_leg
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    feet i ∉ H.rimVertexSet := by
  rintro ⟨j, hj⟩
  exact H.foot_not_mem_rim_support_of_positive_leg hpos j hj

theorem Tripod.foot_not_mem_other_leg_support
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hij : i ≠ j) :
    feet i ∉ (H.leg j).support := by
  intro hj
  exact Set.disjoint_left.mp (H.legs_disjoint i j hij)
    (H.leg i).end_mem_support hj

def Tripod.feetWithPenultimate
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    Fin 3 -> V :=
  Function.update feet i (H.leg i).penultimate

@[simp]
theorem Tripod.feetWithPenultimate_apply_self
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    (H.feetWithPenultimate i) i = (H.leg i).penultimate := by
  simp [Tripod.feetWithPenultimate]

@[simp]
theorem Tripod.feetWithPenultimate_apply_ne
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i) :
    (H.feetWithPenultimate i) j = feet j := by
  simp [Tripod.feetWithPenultimate, hji]

theorem Tripod.leg_penultimate_mem_support_of_positive
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3} :
    (H.leg i).penultimate ∈ (H.leg i).support :=
  SimpleGraph.Walk.getVert_mem_support (H.leg i) ((H.leg i).length - 1)

theorem Tripod.positive_leg_penultimate_adj_foot
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    G.Adj (H.leg i).penultimate (feet i) := by
  have hnot_nil : ¬ (H.leg i).Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact hpos
  exact (H.leg i).adj_penultimate hnot_nil

theorem Tripod.leg_penultimate_ne_foot_of_positive
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    (H.leg i).penultimate ≠ feet i :=
  (H.positive_leg_penultimate_adj_foot hpos).ne

theorem Tripod.leg_penultimate_ne_attach_of_length_gt_one
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hlen : 1 < (H.leg i).length) :
    (H.leg i).penultimate ≠ H.attach i := by
  intro hpen
  have hdrop_path : (H.leg i).dropLast.IsPath :=
    SimpleGraph.Walk.isPath_of_isSubwalk
      ((SimpleGraph.Walk.isSubwalk_rfl (H.leg i)).dropLast)
      (H.leg_isPath i)
  have hclosed_path :
      (((H.leg i).dropLast).copy rfl hpen).IsPath := by
    exact (SimpleGraph.Walk.isPath_copy _ rfl hpen).mpr hdrop_path
  have hnil :
      ((H.leg i).dropLast).copy rfl hpen =
        (SimpleGraph.Walk.nil : G.Walk (H.attach i) (H.attach i)) :=
    (SimpleGraph.Walk.isPath_iff_eq_nil _).mp hclosed_path
  have hdrop_zero : (H.leg i).dropLast.length = 0 := by
    have hlen_eq := congrArg SimpleGraph.Walk.length hnil
    simpa [SimpleGraph.Walk.length_copy] using hlen_eq
  have hnot_nil : ¬ (H.leg i).Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hdrop_add := SimpleGraph.Walk.length_dropLast_add_one
    (p := H.leg i) hnot_nil
  omega

theorem Tripod.leg_penultimate_not_mem_attach_range_of_length_gt_one
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hlen : 1 < (H.leg i).length) :
    (H.leg i).penultimate ∉ Set.range H.attach := by
  rintro ⟨j, hj⟩
  have hleg :
      (H.leg i).penultimate ∈ (H.leg i).support :=
    H.leg_penultimate_mem_support_of_positive
  have hrim :
      (H.leg i).penultimate ∈ (H.rim j).support := by
    simpa [hj] using (H.attach_mem_rim j).1
  have hpen_attach :
      (H.leg i).penultimate = H.attach i :=
    H.leg_meets_rims_only_at_attach i j (H.leg i).penultimate hleg hrim
  exact H.leg_penultimate_ne_attach_of_length_gt_one hlen hpen_attach

theorem Tripod.leg_penultimate_not_mem_feet_of_positive
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    (H.leg i).penultimate ∉ Set.range feet := by
  rintro ⟨j, hj⟩
  have hpen_support : feet j ∈ (H.leg i).support := by
    simp [hj, H.leg_penultimate_mem_support_of_positive]
  by_cases hji : j = i
  · subst j
    exact H.leg_penultimate_ne_foot_of_positive hpos hj.symm
  · exact Set.disjoint_left.mp (H.legs_disjoint i j (fun hij => hji hij.symm))
      hpen_support (H.leg j).end_mem_support

theorem Tripod.feetWithPenultimate_injective
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hfeet_injective : Function.Injective feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    Function.Injective (H.feetWithPenultimate i) := by
  intro j k hjk
  by_cases hji : j = i
  · subst j
    by_cases hki : k = i
    · subst k
      rfl
    · exfalso
      have hpen_eq_foot : (H.leg i).penultimate = feet k := by
        simpa [H.feetWithPenultimate_apply_ne hki] using hjk
      exact H.leg_penultimate_not_mem_feet_of_positive hpos
        ⟨k, hpen_eq_foot.symm⟩
  · by_cases hki : k = i
    · subst k
      exfalso
      have hfoot_eq_pen : feet j = (H.leg i).penultimate := by
        simpa [H.feetWithPenultimate_apply_ne hji] using hjk
      exact H.leg_penultimate_not_mem_feet_of_positive hpos
        ⟨j, hfoot_eq_pen⟩
    · have hfeet : feet j = feet k := by
        simpa [H.feetWithPenultimate_apply_ne hji,
          H.feetWithPenultimate_apply_ne hki] using hjk
      exact hfeet_injective hfeet

theorem Tripod.feetWithPenultimate_range_ncard_eq_three
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hfeet_injective : Function.Injective feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    (Set.range (H.feetWithPenultimate i)).ncard = 3 := by
  rw [Set.ncard_range_of_injective
    (H.feetWithPenultimate_injective hfeet_injective hpos)]
  simp

theorem Tripod.old_foot_not_mem_feetWithPenultimate_range
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hfeet_injective : Function.Injective feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    feet i ∉ Set.range (H.feetWithPenultimate i) := by
  rintro ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    have hfoot_eq_pen : feet i = (H.leg i).penultimate := by
      simpa using hj.symm
    exact H.leg_penultimate_ne_foot_of_positive hpos hfoot_eq_pen.symm
  · have hfoot_eq : feet i = feet j := by
      simpa [H.feetWithPenultimate_apply_ne hji] using hj.symm
    exact hji (hfeet_injective hfoot_eq).symm

theorem Tripod.oldFoot_insert_feetWithPenultimate_range_ncard_eq_four
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hfeet_injective : Function.Injective feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    (insert (feet i) (Set.range (H.feetWithPenultimate i))).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem
    (H.old_foot_not_mem_feetWithPenultimate_range hfeet_injective hpos)]
  rw [H.feetWithPenultimate_range_ncard_eq_three hfeet_injective hpos]

theorem Tripod.leg_penultimate_not_left_of_positive
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    (H.leg i).penultimate ≠ H.left := by
  intro hpen_left
  have hleg : H.left ∈ (H.leg i).support := by
    have hnot_nil : ¬(H.leg i).Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hpos
    simpa [hpen_left] using
      List.mem_of_mem_dropLast
        (SimpleGraph.Walk.penultimate_mem_dropLast_support hnot_nil)
  have hrim : H.left ∈ (H.rim i).support :=
    (H.rim i).start_mem_support
  have hleft_attach : H.left = H.attach i :=
    H.leg_meets_rims_only_at_attach i i H.left hleg hrim
  exact (H.attach_ne_left i) hleft_attach.symm

theorem Tripod.leg_penultimate_not_right_of_positive
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    (H.leg i).penultimate ≠ H.right := by
  simpa using H.flip.leg_penultimate_not_left_of_positive hpos

def Tripod.trimPositiveLegLeg
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i j : Fin 3) :
    G.Walk (H.attach j) ((H.feetWithPenultimate i) j) := by
  by_cases hji : j = i
  · subst j
    exact (H.leg i).dropLast.copy rfl (by
      simp [Tripod.feetWithPenultimate])
  · exact (H.leg j).copy rfl (by
      simp [Tripod.feetWithPenultimate, hji])

theorem Tripod.trimPositiveLegLeg_isPath
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i j : Fin 3) :
    (H.trimPositiveLegLeg i j).IsPath := by
  unfold Tripod.trimPositiveLegLeg
  split_ifs with hji
  · subst j
    exact (SimpleGraph.Walk.isPath_copy _ rfl _).mpr
      (SimpleGraph.Walk.isPath_of_isSubwalk
        ((SimpleGraph.Walk.isSubwalk_rfl (H.leg i)).dropLast)
        (H.leg_isPath i))
  · exact (SimpleGraph.Walk.isPath_copy _ rfl _).mpr (H.leg_isPath j)

theorem Tripod.trimPositiveLegLeg_support_subset
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i j : Fin 3) :
    {v : V | v ∈ (H.trimPositiveLegLeg i j).support} ⊆
      {v : V | v ∈ (H.leg j).support} := by
  intro v hv
  unfold Tripod.trimPositiveLegLeg at hv
  split_ifs at hv with hji
  · subst j
    exact ((SimpleGraph.Walk.isSubwalk_rfl (H.leg i)).dropLast).support_subset
      (by simpa using hv)
  · simpa using hv

@[simp]
theorem Tripod.trimPositiveLegLeg_length_self
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    (H.trimPositiveLegLeg i i).length = (H.leg i).dropLast.length := by
  unfold Tripod.trimPositiveLegLeg
  simp

@[simp]
theorem Tripod.trimPositiveLegLeg_length_ne
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i) :
    (H.trimPositiveLegLeg i j).length = (H.leg j).length := by
  unfold Tripod.trimPositiveLegLeg
  simp [hji]

def Tripod.trimPositiveLeg
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (hpos : 0 < (H.leg i).length) :
    Tripod G (H.feetWithPenultimate i) where
  left := H.left
  right := H.right
  left_ne_right := H.left_ne_right
  left_not_foot := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [Tripod.feetWithPenultimate] using
        (H.leg_penultimate_not_left_of_positive hpos).symm
    · simpa [Tripod.feetWithPenultimate, hji] using H.left_not_foot j
  right_not_foot := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [Tripod.feetWithPenultimate] using
        (H.leg_penultimate_not_right_of_positive hpos).symm
    · simpa [Tripod.feetWithPenultimate, hji] using H.right_not_foot j
  rim := H.rim
  rim_isPath := H.rim_isPath
  attach := H.attach
  attach_mem_rim := H.attach_mem_rim
  rim_internals_disjoint := H.rim_internals_disjoint
  leg := H.trimPositiveLegLeg i
  leg_isPath := H.trimPositiveLegLeg_isPath i
  legs_disjoint := by
    intro j k hjk
    rw [Set.disjoint_left]
    intro v hvj hvk
    have hvj_old : v ∈ (H.leg j).support :=
      H.trimPositiveLegLeg_support_subset i j hvj
    have hvk_old : v ∈ (H.leg k).support :=
      H.trimPositiveLegLeg_support_subset i k hvk
    exact Set.disjoint_left.mp (H.legs_disjoint j k hjk) hvj_old hvk_old
  leg_meets_rims_only_at_attach := by
    intro j k v hvleg hvrim
    have hvleg_old : v ∈ (H.leg j).support :=
      H.trimPositiveLegLeg_support_subset i j hvleg
    exact H.leg_meets_rims_only_at_attach j k v hvleg_old hvrim

theorem Tripod.foot_not_mem_trimPositiveLegLeg_support
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    (j : Fin 3) :
    feet i ∉ (H.trimPositiveLegLeg i j).support := by
  by_cases hji : j = i
  · subst j
    have hnot_nil : Not (H.leg i).Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hpos
    intro hmem
    have hmem_drop : feet i ∈ (H.leg i).dropLast.support := by
      simpa [Tripod.trimPositiveLegLeg] using hmem
    exact Walk.IsPath.end_notMem_walk_dropLast_support
      (H.leg_isPath i) hnot_nil hmem_drop
  · intro hmem
    have hmem_old : feet i ∈ (H.leg j).support :=
      H.trimPositiveLegLeg_support_subset i j hmem
    exact H.foot_not_mem_other_leg_support (fun hij => hji hij.symm) hmem_old

theorem Tripod.foot_not_mem_trimPositiveLeg_legVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    feet i ∉ (H.trimPositiveLeg i hpos).legVertexSet := by
  rintro ⟨j, hj⟩
  exact H.foot_not_mem_trimPositiveLegLeg_support hpos j hj

theorem Tripod.foot_not_mem_trimPositiveLeg_vertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    feet i ∉ (H.trimPositiveLeg i hpos).vertexSet := by
  intro hmem
  rcases hmem with hrim | hleg
  · exact H.foot_not_mem_rimVertexSet_of_positive_leg hpos hrim
  · exact H.foot_not_mem_trimPositiveLeg_legVertexSet hpos hleg

theorem Tripod.trimPositiveLeg_rimVertexSet_subset
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (hpos : 0 < (H.leg i).length) :
    (H.trimPositiveLeg i hpos).rimVertexSet ⊆ H.rimVertexSet := by
  rintro v ⟨j, hv⟩
  exact ⟨j, by simpa [Tripod.trimPositiveLeg] using hv⟩

theorem Tripod.trimPositiveLeg_legVertexSet_subset
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (hpos : 0 < (H.leg i).length) :
    (H.trimPositiveLeg i hpos).legVertexSet ⊆ H.legVertexSet := by
  rintro v ⟨j, hv⟩
  have hv' : v ∈ (H.trimPositiveLegLeg i j).support := by
    simpa [Tripod.trimPositiveLeg] using hv
  exact ⟨j, H.trimPositiveLegLeg_support_subset i j hv'⟩

theorem Tripod.trimPositiveLeg_leg_hit_old_suffix_shorter
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {y : V}
    (hy : y ∈ ((H.trimPositiveLeg i hpos).leg j).support)
    (hy_not_attach :
      y ∉ Set.range (H.trimPositiveLeg i hpos).attach) :
    Exists fun hy_old : y ∈ (H.leg j).support =>
      ((H.leg j).dropUntil y hy_old).length < (H.leg j).length := by
  have hy_trim : y ∈ (H.trimPositiveLegLeg i j).support := by
    simpa [Tripod.trimPositiveLeg] using hy
  have hy_old : y ∈ (H.leg j).support :=
    H.trimPositiveLegLeg_support_subset i j hy_trim
  refine ⟨hy_old, H.leg_dropUntil_length_lt_of_mem_support_ne_attach hy_old ?_⟩
  intro hy_attach
  exact hy_not_attach ⟨j, by simp [Tripod.trimPositiveLeg, hy_attach]⟩

theorem Tripod.mem_trimPositiveLeg_legVertexSet_self_of_mem_leg_ne_foot
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {v : V}
    (hv : v ∈ (H.leg i).support)
    (hv_ne_foot : v ≠ feet i) :
    v ∈ (H.trimPositiveLeg i hpos).legVertexSet := by
  refine ⟨i, ?_⟩
  have hv_drop : v ∈ (H.leg i).dropLast.support :=
    Schematic.Math.GraphTheory.Walk.mem_dropLast_support_of_mem_support_ne_end hv hv_ne_foot
  simpa [Tripod.trimPositiveLeg, Tripod.trimPositiveLegLeg] using hv_drop

theorem Tripod.trimPositiveLeg_path_meets_old_leg_only_at_hit
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    {x y : V}
    (p : G.Walk x y)
    (hfirst_leg :
      forall v : V, v ∈ p.support ->
        v ∈ (H.trimPositiveLeg i hpos).legVertexSet -> v = y)
    (hfirst_Z :
      forall v : V, v ∈ p.support ->
        v ∈ insert (feet i) (Set.range (H.feetWithPenultimate i)) -> v = y) :
    forall j : Fin 3, forall v : V,
      v ∈ p.support -> v ∈ (H.leg j).support -> v = y := by
  intro j v hvp hvleg
  by_cases hvfoot : v = feet i
  · exact hfirst_Z v hvp (by simp [hvfoot])
  · by_cases hji : j = i
    · subst j
      exact hfirst_leg v hvp
        (H.mem_trimPositiveLeg_legVertexSet_self_of_mem_leg_ne_foot
          hpos hvleg hvfoot)
    · exact hfirst_leg v hvp ⟨j, by
        simpa [Tripod.trimPositiveLeg, Tripod.trimPositiveLegLeg, hji] using hvleg⟩

theorem Tripod.prefixFootRerouteRim_isPath_of_trim_clean
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
        (H.rim i).support.idxOf (H.attach i)) :
    (H.prefixFootRerouteRim i hx_rim p).IsPath :=
  H.prefixFootRerouteRim_isPath hx_rim p hp
    (by
      intro v hvp hvleg
      by_cases hvfoot : v = feet i
      · exact hvfoot
      · exact False.elim
          (hp_clean v hvp
            (H.mem_trimPositiveLeg_legVertexSet_self_of_mem_leg_ne_foot
              hpos hvleg hvfoot)))
    hp_meets_rim hidx

theorem Tripod.suffixFootRerouteRim_isPath_of_trim_clean
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
        (H.rim i).support.idxOf x) :
    (H.suffixFootRerouteRim i hx_rim p).IsPath :=
  H.suffixFootRerouteRim_isPath hx_rim p hp
    (by
      intro v hvp hvleg
      by_cases hvfoot : v = feet i
      · exact hvfoot
      · exact False.elim
          (hp_clean v hvp
            (H.mem_trimPositiveLeg_legVertexSet_self_of_mem_leg_ne_foot
              hpos hvleg hvfoot)))
    hp_meets_rim hidx

theorem Tripod.crossPrefixPositiveRim_isPath_of_trim_clean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    ((p.append (H.leg i).reverse).append
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
  have hp_meets_leg_only_at_foot :
      forall v : V, v ∈ p.support -> v ∈ (H.leg i).support ->
        v = feet i := by
    intro v hvp hvleg
    by_cases hvfoot : v = feet i
    · exact hvfoot
    · exact False.elim
        (hp_clean v hvp
          (H.mem_trimPositiveLeg_legVertexSet_self_of_mem_leg_ne_foot
            hpos hvleg hvfoot))
  have hp_leg : (p.append (H.leg i).reverse).IsPath := by
    refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
      hp (H.leg_isPath i).reverse ?_
    intro z hzp hzlegrev
    rw [SimpleGraph.Walk.support_reverse] at hzlegrev
    exact hp_meets_leg_only_at_foot z hzp (List.mem_reverse.mp hzlegrev)
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
      have hzleg : z ∈ (H.leg i).support := List.mem_reverse.mp hzlegrev
      exact H.leg_meets_rims_only_at_attach i i z hzleg hzrim

theorem Tripod.crossSuffixPositiveRim_isPath_of_trim_clean
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    (hpos : 0 < (H.leg i).length)
    {x : V}
    (hxj : x ∈ Walk.InternalVertices (H.rim j))
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hp_clean :
      forall v : V, v ∈ p.support ->
        v ∉ (H.trimPositiveLeg i hpos).legVertexSet)
    (hp_meets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim k).support -> v = x) :
    ((((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).append
      (H.leg i)).append p.reverse).IsPath := by
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
  have hp_meets_leg_only_at_foot :
      forall v : V, v ∈ p.support -> v ∈ (H.leg i).support ->
        v = feet i := by
    intro v hvp hvleg
    by_cases hvfoot : v = feet i
    · exact hvfoot
    · exact False.elim
        (hp_clean v hvp
          (H.mem_trimPositiveLeg_legVertexSet_self_of_mem_leg_ne_foot
            hpos hvleg hvfoot))
  let pref : G.Walk H.left (H.attach i) :=
    (H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1
  have hpref : pref.IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_takeUntil (H.rim i)
        (H.attach_mem_rim i).1)
      (H.rim_isPath i)
  have hpref_leg : (pref.append (H.leg i)).IsPath := by
    refine Schematic.Math.GraphTheory.Walk.IsPath.append_of_support_inter_eq_endpoint
      hpref (H.leg_isPath i) ?_
    intro z hzpref hzleg
    have hzrim : z ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 (by simpa [pref] using hzpref)
    exact H.leg_meets_rims_only_at_attach i i z hzleg hzrim
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
  · exact hp_meets_leg_only_at_foot z hzp hzleg


end Schematic.Math.GraphTheory
