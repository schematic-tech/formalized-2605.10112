import DominatingFourColour.Prerequisites.TripodMinimal.Separation

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

def RST35NoSeparation (G : SimpleGraph V) (feet : Fin 3 -> V) : Prop :=
  forall S : Separation G,
    (forall i : Fin 3, feet i ∈ S.left) ->
      2 <= (S.right \ S.left).ncard ->
        S.OrderAtMost 2 ->
          False

theorem RST35NoSeparation.no_blocked_core
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST35NoSeparation G feet)
    {K B : Set V}
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b))
    (hfeet : forall i : Fin 3, feet i ∉ K)
    (hK_card : 2 <= K.ncard)
    (hB_card : B.ncard <= 2) :
    False := by
  classical
  let S : Separation G := Separation.ofCoreAndBoundary K B hclosed
  have hfeet_left : forall i : Fin 3, feet i ∈ S.left := by
    intro i
    exact hfeet i
  have hright_eq : S.right \ S.left = K := by
    ext v
    constructor
    · rintro ⟨hv_right, hv_not_left⟩
      by_contra hvK
      exact hv_not_left (by simpa [S, Separation.ofCoreAndBoundary] using hvK)
    · intro hvK
      exact ⟨Or.inl hvK, fun hv_notK => hv_notK hvK⟩
  have hright_card : 2 <= (S.right \ S.left).ncard := by
    simpa [hright_eq] using hK_card
  have horder : S.OrderAtMost 2 := by
    simpa [S] using
      Separation.ofCoreAndBoundary_orderAtMost_of_boundary_ncard_le
        (G := G) K B hclosed hB_card
  exact hno S hfeet_left hright_card horder

theorem RST35NoSeparation.delete_feet_component_adjacent_to_foot_of_large
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hno : RST35NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (C : (G.induce (Set.range feet)ᶜ).ConnectedComponent)
    (hlarge : 2 <= (induceComponentSupport (G := G) C).ncard)
    (i : Fin 3) :
    Exists fun u : V =>
      u ∈ induceComponentSupport (G := G) C ∧ G.Adj u (feet i) := by
  classical
  let K : Set V := induceComponentSupport (G := G) C
  by_contra hno_adj
  let B : Set V := Set.range feet \ {feet i}
  have hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b) := by
    intro a b ha hbK hbB hab
    by_cases hbFeet : b ∈ Set.range feet
    · have hb_eq : b = feet i := by
        by_cases hbi : b = feet i
        · exact hbi
        · exact False.elim (hbB ⟨hbFeet, by
            simpa [Set.mem_singleton_iff] using hbi⟩)
      subst b
      exact hno_adj ⟨a, by simpa [K] using ha, hab⟩
    · exact hbK (by
        have hb_compl : b ∈ (Set.range feet)ᶜ := by
          simpa using hbFeet
        exact induceComponentSupport_mem_of_adj (G := G) C
          (by simpa [K] using ha) hb_compl hab)
  have hfeet_not_K : forall j : Fin 3, feet j ∉ K := by
    intro j hfootK
    have hfoot_compl :
        feet j ∈ (Set.range feet)ᶜ :=
      induceComponentSupport_subset (G := G) C (by simpa [K] using hfootK)
    exact hfoot_compl ⟨j, rfl⟩
  have hB_card : B.ncard <= 2 := by
    simpa [B] using
      ncard_range_fin3_diff_singleton_le_two hfeet_injective i
  exact hno.no_blocked_core hclosed hfeet_not_K
    (by simpa [K] using hlarge) (by simpa [B] using hB_card)

theorem RST35NoSeparation.component_boundary_ncard_ge_three_of_large
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST35NoSeparation G feet)
    {X : Set V}
    (hfeet_X : forall i : Fin 3, feet i ∈ X)
    (C : (G.induce Xᶜ).ConnectedComponent)
    (hlarge : 2 <= (induceComponentSupport (G := G) C).ncard) :
    3 <=
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) X).ncard := by
  classical
  let K : Set V := induceComponentSupport (G := G) C
  let B : Set V := relativeVertexBoundary G K X
  by_contra hnot
  have hB_card : B.ncard <= 2 := by
    have hrel_card :
        (relativeVertexBoundary G (induceComponentSupport (G := G) C) X).ncard <= 2 := by
      omega
    simpa [B, K] using hrel_card
  have hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b) := by
    intro a b ha hbK hbB hab
    by_cases hbX : b ∈ X
    · exact hbB ⟨hbX, a, ha, hab⟩
    · exact hbK
        (induceComponentSupport_mem_of_adj (G := G) C
          (by simpa [K] using ha) (by simpa using hbX) hab)
  have hfeet_not_K : forall i : Fin 3, feet i ∉ K := by
    intro i hfootK
    exact (induceComponentSupport_subset (G := G) C
      (by simpa [K] using hfootK)) (hfeet_X i)
  exact hno.no_blocked_core hclosed hfeet_not_K
    (by simpa [K] using hlarge) (by simpa [B] using hB_card)

theorem IsFourConnected.component_boundary_ncard_ge_four
    [Fintype V]
    (hG : IsFourConnected G)
    {X : Set V}
    (hX_large : 4 <= X.ncard)
    (C : (G.induce Xᶜ).ConnectedComponent) :
    4 <=
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) X).ncard := by
  classical
  let K : Set V := induceComponentSupport (G := G) C
  let B : Set V := relativeVertexBoundary G K X
  by_contra hnot
  have hB_card : B.ncard <= 3 := by
    have hrel_card :
        (relativeVertexBoundary G (induceComponentSupport (G := G) C) X).ncard <= 3 := by
      omega
    simpa [B, K] using hrel_card
  have hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b) := by
    intro a b ha hbK hbB hab
    by_cases hbX : b ∈ X
    · exact hbB ⟨hbX, a, ha, hab⟩
    · exact hbK
        (induceComponentSupport_mem_of_adj (G := G) C
          (by simpa [K] using ha) (by simpa using hbX) hab)
  have hX_not_subset_B : Not (X ⊆ B) := by
    intro hXB
    have hle : X.ncard <= B.ncard := Set.ncard_le_ncard hXB
    omega
  obtain ⟨x, hxX, hxB⟩ :
      Exists fun x : V => x ∈ X ∧ x ∉ B := by
    by_contra hnone
    apply hX_not_subset_B
    intro x hxX
    by_contra hxB
    exact hnone ⟨x, hxX, hxB⟩
  let S : Separation G := Separation.ofCoreAndBoundary K B hclosed
  have hleft_only : (S.left \ S.right).Nonempty := by
    have hxK : x ∉ K := by
      intro hxK
      exact (induceComponentSupport_subset (G := G) C
        (by simpa [K] using hxK)) hxX
    refine ⟨x, ?_, ?_⟩
    · simpa [S, Separation.ofCoreAndBoundary] using hxK
    · intro hxright
      rcases hxright with hxK' | hxB'
      · exact hxK hxK'
      · exact hxB hxB'
  have hright_only : (S.right \ S.left).Nonempty := by
    simpa [S] using
      Separation.ofCoreAndBoundary_right_only_nonempty
        (G := G) K B hclosed (induceComponentSupport_nonempty (G := G) C)
  have hproper : S.Proper := ⟨hleft_only, hright_only⟩
  have horder : S.OrderAtMost 3 := by
    simpa [S] using
      Separation.ofCoreAndBoundary_orderAtMost_of_boundary_ncard_le
        (G := G) K B hclosed hB_card
  exact isFourConnected_no_proper_separation_orderAtMost_three
    (G := G) hG S hproper horder

theorem RST35NoSeparation.delete_feet_component_adjacent_to_all_feet_of_large
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hno : RST35NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (C : (G.induce (Set.range feet)ᶜ).ConnectedComponent)
    (hlarge : 2 <= (induceComponentSupport (G := G) C).ncard) :
    forall i : Fin 3,
      Exists fun u : V =>
        u ∈ induceComponentSupport (G := G) C ∧ G.Adj u (feet i) := by
  intro i
  exact hno.delete_feet_component_adjacent_to_foot_of_large
    hfeet_injective C hlarge i

theorem RST35NoSeparation.leglessTripod_of_two_large_delete_feet_components
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (hno : RST35NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {C D : (G.induce (Set.range feet)ᶜ).ConnectedComponent}
    (hCD : C ≠ D)
    (hC_large : 2 <= (induceComponentSupport (G := G) C).ncard)
    (hD_large : 2 <= (induceComponentSupport (G := G) D).ncard) :
    Nonempty (LeglessTripod G feet) := by
  classical
  let HC : G.Subgraph := induceComponentSubgraph (G := G) C
  let HD : G.Subgraph := induceComponentSubgraph (G := G) D
  have hHC_connected : HC.coe.Connected := by
    exact SimpleGraph.Subgraph.connected_iff'.mp (by
      simpa [HC] using induceComponentSubgraph_connected (G := G) C)
  have hHD_connected : HD.coe.Connected := by
    exact SimpleGraph.Subgraph.connected_iff'.mp (by
      simpa [HD] using induceComponentSubgraph_connected (G := G) D)
  have hCadj :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ induceComponentSupport (G := G) C ∧ G.Adj u (feet i) :=
    hno.delete_feet_component_adjacent_to_all_feet_of_large
      hfeet_injective C hC_large
  have hDadj :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ induceComponentSupport (G := G) D ∧ G.Adj u (feet i) :=
    hno.delete_feet_component_adjacent_to_all_feet_of_large
      hfeet_injective D hD_large
  let xC : Fin 3 -> V := fun i => Classical.choose (hCadj i)
  let xD : Fin 3 -> V := fun i => Classical.choose (hDadj i)
  have hxCH : forall i : Fin 3, xC i ∈ HC.verts := by
    intro i
    rw [show HC.verts = induceComponentSupport (G := G) C by
      simp [HC]]
    exact (Classical.choose_spec (hCadj i)).1
  have hxDH : forall i : Fin 3, xD i ∈ HD.verts := by
    intro i
    rw [show HD.verts = induceComponentSupport (G := G) D by
      simp [HD]]
    exact (Classical.choose_spec (hDadj i)).1
  have hfeet_not_HC : forall i : Fin 3, feet i ∉ HC.verts := by
    intro i hfoot
    have hfootK : feet i ∈ induceComponentSupport (G := G) C := by
      simpa [HC] using hfoot
    have hfoot_compl :
        feet i ∈ (Set.range feet)ᶜ :=
      induceComponentSupport_subset (G := G) C hfootK
    exact hfoot_compl ⟨i, rfl⟩
  have hfeet_not_HD : forall i : Fin 3, feet i ∉ HD.verts := by
    intro i hfoot
    have hfootK : feet i ∈ induceComponentSupport (G := G) D := by
      simpa [HD] using hfoot
    have hfoot_compl :
        feet i ∈ (Set.range feet)ᶜ :=
      induceComponentSupport_subset (G := G) D hfootK
    exact hfoot_compl ⟨i, rfl⟩
  have hadjC : forall i : Fin 3, G.Adj (xC i) (feet i) := by
    intro i
    exact (Classical.choose_spec (hCadj i)).2
  have hadjD : forall i : Fin 3, G.Adj (xD i) (feet i) := by
    intro i
    exact (Classical.choose_spec (hDadj i)).2
  obtain ⟨TC, hTC_subset⟩ :=
    Triad.exists_of_connected_fragment_adjacent_to_feet_subset
      (G := G) (feet := feet) (x := xC) HC hHC_connected
      hfeet_injective hxCH hfeet_not_HC hadjC
  obtain ⟨TD, hTD_subset⟩ :=
    Triad.exists_of_connected_fragment_adjacent_to_feet_subset
      (G := G) (feet := feet) (x := xD) HD hHD_connected
      hfeet_injective hxDH hfeet_not_HD hadjD
  have hTC_subset_K :
      TC.vertexSet ⊆ induceComponentSupport (G := G) C ∪ Set.range feet := by
    intro v hv
    have hvCverts := hTC_subset hv
    have hvHC_or_feet :
        v ∈ HC.verts ∪ Set.range feet :=
      connected_fragment_with_pendant_edges_verts_subset
        (G := G) HC hxCH hadjC hvCverts
    rcases hvHC_or_feet with hvHC | hvfeet
    · exact Or.inl (by simpa [HC] using hvHC)
    · exact Or.inr hvfeet
  have hTD_subset_K :
      TD.vertexSet ⊆ induceComponentSupport (G := G) D ∪ Set.range feet := by
    intro v hv
    have hvDverts := hTD_subset hv
    have hvHD_or_feet :
        v ∈ HD.verts ∪ Set.range feet :=
      connected_fragment_with_pendant_edges_verts_subset
        (G := G) HD hxDH hadjD hvDverts
    rcases hvHD_or_feet with hvHD | hvfeet
    · exact Or.inl (by simpa [HD] using hvHD)
    · exact Or.inr hvfeet
  have hCD_disjoint :
      Disjoint
        (induceComponentSupport (G := G) C)
        (induceComponentSupport (G := G) D) :=
    induceComponentSupport_disjoint_of_ne (G := G) hCD
  have hmeet : TC.vertexSet ∩ TD.vertexSet ⊆ Set.range feet := by
    intro v hv
    by_cases hvfeet : v ∈ Set.range feet
    · exact hvfeet
    · have hvC : v ∈ induceComponentSupport (G := G) C := by
        rcases hTC_subset_K hv.1 with hvC | hvfeet'
        · exact hvC
        · exact False.elim (hvfeet hvfeet')
      have hvD : v ∈ induceComponentSupport (G := G) D := by
        rcases hTD_subset_K hv.2 with hvD | hvfeet'
        · exact hvD
        · exact False.elim (hvfeet hvfeet')
      exact False.elim (Set.disjoint_left.mp hCD_disjoint hvC hvD)
  exact ⟨{
    first := TC
    second := TD
    edge_disjoint :=
      Triad.carrier_edgeSet_disjoint_of_inter_vertexSet_subset_feet
        hfeet_injective TC TD hmeet
    meet_only_at_feet := hmeet }⟩

theorem RST35NoSeparation.large_delete_feet_components_eq_of_no_legless
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (hno : RST35NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (hno_legless : Not (Nonempty (LeglessTripod G feet)))
    {C D : (G.induce (Set.range feet)ᶜ).ConnectedComponent}
    (hC_large : 2 <= (induceComponentSupport (G := G) C).ncard)
    (hD_large : 2 <= (induceComponentSupport (G := G) D).ncard) :
    C = D := by
  by_contra hCD
  exact hno_legless
    (hno.leglessTripod_of_two_large_delete_feet_components
      hfeet_injective hCD hC_large hD_large)

structure RSTDiscDrawing (G : SimpleGraph V) (feet : Fin 3 -> V) : Prop where
  planar : IsPlanar G

def RST34Statement (G : SimpleGraph V) (feet : Fin 3 -> V) : Prop :=
  Nonempty (Tripod G feet) ->
    RST34NoThreeSeparation G feet ->
      Nonempty (LeglessTripod G feet)

def RST34LeglessTripodStatement (G : SimpleGraph V) (feet : Fin 3 -> V) : Prop :=
  Nonempty (Tripod G feet) ->
    RST34NoThreeSeparation G feet ->
      Exists fun H : Tripod G feet => H.Legless

def RST35Statement (G : SimpleGraph V) (feet : Fin 3 -> V) : Prop :=
  RST35NoSeparation G feet ->
    Nonempty (Tripod G feet) ∨ Nonempty (RSTDiscDrawing G feet)

def ThreeBoundaryTripod.toTripod
    {feet : Fin 3 -> V}
    (H : ThreeBoundaryTripod G feet) :
    Tripod G feet where
  left := H.left
  right := H.right
  left_ne_right := H.left_ne_right
  left_not_foot := H.left_not_boundary
  right_not_foot := H.right_not_boundary
  rim := H.rim
  rim_isPath := H.rim_isPath
  attach := H.attach
  attach_mem_rim := H.attach_mem_rim
  rim_internals_disjoint := H.rim_internals_disjoint
  leg := H.leg
  leg_isPath := H.leg_isPath
  legs_disjoint := H.legs_disjoint
  leg_meets_rims_only_at_attach := H.leg_meets_rims_only_at_attach

theorem RST35Statement.of_tripod
    {feet : Fin 3 -> V}
    (htripod : Nonempty (Tripod G feet)) :
    RST35Statement G feet := by
  intro _hno
  exact Or.inl htripod

theorem RSTDiscDrawing.of_threeBoundaryRural
    {feet : Fin 3 -> V}
    (R : ThreeBoundaryRural G feet) :
    RSTDiscDrawing G feet where
  planar := R.isPlanar

/-- RST (3.5) from the general-society GM IX `(2.4)` endpoint in the
four-connected setting used by the dominating-four-colour prerequisites. -/
theorem RST35Statement.of_GMIX24Statement_fourConnected
    [Fintype V]
    [DecidableEq V]
    (hGM : GeneralSociety.GMIX24Statement (V := V))
    (hG : IsFourConnected G)
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet) :
    RST35Statement G feet := by
  intro _hno
  rcases
      generalSocietyOfThreeBoundary_rural_or_tripod_of_GMIX24Statement
        (G := G) hGM hfeet_injective
        (generalSocietyOfThreeBoundary_threeConnected_of_fourConnected
          (G := G) hfeet_injective hG) with htripod | hrural
  · rcases htripod with ⟨H⟩
    exact Or.inl ⟨H.toTripod⟩
  · rcases hrural with ⟨R⟩
    exact Or.inr ⟨RSTDiscDrawing.of_threeBoundaryRural R⟩

theorem RST34LeglessTripodStatement.of_tripod_legless
    {feet : Fin 3 -> V}
    (hlegless : Exists fun H : Tripod G feet => H.Legless) :
    RST34LeglessTripodStatement G feet := by
  intro _htripod _hno
  exact hlegless

theorem RST34LeglessTripodStatement.of_leglessTripod
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hlegless : Nonempty (LeglessTripod G feet)) :
    RST34LeglessTripodStatement G feet :=
  RST34LeglessTripodStatement.of_tripod_legless
    (G := G)
    (LeglessTripod.exists_tripod_legless_of_nonempty
      hfeet_injective hlegless)

theorem RST34LeglessTripodStatement.of_minimal_legLength_zero
    {feet : Fin 3 -> V}
    (hzero :
      forall H : Tripod G feet, H.LegLengthMinimal -> H.legLengthSum = 0) :
    RST34LeglessTripodStatement G feet := by
  intro htripod _hno
  obtain ⟨H, hmin⟩ := Tripod.exists_legLengthMinimal (G := G) htripod
  exact ⟨H, H.legless_of_legLengthSum_eq_zero (hzero H hmin)⟩

theorem RST34LeglessTripodStatement.of_minimal_legLength_zero_of_noThree
    {feet : Fin 3 -> V}
    (hzero :
      forall H : Tripod G feet,
        H.LegLengthMinimal -> RST34NoThreeSeparation G feet ->
          H.legLengthSum = 0) :
    RST34LeglessTripodStatement G feet := by
  intro htripod hno
  obtain ⟨H, hmin⟩ := Tripod.exists_legLengthMinimal (G := G) htripod
  exact ⟨H, H.legless_of_legLengthSum_eq_zero (hzero H hmin hno)⟩

theorem RST34LeglessTripodStatement.of_positive_leg_rerouting
    {feet : Fin 3 -> V}
    (hreroute :
      forall H : Tripod G feet,
        H.LegLengthMinimal ->
          RST34NoThreeSeparation G feet ->
            forall i : Fin 3,
              0 < (H.leg i).length ->
                Exists fun H' : Tripod G feet =>
                  H'.legLengthSum < H.legLengthSum) :
    RST34LeglessTripodStatement G feet :=
  RST34LeglessTripodStatement.of_minimal_legLength_zero_of_noThree
    (G := G)
    (by
      intro H hmin hno
      exact H.legLengthSum_eq_zero_of_minimal_and_positive_leg_rerouting
        hmin (hreroute H hmin hno))

theorem RST34LeglessTripodStatement.of_trimPositiveLeg_path_cases
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hclean :
      forall H : Tripod G feet,
        H.LegLengthMinimal ->
          RST34NoThreeSeparation G feet ->
            forall (i : Fin 3) (hpos : 0 < (H.leg i).length),
              (Exists fun x : V =>
                x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
                    (H.trimPositiveLeg i hpos).legVertexSet ∧
                  Exists fun p : G.Walk x (feet i) =>
                    forall v : V, v ∈ p.support ->
                      v ∉ (H.trimPositiveLeg i hpos).legVertexSet) ->
                Exists fun H' : Tripod G feet =>
                  H'.legLengthSum < H.legLengthSum)
    (hshort_suffix :
      forall H : Tripod G feet,
        H.LegLengthMinimal ->
          RST34NoThreeSeparation G feet ->
            forall (i : Fin 3) (hpos : 0 < (H.leg i).length),
              (Exists fun j : Fin 3 =>
                Exists fun y : V =>
                  Exists fun hy : y ∈ ((H.trimPositiveLeg i hpos).leg j).support =>
                    (((H.trimPositiveLeg i hpos).leg j).dropUntil y hy).length <
                      ((H.trimPositiveLeg i hpos).leg j).length) ->
                Exists fun H' : Tripod G feet =>
                  H'.legLengthSum < H.legLengthSum) :
    RST34LeglessTripodStatement G feet :=
  RST34LeglessTripodStatement.of_positive_leg_rerouting
    (G := G)
    (by
      intro H hmin hno i hpos
      rcases hno.trimPositiveLeg_path_to_old_foot_or_shorter_leg_suffix
          hfeet_injective H hpos with hpath | hsuffix
      · exact hclean H hmin hno i hpos hpath
      · exact hshort_suffix H hmin hno i hpos hsuffix)

theorem RST34LeglessTripodStatement.of_trimPositiveLeg_shorter_suffix
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hshort_suffix :
      forall H : Tripod G feet,
        H.LegLengthMinimal ->
          RST34NoThreeSeparation G feet ->
            forall (i : Fin 3) (hpos : 0 < (H.leg i).length),
              (Exists fun j : Fin 3 =>
                Exists fun y : V =>
                  Exists fun hy : y ∈ ((H.trimPositiveLeg i hpos).leg j).support =>
                    (((H.trimPositiveLeg i hpos).leg j).dropUntil y hy).length <
                      ((H.trimPositiveLeg i hpos).leg j).length) ->
                Exists fun H' : Tripod G feet =>
                  H'.legLengthSum < H.legLengthSum) :
    RST34LeglessTripodStatement G feet :=
  RST34LeglessTripodStatement.of_trimPositiveLeg_path_cases
    (G := G) hfeet_injective
    (by
      intro H _hmin _hno i hpos hpath
      exact H.exists_legLengthSum_lt_of_trim_clean_path_to_old_foot hpos hpath)
    hshort_suffix

theorem RST34LeglessTripodStatement.of_trimPositiveLeg_full_path_cases
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hclean :
      forall H : Tripod G feet,
        H.LegLengthMinimal ->
          RST34NoThreeSeparation G feet ->
            forall (i : Fin 3) (hpos : 0 < (H.leg i).length),
              (Exists fun x : V =>
                x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
                    (H.trimPositiveLeg i hpos).legVertexSet ∧
                  Exists fun p : G.Walk x (feet i) =>
                    forall v : V, v ∈ p.support ->
                      v ∉ (H.trimPositiveLeg i hpos).legVertexSet) ->
                Exists fun H' : Tripod G feet =>
                  H'.legLengthSum < H.legLengthSum)
    (hhit :
      forall H : Tripod G feet,
        H.LegLengthMinimal ->
          RST34NoThreeSeparation G feet ->
            forall (i : Fin 3) (hpos : 0 < (H.leg i).length),
              (Exists fun x : V =>
                x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
                    (H.trimPositiveLeg i hpos).legVertexSet ∧
                  Exists fun y : V =>
                    y ∈ (H.trimPositiveLeg i hpos).legVertexSet ∧
                      Exists fun p : G.Walk x y =>
                        ((forall v : V, v ∈ p.support ->
                            v ∈ (H.trimPositiveLeg i hpos).legVertexSet -> v = y) ∧
                          forall v : V, v ∈ p.support ->
                            v ∉ Set.range (H.trimPositiveLeg i hpos).attach) ∧
                            Exists fun j : Fin 3 =>
                              Exists fun hy :
                                y ∈ ((H.trimPositiveLeg i hpos).leg j).support =>
                                  (((H.trimPositiveLeg i hpos).leg j).dropUntil y hy).length <
                                    ((H.trimPositiveLeg i hpos).leg j).length) ->
                Exists fun H' : Tripod G feet =>
                  H'.legLengthSum < H.legLengthSum) :
    RST34LeglessTripodStatement G feet :=
  RST34LeglessTripodStatement.of_positive_leg_rerouting
    (G := G)
    (by
      intro H hmin hno i hpos
      rcases hno.trimPositiveLeg_path_to_old_foot_or_leg_hit_shorter_suffix
          hfeet_injective H hpos with hpath | hleg_hit
      · exact hclean H hmin hno i hpos hpath
      · exact hhit H hmin hno i hpos hleg_hit)

theorem RST34LeglessTripodStatement.of_trimPositiveLeg_full_rerouting
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet) :
    RST34LeglessTripodStatement G feet :=
  RST34LeglessTripodStatement.of_positive_leg_rerouting
    (G := G)
    (by
      intro H _hmin hno i hpos
      rcases hno.trimPositiveLeg_path_to_old_foot_or_leg_hit_old_suffix_with_first
          hfeet_injective H hpos with hpath | hleg_hit
      · exact H.exists_legLengthSum_lt_of_trim_clean_path_to_old_foot
          hpos hpath
      · rcases hleg_hit with
          ⟨x, hx, y, _hy_trim_leg, p, hp, hfirst_leg, hfirst_Z,
            hp_attach, j, hyj, hlt⟩
        obtain ⟨z, hz, hzdata, hq_path, hq_first_leg, hq_first_Z,
          hq_attach, hq_last_rim, _hq_subset⟩ :=
          H.trimPositiveLeg_leg_hit_suffix_from_last_rim
            hpos hx p hp hfirst_leg hfirst_Z hp_attach
        let q : G.Walk z y := (p.reverse.takeUntil z hz).reverse
        exact H.exists_legLengthSum_lt_of_normalized_trim_leg_hit
          hpos hzdata hyj q hq_path hq_first_leg hq_first_Z
          hq_attach hq_last_rim hlt)

theorem RSTDiscDrawing.isPlanar
    {feet : Fin 3 -> V}
    (D : RSTDiscDrawing G feet) :
    IsPlanar G :=
  D.planar

theorem RST35Statement.tripod_or_planar
    {feet : Fin 3 -> V}
    (h35 : RST35Statement G feet)
    (hno : RST35NoSeparation G feet) :
    Nonempty (Tripod G feet) ∨ IsPlanar G := by
  rcases h35 hno with htripod | hdisc
  · exact Or.inl htripod
  · rcases hdisc with ⟨D⟩
    exact Or.inr D.isPlanar

theorem RST35Statement.tripod_of_nonplanar
    {feet : Fin 3 -> V}
    (h35 : RST35Statement G feet)
    (hno : RST35NoSeparation G feet)
    (hnonplanar : Not (IsPlanar G)) :
    Nonempty (Tripod G feet) := by
  rcases h35.tripod_or_planar hno with htripod | hplanar
  · exact htripod
  · exact False.elim (hnonplanar hplanar)

theorem RST34LeglessTripodStatement.to_rst34Statement
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (h34 : RST34LeglessTripodStatement G feet)
    (hfeet_injective : Function.Injective feet) :
    RST34Statement G feet := by
  intro htripod hno34
  rcases h34 htripod hno34 with ⟨H, hH⟩
  exact ⟨H.toLeglessTripod hH hfeet_injective⟩

theorem RST34Statement.of_trimPositiveLeg_full_rerouting
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet) :
    RST34Statement G feet :=
  (RST34LeglessTripodStatement.of_trimPositiveLeg_full_rerouting
    (G := G) hfeet_injective).to_rst34Statement hfeet_injective

theorem RST34Statement.legless_tripod_of_rst35
    {feet : Fin 3 -> V}
    (h34 : RST34Statement G feet)
    (h35 : RST35Statement G feet)
    (hno34 : RST34NoThreeSeparation G feet)
    (hno35 : RST35NoSeparation G feet)
    (hnonplanar : Not (IsPlanar G)) :
    Nonempty (LeglessTripod G feet) := by
  exact h34 (h35.tripod_of_nonplanar hno35 hnonplanar) hno34

theorem IsFourConnected.rst31_noSeparation
    [Fintype V]
    (hG : IsFourConnected G)
    (feet : Fin 3 -> V) :
    RST31NoSeparation G feet := by
  intro S _hfeet hleft_card hright_only horder
  have hleft_only : (S.left \ S.right).Nonempty := by
    by_contra hnone
    have hleft_subset_right : S.left ⊆ S.right := by
      intro v hvleft
      by_contra hvright
      exact hnone ⟨v, hvleft, hvright⟩
    have hleft_subset_separator : S.left ⊆ S.separator := by
      intro v hvleft
      exact ⟨hvleft, hleft_subset_right hvleft⟩
    have hleft_le_sep : S.left.ncard <= S.separator.ncard :=
      Set.ncard_le_ncard hleft_subset_separator
    have hsep_le : S.separator.ncard <= 3 :=
      S.separator_ncard_le_of_orderAtMost horder
    omega
  exact isFourConnected_no_proper_separation_orderAtMost_three
    hG S ⟨hleft_only, hright_only⟩ horder

theorem IsFourConnected.rst34_noSeparation
    [Fintype V]
    (hG : IsFourConnected G)
    (feet : Fin 3 -> V) :
    RST34NoSeparation G feet := by
  intro S _hfeet hleft_card hright_card horder
  have hright_only : (S.right \ S.left).Nonempty := by
    exact (Set.ncard_pos (s := S.right \ S.left)).mp (by omega)
  have hleft_only : (S.left \ S.right).Nonempty := by
    by_contra hnone
    have hleft_subset_right : S.left ⊆ S.right := by
      intro v hvleft
      by_contra hvright
      exact hnone ⟨v, hvleft, hvright⟩
    have hleft_subset_separator : S.left ⊆ S.separator := by
      intro v hvleft
      exact ⟨hvleft, hleft_subset_right hvleft⟩
    have hleft_le_sep : S.left.ncard <= S.separator.ncard :=
      Set.ncard_le_ncard hleft_subset_separator
    have hsep_le : S.separator.ncard <= 3 :=
      S.separator_ncard_le_of_orderAtMost horder
    omega
  exact isFourConnected_no_proper_separation_orderAtMost_three
    hG S ⟨hleft_only, hright_only⟩ horder

theorem IsFourConnected.rst34_noThreeSeparation
    [Fintype V]
    (hG : IsFourConnected G)
    (feet : Fin 3 -> V) :
    RST34NoThreeSeparation G feet :=
  (hG.rst34_noSeparation feet).no_three

theorem IsThreeConnected.rst35_noSeparation
    [Fintype V]
    (hG : IsThreeConnected G)
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet) :
    RST35NoSeparation G feet := by
  intro S hfeet hright_card horder
  have hright_only : (S.right \ S.left).Nonempty := by
    exact (Set.ncard_pos (s := S.right \ S.left)).mp (by omega)
  have hleft_only : (S.left \ S.right).Nonempty := by
    by_contra hnone
    have hleft_subset_right : S.left ⊆ S.right := by
      intro v hvleft
      by_contra hvright
      exact hnone ⟨v, hvleft, hvright⟩
    have hrange_subset_separator : Set.range feet ⊆ S.separator := by
      rintro v ⟨i, rfl⟩
      exact ⟨hfeet i, hleft_subset_right (hfeet i)⟩
    have hrange_le_sep : (Set.range feet).ncard <= S.separator.ncard :=
      Set.ncard_le_ncard hrange_subset_separator
    have hrange_card : (Set.range feet).ncard = 3 :=
      ncard_range_fin3_of_injective hfeet_injective
    have hsep_le : S.separator.ncard <= 2 :=
      S.separator_ncard_le_of_orderAtMost horder
    omega
  exact isKConnected_no_proper_separation_orderAtMost
    (G := G) (k := 2) hG S ⟨hleft_only, hright_only⟩ horder

theorem IsFourConnected.rst35_noSeparation
    [Fintype V]
    (hG : IsFourConnected G)
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet) :
    RST35NoSeparation G feet :=
  IsThreeConnected.rst35_noSeparation
    (G := G)
    (IsKConnected.mono (G := G) (k := 3) (l := 4) (by decide) hG)
    hfeet_injective

theorem RST34Statement.legless_tripod_of_rst35_fourConnected_nonplanar
    [Fintype V]
    {feet : Fin 3 -> V}
    (h34 : RST34Statement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hnonplanar : Not (IsPlanar G)) :
    Nonempty (LeglessTripod G feet) := by
  exact h34.legless_tripod_of_rst35 h35
    (hG.rst34_noThreeSeparation feet)
    (hG.rst35_noSeparation hfeet_injective)
    hnonplanar

theorem RST34Statement.tripod_legless_of_rst35_fourConnected_nonplanar
    [Fintype V]
    {feet : Fin 3 -> V}
    (h34 : RST34Statement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hnonplanar : Not (IsPlanar G)) :
    Exists fun H : Tripod G feet => H.Legless :=
  LeglessTripod.exists_tripod_legless_of_nonempty hfeet_injective
    (h34.legless_tripod_of_rst35_fourConnected_nonplanar
      h35 hG hfeet_injective hnonplanar)

theorem RST34LeglessTripodStatement.tripod_legless_of_rst35_fourConnected_nonplanar
    [Fintype V]
    {feet : Fin 3 -> V}
    (h34 : RST34LeglessTripodStatement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hnonplanar : Not (IsPlanar G)) :
    Exists fun H : Tripod G feet => H.Legless := by
  exact h34
    (h35.tripod_of_nonplanar
      (hG.rst35_noSeparation hfeet_injective) hnonplanar)
    (hG.rst34_noThreeSeparation feet)

theorem RST34LeglessTripodStatement.legless_tripod_of_rst35_fourConnected_nonplanar
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (h34 : RST34LeglessTripodStatement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hnonplanar : Not (IsPlanar G)) :
    Nonempty (LeglessTripod G feet) := by
  rcases h34.tripod_legless_of_rst35_fourConnected_nonplanar
      h35 hG hfeet_injective hnonplanar with ⟨H, hH⟩
  exact ⟨H.toLeglessTripod hH hfeet_injective⟩

end Schematic.Math.GraphTheory
