import DominatingFourColour.Prerequisites.TripodMinimal.LeglessTripods

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

def RST31NoSeparation (G : SimpleGraph V) (feet : Fin 3 -> V) : Prop :=
  forall S : Separation G,
    (forall i : Fin 3, feet i ∈ S.left) ->
      4 <= S.left.ncard ->
        (S.right \ S.left).Nonempty ->
          S.OrderAtMost 3 ->
            False

def RST34NoSeparation (G : SimpleGraph V) (feet : Fin 3 -> V) : Prop :=
  forall S : Separation G,
    (forall i : Fin 3, feet i ∈ S.left) ->
      4 <= S.left.ncard ->
        2 <= (S.right \ S.left).ncard ->
          S.OrderAtMost 3 ->
            False

def RST34NoThreeSeparation (G : SimpleGraph V) (feet : Fin 3 -> V) : Prop :=
  forall S : Separation G,
    (forall i : Fin 3, feet i ∈ S.left) ->
      4 <= S.left.ncard ->
        2 <= (S.right \ S.left).ncard ->
          S.OrderEq 3 ->
            False

def RST33NoThreeSeparation (G : SimpleGraph V) (Z : Set V) : Prop :=
  forall S : Separation G,
    Z ⊆ S.left ->
      2 <= (S.right \ S.left).ncard ->
        S.OrderEq 3 ->
          False

def Tripod.RST33PathToZ
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (Z : Set V) : Prop :=
  AvoidingSetPath G (H.rimVertexSet \ H.legVertexSet) Z H.legVertexSet

theorem Tripod.RST33PathToZ.exists_path_to_extra_Z
    {feet : Fin 3 -> V}
    {H : Tripod G feet}
    {Z : Set V}
    (hpath : H.RST33PathToZ Z)
    (hno_other : H.NoOtherVertexIn Z) :
    Exists fun x : V =>
      x ∈ H.rimVertexSet \ H.legVertexSet ∧
        Exists fun z : V =>
          z ∈ Z ∧ z ∉ Set.range feet ∧ z ∉ H.vertexSet ∧
            Exists fun p : G.Walk x z =>
              forall v : V, v ∈ p.support -> v ∉ H.legVertexSet := by
  rcases hpath with ⟨x, hx, z, hzZ, p, hp⟩
  have hz_not_leg : z ∉ H.legVertexSet :=
    hp z p.end_mem_support
  have hz_not_feet : z ∉ Set.range feet := by
    rintro ⟨i, rfl⟩
    exact hz_not_leg (H.foot_mem_legVertexSet i)
  have hz_not_vertex : z ∉ H.vertexSet := by
    intro hzH
    exact hz_not_feet (hno_other ⟨hzH, hzZ⟩)
  exact ⟨x, hx, z, hzZ, hz_not_feet, hz_not_vertex, p, hp⟩

theorem Tripod.RST33PathToZ.exists_path_to_old_foot_of_trimPositiveLeg
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    (hpath :
      (H.trimPositiveLeg i hpos).RST33PathToZ
        (insert (feet i) (Set.range (H.feetWithPenultimate i)))) :
    Exists fun x : V =>
      x ∈ (H.trimPositiveLeg i hpos).rimVertexSet \
        (H.trimPositiveLeg i hpos).legVertexSet ∧
        Exists fun p : G.Walk x (feet i) =>
          forall v : V, v ∈ p.support ->
            v ∉ (H.trimPositiveLeg i hpos).legVertexSet := by
  rcases hpath.exists_path_to_extra_Z
      (H.trimPositiveLeg_noOtherVertexIn_oldFoot_insert_newFeet i hpos) with
    ⟨x, hx, z, hzZ, hz_not_new_feet, _hz_not_vertex, p, hp⟩
  have hz_old : z = feet i := by
    simp only [Set.mem_insert_iff] at hzZ
    rcases hzZ with hz_old | hz_new
    · exact hz_old
    · exact False.elim (hz_not_new_feet hz_new)
  refine ⟨x, hx, p.copy rfl hz_old, ?_⟩
  intro v hv
  exact hp v (by simpa using hv)

theorem Tripod.rst33PathToZ_or_path_to_legVertexSet_of_avoiding_attach_path
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {H : Tripod G feet}
    {Z : Set V}
    (hpath : AvoidingSetPath G H.rimVertexSet Z (Set.range H.attach)) :
    H.RST33PathToZ Z ∨
      Exists fun x : V =>
        x ∈ H.rimVertexSet \ H.legVertexSet ∧
          Exists fun y : V =>
            y ∈ H.legVertexSet ∧
              Exists fun p : G.Walk x y =>
                (forall v : V, v ∈ p.support -> v ∈ H.legVertexSet -> v = y) ∧
                  forall v : V, v ∈ p.support -> v ∉ Set.range H.attach := by
  classical
  rcases hpath with ⟨x, hxrim, z, hzZ, p, hp_attach⟩
  let q : G.Walk x z := p.toPath
  have hq_path : q.IsPath := p.toPath.property
  have hq_attach : forall v : V, v ∈ q.support -> v ∉ Set.range H.attach := by
    intro v hv
    exact hp_attach v (SimpleGraph.Walk.support_toPath_subset p hv)
  have hx_not_attach : x ∉ Set.range H.attach :=
    hq_attach x q.start_mem_support
  have hx_not_leg : x ∉ H.legVertexSet :=
    H.not_mem_legVertexSet_of_mem_rimVertexSet_of_not_attach hxrim hx_not_attach
  let A : Set V := Z ∪ H.legVertexSet
  have hzA : z ∈ A := Or.inl hzZ
  obtain ⟨y, hy_support, hyA, hfirst⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem (G := G) hq_path A hzA
  by_cases hyleg : y ∈ H.legVertexSet
  · right
    exact ⟨x, ⟨hxrim, hx_not_leg⟩, y, hyleg, q.takeUntil y hy_support,
      by
        constructor
        · intro v hv hvleg
          exact hfirst v hv (Or.inr hvleg)
        · intro v hv
          exact hq_attach v
            (SimpleGraph.Walk.support_takeUntil_subset q hy_support hv)⟩
  · left
    have hyZ : y ∈ Z := by
      rcases hyA with hyZ | hyleg'
      · exact hyZ
      · exact False.elim (hyleg hyleg')
    refine ⟨x, ⟨hxrim, hx_not_leg⟩, y, hyZ,
      q.takeUntil y hy_support, ?_⟩
    intro v hv hvleg
    have hv_eq : v = y := hfirst v hv (Or.inr hvleg)
    exact hyleg (by simpa [hv_eq] using hvleg)

theorem Tripod.rst33PathToZ_or_path_to_legVertexSet_of_avoiding_attach_path_with_first
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {H : Tripod G feet}
    {Z : Set V}
    (hpath : AvoidingSetPath G H.rimVertexSet Z (Set.range H.attach)) :
    H.RST33PathToZ Z ∨
      Exists fun x : V =>
        x ∈ H.rimVertexSet \ H.legVertexSet ∧
          Exists fun y : V =>
            y ∈ H.legVertexSet ∧
              Exists fun p : G.Walk x y =>
                p.IsPath ∧
                  (forall v : V, v ∈ p.support -> v ∈ H.legVertexSet -> v = y) ∧
                    (forall v : V, v ∈ p.support -> v ∈ Z -> v = y) ∧
                      forall v : V, v ∈ p.support -> v ∉ Set.range H.attach := by
  classical
  rcases hpath with ⟨x, hxrim, z, hzZ, p, hp_attach⟩
  let q : G.Walk x z := p.toPath
  have hq_path : q.IsPath := p.toPath.property
  have hq_attach : forall v : V, v ∈ q.support -> v ∉ Set.range H.attach := by
    intro v hv
    exact hp_attach v (SimpleGraph.Walk.support_toPath_subset p hv)
  have hx_not_attach : x ∉ Set.range H.attach :=
    hq_attach x q.start_mem_support
  have hx_not_leg : x ∉ H.legVertexSet :=
    H.not_mem_legVertexSet_of_mem_rimVertexSet_of_not_attach hxrim hx_not_attach
  let A : Set V := Z ∪ H.legVertexSet
  have hzA : z ∈ A := Or.inl hzZ
  obtain ⟨y, hy_support, hyA, hfirst⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem (G := G) hq_path A hzA
  by_cases hyleg : y ∈ H.legVertexSet
  · right
    refine ⟨x, ⟨hxrim, hx_not_leg⟩, y, hyleg,
      q.takeUntil y hy_support, ?_, ?_, ?_, ?_⟩
    · exact hq_path.takeUntil hy_support
    · intro v hv hvleg
      exact hfirst v hv (Or.inr hvleg)
    · intro v hv hvZ
      exact hfirst v hv (Or.inl hvZ)
    · intro v hv
      exact hq_attach v
        (SimpleGraph.Walk.support_takeUntil_subset q hy_support hv)
  · left
    have hyZ : y ∈ Z := by
      rcases hyA with hyZ | hyleg'
      · exact hyZ
      · exact False.elim (hyleg hyleg')
    refine ⟨x, ⟨hxrim, hx_not_leg⟩, y, hyZ,
      q.takeUntil y hy_support, ?_⟩
    intro v hv hvleg
    have hv_eq : v = y := hfirst v hv (Or.inr hvleg)
    exact hyleg (by simpa [hv_eq] using hvleg)

theorem RST34NoThreeSeparation.to_rst33NoThreeSeparation
    [Fintype V]
    {feet : Fin 3 -> V}
    {Z : Set V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (hfeetZ : forall i : Fin 3, feet i ∈ Z)
    {z : V}
    (hzZ : z ∈ Z)
    (hz_not_feet : z ∉ Set.range feet) :
    RST33NoThreeSeparation G Z := by
  classical
  intro S hZ_left hright_card horder
  have hfeet_left : forall i : Fin 3, feet i ∈ S.left := fun i =>
    hZ_left (hfeetZ i)
  have h01 : feet 0 ≠ feet 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (hfeet_injective h)
  have h02 : feet 0 ≠ feet 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (hfeet_injective h)
  have h12 : feet 1 ≠ feet 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (hfeet_injective h)
  have h0z : feet 0 ≠ z := by
    intro h
    exact hz_not_feet ⟨0, h⟩
  have h1z : feet 1 ≠ z := by
    intro h
    exact hz_not_feet ⟨1, h⟩
  have h2z : feet 2 ≠ z := by
    intro h
    exact hz_not_feet ⟨2, h⟩
  let Q : Set V := {feet 0, feet 1, feet 2, z}
  have hQ_card : Q.ncard = 4 := by
    rw [Set.ncard_eq_four]
    exact ⟨feet 0, feet 1, feet 2, z,
      h01, h02, h0z, h12, h1z, h2z, rfl⟩
  have hQ_subset_left : Q ⊆ S.left := by
    intro v hv
    simp only [Q, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hfeet_left 0
    · exact hfeet_left 1
    · exact hfeet_left 2
    · exact hZ_left hzZ
  have hleft_card : 4 <= S.left.ncard := by
    have hle := Set.ncard_le_ncard hQ_subset_left
    omega
  exact hno S hfeet_left hleft_card hright_card horder

theorem RST34NoThreeSeparation.to_rst33NoThreeSeparation_trimPositiveLeg
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    RST33NoThreeSeparation G
      (insert (feet i) (Set.range (H.feetWithPenultimate i))) := by
  classical
  refine hno.to_rst33NoThreeSeparation hfeet_injective ?_
    (z := (H.feetWithPenultimate i) i) ?_ ?_
  · intro j
    by_cases hji : j = i
    · subst j
      exact Set.mem_insert (feet i) (Set.range (H.feetWithPenultimate i))
    · exact Set.mem_insert_of_mem (feet i)
        ⟨j, by simp [H.feetWithPenultimate_apply_ne hji]⟩
  · exact Set.mem_insert_of_mem (feet i) ⟨i, rfl⟩
  · simpa using H.leg_penultimate_not_mem_feet_of_positive hpos

theorem RST34NoThreeSeparation.trimPositiveLeg_rst33_inputs
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    let H' : Tripod G (H.feetWithPenultimate i) :=
      H.trimPositiveLeg i hpos
    let Z : Set V := insert (feet i) (Set.range (H.feetWithPenultimate i))
    RST33NoThreeSeparation G Z ∧
      H'.NoOtherVertexIn Z ∧
        (forall j : Fin 3, (H.feetWithPenultimate i) j ∈ Z) ∧
          feet i ∈ Z ∧ Z.ncard = 4 := by
  classical
  dsimp
  exact ⟨
    hno.to_rst33NoThreeSeparation_trimPositiveLeg
      hfeet_injective H hpos,
    H.trimPositiveLeg_noOtherVertexIn_oldFoot_insert_newFeet i hpos,
    H.trimPositiveLeg_newFeet_subset_oldFoot_insert_newFeet i,
    H.trimPositiveLeg_oldFoot_mem_oldFoot_insert_newFeet i,
    H.oldFoot_insert_feetWithPenultimate_range_ncard_eq_four
      hfeet_injective hpos⟩

theorem RST33NoThreeSeparation.attachComponentOf_ncard_le_one
    {feet : Fin 3 -> V}
    {Z : Set V}
    (hno : RST33NoThreeSeparation G Z)
    (H : Tripod G feet)
    {x : V}
    (hx_attach : x ∉ Set.range H.attach)
    (hZ_notK : Z ⊆ (H.attachComponentOf hx_attach)ᶜ) :
    (H.attachComponentOf hx_attach).ncard <= 1 := by
  classical
  by_contra hlarge_not
  have hK_card : 2 <= (H.attachComponentOf hx_attach).ncard := by omega
  let K : Set V := H.attachComponentOf hx_attach
  let B : Set V := Set.range H.attach
  let S : Separation G := Separation.ofCoreAndBoundary K B (by
    intro a b ha hb hbB
    exact H.attachComponentOf_closed hx_attach ha hb (by simpa [B, K] using hbB))
  have hZ_left : Z ⊆ S.left := by
    intro z hz
    exact hZ_notK hz
  have hright_eq : S.right \ S.left = K := by
    ext v
    constructor
    · rintro ⟨hv_right, hv_not_left⟩
      rcases hv_right with hvK | hvB
      · exact hvK
      · exfalso
        exact hv_not_left (by
          intro hvK
          exact H.attachComponentOf_subset_attach_compl hx_attach hvK
            (by simpa [B] using hvB))
    · intro hvK
      exact ⟨Or.inl hvK, fun hv_notK => hv_notK hvK⟩
  have hright_card : 2 <= (S.right \ S.left).ncard := by
    simpa [hright_eq, K] using hK_card
  have hsep : S.separator = Set.range H.attach := by
    simpa [S, K, B] using
      Separation.ofCoreAndBoundary_separator_eq_boundary_of_core_subset_compl
        (G := G) K B (by
          intro a b ha hb hbB
          exact H.attachComponentOf_closed hx_attach ha hb
            (by simpa [B, K] using hbB))
        (by
          intro v hvK hvB
          exact H.attachComponentOf_subset_attach_compl hx_attach hvK
            (by simpa [B] using hvB))
  exact hno S hZ_left hright_card (H.attach_range_orderEq_three S hsep)

theorem RST33NoThreeSeparation.not_two_vertices_in_attachComponentOf
    [Fintype V]
    {feet : Fin 3 -> V}
    {Z : Set V}
    (hno : RST33NoThreeSeparation G Z)
    (H : Tripod G feet)
    {x : V}
    (hx_attach : x ∉ Set.range H.attach)
    (hZ_notK : Z ⊆ (H.attachComponentOf hx_attach)ᶜ)
    {y : V}
    (hyK : y ∈ H.attachComponentOf hx_attach)
    (hxy : x ≠ y) :
    False := by
  have hle :
      (H.attachComponentOf hx_attach).ncard <= 1 :=
    hno.attachComponentOf_ncard_le_one H hx_attach hZ_notK
  have hpair_subset : ({x, y} : Set V) ⊆ H.attachComponentOf hx_attach := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact H.mem_attachComponentOf_self hx_attach
    · exact hyK
  have hpair_card : ({x, y} : Set V).ncard = 2 :=
    Set.ncard_pair hxy
  have htwo : 2 <= (H.attachComponentOf hx_attach).ncard := by
    have hsub := Set.ncard_le_ncard hpair_subset
    omega
  omega

theorem RST33NoThreeSeparation.avoidingSetPath_of_pair_in_set
    [Fintype V]
    {feet : Fin 3 -> V}
    {Z X : Set V}
    (hno : RST33NoThreeSeparation G Z)
    (H : Tripod G feet)
    {x y : V}
    (hxX : x ∈ X)
    (hyX : y ∈ X)
    (hx_attach : x ∉ Set.range H.attach)
    (hy_attach : y ∉ Set.range H.attach)
    (hxy : x ≠ y) :
    AvoidingSetPath G X Z (Set.range H.attach) := by
  classical
  by_contra hno_path
  let K : Set V := reachableFromSetOutside G X (Set.range H.attach)
  let B : Set V := Set.range H.attach
  have hK_attach_compl : K ⊆ Bᶜ := by
    intro v hvK
    exact reachableFromSetOutside_subset_compl (G := G) (X := X)
      (F := Set.range H.attach) hvK
  have hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B ->
        Not (G.Adj a b) := by
    intro a b ha hb hbB
    exact reachableFromSetOutside_closed (G := G) (X := X)
      (F := Set.range H.attach) ha hb (by simpa [B] using hbB)
  let S : Separation G := Separation.ofCoreAndBoundary K B hclosed
  have hZ_notK : Z ⊆ Kᶜ := by
    have hdis :
        Disjoint (reachableFromSetOutside G X (Set.range H.attach)) Z :=
      reachableFromSetOutside_disjoint_of_no_avoidingSetPath
        (G := G) hno_path
    rw [Set.disjoint_left] at hdis
    intro z hzZ hzK
    exact hdis (by simpa [K] using hzK) hzZ
  have hZ_left : Z ⊆ S.left := by
    intro z hz
    exact hZ_notK hz
  have hright_eq : S.right \ S.left = K := by
    ext v
    constructor
    · rintro ⟨hv_right, hv_not_left⟩
      rcases hv_right with hvK | hvB
      · exact hvK
      · exfalso
        exact hv_not_left (by
          intro hvK
          exact hK_attach_compl hvK (by simpa [B] using hvB))
    · intro hvK
      exact ⟨Or.inl hvK, fun hv_notK => hv_notK hvK⟩
  have hxK : x ∈ K := by
    exact mem_reachableFromSetOutside_self (G := G) hxX hx_attach
  have hyK : y ∈ K := by
    exact mem_reachableFromSetOutside_self (G := G) hyX hy_attach
  have hpair_subset : ({x, y} : Set V) ⊆ K := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hxK
    · exact hyK
  have hpair_card : ({x, y} : Set V).ncard = 2 :=
    Set.ncard_pair hxy
  have hK_card : 2 <= K.ncard := by
    have hsub := Set.ncard_le_ncard hpair_subset
    omega
  have hright_card : 2 <= (S.right \ S.left).ncard := by
    simpa [hright_eq, K] using hK_card
  have hsep : S.separator = Set.range H.attach := by
    simpa [S, K, B] using
      Separation.ofCoreAndBoundary_separator_eq_boundary_of_core_subset_compl
        (G := G) K B hclosed hK_attach_compl
  exact hno S hZ_left hright_card (H.attach_range_orderEq_three S hsep)

theorem RST33NoThreeSeparation.avoidingSetPath_from_rimVertexSet
    [Fintype V]
    {feet : Fin 3 -> V}
    {Z : Set V}
    (hno : RST33NoThreeSeparation G Z)
    (H : Tripod G feet) :
    AvoidingSetPath G H.rimVertexSet Z (Set.range H.attach) :=
  hno.avoidingSetPath_of_pair_in_set H
    H.left_mem_rimVertexSet H.right_mem_rimVertexSet
    H.left_not_mem_attach_range H.right_not_mem_attach_range
    H.left_ne_right

theorem RST34NoThreeSeparation.trimPositiveLeg_avoidingSetPath_from_rimVertexSet
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    let H' : Tripod G (H.feetWithPenultimate i) :=
      H.trimPositiveLeg i hpos
    let Z : Set V := insert (feet i) (Set.range (H.feetWithPenultimate i))
    AvoidingSetPath G H'.rimVertexSet Z (Set.range H'.attach) := by
  classical
  dsimp
  have hinputs :=
    hno.trimPositiveLeg_rst33_inputs hfeet_injective H hpos
  dsimp at hinputs
  exact hinputs.1.avoidingSetPath_from_rimVertexSet
    (H.trimPositiveLeg i hpos)

theorem RST34NoThreeSeparation.trimPositiveLeg_rst33Path_or_path_to_legVertexSet
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    let H' : Tripod G (H.feetWithPenultimate i) :=
      H.trimPositiveLeg i hpos
    let Z : Set V := insert (feet i) (Set.range (H.feetWithPenultimate i))
    H'.RST33PathToZ Z ∨
      Exists fun x : V =>
        x ∈ H'.rimVertexSet \ H'.legVertexSet ∧
          Exists fun y : V =>
            y ∈ H'.legVertexSet ∧
              Exists fun p : G.Walk x y =>
                (forall v : V, v ∈ p.support -> v ∈ H'.legVertexSet -> v = y) ∧
                  forall v : V, v ∈ p.support -> v ∉ Set.range H'.attach := by
  classical
  dsimp
  exact Tripod.rst33PathToZ_or_path_to_legVertexSet_of_avoiding_attach_path
    (G := G)
    (hno.trimPositiveLeg_avoidingSetPath_from_rimVertexSet
      hfeet_injective H hpos)

theorem RST34NoThreeSeparation.trimPositiveLeg_path_to_old_foot_or_path_to_legVertexSet
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    let H' : Tripod G (H.feetWithPenultimate i) :=
      H.trimPositiveLeg i hpos
    (Exists fun x : V =>
      x ∈ H'.rimVertexSet \ H'.legVertexSet ∧
        Exists fun p : G.Walk x (feet i) =>
          forall v : V, v ∈ p.support -> v ∉ H'.legVertexSet) ∨
      (Exists fun x : V =>
        x ∈ H'.rimVertexSet \ H'.legVertexSet ∧
          Exists fun y : V =>
            y ∈ H'.legVertexSet ∧
              Exists fun p : G.Walk x y =>
                (forall v : V, v ∈ p.support -> v ∈ H'.legVertexSet -> v = y) ∧
                  forall v : V, v ∈ p.support -> v ∉ Set.range H'.attach) := by
  classical
  dsimp
  rcases hno.trimPositiveLeg_rst33Path_or_path_to_legVertexSet
      hfeet_injective H hpos with hpath | hleg
  · left
    exact Tripod.RST33PathToZ.exists_path_to_old_foot_of_trimPositiveLeg
      (G := G) H hpos hpath
  · exact Or.inr hleg

theorem RST34NoThreeSeparation.trimPositiveLeg_path_to_old_foot_or_leg_hit_old_suffix_with_first
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    let H' : Tripod G (H.feetWithPenultimate i) :=
      H.trimPositiveLeg i hpos
    let Z : Set V := insert (feet i) (Set.range (H.feetWithPenultimate i))
    (Exists fun x : V =>
      x ∈ H'.rimVertexSet \ H'.legVertexSet ∧
        Exists fun p : G.Walk x (feet i) =>
          forall v : V, v ∈ p.support -> v ∉ H'.legVertexSet) ∨
      (Exists fun x : V =>
        x ∈ H'.rimVertexSet \ H'.legVertexSet ∧
          Exists fun y : V =>
            y ∈ H'.legVertexSet ∧
              Exists fun p : G.Walk x y =>
                p.IsPath ∧
                  (forall v : V, v ∈ p.support -> v ∈ H'.legVertexSet -> v = y) ∧
                    (forall v : V, v ∈ p.support -> v ∈ Z -> v = y) ∧
                      (forall v : V, v ∈ p.support -> v ∉ Set.range H'.attach) ∧
                        Exists fun j : Fin 3 =>
                          Exists fun hy : y ∈ (H.leg j).support =>
                            ((H.leg j).dropUntil y hy).length < (H.leg j).length) := by
  classical
  dsimp
  let H' : Tripod G (H.feetWithPenultimate i) := H.trimPositiveLeg i hpos
  let Z : Set V := insert (feet i) (Set.range (H.feetWithPenultimate i))
  have havoid :
      AvoidingSetPath G H'.rimVertexSet Z (Set.range H'.attach) := by
    simpa [H', Z] using
      hno.trimPositiveLeg_avoidingSetPath_from_rimVertexSet
        hfeet_injective H hpos
  rcases Tripod.rst33PathToZ_or_path_to_legVertexSet_of_avoiding_attach_path_with_first
      (G := G) (H := H') (Z := Z) havoid with hpath | hleg
  · left
    simpa [H', Z] using
      Tripod.RST33PathToZ.exists_path_to_old_foot_of_trimPositiveLeg
        (G := G) H hpos hpath
  · right
    rcases hleg with ⟨x, hx, y, hy_leg, p, hp, hfirst_leg, hfirst_Z, hp_attach⟩
    rcases hy_leg with ⟨j, hyj⟩
    rcases H.trimPositiveLeg_leg_hit_old_suffix_shorter hpos hyj
        (by simpa [H'] using hp_attach y p.end_mem_support) with
      ⟨hy_old, hlt⟩
    exact ⟨x, by simpa [H'] using hx, y, by simpa [H'] using ⟨j, hyj⟩,
      p, hp, by simpa [H'] using hfirst_leg, by simpa [Z] using hfirst_Z,
      by simpa [H'] using hp_attach, j, hy_old, hlt⟩

theorem RST34NoThreeSeparation.trimPositiveLeg_path_to_old_foot_or_shorter_leg_suffix
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    let H' : Tripod G (H.feetWithPenultimate i) :=
      H.trimPositiveLeg i hpos
    (Exists fun x : V =>
      x ∈ H'.rimVertexSet \ H'.legVertexSet ∧
        Exists fun p : G.Walk x (feet i) =>
          forall v : V, v ∈ p.support -> v ∉ H'.legVertexSet) ∨
      (Exists fun j : Fin 3 =>
        Exists fun y : V =>
          Exists fun hy : y ∈ (H'.leg j).support =>
            ((H'.leg j).dropUntil y hy).length < (H'.leg j).length) := by
  classical
  dsimp
  rcases hno.trimPositiveLeg_path_to_old_foot_or_path_to_legVertexSet
      hfeet_injective H hpos with hpath | hleg
  · exact Or.inl hpath
  · right
    rcases hleg with ⟨x, hx, y, hy_leg, p, _hfirst, hp_attach⟩
    rcases (H.trimPositiveLeg i hpos).exists_leg_dropUntil_length_lt_of_legVertexSet_not_attach
        hy_leg (hp_attach y p.end_mem_support) with
      ⟨j, hyj, hlt⟩
    exact ⟨j, y, hyj, hlt⟩

theorem RST34NoThreeSeparation.trimPositiveLeg_path_to_old_foot_or_leg_hit_shorter_suffix
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    let H' : Tripod G (H.feetWithPenultimate i) :=
      H.trimPositiveLeg i hpos
    (Exists fun x : V =>
      x ∈ H'.rimVertexSet \ H'.legVertexSet ∧
        Exists fun p : G.Walk x (feet i) =>
          forall v : V, v ∈ p.support -> v ∉ H'.legVertexSet) ∨
      (Exists fun x : V =>
        x ∈ H'.rimVertexSet \ H'.legVertexSet ∧
          Exists fun y : V =>
            y ∈ H'.legVertexSet ∧
              Exists fun p : G.Walk x y =>
                ((forall v : V, v ∈ p.support -> v ∈ H'.legVertexSet -> v = y) ∧
                  forall v : V, v ∈ p.support -> v ∉ Set.range H'.attach) ∧
                    Exists fun j : Fin 3 =>
                      Exists fun hy : y ∈ (H'.leg j).support =>
                        ((H'.leg j).dropUntil y hy).length < (H'.leg j).length) := by
  classical
  dsimp
  rcases hno.trimPositiveLeg_path_to_old_foot_or_path_to_legVertexSet
      hfeet_injective H hpos with hpath | hleg
  · exact Or.inl hpath
  · right
    rcases hleg with ⟨x, hx, y, hy_leg, p, hfirst, hp_attach⟩
    rcases (H.trimPositiveLeg i hpos).exists_leg_dropUntil_length_lt_of_legVertexSet_not_attach
        hy_leg (hp_attach y p.end_mem_support) with
      ⟨j, hyj, hlt⟩
    exact ⟨x, hx, y, hy_leg, p, ⟨hfirst, hp_attach⟩, j, hyj, hlt⟩

theorem RST34NoThreeSeparation.trimPositiveLeg_path_to_old_foot_or_leg_hit_old_suffix
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length) :
    let H' : Tripod G (H.feetWithPenultimate i) :=
      H.trimPositiveLeg i hpos
    (Exists fun x : V =>
      x ∈ H'.rimVertexSet \ H'.legVertexSet ∧
        Exists fun p : G.Walk x (feet i) =>
          forall v : V, v ∈ p.support -> v ∉ H'.legVertexSet) ∨
      (Exists fun x : V =>
        x ∈ H'.rimVertexSet \ H'.legVertexSet ∧
          Exists fun y : V =>
            y ∈ H'.legVertexSet ∧
              Exists fun p : G.Walk x y =>
                ((forall v : V, v ∈ p.support -> v ∈ H'.legVertexSet -> v = y) ∧
                  forall v : V, v ∈ p.support -> v ∉ Set.range H'.attach) ∧
                    Exists fun j : Fin 3 =>
                      Exists fun hy : y ∈ (H.leg j).support =>
                        ((H.leg j).dropUntil y hy).length < (H.leg j).length) := by
  classical
  dsimp
  rcases hno.trimPositiveLeg_path_to_old_foot_or_path_to_legVertexSet
      hfeet_injective H hpos with hpath | hleg
  · exact Or.inl hpath
  · right
    rcases hleg with ⟨x, hx, y, hy_leg, p, hfirst, hp_attach⟩
    rcases hy_leg with ⟨j, hyj⟩
    rcases H.trimPositiveLeg_leg_hit_old_suffix_shorter hpos hyj
        (hp_attach y p.end_mem_support) with
      ⟨hy_old, hlt⟩
    exact ⟨x, hx, y, ⟨j, hyj⟩, p, ⟨hfirst, hp_attach⟩, j, hy_old, hlt⟩

theorem RST33NoThreeSeparation.avoidingSetPath_of_attachComponentOf_pair
    [Fintype V]
    {feet : Fin 3 -> V}
    {Z : Set V}
    (hno : RST33NoThreeSeparation G Z)
    (H : Tripod G feet)
    {x y : V}
    (hx_attach : x ∉ Set.range H.attach)
    (hyK : y ∈ H.attachComponentOf hx_attach)
    (hxy : x ≠ y) :
    AvoidingSetPath G ({x} : Set V) Z (Set.range H.attach) := by
  classical
  by_contra hno_path
  have hZ_notK : Z ⊆ (H.attachComponentOf hx_attach)ᶜ := by
    intro z hzZ hzK
    have hconn := H.attachComponentOf_connected hx_attach
    obtain ⟨p, hpK⟩ :=
      connected_induce_exists_walk_support_subset
        (G := G) hconn (H.mem_attachComponentOf_self hx_attach) hzK
    exact hno_path ⟨x, by simp, z, hzZ, p, by
      intro v hv
      exact H.attachComponentOf_subset_attach_compl hx_attach (hpK v hv)⟩
  exact hno.not_two_vertices_in_attachComponentOf H hx_attach hZ_notK hyK hxy

theorem RST33NoThreeSeparation.avoidingSetPath_from_left_component_pair
    [Fintype V]
    {feet : Fin 3 -> V}
    {Z : Set V}
    (hno : RST33NoThreeSeparation G Z)
    (H : Tripod G feet)
    {y : V}
    (hyK : y ∈ H.attachComponentOf H.left_not_mem_attach_range)
    (hleft_ne_y : H.left ≠ y) :
    AvoidingSetPath G ({H.left} : Set V) Z (Set.range H.attach) :=
  hno.avoidingSetPath_of_attachComponentOf_pair H
    H.left_not_mem_attach_range hyK hleft_ne_y

theorem RST33NoThreeSeparation.avoidingSetPath_from_right_component_pair
    [Fintype V]
    {feet : Fin 3 -> V}
    {Z : Set V}
    (hno : RST33NoThreeSeparation G Z)
    (H : Tripod G feet)
    {y : V}
    (hyK : y ∈ H.attachComponentOf H.right_not_mem_attach_range)
    (hright_ne_y : H.right ≠ y) :
    AvoidingSetPath G ({H.right} : Set V) Z (Set.range H.attach) :=
  hno.avoidingSetPath_of_attachComponentOf_pair H
    H.right_not_mem_attach_range hyK hright_ne_y

theorem RST34NoSeparation.no_three
    {feet : Fin 3 -> V}
    (hno : RST34NoSeparation G feet) :
    RST34NoThreeSeparation G feet := by
  intro S hfeet hleft_card hright_card horder
  exact hno S hfeet hleft_card hright_card (S.orderEq_orderAtMost horder)

theorem RST34NoThreeSeparation.no_blocked_attach_core
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (H : Tripod G feet)
    {K : Set V}
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ Set.range H.attach ->
        Not (G.Adj a b))
    (hfeet : forall i : Fin 3, feet i ∉ K)
    (hleft_card : 4 <= Kᶜ.ncard)
    (hK_card : 2 <= K.ncard)
    (hK_attach_compl : K ⊆ (Set.range H.attach)ᶜ) :
    False := by
  classical
  let B : Set V := Set.range H.attach
  let S : Separation G := Separation.ofCoreAndBoundary K B (by
    intro a b ha hb hbB
    exact hclosed ha hb (by simpa [B] using hbB))
  have hfeet_left : forall i : Fin 3, feet i ∈ S.left := by
    intro i
    exact hfeet i
  have hright_eq : S.right \ S.left = K := by
    ext v
    constructor
    · rintro ⟨hv_right, hv_not_left⟩
      rcases hv_right with hvK | hvB
      · exact hvK
      · exfalso
        exact hv_not_left (by
          intro hvK
          exact hK_attach_compl hvK (by simpa [B] using hvB))
    · intro hvK
      exact ⟨Or.inl hvK, fun hv_notK => hv_notK hvK⟩
  have hright_card : 2 <= (S.right \ S.left).ncard := by
    simpa [hright_eq] using hK_card
  have hsep : S.separator = Set.range H.attach := by
    simpa [S, B] using
      Separation.ofCoreAndBoundary_separator_eq_boundary_of_core_subset_compl
        (G := G) K B (by
          intro a b ha hb hbB
          exact hclosed ha hb (by simpa [B] using hbB))
        (by
          intro v hvK hvB
          exact hK_attach_compl hvK (by simpa [B] using hvB))
  exact hno S hfeet_left (by simpa [S] using hleft_card) hright_card
    (H.attach_range_orderEq_three S hsep)

theorem RST34NoThreeSeparation.attach_core_ncard_le_one
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (H : Tripod G feet)
    {K : Set V}
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ Set.range H.attach ->
        Not (G.Adj a b))
    (hfeet : forall i : Fin 3, feet i ∉ K)
    (hleft_card : 4 <= Kᶜ.ncard)
    (hK_attach_compl : K ⊆ (Set.range H.attach)ᶜ) :
    K.ncard <= 1 := by
  by_contra hlarge_not
  have hK_card : 2 <= K.ncard := by omega
  exact hno.no_blocked_attach_core H hclosed hfeet hleft_card hK_card
    hK_attach_compl

theorem RST34NoThreeSeparation.attach_core_ncard_le_one_of_extra_left
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {K : Set V}
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ Set.range H.attach ->
        Not (G.Adj a b))
    (hfeet : forall i : Fin 3, feet i ∉ K)
    {x : V}
    (hxK : x ∉ K)
    (hx_not_feet : x ∉ Set.range feet)
    (hK_attach_compl : K ⊆ (Set.range H.attach)ᶜ) :
    K.ncard <= 1 := by
  classical
  have h01 : feet 0 ≠ feet 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (hfeet_injective h)
  have h02 : feet 0 ≠ feet 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (hfeet_injective h)
  have h12 : feet 1 ≠ feet 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (hfeet_injective h)
  have h0x : feet 0 ≠ x := by
    intro h
    exact hx_not_feet ⟨0, h⟩
  have h1x : feet 1 ≠ x := by
    intro h
    exact hx_not_feet ⟨1, h⟩
  have h2x : feet 2 ≠ x := by
    intro h
    exact hx_not_feet ⟨2, h⟩
  let Q : Set V := {feet 0, feet 1, feet 2, x}
  have hQ_card : Q.ncard = 4 := by
    rw [Set.ncard_eq_four]
    exact ⟨feet 0, feet 1, feet 2, x, h01, h02, h0x, h12, h1x, h2x, rfl⟩
  have hQ_subset : Q ⊆ Kᶜ := by
    intro v hv
    simp only [Q, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hfeet 0
    · exact hfeet 1
    · exact hfeet 2
    · exact hxK
  have hleft_card : 4 <= Kᶜ.ncard := by
    have hle : Q.ncard <= Kᶜ.ncard := Set.ncard_le_ncard hQ_subset
    omega
  exact hno.attach_core_ncard_le_one H hclosed hfeet hleft_card
    hK_attach_compl

theorem RST34NoThreeSeparation.attachComponentOf_ncard_le_one_of_extra_left
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {x : V}
    (hx_attach : x ∉ Set.range H.attach)
    (hfeet :
      forall i : Fin 3, feet i ∉ H.attachComponentOf hx_attach)
    {z : V}
    (hzK : z ∉ H.attachComponentOf hx_attach)
    (hz_not_feet : z ∉ Set.range feet) :
    (H.attachComponentOf hx_attach).ncard <= 1 := by
  exact hno.attach_core_ncard_le_one_of_extra_left hfeet_injective H
    (H.attachComponentOf_closed hx_attach) hfeet hzK hz_not_feet
    (H.attachComponentOf_subset_attach_compl hx_attach)

theorem RST34NoThreeSeparation.not_two_vertices_in_attachComponentOf_of_extra_left
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {x : V}
    (hx_attach : x ∉ Set.range H.attach)
    (hfeet :
      forall i : Fin 3, feet i ∉ H.attachComponentOf hx_attach)
    {z : V}
    (hzK : z ∉ H.attachComponentOf hx_attach)
    (hz_not_feet : z ∉ Set.range feet)
    {y : V}
    (hyK : y ∈ H.attachComponentOf hx_attach)
    (hxy : x ≠ y) :
    False := by
  have hle :
      (H.attachComponentOf hx_attach).ncard <= 1 :=
    hno.attachComponentOf_ncard_le_one_of_extra_left hfeet_injective H
      hx_attach hfeet hzK hz_not_feet
  have hpair_subset : ({x, y} : Set V) ⊆ H.attachComponentOf hx_attach := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact H.mem_attachComponentOf_self hx_attach
    · exact hyK
  have hpair_card : ({x, y} : Set V).ncard = 2 :=
    Set.ncard_pair hxy
  have htwo : 2 <= (H.attachComponentOf hx_attach).ncard := by
    have hsub := Set.ncard_le_ncard hpair_subset
    omega
  omega

theorem RST34NoThreeSeparation.avoidingSetPath_of_attachComponentOf_pair
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {x y z : V}
    (hx_attach : x ∉ Set.range H.attach)
    (hyK : y ∈ H.attachComponentOf hx_attach)
    (hxy : x ≠ y)
    {Z : Set V}
    (hfeetZ : forall i : Fin 3, feet i ∈ Z)
    (hzZ : z ∈ Z)
    (hz_not_feet : z ∉ Set.range feet) :
    AvoidingSetPath G ({x} : Set V) Z (Set.range H.attach) := by
  classical
  by_contra hno_path
  have hfeet_notK :
      forall i : Fin 3, feet i ∉ H.attachComponentOf hx_attach := by
    intro i hfiK
    have hconn := H.attachComponentOf_connected hx_attach
    obtain ⟨p, hpK⟩ :=
      connected_induce_exists_walk_support_subset
        (G := G) hconn (H.mem_attachComponentOf_self hx_attach) hfiK
    exact hno_path ⟨x, by simp, feet i, hfeetZ i, p, by
      intro v hv
      exact H.attachComponentOf_subset_attach_compl hx_attach (hpK v hv)⟩
  have hz_notK : z ∉ H.attachComponentOf hx_attach := by
    intro hzK
    have hconn := H.attachComponentOf_connected hx_attach
    obtain ⟨p, hpK⟩ :=
      connected_induce_exists_walk_support_subset
        (G := G) hconn (H.mem_attachComponentOf_self hx_attach) hzK
    exact hno_path ⟨x, by simp, z, hzZ, p, by
      intro v hv
      exact H.attachComponentOf_subset_attach_compl hx_attach (hpK v hv)⟩
  exact hno.not_two_vertices_in_attachComponentOf_of_extra_left
    hfeet_injective H hx_attach hfeet_notK hz_notK hz_not_feet hyK hxy

theorem RST34NoThreeSeparation.avoidingSetPath_from_left_component_pair
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {y z : V}
    (hyK : y ∈ H.attachComponentOf H.left_not_mem_attach_range)
    (hleft_ne_y : H.left ≠ y)
    {Z : Set V}
    (hfeetZ : forall i : Fin 3, feet i ∈ Z)
    (hzZ : z ∈ Z)
    (hz_not_feet : z ∉ Set.range feet) :
    AvoidingSetPath G ({H.left} : Set V) Z (Set.range H.attach) :=
  hno.avoidingSetPath_of_attachComponentOf_pair hfeet_injective H
    H.left_not_mem_attach_range hyK hleft_ne_y hfeetZ hzZ hz_not_feet

theorem RST34NoThreeSeparation.avoidingSetPath_from_right_component_pair
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST34NoThreeSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (H : Tripod G feet)
    {y z : V}
    (hyK : y ∈ H.attachComponentOf H.right_not_mem_attach_range)
    (hright_ne_y : H.right ≠ y)
    {Z : Set V}
    (hfeetZ : forall i : Fin 3, feet i ∈ Z)
    (hzZ : z ∈ Z)
    (hz_not_feet : z ∉ Set.range feet) :
    AvoidingSetPath G ({H.right} : Set V) Z (Set.range H.attach) :=
  hno.avoidingSetPath_of_attachComponentOf_pair hfeet_injective H
    H.right_not_mem_attach_range hyK hright_ne_y hfeetZ hzZ hz_not_feet

end Schematic.Math.GraphTheory
