import DominatingFourColour.Prerequisites.RSTFlaps.FlapPaths

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

theorem Triad.disjoint_flapVertexSet_of_ne
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {B C : T.Flap}
    (hBC : B ≠ C) :
    Disjoint (T.flapVertexSet B) (T.flapVertexSet C) := by
  rw [Set.disjoint_left]
  intro x hxB hxC
  rcases hxB with ⟨hxBT, hxBsupp⟩
  rcases hxC with ⟨hxCT, hxCsupp⟩
  have hxCsupp' : (⟨x, hxBT⟩ : (T.vertexSetᶜ : Set V)) ∈ C.supp := by
    simpa [Subtype.ext_iff] using hxCsupp
  exact hBC
    (SimpleGraph.ConnectedComponent.eq_of_common_vertex hxBsupp hxCsupp')

theorem Triad.exists_flap_containing_flap_of_subtriad_union_other_flap
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {C D : T.Flap}
    (hCD : C ≠ D)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D) :
    Exists fun C' : T'.Flap =>
      T.flapVertexSet C ⊆ T'.flapVertexSet C' := by
  have hC_subset_T' :
      T.flapVertexSet C ⊆ T'.vertexSetᶜ := by
    intro y hyC hyT'
    rcases hT'_subset hyT' with hyT | hyD
    · exact (T.flapVertexSet_subset_complement C hyC) hyT
    · exact Set.disjoint_left.mp (T.disjoint_flapVertexSet_of_ne hCD) hyC hyD
  exact T'.exists_flap_containing_connected_set
    (T.flapVertexSet_connected C) hC_subset_T'

theorem Triad.exists_non_distinguished_flap_containing_flap_of_subtriad_union_other_flap
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B C D : T.Flap}
    {B' : T'.Flap}
    (hCD : C ≠ D)
    (hCB : C ≠ B)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hB_eq : T.flapVertexSet B = T'.flapVertexSet B') :
    Exists fun C' : T'.Flap =>
      C' ≠ B' ∧ T.flapVertexSet C ⊆ T'.flapVertexSet C' := by
  obtain ⟨C', hC_subset⟩ :=
    T.exists_flap_containing_flap_of_subtriad_union_other_flap
      (T' := T') hCD hT'_subset
  refine ⟨C', ?_, hC_subset⟩
  intro hC'B'
  obtain ⟨y, hyC⟩ := T.flapVertexSet_nonempty C
  have hyB' : y ∈ T'.flapVertexSet B' := by
    simpa [hC'B'] using hC_subset hyC
  have hyB : y ∈ T.flapVertexSet B := by
    simpa [hB_eq] using hyB'
  exact Set.disjoint_left.mp (T.disjoint_flapVertexSet_of_ne hCB) hyC hyB

theorem Triad.exists_non_distinguished_flap_containing_flap_of_subtriad
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B C : T.Flap}
    {B' : T'.Flap}
    (hCB : C ≠ B)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet)
    (hB_eq : T'.flapVertexSet B' = T.flapVertexSet B) :
    Exists fun C' : T'.Flap =>
      C' ≠ B' ∧ T.flapVertexSet C ⊆ T'.flapVertexSet C' := by
  obtain ⟨C', hC_subset⟩ :=
    T.exists_flap_containing_connected_set_of_subtriad
      (T' := T') hT'_subset (T.flapVertexSet_connected C)
      (T.flapVertexSet_subset_complement C)
  refine ⟨C', ?_, hC_subset⟩
  intro hC'B'
  obtain ⟨y, hyC⟩ := T.flapVertexSet_nonempty C
  have hyB' : y ∈ T'.flapVertexSet B' := by
    simpa [hC'B'] using hC_subset hyC
  have hyB : y ∈ T.flapVertexSet B := by
    simpa [hB_eq] using hyB'
  exact Set.disjoint_left.mp (T.disjoint_flapVertexSet_of_ne hCB) hyC hyB

theorem Triad.flapSizeTailWith_le_of_subtriad_flap_eq
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B : T.Flap}
    {B' : T'.Flap}
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet)
    (hB_eq : T'.flapVertexSet B' = T.flapVertexSet B) :
    T.flapSizeTailWith B <= T'.flapSizeTailWith B' := by
  classical
  letI : Fintype (T.vertexSetᶜ : Set V) := (T.vertexSetᶜ).toFinite.fintype
  letI : Fintype (T'.vertexSetᶜ : Set V) := (T'.vertexSetᶜ).toFinite.fintype
  let targetOf : T.Flap -> T'.Flap := fun C =>
    if hCB : C = B then B' else
      Classical.choose
        (T.exists_non_distinguished_flap_containing_flap_of_subtriad
          (T' := T') (B' := B') hCB hT'_subset hB_eq)
  have htarget_ne : forall C : T.Flap, C ≠ B -> targetOf C ≠ B' := by
    intro C hCB
    dsimp [targetOf]
    simp [hCB]
    exact (Classical.choose_spec
      (T.exists_non_distinguished_flap_containing_flap_of_subtriad
        (T' := T') (B' := B') hCB hT'_subset hB_eq)).1
  have htarget_subset : forall C : T.Flap, C ≠ B ->
      T.flapVertexSet C ⊆ T'.flapVertexSet (targetOf C) := by
    intro C hCB
    dsimp [targetOf]
    simp [hCB]
    exact (Classical.choose_spec
      (T.exists_non_distinguished_flap_containing_flap_of_subtriad
        (T' := T') (B' := B') hCB hT'_subset hB_eq)).2
  change
    Multiset.sort
        (((Finset.univ.erase B : Finset T.Flap).val.map
          fun C => (T.flapVertexSet C).ncard))
        (fun a b : Nat => b <= a) <=
      Multiset.sort
        (((Finset.univ.erase B' : Finset T'.Flap).val.map
          fun C => (T'.flapVertexSet C).ncard))
        (fun a b : Nat => b <= a)
  refine multiset_sort_map_le_of_coarsening
    (fun C : T.Flap => (T.flapVertexSet C).ncard)
    (fun C' : T'.Flap => (T'.flapVertexSet C').ncard)
    targetOf
    ((Finset.univ.erase B : Finset T.Flap).val)
    ((Finset.univ.erase B' : Finset T'.Flap).val)
    ?_ ?_ ?_ ?_ ?_
  · exact (Finset.univ.erase B).nodup
  · intro C _hC
    exact (Set.ncard_pos (s := T.flapVertexSet C)).mpr
      (T.flapVertexSet_nonempty C)
  · intro C hC
    have hC_fin : C ∈ (Finset.univ.erase B : Finset T.Flap) := hC
    have hCB : C ≠ B := (Finset.mem_erase.mp hC_fin).1
    have hne : targetOf C ≠ B' := htarget_ne C hCB
    have htarget_mem : targetOf C ∈ (Finset.univ.erase B' : Finset T'.Flap) := by
      simp [Finset.mem_erase, hne]
    exact htarget_mem
  · intro C hC
    have hC_fin : C ∈ (Finset.univ.erase B : Finset T.Flap) := hC
    have hCB : C ≠ B := (Finset.mem_erase.mp hC_fin).1
    exact Set.ncard_le_ncard (htarget_subset C hCB)
  · intro C D hC hD hDC htarget_eq hcard_eq
    have hC_fin : C ∈ (Finset.univ.erase B : Finset T.Flap) := hC
    have hD_fin : D ∈ (Finset.univ.erase B : Finset T.Flap) := hD
    have hCB : C ≠ B := (Finset.mem_erase.mp hC_fin).1
    have hDB : D ≠ B := (Finset.mem_erase.mp hD_fin).1
    have hC_subset : T.flapVertexSet C ⊆ T'.flapVertexSet (targetOf C) :=
      htarget_subset C hCB
    have hD_subset : T.flapVertexSet D ⊆ T'.flapVertexSet (targetOf D) :=
      htarget_subset D hDB
    have hC_eq_old_new : T.flapVertexSet C = T'.flapVertexSet (targetOf C) := by
      refine Set.eq_of_subset_of_ncard_le hC_subset ?_
      simp [hcard_eq]
    have hC_eq :
        T'.flapVertexSet (targetOf C) = T.flapVertexSet C :=
      hC_eq_old_new.symm
    obtain ⟨y, hyD⟩ := T.flapVertexSet_nonempty D
    have hy_new : y ∈ T'.flapVertexSet (targetOf C) := by
      simpa [htarget_eq] using hD_subset hyD
    have hyC : y ∈ T.flapVertexSet C := by
      simpa [hC_eq] using hy_new
    exact Set.disjoint_left.mp
      (T.disjoint_flapVertexSet_of_ne (B := D) (C := C) hDC) hyD hyC

theorem Triad.flapSizeProfileWith_le_of_subtriad_flap_eq
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B : T.Flap}
    {B' : T'.Flap}
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet)
    (hB_eq : T'.flapVertexSet B' = T.flapVertexSet B) :
    T.flapSizeProfileWith B <= T'.flapSizeProfileWith B' := by
  have htail : T.flapSizeTailWith B <= T'.flapSizeTailWith B' :=
    T.flapSizeTailWith_le_of_subtriad_flap_eq (T' := T') (B' := B')
      hT'_subset hB_eq
  have hhead :
      (T.flapVertexSet B).ncard = (T'.flapVertexSet B').ncard := by
    rw [hB_eq]
  rw [T.flapSizeProfileWith_eq_cons_tailWith B,
    T'.flapSizeProfileWith_eq_cons_tailWith B', hhead]
  exact List.cons_le_cons _ htail

theorem Triad.flapSizeTailWith_lt_of_replacement_flap_growth
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B D E : T.Flap}
    {B' E' : T'.Flap}
    (hED : E ≠ D)
    (hEB : E ≠ B)
    (hDB : D ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hB_eq : T.flapVertexSet B = T'.flapVertexSet B')
    (hE'B' : E' ≠ B')
    (hE_subset : T.flapVertexSet E ⊆ T'.flapVertexSet E')
    (hE_lt : (T.flapVertexSet E).ncard < (T'.flapVertexSet E').ncard) :
    T.flapSizeTailWith B < T'.flapSizeTailWith B' := by
  classical
  letI : Fintype (T.vertexSetᶜ : Set V) := (T.vertexSetᶜ).toFinite.fintype
  letI : Fintype (T'.vertexSetᶜ : Set V) := (T'.vertexSetᶜ).toFinite.fintype
  let targetOf : T.Flap -> T'.Flap := fun C =>
    if _hCB : C = B then B' else
      if _hCD : C = D then E' else
        if _hCE : C = E then E' else
          Classical.choose
            (T.exists_non_distinguished_flap_containing_flap_of_subtriad_union_other_flap
              (T' := T') (B := B) (C := C) (D := D) (B' := B')
              _hCD _hCB hT'_subset hB_eq)
  have htarget_D : targetOf D = E' := by
    dsimp [targetOf]
    simp [hDB]
  have htarget_E : targetOf E = E' := by
    dsimp [targetOf]
    simp [hEB, hED]
  have htarget_ne : forall C : T.Flap, C ≠ B -> targetOf C ≠ B' := by
    intro C hCB
    by_cases hCD : C = D
    · subst C
      simpa [htarget_D] using hE'B'
    · by_cases hCE : C = E
      · subst C
        simpa [htarget_E] using hE'B'
      · dsimp [targetOf]
        simp [hCB, hCD, hCE]
        exact (Classical.choose_spec
          (T.exists_non_distinguished_flap_containing_flap_of_subtriad_union_other_flap
            (T' := T') (B := B) (C := C) (D := D) (B' := B')
            hCD hCB hT'_subset hB_eq)).1
  have htarget_subset : forall C : T.Flap, C ≠ B -> C ≠ D ->
      T.flapVertexSet C ⊆ T'.flapVertexSet (targetOf C) := by
    intro C hCB hCD
    by_cases hCE : C = E
    · subst C
      simpa [htarget_E] using hE_subset
    · dsimp [targetOf]
      simp [hCB, hCD, hCE]
      exact (Classical.choose_spec
        (T.exists_non_distinguished_flap_containing_flap_of_subtriad_union_other_flap
          (T' := T') (B := B) (C := C) (D := D) (B' := B')
          hCD hCB hT'_subset hB_eq)).2
  have hD_lt_E' : (T.flapVertexSet D).ncard < (T'.flapVertexSet E').ncard := by
    exact lt_of_le_of_lt (hD_min E hEB) hE_lt
  change
    Multiset.sort
        (((Finset.univ.erase B : Finset T.Flap).val.map
          fun C => (T.flapVertexSet C).ncard))
        (fun a b : Nat => b <= a) <
      Multiset.sort
        (((Finset.univ.erase B' : Finset T'.Flap).val.map
          fun C => (T'.flapVertexSet C).ncard))
        (fun a b : Nat => b <= a)
  refine multiset_sort_map_lt_of_coarsening
    (fun C : T.Flap => (T.flapVertexSet C).ncard)
    (fun C' : T'.Flap => (T'.flapVertexSet C').ncard)
    targetOf
    ((Finset.univ.erase B : Finset T.Flap).val)
    ((Finset.univ.erase B' : Finset T'.Flap).val)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact (Finset.univ.erase B).nodup
  · intro C _hC
    exact (Set.ncard_pos (s := T.flapVertexSet C)).mpr
      (T.flapVertexSet_nonempty C)
  · intro C hC
    have hC_fin : C ∈ (Finset.univ.erase B : Finset T.Flap) := hC
    have hCB : C ≠ B := (Finset.mem_erase.mp hC_fin).1
    have hne : targetOf C ≠ B' := htarget_ne C hCB
    have htarget_mem : targetOf C ∈ (Finset.univ.erase B' : Finset T'.Flap) := by
      simp [Finset.mem_erase, hne]
    exact htarget_mem
  · intro C hC
    have hC_fin : C ∈ (Finset.univ.erase B : Finset T.Flap) := hC
    have hCB : C ≠ B := (Finset.mem_erase.mp hC_fin).1
    by_cases hCD : C = D
    · subst C
      simpa [htarget_D] using hD_lt_E'.le
    · exact Set.ncard_le_ncard (htarget_subset C hCB hCD)
  · intro C F hC hF hFC htarget_eq hcard_eq
    have hC_fin : C ∈ (Finset.univ.erase B : Finset T.Flap) := hC
    have hF_fin : F ∈ (Finset.univ.erase B : Finset T.Flap) := hF
    have hCB : C ≠ B := (Finset.mem_erase.mp hC_fin).1
    have hFB : F ≠ B := (Finset.mem_erase.mp hF_fin).1
    by_cases hCD : C = D
    · subst C
      have : (T'.flapVertexSet E').ncard = (T.flapVertexSet D).ncard := by
        simpa [htarget_D] using hcard_eq
      omega
    · by_cases hCE : C = E
      · subst C
        have : (T'.flapVertexSet E').ncard = (T.flapVertexSet E).ncard := by
          simpa [htarget_E] using hcard_eq
        omega
      · have hC_subset : T.flapVertexSet C ⊆ T'.flapVertexSet (targetOf C) :=
          htarget_subset C hCB hCD
        have hC_eq_old_new : T.flapVertexSet C = T'.flapVertexSet (targetOf C) := by
          refine Set.eq_of_subset_of_ncard_le hC_subset ?_
          simp [hcard_eq]
        have hC_eq : T'.flapVertexSet (targetOf C) = T.flapVertexSet C :=
          hC_eq_old_new.symm
        by_cases hFD : F = D
        · subst F
          have hE_in_target : T.flapVertexSet E ⊆ T'.flapVertexSet (targetOf C) := by
            intro x hxE
            have hxE' : x ∈ T'.flapVertexSet E' := hE_subset hxE
            simpa [← htarget_eq, htarget_D] using hxE'
          obtain ⟨y, hyE⟩ := T.flapVertexSet_nonempty E
          have hyC : y ∈ T.flapVertexSet C := by
            simpa [hC_eq] using hE_in_target hyE
          exact Set.disjoint_left.mp
            (T.disjoint_flapVertexSet_of_ne (B := E) (C := C)
              (fun hEC => hCE hEC.symm)) hyE hyC
        · by_cases hFE : F = E
          · subst F
            have hE_in_target : T.flapVertexSet E ⊆ T'.flapVertexSet (targetOf C) := by
              intro x hxE
              have hxE' : x ∈ T'.flapVertexSet E' := hE_subset hxE
              simpa [← htarget_eq, htarget_E] using hxE'
            obtain ⟨y, hyE⟩ := T.flapVertexSet_nonempty E
            have hyC : y ∈ T.flapVertexSet C := by
              simpa [hC_eq] using hE_in_target hyE
            exact Set.disjoint_left.mp
              (T.disjoint_flapVertexSet_of_ne (B := E) (C := C)
              (fun hEC => hCE hEC.symm)) hyE hyC
          · have hF_subset : T.flapVertexSet F ⊆ T'.flapVertexSet (targetOf F) :=
              htarget_subset F hFB hFD
            obtain ⟨y, hyF⟩ := T.flapVertexSet_nonempty F
            have hy_new : y ∈ T'.flapVertexSet (targetOf C) := by
              simpa [htarget_eq] using hF_subset hyF
            have hyC : y ∈ T.flapVertexSet C := by
              simpa [hC_eq] using hy_new
            exact Set.disjoint_left.mp
              (T.disjoint_flapVertexSet_of_ne (B := F) (C := C) hFC) hyF hyC
  · have hE_mem : E ∈ (Finset.univ.erase B : Finset T.Flap) := by
      simp [Finset.mem_erase, hEB]
    refine ⟨E, hE_mem, ?_⟩
    simpa [htarget_E] using hE_lt

theorem Triad.exists_tail_entry_ge_of_flap_subtriad_union_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B C D : T.Flap}
    {B' : T'.Flap}
    (hCD : C ≠ D)
    (hCB : C ≠ B)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hB_eq : T.flapVertexSet B = T'.flapVertexSet B') :
    Exists fun n : Nat =>
      n ∈ T'.flapSizeTailWith B' ∧
        (T.flapVertexSet C).ncard <= n := by
  obtain ⟨C', hC'B', hC_subset⟩ :=
    T.exists_non_distinguished_flap_containing_flap_of_subtriad_union_other_flap
      (T' := T') (B' := B') hCD hCB hT'_subset hB_eq
  refine ⟨(T'.flapVertexSet C').ncard, ?_, ?_⟩
  · exact T'.mem_flapSizeTailWith_of_ne hC'B'
  · exact Set.ncard_le_ncard hC_subset

theorem Triad.exists_tail_entry_gt_of_flap_growth
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B' E' : T'.Flap}
    {E : T.Flap}
    (hE'B' : E' ≠ B')
    (hE_lt :
      (T.flapVertexSet E).ncard < (T'.flapVertexSet E').ncard) :
    Exists fun n : Nat =>
      n ∈ T'.flapSizeTailWith B' ∧
        (T.flapVertexSet E).ncard < n := by
  exact ⟨(T'.flapVertexSet E').ncard,
    T'.mem_flapSizeTailWith_of_ne hE'B', hE_lt⟩

theorem Triad.add_ncard_le_of_two_flaps_subset_new_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {C₁ C₂ : T.Flap}
    {C' : T'.Flap}
    (hC₁C₂ : C₁ ≠ C₂)
    (hC₁_subset : T.flapVertexSet C₁ ⊆ T'.flapVertexSet C')
    (hC₂_subset : T.flapVertexSet C₂ ⊆ T'.flapVertexSet C') :
    (T.flapVertexSet C₁).ncard + (T.flapVertexSet C₂).ncard <=
      (T'.flapVertexSet C').ncard := by
  have hunion_subset :
      T.flapVertexSet C₁ ∪ T.flapVertexSet C₂ ⊆ T'.flapVertexSet C' := by
    intro x hx
    rcases hx with hx | hx
    · exact hC₁_subset hx
    · exact hC₂_subset hx
  have hcard_union_le :
      (T.flapVertexSet C₁ ∪ T.flapVertexSet C₂).ncard <=
        (T'.flapVertexSet C').ncard :=
    Set.ncard_le_ncard hunion_subset
  have hdisjoint : Disjoint (T.flapVertexSet C₁) (T.flapVertexSet C₂) :=
    T.disjoint_flapVertexSet_of_ne hC₁C₂
  have hcard_union :
      (T.flapVertexSet C₁ ∪ T.flapVertexSet C₂).ncard =
        (T.flapVertexSet C₁).ncard + (T.flapVertexSet C₂).ncard :=
    Set.ncard_union_eq hdisjoint
  omega

theorem Triad.not_adj_of_mem_flapVertexSet_of_ne
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {B C : T.Flap}
    (hBC : B ≠ C)
    {x y : V}
    (hx : x ∈ T.flapVertexSet B)
    (hy : y ∈ T.flapVertexSet C) :
    Not (G.Adj x y) := by
  intro hxy
  have hyB : y ∈ T.flapVertexSet B :=
    T.flapVertexSet_mem_of_adj B hx (T.flapVertexSet_subset_complement C hy) hxy
  exact Set.disjoint_left.mp (T.disjoint_flapVertexSet_of_ne hBC) hyB hy

theorem Triad.exists_other_flap_ncard_minimal
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {B : T.Flap}
    (hnot_unique : ¬ forall C : T.Flap, C = B) :
    Exists fun D : T.Flap =>
      D ≠ B ∧
        forall E : T.Flap, E ≠ B ->
          (T.flapVertexSet D).ncard <= (T.flapVertexSet E).ncard := by
  classical
  let others : Set T.Flap := {D | D ≠ B}
  have hothers_finite : others.Finite := Set.toFinite others
  have hothers_nonempty : others.Nonempty := by
    by_contra hnone
    exact hnot_unique (by
      intro C
      by_contra hCB
      exact hnone ⟨C, by simpa [others] using hCB⟩)
  obtain ⟨D, hD, hmin⟩ :=
    Set.exists_min_image others (fun E : T.Flap => (T.flapVertexSet E).ncard)
      hothers_finite hothers_nonempty
  exact ⟨D, by simpa [others] using hD, by
    intro E hE
    exact hmin E (by simpa [others] using hE)⟩

theorem Triad.exists_distinguished_profile_larger_or_tail_flap_ncard_larger
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T T' : Triad G feet}
    {B D E : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hED : E ≠ D)
    (hEB : E ≠ B)
    (hDB : D ≠ B)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D)
    {x : V}
    (hx_boundary :
      x ∈ relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet)
    (hxT' : x ∉ T'.vertexSet) :
    Exists fun B' : T'.Flap =>
      W ⊆ T'.flapVertexSet B' ∧
        T.flapVertexSet B ⊆ T'.flapVertexSet B' ∧
          (T.flapSizeProfileWith B < T'.flapSizeProfileWith B' ∨
            Exists fun E' : T'.Flap =>
              E' ≠ B' ∧
                T.flapVertexSet E ⊆ T'.flapVertexSet E' ∧
                  (T.flapVertexSet E).ncard <
                    (T'.flapVertexSet E').ncard) := by
  classical
  have hD_disjoint_B :
      Disjoint (T.flapVertexSet D) (T.flapVertexSet B) :=
    T.disjoint_flapVertexSet_of_ne hDB
  have hB_subset_T' :
      T.flapVertexSet B ⊆ T'.vertexSetᶜ := by
    intro y hyB hyT'
    rcases hT'_subset hyT' with hyT | hyD
    · exact (T.flapVertexSet_subset_complement B hyB) hyT
    · exact Set.disjoint_left.mp hD_disjoint_B hyD hyB
  obtain ⟨B', hB_subset⟩ :=
    T'.exists_flap_containing_connected_set
      (T.flapVertexSet_connected B) hB_subset_T'
  have hD_disjoint_E :
      Disjoint (T.flapVertexSet D) (T.flapVertexSet E) :=
    T.disjoint_flapVertexSet_of_ne (fun hDE => hED hDE.symm)
  obtain ⟨E', hE_subset, hE_lt⟩ :=
    T.exists_flap_ncard_larger_of_subtriad_union_omits_flap_boundary_vertex
      (T' := T') (B := E) (W := T.flapVertexSet E)
      (X := T.flapVertexSet D) subset_rfl hT'_subset hD_disjoint_E
      hx_boundary hxT'
  refine ⟨B', Set.Subset.trans hW hB_subset, hB_subset, ?_⟩
  by_cases hE'B' : E' = B'
  · subst E'
    obtain ⟨y, hyE⟩ := T.flapVertexSet_nonempty E
    have hyB' : y ∈ T'.flapVertexSet B' := hE_subset hyE
    have hy_not_B : y ∉ T.flapVertexSet B := by
      intro hyB
      exact Set.disjoint_left.mp
        (T.disjoint_flapVertexSet_of_ne (B := E) (C := B) hEB)
        hyE hyB
    have hB_strict : T.flapVertexSet B ⊂ T'.flapVertexSet B' := by
      refine ⟨hB_subset, ?_⟩
      intro hnew_subset_old
      exact hy_not_B (hnew_subset_old hyB')
    exact Or.inl
      (Triad.flapSizeProfileWith_lt_of_distinguished_flap_ssubset
        (G := G) hB_strict)
  · exact Or.inr ⟨E', hE'B', hE_subset, hE_lt⟩

theorem Triad.flapVertexSet_closed_outside_of_boundary_subset
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {S : Set V}
    {B : T.Flap}
    (hboundary :
      relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆ S) :
    forall {a b : V},
      a ∈ T.flapVertexSet B ->
        b ∉ T.flapVertexSet B ->
          b ∉ S ->
            Not (G.Adj a b) := by
  intro a b ha hb hbS hab
  by_cases hbT : b ∈ T.vertexSet
  · exact hbS (hboundary ⟨hbT, a, ha, hab⟩)
  · exact hb (T.flapVertexSet_mem_of_adj B ha hbT hab)

theorem Triad.induceComponentSupport_subset_flapVertexSet_of_mem_of_boundary_subset
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {S : Set V}
    {B : T.Flap}
    (hboundary :
      relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆ S)
    (C : (G.induce Sᶜ).ConnectedComponent)
    {x : V}
    (hxC : x ∈ induceComponentSupport (G := G) C)
    (hxB : x ∈ T.flapVertexSet B) :
    induceComponentSupport (G := G) C ⊆ T.flapVertexSet B := by
  intro y hyC
  rcases hxC with ⟨hxS, hxCsupp⟩
  rcases hyC with ⟨hyS, hyCsupp⟩
  let ux : (Sᶜ : Set V) := ⟨x, hxS⟩
  let vy : (Sᶜ : Set V) := ⟨y, hyS⟩
  have hreach : (G.induce Sᶜ).Reachable ux vy :=
    C.reachable_of_mem_supp (by simpa [ux] using hxCsupp)
      (by simpa [vy] using hyCsupp)
  exact reachable_induce_compl_mem_of_closed
    (G := G) (S := S) (K := T.flapVertexSet B)
    (u := ux) (v := vy) hxB
    (T.flapVertexSet_closed_outside_of_boundary_subset hboundary) hreach

theorem Triad.induceComponentSupport_eq_flapVertexSet_of_subset_of_boundary_subset
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {S : Set V}
    {B : T.Flap}
    (hboundary :
      relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆ S)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hB_subset_C :
      T.flapVertexSet B ⊆ induceComponentSupport (G := G) C) :
    induceComponentSupport (G := G) C = T.flapVertexSet B := by
  obtain ⟨x, hxB⟩ := T.flapVertexSet_nonempty B
  have hxC : x ∈ induceComponentSupport (G := G) C := hB_subset_C hxB
  exact Set.Subset.antisymm
    (T.induceComponentSupport_subset_flapVertexSet_of_mem_of_boundary_subset
      hboundary C hxC hxB)
    hB_subset_C

theorem Triad.exists_induceComponentSupport_eq_flapVertexSet_of_boundary_subset
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {S : Set V}
    {B : T.Flap}
    (hboundary :
      relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆ S)
    (hB_subset_S_compl : T.flapVertexSet B ⊆ Sᶜ) :
    Exists fun C : (G.induce Sᶜ).ConnectedComponent =>
      induceComponentSupport (G := G) C = T.flapVertexSet B := by
  obtain ⟨C, hB_subset_C⟩ :=
    connected_set_subset_induceComponentSupport
      (G := G) (A := Sᶜ) (K := T.flapVertexSet B)
      (T.flapVertexSet_connected B) hB_subset_S_compl
  exact ⟨C,
    T.induceComponentSupport_eq_flapVertexSet_of_subset_of_boundary_subset
      hboundary C hB_subset_C⟩

theorem Triad.flapVertexSet_eq_of_boundary_subset
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {S : Set V}
    {B : T.Flap}
    (hboundary :
      relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆ S)
    {C : (G.induce Sᶜ).ConnectedComponent}
    (hB_subset_C : T.flapVertexSet B ⊆ induceComponentSupport (G := G) C) :
    induceComponentSupport (G := G) C = T.flapVertexSet B :=
  T.induceComponentSupport_eq_flapVertexSet_of_subset_of_boundary_subset
    hboundary C hB_subset_C

theorem Triad.exists_subtriad_flap_eq_of_boundary_subset
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B : T.Flap}
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet)
    (hboundary :
      relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆ T'.vertexSet) :
    Exists fun B' : T'.Flap => T'.flapVertexSet B' = T.flapVertexSet B := by
  obtain ⟨B', hB_subset⟩ :=
    T.exists_flap_containing_connected_set_of_subtriad
      (T' := T') hT'_subset (T.flapVertexSet_connected B)
      (T.flapVertexSet_subset_complement B)
  exact ⟨B', by
    exact T.flapVertexSet_eq_of_boundary_subset
      (S := T'.vertexSet) hboundary hB_subset⟩

theorem Triad.exists_subtriad_profile_not_smaller_of_boundary_persistence
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hboundary :
      forall T' : Triad G feet,
        T'.vertexSet ⊆ T.vertexSet ->
          relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
            T'.vertexSet)
    (T' : Triad G feet)
    (hstrict : T'.vertexSet ⊂ T.vertexSet) :
    Exists fun B' : T'.Flap =>
      W ⊆ T'.flapVertexSet B' ∧
        T.flapSizeProfileWith B <= T'.flapSizeProfileWith B' := by
  obtain ⟨B', hB_eq⟩ :=
    T.exists_subtriad_flap_eq_of_boundary_subset
      (T' := T') hstrict.1 (hboundary T' hstrict.1)
  refine ⟨B', ?_, ?_⟩
  · simpa [hB_eq] using hW
  · exact T.flapSizeProfileWith_le_of_subtriad_flap_eq
      (T' := T') (B' := B') hstrict.1 hB_eq

theorem Triad.subsingleton_flaps_of_complement_connected
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hconnected : (G.induce T.vertexSetᶜ).Connected) :
    Subsingleton T.Flap :=
  hconnected.preconnected.subsingleton_connectedComponent

theorem Triad.complement_connected_of_subsingleton_flaps
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hnonempty : T.vertexSetᶜ.Nonempty)
    (hsubsingleton : Subsingleton T.Flap) :
    (G.induce T.vertexSetᶜ).Connected := by
  letI : Nonempty (T.vertexSetᶜ : Set V) := by
    rcases hnonempty with ⟨v, hv⟩
    exact ⟨⟨v, hv⟩⟩
  letI : Subsingleton T.Flap := hsubsingleton
  refine ⟨?_⟩
  intro u v
  exact SimpleGraph.ConnectedComponent.exact (Subsingleton.elim
    ((G.induce T.vertexSetᶜ).connectedComponentMk u)
    ((G.induce T.vertexSetᶜ).connectedComponentMk v))

theorem Triad.complement_connected_iff_subsingleton_flaps
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hnonempty : T.vertexSetᶜ.Nonempty) :
    (G.induce T.vertexSetᶜ).Connected ↔ Subsingleton T.Flap := by
  constructor
  · exact T.subsingleton_flaps_of_complement_connected
  · exact T.complement_connected_of_subsingleton_flaps hnonempty

theorem Triad.flapVertexSet_eq_complement_of_complement_connected
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hconnected : (G.induce T.vertexSetᶜ).Connected)
    (B : T.Flap) :
    T.flapVertexSet B = T.vertexSetᶜ := by
  letI : Subsingleton T.Flap := T.subsingleton_flaps_of_complement_connected hconnected
  refine Set.Subset.antisymm (T.flapVertexSet_subset_complement B) ?_
  intro v hv
  obtain ⟨B', hvB'⟩ := T.exists_flap_containing_vertex_outside hv
  have hB'B : B' = B := Subsingleton.elim B' B
  simpa [hB'B] using hvB'

theorem Triad.subsingleton_flaps_of_flap_complement_subset_feet
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B₀ : T.Flap)
    (hB₀_complement : (T.flapVertexSet B₀)ᶜ ⊆ Set.range feet) :
    Subsingleton T.Flap := by
  classical
  have h_eq_B₀ : forall B : T.Flap, B = B₀ := by
    intro B
    by_contra hB
    obtain ⟨x, hxB⟩ := T.flapVertexSet_nonempty B
    have hx_not_B₀ : x ∉ T.flapVertexSet B₀ := by
      intro hxB₀
      exact Set.disjoint_left.mp
        (T.disjoint_flapVertexSet_of_ne (fun h => hB h.symm)) hxB₀ hxB
    rcases hB₀_complement hx_not_B₀ with ⟨i, rfl⟩
    exact (T.flapVertexSet_subset_complement B hxB) (T.foot_mem_vertexSet i)
  exact ⟨fun B C => (h_eq_B₀ B).trans (h_eq_B₀ C).symm⟩

theorem Triad.complement_connected_of_flap_complement_subset_feet
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B₀ : T.Flap)
    (hB₀_complement : (T.flapVertexSet B₀)ᶜ ⊆ Set.range feet) :
    (G.induce T.vertexSetᶜ).Connected := by
  have hnonempty : T.vertexSetᶜ.Nonempty := by
    obtain ⟨x, hxB₀⟩ := T.flapVertexSet_nonempty B₀
    exact ⟨x, T.flapVertexSet_subset_complement B₀ hxB₀⟩
  exact T.complement_connected_of_subsingleton_flaps hnonempty
    (T.subsingleton_flaps_of_flap_complement_subset_feet B₀ hB₀_complement)

theorem Triad.subsingleton_flaps_of_core_complement_subset_feet
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    {K : Set V}
    (hK_complement : Kᶜ ⊆ Set.range feet)
    (hother_subset :
      forall C : T.Flap, C ≠ D -> T.flapVertexSet C ⊆ Kᶜ) :
    Subsingleton T.Flap := by
  classical
  have h_eq_D : forall C : T.Flap, C = D := by
    intro C
    by_contra hCD
    obtain ⟨x, hxC⟩ := T.flapVertexSet_nonempty C
    have hxK : x ∈ Kᶜ := hother_subset C hCD hxC
    rcases hK_complement hxK with ⟨i, rfl⟩
    exact (T.flapVertexSet_subset_complement C hxC) (T.foot_mem_vertexSet i)
  exact ⟨fun C E => (h_eq_D C).trans (h_eq_D E).symm⟩

theorem Triad.complement_connected_of_core_complement_subset_feet
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    {K : Set V}
    (hK_complement : Kᶜ ⊆ Set.range feet)
    (hother_subset :
      forall C : T.Flap, C ≠ D -> T.flapVertexSet C ⊆ Kᶜ) :
    (G.induce T.vertexSetᶜ).Connected := by
  have hnonempty : T.vertexSetᶜ.Nonempty := by
    obtain ⟨x, hxD⟩ := T.flapVertexSet_nonempty D
    exact ⟨x, T.flapVertexSet_subset_complement D hxD⟩
  exact T.complement_connected_of_subsingleton_flaps hnonempty
    (T.subsingleton_flaps_of_core_complement_subset_feet hK_complement hother_subset)

end Schematic.Math.GraphTheory
