import DominatingFourColour.Prerequisites.RSTFlaps.ProfileGrowth

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

def Triad.EssentialWithin
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (X : Set V)
    (v : V) : Prop :=
  forall T' : Triad G feet, T'.vertexSet ⊆ T.vertexSet ∪ X -> v ∈ T'.vertexSet

theorem Triad.mem_vertexSet_of_essentialWithin
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {X : Set V}
    {v : V}
    (hv : T.EssentialWithin X v) :
    v ∈ T.vertexSet := by
  exact hv T (by
    intro x hx
    exact Or.inl hx)

theorem Triad.foot_essentialWithin
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (X : Set V)
    (i : Fin 3) :
    T.EssentialWithin X (feet i) := by
  intro T' _hsubset
  exact T'.foot_mem_vertexSet i

theorem Triad.essentialWithin_set_subset_vertexSet
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (X : Set V) :
    {v : V | T.EssentialWithin X v} ⊆ T.vertexSet := by
  intro v hv
  exact T.mem_vertexSet_of_essentialWithin hv

theorem Triad.EssentialWithin.mono
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {X Y : Set V}
    {v : V}
    (hv : T.EssentialWithin Y v)
    (hXY : X ⊆ Y) :
    T.EssentialWithin X v := by
  intro T' hT'_subset
  exact hv T' (by
    intro z hz
    rcases hT'_subset hz with hzT | hzX
    · exact Or.inl hzT
    · exact Or.inr (hXY hzX))

theorem Triad.essentialWithin_set_mono
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {X Y : Set V}
    (hXY : X ⊆ Y) :
    {v : V | T.EssentialWithin Y v} ⊆
      {v : V | T.EssentialWithin X v} := by
  intro v hv
  exact hv.mono hXY

theorem Triad.range_feet_subset_essentialWithin_set
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (X : Set V) :
    Set.range feet ⊆ {v : V | T.EssentialWithin X v} := by
  rintro v ⟨i, rfl⟩
  exact T.foot_essentialWithin X i

theorem Triad.subset_essentialWithin_of_persistent_subset
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {X S : Set V}
    (hpersistent :
      forall T' : Triad G feet,
        T'.vertexSet ⊆ T.vertexSet ∪ X ->
          S ⊆ T'.vertexSet) :
    S ⊆ {v : V | T.EssentialWithin X v} := by
  intro v hv T' hT'_subset
  exact hpersistent T' hT'_subset hv

theorem Triad.flap_boundary_essentialWithin_empty_of_profile_maximal
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B) :
    relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
      {v : V | T.EssentialWithin ∅ v} := by
  exact T.subset_essentialWithin_of_persistent_subset (X := ∅)
    (S := relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet) (by
      intro T' hT'_subset
      have hT'_subset_T : T'.vertexSet ⊆ T.vertexSet := by
        intro v hv
        have hv_union := hT'_subset hv
        simpa using hv_union
      exact T.flap_boundary_subset_subtriad_of_profile_maximal
        (T' := T') hW hT'_subset_T hmax)

theorem Triad.flap_boundary_essentialWithin_of_profile_maximal_disjoint
    [Fintype V]
    {feet : Fin 3 -> V}
    {W X : Set V}
    {T : Triad G feet}
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hX_disjoint_B : Disjoint X (T.flapVertexSet B))
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B) :
    relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
      {v : V | T.EssentialWithin X v} := by
  intro x hx_boundary T' hT'_subset
  by_contra hxT'
  obtain ⟨B', hW', hlt⟩ :=
    T.exists_flap_profile_larger_of_subtriad_union_omits_flap_boundary_vertex
      (T' := T') hW hT'_subset hX_disjoint_B hx_boundary hxT'
  exact (not_lt_of_ge (hmax T' B' hW')) hlt

theorem Triad.flap_boundary_essentialWithin_of_distinguished_ncard_maximal_disjoint
    [Fintype V]
    {feet : Fin 3 -> V}
    {W X : Set V}
    {T : Triad G feet}
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hX_disjoint_B : Disjoint X (T.flapVertexSet B))
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) :
    relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
      {v : V | T.EssentialWithin X v} := by
  intro x hx_boundary T' hT'_subset
  by_contra hxT'
  obtain ⟨B', hW', hlt⟩ :=
    T.exists_flap_ncard_larger_of_subtriad_union_omits_flap_boundary_vertex
      (T' := T') hW hT'_subset hX_disjoint_B hx_boundary hxT'
  exact (not_lt_of_ge (hmax T' B' hW')) hlt

theorem Triad.flap_boundary_essentialWithin_of_profile_maximal_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B C : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hCB : C ≠ B)
    (hmax :
      forall (U : Triad G feet) (D : U.Flap),
        W ⊆ U.flapVertexSet D ->
          U.flapSizeProfileWith D <= T.flapSizeProfileWith B) :
    relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
      {v : V | T.EssentialWithin (T.flapVertexSet C) v} := by
  exact T.flap_boundary_essentialWithin_of_profile_maximal_disjoint
    hW (T.disjoint_flapVertexSet_of_ne (B := C) (C := B) hCB) hmax

theorem Triad.flap_boundary_essentialWithin_of_profile_maximal_tail_growth
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D E : T.Flap}
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (hgrowth :
      forall (T' : Triad G feet),
        T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ->
          forall {x : V},
            x ∈ relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ->
              x ∉ T'.vertexSet ->
                Exists fun B' : T'.Flap =>
                  W ⊆ T'.flapVertexSet B' ∧
                    T.flapSizeProfileWith B < T'.flapSizeProfileWith B') :
    relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  intro x hx_boundary T' hT'_subset
  by_contra hxT'
  obtain ⟨B', hW', hlt⟩ :=
    hgrowth T' hT'_subset hx_boundary hxT'
  exact (not_lt_of_ge (hmax T' B' hW')) hlt

theorem Triad.flap_boundary_essentialWithin_of_profile_maximal_tail_flap_growth
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D E : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hED : E ≠ D)
    (hEB : E ≠ B)
    (hDB : D ≠ B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (htail_growth_to_profile :
      forall (T' : Triad G feet) (B' E' : T'.Flap),
        W ⊆ T'.flapVertexSet B' ->
          E' ≠ B' ->
            T.flapVertexSet E ⊆ T'.flapVertexSet E' ->
              (T.flapVertexSet E).ncard <
                (T'.flapVertexSet E').ncard ->
                  T.flapSizeProfileWith B < T'.flapSizeProfileWith B') :
    relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundary_essentialWithin_of_profile_maximal_tail_growth
    (B := B) (D := D) (E := E) hmax ?_
  intro T' hT'_subset x hx_boundary hxT'
  obtain ⟨B', hW', hB_subset, hprofile_or_tail⟩ :=
    T.exists_distinguished_profile_larger_or_tail_flap_ncard_larger
      (T' := T') hW hED hEB hDB hT'_subset hx_boundary hxT'
  refine ⟨B', hW', ?_⟩
  rcases hprofile_or_tail with hprofile | ⟨E', hE'B', hE_subset, hE_lt⟩
  · exact hprofile
  · by_cases hB_eq : T.flapVertexSet B = T'.flapVertexSet B'
    · exact htail_growth_to_profile T' B' E' hW' hE'B' hE_subset hE_lt
    · exact Triad.flapSizeProfileWith_lt_of_distinguished_flap_ssubset
        (G := G) (Set.ssubset_iff_subset_ne.mpr ⟨hB_subset, hB_eq⟩)

theorem Triad.flap_boundary_essentialWithin_of_profile_maximal_tail_order
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D E : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hED : E ≠ D)
    (hEB : E ≠ B)
    (hDB : D ≠ B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (htail_growth_to_tail :
      forall (T' : Triad G feet) (B' E' : T'.Flap),
        T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ->
          W ⊆ T'.flapVertexSet B' ->
            T.flapVertexSet B = T'.flapVertexSet B' ->
              E' ≠ B' ->
                T.flapVertexSet E ⊆ T'.flapVertexSet E' ->
                  (T.flapVertexSet E).ncard <
                    (T'.flapVertexSet E').ncard ->
                      T.flapSizeTailWith B < T'.flapSizeTailWith B') :
    relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundary_essentialWithin_of_profile_maximal_tail_growth
    (B := B) (D := D) (E := E) hmax ?_
  intro T' hT'_subset x hx_boundary hxT'
  obtain ⟨B', hW', hB_subset, hprofile_or_tail⟩ :=
    T.exists_distinguished_profile_larger_or_tail_flap_ncard_larger
      (T' := T') hW hED hEB hDB hT'_subset hx_boundary hxT'
  refine ⟨B', hW', ?_⟩
  rcases hprofile_or_tail with hprofile | ⟨E', hE'B', hE_subset, hE_lt⟩
  · exact hprofile
  · by_cases hB_eq : T.flapVertexSet B = T'.flapVertexSet B'
    · exact T.flapSizeProfileWith_lt_of_tailWith_lt_of_distinguished_eq
        (T' := T') (B := B) (B' := B') hB_eq
        (htail_growth_to_tail T' B' E' hT'_subset hW' hB_eq hE'B'
          hE_subset hE_lt)
    · exact Triad.flapSizeProfileWith_lt_of_distinguished_flap_ssubset
        (G := G) (Set.ssubset_iff_subset_ne.mpr ⟨hB_subset, hB_eq⟩)

theorem Triad.flap_boundary_essentialWithin_of_profile_maximal_replacement_flap_growth
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D E : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hED : E ≠ D)
    (hEB : E ≠ B)
    (hDB : D ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B) :
    relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundary_essentialWithin_of_profile_maximal_tail_order
    (B := B) (D := D) (E := E) hW hED hEB hDB hmax ?_
  intro T' B' E' hT'_subset _hW' hB_eq hE'B' hE_subset hE_lt
  exact T.flapSizeTailWith_lt_of_replacement_flap_growth
    (T' := T') (B' := B') (E' := E') hED hEB hDB hD_min
    hT'_subset hB_eq hE'B' hE_subset hE_lt

theorem Triad.flap_boundary_essentialWithin_of_profile_maximal_tail_order_multiset
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D E : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hED : E ≠ D)
    (hEB : E ≠ B)
    (hDB : D ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (hreplacement_tail_le :
      forall (T' : Triad G feet) (B' E' : T'.Flap),
        T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ->
          W ⊆ T'.flapVertexSet B' ->
            T.flapVertexSet B = T'.flapVertexSet B' ->
              E' ≠ B' ->
                T.flapVertexSet E ⊆ T'.flapVertexSet E' ->
                  (T.flapVertexSet E).ncard <
                    (T'.flapVertexSet E').ncard ->
                      (T'.flapVertexSet E').ncard ::ₘ
                          ((T.flapSizeTailWith B : Multiset Nat).erase
                            (T.flapVertexSet D).ncard) <=
                        (T'.flapSizeTailWith B' : Multiset Nat)) :
    relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundary_essentialWithin_of_profile_maximal_tail_order
    (B := B) (D := D) (E := E) hW hED hEB hDB hmax ?_
  intro T' B' E' hT'_subset hW' hB_eq hE'B' hE_subset hE_lt
  exact T.flapSizeTailWith_lt_of_sort_cons_erase_min_multiset_le
    (T' := T') (B' := B') hDB hEB hD_min hE_lt
    (hreplacement_tail_le T' B' E' hT'_subset hW' hB_eq hE'B'
      hE_subset hE_lt)

theorem Triad.flap_boundary_essentialWithin_of_profile_maximal_tail_order_sublistForall₂
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D E : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hED : E ≠ D)
    (hEB : E ≠ B)
    (hDB : D ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (hreplacement_tail_le :
      forall (T' : Triad G feet) (B' E' : T'.Flap),
        T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ->
          W ⊆ T'.flapVertexSet B' ->
            T.flapVertexSet B = T'.flapVertexSet B' ->
              E' ≠ B' ->
                T.flapVertexSet E ⊆ T'.flapVertexSet E' ->
                  (T.flapVertexSet E).ncard <
                    (T'.flapVertexSet E').ncard ->
                      List.SublistForall₂ (fun x y : Nat => x <= y)
                        (Multiset.sort
                          ((T'.flapVertexSet E').ncard ::ₘ
                            ((T.flapSizeTailWith B : Multiset Nat).erase
                              (T.flapVertexSet D).ncard))
                          (fun x y : Nat => y <= x))
                        (T'.flapSizeTailWith B')) :
    relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundary_essentialWithin_of_profile_maximal_tail_order
    (B := B) (D := D) (E := E) hW hED hEB hDB hmax ?_
  intro T' B' E' hT'_subset hW' hB_eq hE'B' hE_subset hE_lt
  exact T.flapSizeTailWith_lt_of_sort_cons_erase_min_sublistForall₂
    (T' := T') (B' := B') hDB hEB hD_min hE_lt
    (hreplacement_tail_le T' B' E' hT'_subset hW' hB_eq hE'B'
      hE_subset hE_lt)

theorem Triad.flap_boundary_essentialWithin_of_profile_maximal_tail_order_drop_replaced_sublistForall₂
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D E : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hED : E ≠ D)
    (hEB : E ≠ B)
    (hDB : D ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    (hE_mem_after_erase :
      (T.flapVertexSet E).ncard ∈
        ((T.flapSizeTailWith B : Multiset Nat).erase
          (T.flapVertexSet D).ncard))
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (hreplacement_tail_le :
      forall (T' : Triad G feet) (B' E' : T'.Flap),
        T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ->
          W ⊆ T'.flapVertexSet B' ->
            T.flapVertexSet B = T'.flapVertexSet B' ->
              E' ≠ B' ->
                T.flapVertexSet E ⊆ T'.flapVertexSet E' ->
                  (T.flapVertexSet E).ncard <
                    (T'.flapVertexSet E').ncard ->
                      List.SublistForall₂ (fun x y : Nat => x <= y)
                        (Multiset.sort
                          ((T'.flapVertexSet E').ncard ::ₘ
                            (((T.flapSizeTailWith B : Multiset Nat).erase
                              (T.flapVertexSet D).ncard).erase
                                (T.flapVertexSet E).ncard))
                          (fun x y : Nat => y <= x))
                        (T'.flapSizeTailWith B')) :
    relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundary_essentialWithin_of_profile_maximal_tail_order
    (B := B) (D := D) (E := E) hW hED hEB hDB hmax ?_
  intro T' B' E' hT'_subset hW' hB_eq hE'B' hE_subset hE_lt
  exact T.flapSizeTailWith_lt_of_sort_cons_erase_min_erase_sublistForall₂
    (T' := T') (B' := B') hDB hD_min hE_mem_after_erase hE_lt
    (hreplacement_tail_le T' B' E' hT'_subset hW' hB_eq hE'B'
      hE_subset hE_lt)

theorem Triad.flap_boundary_essentialWithin_of_distinguished_ncard_maximal_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B C : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hCB : C ≠ B)
    (hmax :
      forall (U : Triad G feet) (D : U.Flap),
        W ⊆ U.flapVertexSet D ->
          (U.flapVertexSet D).ncard <= (T.flapVertexSet B).ncard) :
    relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
      {v : V | T.EssentialWithin (T.flapVertexSet C) v} := by
  exact T.flap_boundary_essentialWithin_of_distinguished_ncard_maximal_disjoint
    hW (T.disjoint_flapVertexSet_of_ne (B := C) (C := B) hCB) hmax

theorem Triad.flap_boundaries_essentialWithin_of_distinguished_and_other_flaps
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard)
    (hother :
      forall E : T.Flap, E ≠ D -> E ≠ B ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v}) :
    forall E : T.Flap, E ≠ D ->
      relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  intro E hED
  by_cases hEB : E = B
  · subst E
    exact T.flap_boundary_essentialWithin_of_distinguished_ncard_maximal_other_flap
      hW hDB hmax
  · exact hother E hED hEB

theorem Triad.flap_boundaries_essentialWithin_of_profile_maximal_tail_growth
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax_ncard :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard)
    (hmax_profile :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (htail_growth_to_profile :
      forall E : T.Flap, E ≠ D -> E ≠ B ->
        forall (T' : Triad G feet) (B' E' : T'.Flap),
          W ⊆ T'.flapVertexSet B' ->
            E' ≠ B' ->
              T.flapVertexSet E ⊆ T'.flapVertexSet E' ->
                (T.flapVertexSet E).ncard <
                  (T'.flapVertexSet E').ncard ->
                    T.flapSizeProfileWith B < T'.flapSizeProfileWith B') :
    forall E : T.Flap, E ≠ D ->
      relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundaries_essentialWithin_of_distinguished_and_other_flaps
    hW hDB hmax_ncard ?_
  intro E hED hEB
  exact T.flap_boundary_essentialWithin_of_profile_maximal_tail_flap_growth
    (B := B) (D := D) (E := E) hW hED hEB hDB hmax_profile
    (htail_growth_to_profile E hED hEB)

theorem Triad.flap_boundaries_essentialWithin_of_profile_maximal_tail_growth'
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax_profile :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (htail_growth_to_profile :
      forall E : T.Flap, E ≠ D -> E ≠ B ->
        forall (T' : Triad G feet) (B' E' : T'.Flap),
          W ⊆ T'.flapVertexSet B' ->
            E' ≠ B' ->
              T.flapVertexSet E ⊆ T'.flapVertexSet E' ->
                (T.flapVertexSet E).ncard <
                  (T'.flapVertexSet E').ncard ->
                    T.flapSizeProfileWith B < T'.flapSizeProfileWith B') :
    forall E : T.Flap, E ≠ D ->
      relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundaries_essentialWithin_of_profile_maximal_tail_growth
    hW hDB ?_ hmax_profile htail_growth_to_profile
  intro U C hWU
  exact Triad.distinguished_ncard_le_of_flapSizeProfileWith_le
    (G := G) (hmax_profile U C hWU)

theorem Triad.flap_boundaries_essentialWithin_of_profile_maximal_tail_order
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax_profile :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (htail_growth_to_tail :
      forall E : T.Flap, E ≠ D -> E ≠ B ->
        forall (T' : Triad G feet) (B' E' : T'.Flap),
          T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ->
            W ⊆ T'.flapVertexSet B' ->
              T.flapVertexSet B = T'.flapVertexSet B' ->
                E' ≠ B' ->
                  T.flapVertexSet E ⊆ T'.flapVertexSet E' ->
                    (T.flapVertexSet E).ncard <
                      (T'.flapVertexSet E').ncard ->
                        T.flapSizeTailWith B < T'.flapSizeTailWith B') :
    forall E : T.Flap, E ≠ D ->
      relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundaries_essentialWithin_of_distinguished_and_other_flaps
    hW hDB ?_ ?_
  · intro U C hWU
    exact Triad.distinguished_ncard_le_of_flapSizeProfileWith_le
      (G := G) (hmax_profile U C hWU)
  · intro E hED hEB
    exact T.flap_boundary_essentialWithin_of_profile_maximal_tail_order
      (B := B) (D := D) (E := E) hW hED hEB hDB hmax_profile
      (htail_growth_to_tail E hED hEB)

theorem Triad.flap_boundaries_essentialWithin_of_profile_maximal_replacement_flap_growth
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    (hmax_profile :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B) :
    forall E : T.Flap, E ≠ D ->
      relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundaries_essentialWithin_of_distinguished_and_other_flaps
    hW hDB ?_ ?_
  · intro U C hWU
    exact Triad.distinguished_ncard_le_of_flapSizeProfileWith_le
      (G := G) (hmax_profile U C hWU)
  · intro E hED hEB
    exact T.flap_boundary_essentialWithin_of_profile_maximal_replacement_flap_growth
      (B := B) (D := D) (E := E) hW hED hEB hDB hD_min hmax_profile

theorem Triad.flap_boundaries_essentialWithin_of_profile_maximal_tail_order_multiset
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    (hmax_profile :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (hreplacement_tail_le :
      forall E : T.Flap, E ≠ D -> E ≠ B ->
        forall (T' : Triad G feet) (B' E' : T'.Flap),
          T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ->
            W ⊆ T'.flapVertexSet B' ->
              T.flapVertexSet B = T'.flapVertexSet B' ->
                E' ≠ B' ->
                  T.flapVertexSet E ⊆ T'.flapVertexSet E' ->
                    (T.flapVertexSet E).ncard <
                      (T'.flapVertexSet E').ncard ->
                        (T'.flapVertexSet E').ncard ::ₘ
                            ((T.flapSizeTailWith B : Multiset Nat).erase
                              (T.flapVertexSet D).ncard) <=
                          (T'.flapSizeTailWith B' : Multiset Nat)) :
    forall E : T.Flap, E ≠ D ->
      relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundaries_essentialWithin_of_distinguished_and_other_flaps
    hW hDB ?_ ?_
  · intro U C hWU
    exact Triad.distinguished_ncard_le_of_flapSizeProfileWith_le
      (G := G) (hmax_profile U C hWU)
  · intro E hED hEB
    exact T.flap_boundary_essentialWithin_of_profile_maximal_tail_order_multiset
      (B := B) (D := D) (E := E) hW hED hEB hDB hD_min
      hmax_profile (hreplacement_tail_le E hED hEB)

theorem Triad.flap_boundaries_essentialWithin_of_profile_maximal_tail_order_sublistForall₂
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    (hmax_profile :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (hreplacement_tail_le :
      forall E : T.Flap, E ≠ D -> E ≠ B ->
        forall (T' : Triad G feet) (B' E' : T'.Flap),
          T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ->
            W ⊆ T'.flapVertexSet B' ->
              T.flapVertexSet B = T'.flapVertexSet B' ->
                E' ≠ B' ->
                  T.flapVertexSet E ⊆ T'.flapVertexSet E' ->
                    (T.flapVertexSet E).ncard <
                      (T'.flapVertexSet E').ncard ->
                        List.SublistForall₂ (fun x y : Nat => x <= y)
                          (Multiset.sort
                            ((T'.flapVertexSet E').ncard ::ₘ
                              ((T.flapSizeTailWith B : Multiset Nat).erase
                                (T.flapVertexSet D).ncard))
                            (fun x y : Nat => y <= x))
                          (T'.flapSizeTailWith B')) :
    forall E : T.Flap, E ≠ D ->
      relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundaries_essentialWithin_of_distinguished_and_other_flaps
    hW hDB ?_ ?_
  · intro U C hWU
    exact Triad.distinguished_ncard_le_of_flapSizeProfileWith_le
      (G := G) (hmax_profile U C hWU)
  · intro E hED hEB
    exact T.flap_boundary_essentialWithin_of_profile_maximal_tail_order_sublistForall₂
      (B := B) (D := D) (E := E) hW hED hEB hDB hD_min
      hmax_profile (hreplacement_tail_le E hED hEB)

theorem Triad.flap_boundaries_essentialWithin_of_profile_maximal_tail_order_drop_replaced_sublistForall₂
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    (hmax_profile :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (hreplacement_tail_le :
      forall E : T.Flap, E ≠ D -> E ≠ B ->
        forall (T' : Triad G feet) (B' E' : T'.Flap),
          T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ->
            W ⊆ T'.flapVertexSet B' ->
              T.flapVertexSet B = T'.flapVertexSet B' ->
                E' ≠ B' ->
                  T.flapVertexSet E ⊆ T'.flapVertexSet E' ->
                    (T.flapVertexSet E).ncard <
                      (T'.flapVertexSet E').ncard ->
                        List.SublistForall₂ (fun x y : Nat => x <= y)
                          (Multiset.sort
                            ((T'.flapVertexSet E').ncard ::ₘ
                              (((T.flapSizeTailWith B : Multiset Nat).erase
                                (T.flapVertexSet D).ncard).erase
                                  (T.flapVertexSet E).ncard))
                            (fun x y : Nat => y <= x))
                          (T'.flapSizeTailWith B')) :
    forall E : T.Flap, E ≠ D ->
      relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  refine T.flap_boundaries_essentialWithin_of_distinguished_and_other_flaps
    hW hDB ?_ ?_
  · intro U C hWU
    exact Triad.distinguished_ncard_le_of_flapSizeProfileWith_le
      (G := G) (hmax_profile U C hWU)
  · intro E hED hEB
    exact T.flap_boundary_essentialWithin_of_profile_maximal_tail_order_drop_replaced_sublistForall₂
      (B := B) (D := D) (E := E) hW hED hEB hDB hD_min
      (T.mem_erase_flapSizeTailWith_of_ne hDB hEB hED) hmax_profile
      (hreplacement_tail_le E hED hEB)

theorem Triad.flapVertexSet_subset_essential_complement_self
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap) :
    T.flapVertexSet D ⊆
      ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ) := by
  intro x hxD hxessential
  have hxT : x ∈ T.vertexSet := hxessential T (by
    intro v hv
    exact Or.inl hv)
  exact (T.flapVertexSet_subset_complement D hxD) hxT

theorem Triad.foot_not_mem_essential_component_support
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap)
    (C : (G.induce
      ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent)
    (i : Fin 3) :
    feet i ∉ induceComponentSupport (G := G) C := by
  intro hfootC
  have hfoot_not_essential :
      feet i ∈ ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ : Set V) :=
    induceComponentSupport_subset (G := G) C hfootC
  exact hfoot_not_essential (T.foot_essentialWithin (T.flapVertexSet D) i)

theorem Triad.exists_essential_component_containing_flap
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap) :
    Exists fun C :
        (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent =>
      T.flapVertexSet D ⊆ induceComponentSupport (G := G) C := by
  exact connected_set_subset_induceComponentSupport
    (G := G)
    (A := {v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)
    (K := T.flapVertexSet D)
    (T.flapVertexSet_connected D)
    (T.flapVertexSet_subset_essential_complement_self D)

theorem Triad.essential_component_boundary_subset_essential
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap)
    (C : (G.induce
      ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent) :
    relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ⊆
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
  intro v hv
  exact hv.1

theorem Triad.essential_component_boundary_subset_vertexSet
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap)
    (C : (G.induce
      ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent) :
    relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ⊆
      T.vertexSet :=
  Set.Subset.trans
    (T.essential_component_boundary_subset_essential D C)
    (T.essentialWithin_set_subset_vertexSet (T.flapVertexSet D))

theorem exists_mem_of_not_subset
    {A B : Set V}
    (h : ¬ A ⊆ B) :
    Exists fun x : V => x ∈ A ∧ x ∉ B := by
  by_contra hnone
  exact h (by
    intro x hxA
    by_contra hxB
    exact hnone ⟨x, hxA, hxB⟩)

theorem Triad.exists_nonfoot_essential_component_boundary_vertex
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap)
    (C : (G.induce
      ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent)
    (hboundary_not_subset_feet :
      ¬ relativeVertexBoundary G (induceComponentSupport (G := G) C)
          {v : V | T.EssentialWithin (T.flapVertexSet D) v} ⊆
        Set.range feet) :
    Exists fun x : V =>
      x ∈ relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∧
        x ∈ T.vertexSet ∧
          x ∉ Set.range feet := by
  obtain ⟨x, hx_boundary, hx_not_feet⟩ :=
    exists_mem_of_not_subset hboundary_not_subset_feet
  exact ⟨x, hx_boundary,
    T.essential_component_boundary_subset_vertexSet D C hx_boundary,
    hx_not_feet⟩

theorem Triad.other_flap_subset_essential_component_complement_of_boundaries_essential
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (hD_subset_C : T.flapVertexSet D ⊆ induceComponentSupport (G := G) C)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v}) :
    forall E : T.Flap, E ≠ D ->
      T.flapVertexSet E ⊆ (induceComponentSupport (G := G) C)ᶜ := by
  intro E hED x hxE hxC
  obtain ⟨y, hyD⟩ := T.flapVertexSet_nonempty D
  have hyC : y ∈ induceComponentSupport (G := G) C := hD_subset_C hyD
  rcases hxC with ⟨hxEss, hxSupp⟩
  rcases hyC with ⟨hyEss, hySupp⟩
  let ux : ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ : Set V) :=
    ⟨x, hxEss⟩
  let vy : ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ : Set V) :=
    ⟨y, hyEss⟩
  have hreach : (G.induce
      ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).Reachable ux vy :=
    C.reachable_of_mem_supp (by simpa [ux] using hxSupp)
      (by simpa [vy] using hySupp)
  have hyE : y ∈ T.flapVertexSet E :=
    reachable_induce_compl_mem_of_closed
      (G := G)
      (S := {v : V | T.EssentialWithin (T.flapVertexSet D) v})
      (K := T.flapVertexSet E)
      (u := ux) (v := vy) hxE
      (T.flapVertexSet_closed_outside_of_boundary_subset
        (B := E) (hboundary_essential E hED))
      hreach
  exact Set.disjoint_left.mp (T.disjoint_flapVertexSet_of_ne hED) hyE hyD

theorem Triad.essential_component_subset_vertexSet_union_flap_of_boundaries_essential
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (hD_subset_C : T.flapVertexSet D ⊆ induceComponentSupport (G := G) C)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v}) :
    induceComponentSupport (G := G) C ⊆ T.vertexSet ∪ T.flapVertexSet D := by
  intro x hxC
  by_cases hxT : x ∈ T.vertexSet
  · exact Or.inl hxT
  · obtain ⟨E, hxE⟩ := T.exists_flap_containing_vertex_outside hxT
    by_cases hED : E = D
    · subst E
      exact Or.inr hxE
    · have hx_not_C :
          x ∈ (induceComponentSupport (G := G) C)ᶜ :=
        T.other_flap_subset_essential_component_complement_of_boundaries_essential
          hD_subset_C hboundary_essential E hED hxE
      exact False.elim (hx_not_C hxC)

theorem Triad.exists_component_neighbor_in_vertexSet_union_flap_of_essential_boundary
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (hD_subset_C : T.flapVertexSet D ⊆ induceComponentSupport (G := G) C)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    {x : V}
    (hx_boundary :
      x ∈ relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v}) :
    Exists fun y : V =>
      y ∈ induceComponentSupport (G := G) C ∧
        y ∈ T.vertexSet ∪ T.flapVertexSet D ∧ G.Adj y x := by
  rcases hx_boundary with ⟨_hx_essential, y, hyC, hyx⟩
  exact ⟨y, hyC,
    T.essential_component_subset_vertexSet_union_flap_of_boundaries_essential
      hD_subset_C hboundary_essential hyC,
    hyx⟩

end Schematic.Math.GraphTheory
