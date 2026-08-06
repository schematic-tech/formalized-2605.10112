import DominatingFourColour.Prerequisites.TripodMinimal.FlapProfiles

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
theorem exists_profile_maximal_of_finite
    {α β : Type*}
    [LinearOrder β]
    {P : α -> Prop}
    (hfinite : {x : α | P x}.Finite)
    (hnonempty : Exists P)
    (profile : α -> β) :
    Exists fun x : α => P x ∧ forall y : α, P y -> profile y <= profile x := by
  rcases hnonempty with ⟨x₀, hx₀⟩
  obtain ⟨x, hx, hmax⟩ :=
    Set.exists_max_image {x : α | P x} profile hfinite ⟨x₀, hx₀⟩
  exact ⟨x, hx, hmax⟩

abbrev RST31FlapChoiceIndex (G : SimpleGraph V) :=
  Sigma fun X : Set V => (G.induce Xᶜ).ConnectedComponent

def RST31FlapChoiceIndex.IsCandidate
    (G : SimpleGraph V)
    (feet : Fin 3 -> V)
    (W : Set V)
    (I : RST31FlapChoiceIndex G) : Prop :=
  Exists fun T : Triad G feet =>
    T.vertexSet = I.1 ∧
      T.AvoidsSet W ∧
        W ⊆ induceComponentSupport (G := G) I.2

noncomputable def RST31FlapChoiceIndex.profile
    [Fintype V]
    (G : SimpleGraph V)
    (I : RST31FlapChoiceIndex G) :
    List Nat := by
  classical
  rcases I with ⟨X, C⟩
  letI : Fintype (Xᶜ : Set V) := (Xᶜ).toFinite.fintype
  exact
    (induceComponentSupport (G := G) C).ncard ::
      Multiset.sort
        (((Finset.univ.erase C :
            Finset (G.induce Xᶜ).ConnectedComponent).val.map
          fun D => (induceComponentSupport (G := G) D).ncard))
        (fun a b : Nat => b <= a)

noncomputable def RST31FlapChoiceIndex.distinguishedSize
    (G : SimpleGraph V)
    (I : RST31FlapChoiceIndex G) :
    Nat :=
  (induceComponentSupport (G := G) I.2).ncard

theorem RST31FlapChoiceIndex.candidate_of_triad_flap
    {feet : Fin 3 -> V}
    {W : Set V}
    (T : Triad G feet)
    (B : T.Flap)
    (hW : W ⊆ T.flapVertexSet B) :
    RST31FlapChoiceIndex.IsCandidate G feet W ⟨T.vertexSet, B⟩ := by
  refine ⟨T, rfl, ?_, hW⟩
  rw [Triad.AvoidsSet, Set.disjoint_left]
  intro v hvT hvW
  exact (T.flapVertexSet_subset_complement B (hW hvW)) hvT

theorem RST31FlapChoiceIndex.exists_profile_maximal
    [Fintype V]
    (feet : Fin 3 -> V)
    (W : Set V)
    (hnonempty :
      Exists fun I : RST31FlapChoiceIndex G =>
        RST31FlapChoiceIndex.IsCandidate G feet W I) :
    Exists fun I : RST31FlapChoiceIndex G =>
      RST31FlapChoiceIndex.IsCandidate G feet W I ∧
        forall J : RST31FlapChoiceIndex G,
          RST31FlapChoiceIndex.IsCandidate G feet W J ->
            RST31FlapChoiceIndex.profile G J <=
              RST31FlapChoiceIndex.profile G I := by
  classical
  letI : Fintype (RST31FlapChoiceIndex G) := by
    dsimp [RST31FlapChoiceIndex]
    infer_instance
  exact exists_profile_maximal_of_finite
    (P := RST31FlapChoiceIndex.IsCandidate G feet W)
    (Set.toFinite _)
    hnonempty
    (RST31FlapChoiceIndex.profile G)

theorem exists_profile_maximal_minimal_of_finite
    {α β γ : Type*}
    [LinearOrder β]
    [LinearOrder γ]
    {P : α -> Prop}
    (hfinite : {x : α | P x}.Finite)
    (hnonempty : Exists P)
    (profile : α -> β)
    (size : α -> γ) :
    Exists fun x : α =>
      P x ∧
        (forall y : α, P y -> profile y <= profile x) ∧
          forall y : α, P y -> profile y = profile x -> size x <= size y := by
  rcases exists_profile_maximal_of_finite hfinite hnonempty profile with
    ⟨x₀, hx₀, hmax₀⟩
  let M : Set α := {x | P x ∧ profile x = profile x₀}
  have hM_finite : M.Finite := by
    exact hfinite.subset (by
      intro x hx
      exact hx.1)
  have hM_nonempty : M.Nonempty := ⟨x₀, hx₀, rfl⟩
  obtain ⟨x, hxM, hmin⟩ :=
    Set.exists_min_image M size hM_finite hM_nonempty
  refine ⟨x, hxM.1, ?_, ?_⟩
  · intro y hy
    have hprofile_y : profile y <= profile x₀ := hmax₀ y hy
    simpa [hxM.2] using hprofile_y
  · intro y hy hprofile_y
    exact hmin y ⟨hy, hprofile_y.trans hxM.2⟩

theorem RST31FlapChoiceIndex.exists_profile_maximal_of_triad_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    (T₀ : Triad G feet)
    (B₀ : T₀.Flap) :
    Exists fun I : RST31FlapChoiceIndex G =>
      RST31FlapChoiceIndex.IsCandidate G feet (T₀.flapVertexSet B₀) I ∧
        forall J : RST31FlapChoiceIndex G,
          RST31FlapChoiceIndex.IsCandidate G feet (T₀.flapVertexSet B₀) J ->
            RST31FlapChoiceIndex.profile G J <=
              RST31FlapChoiceIndex.profile G I := by
  exact RST31FlapChoiceIndex.exists_profile_maximal
    (G := G) feet (T₀.flapVertexSet B₀)
    ⟨⟨T₀.vertexSet, B₀⟩,
      RST31FlapChoiceIndex.candidate_of_triad_flap
        (G := G) T₀ B₀ subset_rfl⟩

theorem RST31FlapChoiceIndex.exists_triad_flap_profile_maximal
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hnonempty :
      Exists fun T : Triad G feet =>
        Exists fun B : T.Flap => W ⊆ T.flapVertexSet B) :
    Exists fun T : Triad G feet =>
      Exists fun B : T.Flap =>
        T.AvoidsSet W ∧
          W ⊆ T.flapVertexSet B ∧
            forall (T' : Triad G feet) (B' : T'.Flap),
              W ⊆ T'.flapVertexSet B' ->
                T'.flapSizeProfileWith B' <= T.flapSizeProfileWith B := by
  classical
  obtain ⟨T₀, B₀, hW₀⟩ := hnonempty
  obtain ⟨I, hI_candidate, hI_max⟩ :=
    RST31FlapChoiceIndex.exists_profile_maximal
      (G := G) feet W
      ⟨⟨T₀.vertexSet, B₀⟩,
        RST31FlapChoiceIndex.candidate_of_triad_flap
          (G := G) T₀ B₀ hW₀⟩
  rcases I with ⟨X, C⟩
  rcases hI_candidate with ⟨T, hTX, havoid, hW⟩
  change T.vertexSet = X at hTX
  subst X
  refine ⟨T, C, havoid, hW, ?_⟩
  intro T' B' hW'
  have hJ_candidate :
      RST31FlapChoiceIndex.IsCandidate G feet W ⟨T'.vertexSet, B'⟩ :=
    RST31FlapChoiceIndex.candidate_of_triad_flap
      (G := G) T' B' hW'
  have hmax :=
    hI_max ⟨T'.vertexSet, B'⟩ hJ_candidate
  simpa [RST31FlapChoiceIndex.profile, Triad.flapSizeProfileWith] using hmax

theorem RST31FlapChoiceIndex.exists_triad_flap_profile_maximal_minimal
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hnonempty :
      Exists fun T : Triad G feet =>
        Exists fun B : T.Flap => W ⊆ T.flapVertexSet B) :
    Exists fun T : Triad G feet =>
      Exists fun B : T.Flap =>
        T.AvoidsSet W ∧
          W ⊆ T.flapVertexSet B ∧
            (forall (U : Triad G feet) (C : U.Flap),
              W ⊆ U.flapVertexSet C ->
                U.flapSizeProfileWith C <= T.flapSizeProfileWith B) ∧
              forall (U : Triad G feet) (C : U.Flap),
                W ⊆ U.flapVertexSet C ->
                  U.flapSizeProfileWith C = T.flapSizeProfileWith B ->
                    T.vertexSet.ncard <= U.vertexSet.ncard := by
  classical
  obtain ⟨T₀, B₀, hW₀⟩ := hnonempty
  obtain ⟨I, hI_candidate, hI_max, hI_min⟩ :=
    exists_profile_maximal_minimal_of_finite
      (P := RST31FlapChoiceIndex.IsCandidate G feet W)
      (Set.toFinite _)
      ⟨⟨T₀.vertexSet, B₀⟩,
        RST31FlapChoiceIndex.candidate_of_triad_flap
          (G := G) T₀ B₀ hW₀⟩
      (RST31FlapChoiceIndex.profile G)
      (fun I : RST31FlapChoiceIndex G => I.1.ncard)
  rcases I with ⟨X, C⟩
  rcases hI_candidate with ⟨T, hTX, havoid, hW⟩
  change T.vertexSet = X at hTX
  subst X
  refine ⟨T, C, havoid, hW, ?_, ?_⟩
  · intro U D hW'
    have hJ_candidate :
        RST31FlapChoiceIndex.IsCandidate G feet W ⟨U.vertexSet, D⟩ :=
      RST31FlapChoiceIndex.candidate_of_triad_flap
        (G := G) U D hW'
    have hmax :=
      hI_max ⟨U.vertexSet, D⟩ hJ_candidate
    simpa [RST31FlapChoiceIndex.profile, Triad.flapSizeProfileWith] using hmax
  · intro U D hW' hprofile_eq
    have hJ_candidate :
        RST31FlapChoiceIndex.IsCandidate G feet W ⟨U.vertexSet, D⟩ :=
      RST31FlapChoiceIndex.candidate_of_triad_flap
        (G := G) U D hW'
    have hprofile_eq' :
        RST31FlapChoiceIndex.profile G ⟨U.vertexSet, D⟩ =
          RST31FlapChoiceIndex.profile G ⟨T.vertexSet, C⟩ := by
      simpa [RST31FlapChoiceIndex.profile, Triad.flapSizeProfileWith] using hprofile_eq
    have hmin := hI_min ⟨U.vertexSet, D⟩ hJ_candidate hprofile_eq'
    simpa using hmin

theorem RST31FlapChoiceIndex.exists_triad_flap_distinguished_ncard_maximal_minimal
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hnonempty :
      Exists fun T : Triad G feet =>
        Exists fun B : T.Flap => W ⊆ T.flapVertexSet B) :
    Exists fun T : Triad G feet =>
      Exists fun B : T.Flap =>
        T.AvoidsSet W ∧
          W ⊆ T.flapVertexSet B ∧
            (forall (U : Triad G feet) (C : U.Flap),
              W ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ∧
              forall (U : Triad G feet) (C : U.Flap),
                W ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard := by
  classical
  obtain ⟨T₀, B₀, hW₀⟩ := hnonempty
  obtain ⟨I, hI_candidate, hI_max, hI_min⟩ :=
    exists_profile_maximal_minimal_of_finite
      (P := RST31FlapChoiceIndex.IsCandidate G feet W)
      (Set.toFinite _)
      ⟨⟨T₀.vertexSet, B₀⟩,
        RST31FlapChoiceIndex.candidate_of_triad_flap
          (G := G) T₀ B₀ hW₀⟩
      (RST31FlapChoiceIndex.distinguishedSize G)
      (fun I : RST31FlapChoiceIndex G => I.1.ncard)
  rcases I with ⟨X, C⟩
  rcases hI_candidate with ⟨T, hTX, havoid, hW⟩
  change T.vertexSet = X at hTX
  subst X
  refine ⟨T, C, havoid, hW, ?_, ?_⟩
  · intro U D hW'
    have hJ_candidate :
        RST31FlapChoiceIndex.IsCandidate G feet W ⟨U.vertexSet, D⟩ :=
      RST31FlapChoiceIndex.candidate_of_triad_flap
        (G := G) U D hW'
    have hmax :=
      hI_max ⟨U.vertexSet, D⟩ hJ_candidate
    simpa [RST31FlapChoiceIndex.distinguishedSize, Triad.flapVertexSet] using hmax
  · intro U D hW' hncard_eq
    have hJ_candidate :
        RST31FlapChoiceIndex.IsCandidate G feet W ⟨U.vertexSet, D⟩ :=
      RST31FlapChoiceIndex.candidate_of_triad_flap
        (G := G) U D hW'
    have hncard_eq' :
        RST31FlapChoiceIndex.distinguishedSize G ⟨U.vertexSet, D⟩ =
          RST31FlapChoiceIndex.distinguishedSize G ⟨T.vertexSet, C⟩ := by
      simpa [RST31FlapChoiceIndex.distinguishedSize, Triad.flapVertexSet] using hncard_eq
    have hmin := hI_min ⟨U.vertexSet, D⟩ hJ_candidate hncard_eq'
    simpa using hmin

theorem RST31FlapChoiceIndex.exists_triad_flap_distinguished_ncard_maximal_minimal_of_vertex
    [Fintype V]
    {feet : Fin 3 -> V}
    (T₀ : Triad G feet)
    {root : V}
    (hroot : root ∉ T₀.vertexSet) :
    Exists fun T : Triad G feet =>
      Exists fun B : T.Flap =>
        T.AvoidsSet ({root} : Set V) ∧
          root ∈ T.flapVertexSet B ∧
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ∧
              forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard := by
  obtain ⟨B₀, hrootB₀⟩ := T₀.exists_flap_containing_vertex_outside hroot
  have hsingle :
      ({root} : Set V) ⊆ T₀.flapVertexSet B₀ := by
    intro v hv
    have hvroot : v = root := by
      simpa using hv
    simpa [hvroot] using hrootB₀
  obtain ⟨T, B, havoid, hroot_subset, hmax, hmin⟩ :=
    RST31FlapChoiceIndex.exists_triad_flap_distinguished_ncard_maximal_minimal
      (G := G) (feet := feet)
      (W := ({root} : Set V))
      ⟨T₀, B₀, hsingle⟩
  refine ⟨T, B, havoid, ?_, hmax, hmin⟩
  exact hroot_subset (by simp)

theorem Triad.lean_of_profile_maximal_of_strict_subtriad_profile_larger
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B : T.Flap}
    (hmax :
      forall (T' : Triad G feet) (B' : T'.Flap),
        W ⊆ T'.flapVertexSet B' ->
          T'.flapSizeProfileWith B' <= T.flapSizeProfileWith B)
    (hstrict_larger :
      forall T' : Triad G feet,
        T'.vertexSet ⊂ T.vertexSet ->
          Exists fun B' : T'.Flap =>
            W ⊆ T'.flapVertexSet B' ∧
              T.flapSizeProfileWith B < T'.flapSizeProfileWith B') :
    T.Lean := by
  rw [Triad.lean_iff_no_strict_subtriad]
  rintro ⟨T', hstrict⟩
  obtain ⟨B', hW', hlt⟩ := hstrict_larger T' hstrict
  exact (not_lt_of_ge (hmax T' B' hW')) hlt

theorem Triad.lean_of_profile_maximal_minimal_of_strict_subtriad_profile_not_smaller
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    {B : T.Flap}
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (hmin :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C = T.flapSizeProfileWith B ->
            T.vertexSet.ncard <= U.vertexSet.ncard)
    (hstrict_not_smaller :
      forall T' : Triad G feet,
        T'.vertexSet ⊂ T.vertexSet ->
          Exists fun B' : T'.Flap =>
            W ⊆ T'.flapVertexSet B' ∧
              T.flapSizeProfileWith B <= T'.flapSizeProfileWith B') :
    T.Lean := by
  rw [Triad.lean_iff_no_strict_subtriad]
  rintro ⟨T', hstrict⟩
  obtain ⟨B', hW', hprofile_ge⟩ := hstrict_not_smaller T' hstrict
  have hprofile_le : T'.flapSizeProfileWith B' <= T.flapSizeProfileWith B :=
    hmax T' B' hW'
  have hprofile_eq : T'.flapSizeProfileWith B' = T.flapSizeProfileWith B :=
    le_antisymm hprofile_le hprofile_ge
  have hmin_card : T.vertexSet.ncard <= T'.vertexSet.ncard :=
    hmin T' B' hW' hprofile_eq
  have hstrict_card : T'.vertexSet.ncard < T.vertexSet.ncard :=
    Set.ncard_lt_ncard hstrict
  omega


end Schematic.Math.GraphTheory
