import DominatingFourColour.Prerequisites.EssentialBoundaries

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

theorem Triad.exists_flap_ne_of_not_unique
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {B : T.Flap}
    (hunique : Not (forall C : T.Flap, C = B)) :
    Exists fun D : T.Flap => D ≠ B := by
  by_contra hnone
  exact hunique (by
    intro C
    by_contra hCB
    exact hnone ⟨C, hCB⟩)

theorem RST31LeanTriadData.exists_of_initial_triad_distinguished_choice
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hseed :
      Exists fun T : Triad G feet =>
        Exists fun B : T.Flap => W ⊆ T.flapVertexSet B)
    (hfinish :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet W ->
          W ⊆ T.flapVertexSet B ->
            T.Lean ->
              (forall (U : Triad G feet) (C : U.Flap),
                W ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
                (forall (U : Triad G feet) (C : U.Flap),
                  W ⊆ U.flapVertexSet C ->
                    (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                      T.vertexSet.ncard <= U.vertexSet.ncard) ->
                  Nonempty (RST31LeanTriadData G feet W)) :
    Nonempty (RST31LeanTriadData G feet W) := by
  classical
  obtain ⟨T, B, havoid, hW, hmax, hmin⟩ :=
    RST31FlapChoiceIndex.exists_triad_flap_distinguished_ncard_maximal_minimal
      (G := G) (feet := feet) (W := W) hseed
  exact hfinish havoid hW
    (T.lean_of_distinguished_ncard_maximal_minimal hW hmax hmin) hmax hmin

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hfinish :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            T.Lean ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B -> Nonempty (RST31LeanTriadData G feet ({root} : Set V))) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  obtain ⟨B₀, hrootB₀⟩ := T₀.exists_flap_containing_vertex_outside hroot
  apply RST31LeanTriadData.exists_of_initial_triad_distinguished_choice
    (G := G) (W := ({root} : Set V)) ⟨T₀, B₀, by simpa using hrootB₀⟩
  intro T B havoid hroot_subset hlean hmax hmin
  have hrootB : root ∈ T.flapVertexSet B := hroot_subset (by simp)
  by_cases hunique : forall C : T.Flap, C = B
  · exact ⟨RST31LeanTriadData.of_unique_flap hlean havoid B hunique⟩
  · obtain ⟨D, hDB⟩ := T.exists_flap_ne_of_not_unique hunique
    exact hfinish havoid hrootB hlean hmax hmin D hDB

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_minimal_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hfinish :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            T.Lean ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    (forall E : T.Flap, E ≠ B ->
                      (T.flapVertexSet D).ncard <= (T.flapVertexSet E).ncard) ->
                      Nonempty (RST31LeanTriadData G feet ({root} : Set V))) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  obtain ⟨B₀, hrootB₀⟩ := T₀.exists_flap_containing_vertex_outside hroot
  apply RST31LeanTriadData.exists_of_initial_triad_distinguished_choice
    (G := G) (W := ({root} : Set V)) ⟨T₀, B₀, by simpa using hrootB₀⟩
  intro T B havoid hroot_subset hlean hmax hmin
  have hrootB : root ∈ T.flapVertexSet B := hroot_subset (by simp)
  by_cases hunique : forall C : T.Flap, C = B
  · exact ⟨RST31LeanTriadData.of_unique_flap hlean havoid B hunique⟩
  · obtain ⟨D, hDB, hD_min⟩ :=
      T.exists_other_flap_ncard_minimal hunique
    exact hfinish havoid hrootB hlean hmax hmin D hDB hD_min

theorem RST31LeanTriadData.exists_of_initial_triad_root_profile_choice
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hfinish :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            ({root} : Set V) ⊆ T.flapVertexSet B ->
              T.Lean ->
                (forall (U : Triad G feet) (C : U.Flap),
                  ({root} : Set V) ⊆ U.flapVertexSet C ->
                    U.flapSizeProfileWith C <= T.flapSizeProfileWith B) ->
                  (forall (U : Triad G feet) (C : U.Flap),
                    ({root} : Set V) ⊆ U.flapVertexSet C ->
                      U.flapSizeProfileWith C = T.flapSizeProfileWith B ->
                        T.vertexSet.ncard <= U.vertexSet.ncard) ->
                    (forall T' : Triad G feet,
                      T'.vertexSet ⊆ T.vertexSet ->
                        relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
                          T'.vertexSet) ->
                      (forall T' : Triad G feet,
                        T'.vertexSet ⊂ T.vertexSet ->
                          Exists fun B' : T'.Flap =>
                            ({root} : Set V) ⊆ T'.flapVertexSet B' ∧
                              T.flapSizeProfileWith B <= T'.flapSizeProfileWith B') ->
                        forall D : T.Flap,
                          D ≠ B ->
                            Nonempty (RST31LeanTriadData G feet ({root} : Set V))) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  obtain ⟨T, B, havoid, hrootB, hmax, hmin, hboundary⟩ :=
    RST31FlapChoiceIndex.exists_triad_flap_profile_maximal_minimal_with_boundary_persistence_of_vertex
      (G := G) T₀ hroot
  have hW : ({root} : Set V) ⊆ T.flapVertexSet B := by
    simpa using hrootB
  have hstrict_not_smaller :
      forall T' : Triad G feet,
        T'.vertexSet ⊂ T.vertexSet ->
          Exists fun B' : T'.Flap =>
            ({root} : Set V) ⊆ T'.flapVertexSet B' ∧
              T.flapSizeProfileWith B <= T'.flapSizeProfileWith B' :=
    fun T' hstrict =>
      T.exists_subtriad_profile_not_smaller_of_boundary_persistence
        (W := ({root} : Set V)) hW hboundary T' hstrict
  have hlean : T.Lean :=
    T.lean_of_profile_maximal_minimal_of_strict_subtriad_profile_not_smaller
      hmax hmin hstrict_not_smaller
  by_cases hunique : forall C : T.Flap, C = B
  · exact ⟨RST31LeanTriadData.of_unique_flap hlean havoid B hunique⟩
  · obtain ⟨D, hDB⟩ := T.exists_flap_ne_of_not_unique hunique
    exact hfinish havoid hrootB hW hlean hmax hmin hboundary
      hstrict_not_smaller D hDB

theorem RST31LeanTriadData.exists_of_initial_triad_root_profile_choice_minimal_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hfinish :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            ({root} : Set V) ⊆ T.flapVertexSet B ->
              T.Lean ->
                (forall (U : Triad G feet) (C : U.Flap),
                  ({root} : Set V) ⊆ U.flapVertexSet C ->
                    U.flapSizeProfileWith C <= T.flapSizeProfileWith B) ->
                  (forall (U : Triad G feet) (C : U.Flap),
                    ({root} : Set V) ⊆ U.flapVertexSet C ->
                      U.flapSizeProfileWith C = T.flapSizeProfileWith B ->
                        T.vertexSet.ncard <= U.vertexSet.ncard) ->
                    (forall T' : Triad G feet,
                      T'.vertexSet ⊆ T.vertexSet ->
                        relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
                          T'.vertexSet) ->
                      (forall T' : Triad G feet,
                        T'.vertexSet ⊂ T.vertexSet ->
                          Exists fun B' : T'.Flap =>
                            ({root} : Set V) ⊆ T'.flapVertexSet B' ∧
                              T.flapSizeProfileWith B <= T'.flapSizeProfileWith B') ->
                        forall D : T.Flap,
                          D ≠ B ->
                            (forall E : T.Flap, E ≠ B ->
                              (T.flapVertexSet D).ncard <=
                                (T.flapVertexSet E).ncard) ->
                              Nonempty (RST31LeanTriadData G feet ({root} : Set V))) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  obtain ⟨T, B, havoid, hrootB, hmax, hmin, hboundary⟩ :=
    RST31FlapChoiceIndex.exists_triad_flap_profile_maximal_minimal_with_boundary_persistence_of_vertex
      (G := G) T₀ hroot
  have hW : ({root} : Set V) ⊆ T.flapVertexSet B := by
    simpa using hrootB
  have hstrict_not_smaller :
      forall T' : Triad G feet,
        T'.vertexSet ⊂ T.vertexSet ->
          Exists fun B' : T'.Flap =>
            ({root} : Set V) ⊆ T'.flapVertexSet B' ∧
              T.flapSizeProfileWith B <= T'.flapSizeProfileWith B' :=
    fun T' hstrict =>
      T.exists_subtriad_profile_not_smaller_of_boundary_persistence
        (W := ({root} : Set V)) hW hboundary T' hstrict
  have hlean : T.Lean :=
    T.lean_of_profile_maximal_minimal_of_strict_subtriad_profile_not_smaller
      hmax hmin hstrict_not_smaller
  by_cases hunique : forall C : T.Flap, C = B
  · exact ⟨RST31LeanTriadData.of_unique_flap hlean havoid B hunique⟩
  · obtain ⟨D, hDB, hD_min⟩ :=
      T.exists_other_flap_ncard_minimal hunique
    exact hfinish havoid hrootB hW hlean hmax hmin hboundary
      hstrict_not_smaller D hDB hD_min

theorem RST31LeanTriadData.exists_of_initial_triad_root_choice_other_flap_pair_paths
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hwitness_of_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                U.flapSizeProfileWith C <= T.flapSizeProfileWith B) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  U.flapSizeProfileWith C = T.flapSizeProfileWith B ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                (forall T' : Triad G feet,
                  T'.vertexSet ⊆ T.vertexSet ->
                    relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ⊆
                      T'.vertexSet) ->
                  forall D : T.Flap,
                    D ≠ B ->
                      RST31OtherFlapPairPathsWitness (G := G) T B D) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  apply RST31LeanTriadData.exists_of_initial_triad_root_profile_choice
    (G := G) T₀ hroot
  intro T B havoid hrootB _hW _hlean hmax hmin hboundary
    hstrict_not_smaller D hDB
  let W : RST31OtherFlapPairPathsWitness (G := G) T B D :=
    hwitness_of_other_flap havoid hrootB hmax hmin hboundary D hDB
  letI : DecidableEq W.H.verts := Classical.decEq W.H.verts
  exact ⟨
    RST31LeanTriadData.of_profile_maximal_minimal_boundary_tree_root_pair_paths_other_flap_singleton
      (G := G) hno hfeet_injective havoid hrootB hDB hmax hmin
      hstrict_not_smaller W.tree W.feet_mem W.apex_not_foot
      W.pair_path_through_apex W.verts_subset W.boundary_inter_ncard_le⟩

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_other_flap_pair_paths
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hwitness_of_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    RST31OtherFlapPairPathsWitness (G := G) T B D) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  apply RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice
    (G := G) T₀ hroot
  intro T B havoid hrootB hlean hmax hmin D hDB
  let W : RST31OtherFlapPairPathsWitness (G := G) T B D :=
    hwitness_of_other_flap havoid hrootB hmax hmin D hDB
  letI : DecidableEq W.H.verts := Classical.decEq W.H.verts
  exact ⟨
    RST31LeanTriadData.of_distinguished_ncard_maximal_minimal_boundary_tree_root_pair_paths_other_flap_singleton
      (G := G) hno hfeet_injective havoid hrootB hDB hmax hmin
      W.tree W.feet_mem W.apex_not_foot W.pair_path_through_apex
      W.verts_subset W.boundary_inter_ncard_le⟩

theorem RST31LeanTriadData.exists_of_initial_triad_flap_distinguished_choice_blocked_core
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (B₀ : T₀.Flap)
    (hwitness_of_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet (T₀.flapVertexSet B₀) ->
          T₀.flapVertexSet B₀ ⊆ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              T₀.flapVertexSet B₀ ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                T₀.flapVertexSet B₀ ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    RST31OtherFlapBlockedCoreWitness (G := G) T D) :
    Nonempty (RST31LeanTriadData G feet (T₀.flapVertexSet B₀)) := by
  classical
  apply RST31LeanTriadData.exists_of_initial_triad_distinguished_choice
    (G := G) (W := T₀.flapVertexSet B₀) ⟨T₀, B₀, subset_rfl⟩
  intro T B havoid hW hlean hmax hmin
  by_cases hunique : forall C : T.Flap, C = B
  · exact ⟨RST31LeanTriadData.of_unique_flap hlean havoid B hunique⟩
  · obtain ⟨D, hDB⟩ := T.exists_flap_ne_of_not_unique hunique
    let W : RST31OtherFlapBlockedCoreWitness (G := G) T D :=
      hwitness_of_other_flap havoid hW hmax hmin D hDB
    exact ⟨RST31LeanTriadData.of_blocked_core_unique_flap
      (G := G) hno hfeet_injective hlean havoid D
      W.closed W.feet_not_mem W.core_nonempty W.boundary_ncard_le
      W.other_flap_subset_compl⟩

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_blocked_core
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hwitness_of_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    RST31OtherFlapBlockedCoreWitness (G := G) T D) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  apply RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice
    (G := G) T₀ hroot
  intro T B havoid hrootB hlean hmax hmin D hDB
  let W : RST31OtherFlapBlockedCoreWitness (G := G) T D :=
    hwitness_of_other_flap havoid hrootB hmax hmin D hDB
  exact ⟨
    RST31LeanTriadData.of_blocked_core_unique_flap
      (G := G) hno hfeet_injective hlean havoid D
      W.closed W.feet_not_mem W.core_nonempty W.boundary_ncard_le
      W.other_flap_subset_compl⟩

theorem RST31LeanTriadData.exists_of_initial_triad_flap_distinguished_choice_essential_component_pair_paths
    [Fintype V]
    {feet : Fin 3 -> V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (B₀ : T₀.Flap)
    (hwitness_of_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet (T₀.flapVertexSet B₀) ->
          T₀.flapVertexSet B₀ ⊆ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              T₀.flapVertexSet B₀ ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                T₀.flapVertexSet B₀ ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    RST31OtherFlapEssentialComponentPairPathsWitness (G := G) T D) :
    Nonempty (RST31LeanTriadData G feet (T₀.flapVertexSet B₀)) := by
  classical
  apply RST31LeanTriadData.exists_of_initial_triad_distinguished_choice
    (G := G) (W := T₀.flapVertexSet B₀) ⟨T₀, B₀, subset_rfl⟩
  intro T B havoid hW hlean hmax hmin
  by_cases hunique : forall C : T.Flap, C = B
  · exact ⟨RST31LeanTriadData.of_unique_flap hlean havoid B hunique⟩
  · obtain ⟨D, hDB⟩ := T.exists_flap_ne_of_not_unique hunique
    let Y : RST31OtherFlapEssentialComponentPairPathsWitness (G := G) T D :=
      hwitness_of_other_flap havoid hW hmax hmin D hDB
    exact ⟨Y.toRST31LeanTriadData
      (G := G) hno hfeet_injective hlean havoid⟩

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_essential_component_pair_paths
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hwitness_of_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    RST31OtherFlapEssentialComponentPairPathsWitness (G := G) T D) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  apply RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice
    (G := G) T₀ hroot
  intro T B havoid hrootB hlean hmax hmin D hDB
  let Y : RST31OtherFlapEssentialComponentPairPathsWitness (G := G) T D :=
    hwitness_of_other_flap havoid hrootB hmax hmin D hDB
  exact ⟨Y.toRST31LeanTriadData
    (G := G) hno hfeet_injective hlean havoid⟩

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_component_triad_witness
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hboundary_essential_of_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    forall E : T.Flap, E ≠ D ->
                      relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
                        {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    (hwitness_of_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    forall C :
                      (G.induce
                        ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent,
                      T.flapVertexSet D ⊆ induceComponentSupport (G := G) C ->
                        Exists fun T' : Triad G feet =>
                          T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ∧
                            (relativeVertexBoundary G (induceComponentSupport (G := G) C)
                              {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
                                T'.vertexSet).ncard <= 3) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  apply RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice
    (G := G) T₀ hroot
  intro T B havoid hrootB hlean hmax hmin D hDB
  exact ⟨
    RST31LeanTriadData.of_boundaries_essential_and_component_triad_witness
      (G := G) hno hfeet_injective hlean havoid D
      (hboundary_essential_of_other_flap havoid hrootB hmax hmin D hDB)
      (hwitness_of_other_flap havoid hrootB hmax hmin D hDB)⟩

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_minimal_other_flap_component_triad_witness
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hboundary_essential_of_minimal_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    (forall E : T.Flap, E ≠ B ->
                      (T.flapVertexSet D).ncard <= (T.flapVertexSet E).ncard) ->
                      forall E : T.Flap, E ≠ D ->
                        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
                          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    (hwitness_of_minimal_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    (forall E : T.Flap, E ≠ B ->
                      (T.flapVertexSet D).ncard <= (T.flapVertexSet E).ncard) ->
                      forall C :
                        (G.induce
                          ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent,
                        T.flapVertexSet D ⊆ induceComponentSupport (G := G) C ->
                          Exists fun T' : Triad G feet =>
                            T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ∧
                              (relativeVertexBoundary G (induceComponentSupport (G := G) C)
                                {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
                                  T'.vertexSet).ncard <= 3) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  apply
    RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_minimal_other_flap
      (G := G) T₀ hroot
  intro T B havoid hrootB hlean hmax hmin D hDB hD_min
  exact ⟨
    RST31LeanTriadData.of_boundaries_essential_and_component_triad_witness
      (G := G) hno hfeet_injective hlean havoid D
      (hboundary_essential_of_minimal_other_flap
        havoid hrootB hmax hmin D hDB hD_min)
      (hwitness_of_minimal_other_flap
        havoid hrootB hmax hmin D hDB hD_min)⟩

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_minimal_other_flap_nonfoot_boundary_vertex_witness
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hboundary_essential_of_minimal_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    (forall E : T.Flap, E ≠ B ->
                      (T.flapVertexSet D).ncard <= (T.flapVertexSet E).ncard) ->
                      forall E : T.Flap, E ≠ D ->
                        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
                          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    (hwitness_of_minimal_other_flap_nonfoot_vertex :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    (forall E : T.Flap, E ≠ B ->
                      (T.flapVertexSet D).ncard <= (T.flapVertexSet E).ncard) ->
                      forall C :
                        (G.induce
                          ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent,
                        T.flapVertexSet D ⊆ induceComponentSupport (G := G) C ->
                          forall x : V,
                            x ∈ relativeVertexBoundary G (induceComponentSupport (G := G) C)
                              {v : V | T.EssentialWithin (T.flapVertexSet D) v} ->
                              x ∈ T.vertexSet ->
                                x ∉ Set.range feet ->
                                  Exists fun T' : Triad G feet =>
                                    T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ∧
                                      (relativeVertexBoundary G
                                        (induceComponentSupport (G := G) C)
                                        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
                                          T'.vertexSet).ncard <= 3) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  apply
    RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_minimal_other_flap
      (G := G) T₀ hroot
  intro T B havoid hrootB hlean hmax hmin D hDB hD_min
  exact ⟨
    RST31LeanTriadData.of_boundaries_essential_and_nonfoot_boundary_vertex_witness
      (G := G) hno hfeet_injective hlean havoid D
      (hboundary_essential_of_minimal_other_flap
        havoid hrootB hmax hmin D hDB hD_min)
      (hwitness_of_minimal_other_flap_nonfoot_vertex
        havoid hrootB hmax hmin D hDB hD_min)⟩

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_minimal_other_flap_nonfoot_boundary
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hboundary_essential_of_minimal_other_flap :
      forall {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet ({root} : Set V) ->
          root ∈ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              ({root} : Set V) ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                ({root} : Set V) ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    (forall E : T.Flap, E ≠ B ->
                      (T.flapVertexSet D).ncard <= (T.flapVertexSet E).ncard) ->
                      forall E : T.Flap, E ≠ D ->
                        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
                          {v : V | T.EssentialWithin (T.flapVertexSet D) v}) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  apply
    RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_minimal_other_flap
      (G := G) T₀ hroot
  intro T B havoid hrootB hlean hmax hmin D hDB hD_min
  exact ⟨
    RST31LeanTriadData.of_boundaries_essential_and_nonfoot_boundary
      (G := G) hno hfeet_injective hlean havoid D
      (hboundary_essential_of_minimal_other_flap
        havoid hrootB hmax hmin D hDB hD_min)⟩

theorem RST31Statement.of_distinguished_choice_minimal_other_flap_nonfoot_boundary
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hboundary_essential_of_minimal_other_flap :
      forall {T₀ : Triad G feet} {B₀ : T₀.Flap}
        {T : Triad G feet} {B : T.Flap},
        T.AvoidsSet (T₀.flapVertexSet B₀) ->
          T₀.flapVertexSet B₀ ⊆ T.flapVertexSet B ->
            (forall (U : Triad G feet) (C : U.Flap),
              T₀.flapVertexSet B₀ ⊆ U.flapVertexSet C ->
                (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard) ->
              (forall (U : Triad G feet) (C : U.Flap),
                T₀.flapVertexSet B₀ ⊆ U.flapVertexSet C ->
                  (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
                    T.vertexSet.ncard <= U.vertexSet.ncard) ->
                forall D : T.Flap,
                  D ≠ B ->
                    (forall E : T.Flap, E ≠ B ->
                      (T.flapVertexSet D).ncard <= (T.flapVertexSet E).ncard) ->
                      forall E : T.Flap, E ≠ D ->
                        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
                          {v : V | T.EssentialWithin (T.flapVertexSet D) v}) :
    RST31Statement G feet := by
  classical
  intro T₀ B₀ hno
  obtain ⟨T, B, havoid, hW, hmax, hmin⟩ :=
    RST31FlapChoiceIndex.exists_triad_flap_distinguished_ncard_maximal_minimal
      (G := G) (feet := feet)
      (W := T₀.flapVertexSet B₀)
      ⟨T₀, B₀, subset_rfl⟩
  have hlean : T.Lean :=
    T.lean_of_distinguished_ncard_maximal_minimal hW hmax hmin
  by_cases hunique : forall C : T.Flap, C = B
  · exact ⟨RST31LeanTriadData.of_unique_flap hlean havoid B hunique⟩
  · obtain ⟨D, hDB, hD_min⟩ :=
      T.exists_other_flap_ncard_minimal hunique
    exact ⟨
      RST31LeanTriadData.of_boundaries_essential_and_nonfoot_boundary
        (G := G) hno hfeet_injective hlean havoid D
        (hboundary_essential_of_minimal_other_flap
          havoid hW hmax hmin D hDB hD_min)⟩

theorem RST31Statement.of_profile_choice_minimal_other_flap_nonfoot_boundary
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet) :
    RST31Statement G feet := by
  classical
  intro T₀ B₀ hno
  obtain ⟨T, B, havoid, hW, hmax, hmin, hboundary⟩ :=
    RST31FlapChoiceIndex.exists_triad_flap_profile_maximal_minimal_with_boundary_persistence
      (G := G) (feet := feet)
      (W := T₀.flapVertexSet B₀)
      ⟨T₀, B₀, subset_rfl⟩
  have hstrict_not_smaller :
      forall T' : Triad G feet,
        T'.vertexSet ⊂ T.vertexSet ->
          Exists fun B' : T'.Flap =>
            T₀.flapVertexSet B₀ ⊆ T'.flapVertexSet B' ∧
              T.flapSizeProfileWith B <= T'.flapSizeProfileWith B' :=
    fun T' hstrict =>
      T.exists_subtriad_profile_not_smaller_of_boundary_persistence
        (W := T₀.flapVertexSet B₀) hW hboundary T' hstrict
  have hlean : T.Lean :=
    T.lean_of_profile_maximal_minimal_of_strict_subtriad_profile_not_smaller
      hmax hmin hstrict_not_smaller
  by_cases hunique : forall C : T.Flap, C = B
  · exact ⟨RST31LeanTriadData.of_unique_flap hlean havoid B hunique⟩
  · obtain ⟨D, hDB, hD_min⟩ :=
      T.exists_other_flap_ncard_minimal hunique
    have hboundary_essential :
        forall E : T.Flap, E ≠ D ->
          relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
            {v : V | T.EssentialWithin (T.flapVertexSet D) v} :=
      T.flap_boundaries_essentialWithin_of_profile_maximal_replacement_flap_growth
        hW hDB hD_min hmax
    exact ⟨
      RST31LeanTriadData.of_boundaries_essential_and_nonfoot_boundary
        (G := G) hno hfeet_injective hlean havoid D hboundary_essential⟩

theorem rst_planar_or_rst_lean_triad_data_of_legless_tripod
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet)
    (hlegless : Nonempty (LeglessTripod G feet)) :
    IsPlanar G ∨ Nonempty (RSTLeanTriadData G feet root) := by
  classical
  rcases hlegless with ⟨T⟩
  exact Or.inr
    ((RST31Statement.of_profile_choice_minimal_other_flap_nonfoot_boundary
      (G := G) hfeet_injective).to_rstLeanTriadData_of_legless_tripod_four_connected
        hG hfeet_injective T hroot_not_feet)

theorem rst_planar_or_rst_lean_triad_data_of_tripod_legless
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet)
    (hlegless : Exists fun H : Tripod G feet => H.Legless) :
    IsPlanar G ∨ Nonempty (RSTLeanTriadData G feet root) := by
  classical
  rcases hlegless with ⟨H, hH⟩
  exact rst_planar_or_rst_lean_triad_data_of_legless_tripod
    (G := G) hG hfeet_injective hroot_not_feet
    ⟨H.toLeglessTripod hH hfeet_injective⟩

theorem rst_planar_or_rst_lean_triad_data_of_rst34_rst35
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (h34 : RST34LeglessTripodStatement G feet)
    (h35 : RST35Statement G feet)
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet) :
    IsPlanar G ∨ Nonempty (RSTLeanTriadData G feet root) :=
  rst_planar_or_rst_lean_triad_data_of_literal_rst_inputs
    (G := G)
    (RST31Statement.of_profile_choice_minimal_other_flap_nonfoot_boundary
      (G := G) hfeet_injective)
    h34 h35 hG hfeet_injective hroot_not_feet

/-- The RST triad-data alternative routed through the completed general
GM IX `(2.4)` theorem rather than the legacy three-boundary endpoint. -/
theorem rst_planar_or_rst_lean_triad_data_of_GMIX24Statement
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (hGM : GeneralSociety.GMIX24Statement (V := V))
    (hG : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet) :
    IsPlanar G ∨ Nonempty (RSTLeanTriadData G feet root) :=
  rst_planar_or_rst_lean_triad_data_of_rst34_rst35
    (G := G)
    (RST34LeglessTripodStatement.of_trimPositiveLeg_full_rerouting
      (G := G) hfeet_injective)
    (RST35Statement.of_GMIX24Statement_fourConnected
      (G := G) hGM hG hfeet_injective)
    hG hfeet_injective hroot_not_feet


end Schematic.Math.GraphTheory
