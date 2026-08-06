import DominatingFourColour.Prerequisites.ProfileChoices

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
theorem rst_planar_or_rst_lean_triad_data
    [Fintype V]
    [DecidableRel G.Adj]
    (h_four_connected : IsFourConnected G)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (root : V)
    (hroot_not_feet : root ∉ Set.range feet) :
    IsPlanar G ∨ Nonempty (RSTLeanTriadData G feet root) := by
  classical
  have hfeet_injective : Function.Injective feet :=
    IsTriangle.injective_fin3 h_triangle
  by_cases h_planar : IsPlanar G
  · exact Or.inl h_planar
  · have htripod : Nonempty (Tripod G feet) :=
      (RST35Statement.of_GMIX24Statement_fourConnected
        (G := G) GeneralSociety.GMIX24Statement.source_proof
        h_four_connected hfeet_injective).tripod_of_nonplanar
        (h_four_connected.rst35_noSeparation hfeet_injective) h_planar
    have hlegless : Exists fun H : Tripod G feet => H.Legless :=
      (RST34LeglessTripodStatement.of_trimPositiveLeg_full_rerouting
        (G := G) hfeet_injective) htripod
        (h_four_connected.rst34_noThreeSeparation feet)
    exact rst_planar_or_rst_lean_triad_data_of_tripod_legless
      (G := G) h_four_connected hfeet_injective hroot_not_feet hlegless

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_two_flap_component_triad_witness
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hflaps_two_of_other_flap :
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
                    forall E : T.Flap, E = B ∨ E = D)
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
  intro T B havoid hrootB _hlean hmax hmin D hDB
  exact ⟨
    RST31LeanTriadData.of_distinguished_two_flap_component_triad_witness
      (G := G) hno hfeet_injective havoid (by simpa using hrootB) hDB
      (hflaps_two_of_other_flap havoid hrootB hmax hmin D hDB)
      hmax hmin
      (hwitness_of_other_flap havoid hrootB hmax hmin D hDB)⟩

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_boundary_le_three
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) :=
  RST31LeanTriadData.exists_of_initial_triad_root_profile_choice_minimal_other_flap_nonfoot_boundary
    (G := G) hno hfeet_injective T₀ hroot

theorem RST31LeanTriadData.exists_of_initial_triad_root_choice_other_flap_tree
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
                      RST31OtherFlapTreeWitness (G := G) T B D) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  apply RST31LeanTriadData.exists_of_initial_triad_root_profile_choice
    (G := G) T₀ hroot
  intro T B havoid hrootB _hW _hlean hmax hmin hboundary
    hstrict_not_smaller D hDB
  let W : RST31OtherFlapTreeWitness (G := G) T B D :=
    hwitness_of_other_flap havoid hrootB hmax hmin hboundary D hDB
  letI : DecidableEq W.H.verts := Classical.decEq W.H.verts
  exact ⟨
    RST31LeanTriadData.of_profile_maximal_minimal_boundary_tree_root_delete_unreachable_other_flap_singleton
      (G := G) hno hfeet_injective havoid hrootB hDB hmax hmin
      hstrict_not_smaller W.tree W.feet_mem W.foot_ne_apex W.unreachable
      W.verts_subset W.boundary_inter_ncard_le⟩

theorem RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice_other_flap_tree
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
                    RST31OtherFlapTreeWitness (G := G) T B D) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  apply RST31LeanTriadData.exists_of_initial_triad_root_distinguished_choice
    (G := G) T₀ hroot
  intro T B havoid hrootB _hlean hmax hmin D hDB
  let W : RST31OtherFlapTreeWitness (G := G) T B D :=
    hwitness_of_other_flap havoid hrootB hmax hmin D hDB
  letI : DecidableEq W.H.verts := Classical.decEq W.H.verts
  exact ⟨
    RST31LeanTriadData.of_distinguished_ncard_maximal_minimal_boundary_tree_root_delete_unreachable_other_flap_singleton
      (G := G) hno hfeet_injective havoid hrootB hDB hmax hmin
      W.tree W.feet_mem W.foot_ne_apex W.unreachable W.verts_subset
      W.boundary_inter_ncard_le⟩


end Schematic.Math.GraphTheory
