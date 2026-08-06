import DominatingFourColour.Prerequisites.InitialTriadChoices

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
theorem RST31LeanTriadData.exists_of_initial_triad_root_profile_choice_minimal_other_flap_nonfoot_boundary_vertex_witness
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet)
    (hwitness_of_minimal_other_flap_nonfoot_vertex :
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
    RST31LeanTriadData.exists_of_initial_triad_root_profile_choice_minimal_other_flap
      (G := G) T₀ hroot
  intro T B havoid hrootB hW hlean hmax hmin hboundary
    _hstrict_not_smaller D hDB hD_min
  have hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v} :=
    T.flap_boundaries_essentialWithin_of_profile_maximal_replacement_flap_growth
      hW hDB hD_min hmax
  exact ⟨
    RST31LeanTriadData.of_boundaries_essential_and_nonfoot_boundary_vertex_witness
      (G := G) hno hfeet_injective hlean havoid D hboundary_essential
      (hwitness_of_minimal_other_flap_nonfoot_vertex
        havoid hrootB hmax hmin hboundary D hDB hD_min)⟩

theorem RST31LeanTriadData.exists_of_initial_triad_root_profile_choice_minimal_other_flap_nonfoot_boundary
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    (T₀ : Triad G feet)
    (hroot : root ∉ T₀.vertexSet) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  apply
    RST31LeanTriadData.exists_of_initial_triad_root_profile_choice_minimal_other_flap
      (G := G) T₀ hroot
  intro T B havoid _hrootB hW hlean hmax _hmin _hboundary
    _hstrict_not_smaller D hDB hD_min
  have hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v} :=
    T.flap_boundaries_essentialWithin_of_profile_maximal_replacement_flap_growth
      hW hDB hD_min hmax
  exact ⟨
    RST31LeanTriadData.of_boundaries_essential_and_nonfoot_boundary
      (G := G) hno hfeet_injective hlean havoid D hboundary_essential⟩

theorem RST31LeanTriadData.exists_of_initial_triad_root_profile_choice_minimal_other_flap_component_boundary_pair_paths
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

theorem RST31LeanTriadData.exists_of_initial_triad_root_profile_choice_minimal_other_flap_component_boundary_tree
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

theorem RST31LeanTriadData.exists_of_four_connected_triangle_root
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    (hG : IsFourConnected G)
    {feet : Fin 3 -> V}
    {root : V}
    (htriangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (hroot_not_feet : root ∉ Set.range feet) :
    Nonempty (RST31LeanTriadData G feet ({root} : Set V)) := by
  classical
  obtain ⟨T₀, hroot_T₀⟩ :=
    hG.exists_triad_avoiding_root_of_triangle htriangle hroot_not_feet
  exact
    RST31LeanTriadData.exists_of_initial_triad_root_profile_choice_minimal_other_flap_nonfoot_boundary
      (G := G) (hG.rst31_noSeparation feet)
      (IsTriangle.injective_fin3 htriangle) T₀ hroot_T₀

theorem rst_lean_triad_data_of_four_connected_triangle_root_common_neighbor
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    (hG : IsFourConnected G)
    {feet : Fin 3 -> V}
    {root : V}
    (htriangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (hroot_not_feet : root ∉ Set.range feet)
    (hroot_adj : forall i : Fin 3, G.Adj root (feet i)) :
    Nonempty (RSTLeanTriadData G feet root) := by
  classical
  obtain ⟨D⟩ :=
    RST31LeanTriadData.exists_of_four_connected_triangle_root
      (G := G) hG htriangle hroot_not_feet
  exact ⟨
    D.to_rstLeanTriadData_of_foot_witnesses_in_W
      (by simp) (IsTriangle.injective_fin3 htriangle)
      (by
        intro i
        exact ⟨root, by simp, hroot_adj i⟩)⟩


end Schematic.Math.GraphTheory
