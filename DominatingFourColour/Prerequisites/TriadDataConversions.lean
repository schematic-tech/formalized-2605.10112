import DominatingFourColour.Prerequisites.LeglessTripodReduction

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

theorem Triad.feet_avoid_essential_complement_component
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap)
    (C : (G.induce
      ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent) :
    forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C := by
  intro i hfootC
  have hfoot_not_essential :
      feet i ∈ {v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ :=
    induceComponentSupport_subset (G := G) C hfootC
  exact hfoot_not_essential (T.foot_essentialWithin (T.flapVertexSet D) i)

def RST31LeanTriadData.to_rstLeanTriadData_of_legless_tripod_first_subset
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {root : V}
    (D : RST31LeanTriadData G feet W)
    (T : LeglessTripod G feet)
    (hrootW : root ∈ W)
    (hfeet_injective : Function.Injective feet)
    (hsubset : D.triad.vertexSet ⊆ T.first.vertexSet) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_lean_and_foot_outside hrootW hfeet_injective
    (Triad.foot_has_neighbor_outside_of_vertexSet_subset
      (G := G) (T := T.first) (T' := D.triad) hsubset
      (T.foot_has_neighbor_outside_first hfeet_injective))

def RST31LeanTriadData.to_rstLeanTriadData_of_legless_tripod_second_subset
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {W : Set V}
    {root : V}
    (D : RST31LeanTriadData G feet W)
    (T : LeglessTripod G feet)
    (hrootW : root ∈ W)
    (hfeet_injective : Function.Injective feet)
    (hsubset : D.triad.vertexSet ⊆ T.second.vertexSet) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_lean_and_foot_outside hrootW hfeet_injective
    (Triad.foot_has_neighbor_outside_of_vertexSet_subset
      (G := G) (T := T.second) (T' := D.triad) hsubset
      (T.foot_has_neighbor_outside_second hfeet_injective))

def RST31LeanTriadData.to_rstLeanTriadData_of_four_connected
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {W : Set V}
    {root : V}
    (D : RST31LeanTriadData G feet W)
    (hrootW : root ∈ W)
    (h_four_connected : IsFourConnected G)
    (hinside :
      forall v : V,
        v ∈ (D.triad.carrier.deleteVerts (Set.range feet)).verts ->
          (G.neighborSet v ∩ D.triad.vertexSet).ncard <= 3)
    (hfoot_inside :
      forall i : Fin 3,
        (G.neighborSet (feet i) ∩ D.triad.vertexSet).ncard <= 3) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_min_degree_four hrootW
    (four_connected_minDegree_atLeast_four h_four_connected)
    hinside hfoot_inside

def RST31LeanTriadData.to_rstLeanTriadData_of_four_connected_chordless
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {W : Set V}
    {root : V}
    (D : RST31LeanTriadData G feet W)
    (hrootW : root ∈ W)
    (h_four_connected : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hchordless : forall i : Fin 3, (D.triad.leg i).IsChordless)
    (hinternal_cross :
      forall {i : Fin 3} {v : V},
        v ∈ Walk.InternalVertices (D.triad.leg i) ->
          Exists fun X : Set V =>
            X.ncard <= 1 ∧
              G.neighborSet v ∩ D.triad.vertexSet ⊆
                (G.neighborSet v ∩
                  {u : V | u ∈ (D.triad.leg i).support}) ∪ X)
    (hfoot_cross :
      forall i : Fin 3,
        G.neighborSet (feet i) ∩ D.triad.vertexSet ⊆
          (G.neighborSet (feet i) ∩
            {v : V | v ∈ (D.triad.leg i).support}) ∪
              (Set.range feet \ {feet i})) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_four_connected hrootW h_four_connected
    (D.triad.inside_neighbors_at_most_three_of_legs_chordless_and_internal_cross
      hchordless hinternal_cross)
    (by
      intro i
      exact D.triad.foot_inside_neighbors_at_most_three_of_leg_chordless
        hfeet_injective i (hchordless i) (hfoot_cross i))

def RST31LeanTriadData.to_rstLeanTriadData_of_four_connected_chordless_singleton
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (D : RST31LeanTriadData G feet ({root} : Set V))
    (h_four_connected : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hchordless : forall i : Fin 3, (D.triad.leg i).IsChordless)
    (hinternal_cross :
      forall {i : Fin 3} {v : V},
        v ∈ Walk.InternalVertices (D.triad.leg i) ->
          Exists fun X : Set V =>
            X.ncard <= 1 ∧
              G.neighborSet v ∩ D.triad.vertexSet ⊆
                (G.neighborSet v ∩
                  {u : V | u ∈ (D.triad.leg i).support}) ∪ X)
    (hfoot_cross :
      forall i : Fin 3,
        G.neighborSet (feet i) ∩ D.triad.vertexSet ⊆
          (G.neighborSet (feet i) ∩
            {v : V | v ∈ (D.triad.leg i).support}) ∪
              (Set.range feet \ {feet i})) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_four_connected_chordless
    (by simp) h_four_connected hfeet_injective hchordless
    hinternal_cross hfoot_cross

def RST31LeanTriadData.to_rstLeanTriadData_of_four_connected_lean_cross
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {W : Set V}
    {root : V}
    (D : RST31LeanTriadData G feet W)
    (hrootW : root ∈ W)
    (h_four_connected : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hinternal_cross :
      forall {i : Fin 3} {v : V},
        v ∈ Walk.InternalVertices (D.triad.leg i) ->
          Exists fun X : Set V =>
            X.ncard <= 1 ∧
              G.neighborSet v ∩ D.triad.vertexSet ⊆
                (G.neighborSet v ∩
                  {u : V | u ∈ (D.triad.leg i).support}) ∪ X)
    (hfoot_cross :
      forall i : Fin 3,
        G.neighborSet (feet i) ∩ D.triad.vertexSet ⊆
          (G.neighborSet (feet i) ∩
            {v : V | v ∈ (D.triad.leg i).support}) ∪
              (Set.range feet \ {feet i})) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_four_connected hrootW h_four_connected
    (D.triad.inside_neighbors_at_most_three_of_lean_and_internal_cross
      D.lean hfeet_injective hinternal_cross)
    (fun i =>
      D.triad.foot_inside_neighbors_at_most_three_of_lean_and_foot_cross
        D.lean hfeet_injective i (hfoot_cross i))

def RST31LeanTriadData.to_rstLeanTriadData_of_four_connected_lean
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {W : Set V}
    {root : V}
    (D : RST31LeanTriadData G feet W)
    (hrootW : root ∈ W)
    (h_four_connected : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hfoot_inside :
      forall i : Fin 3,
        (G.neighborSet (feet i) ∩ D.triad.vertexSet).ncard <= 3) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_four_connected hrootW h_four_connected
    (D.triad.inside_neighbors_at_most_three_of_lean
      D.lean hfeet_injective)
    hfoot_inside

def RST31LeanTriadData.to_rstLeanTriadData_of_four_connected_lean_foot_cross
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {W : Set V}
    {root : V}
    (D : RST31LeanTriadData G feet W)
    (hrootW : root ∈ W)
    (h_four_connected : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hfoot_cross :
      forall i : Fin 3,
        G.neighborSet (feet i) ∩ D.triad.vertexSet ⊆
          (G.neighborSet (feet i) ∩
            {v : V | v ∈ (D.triad.leg i).support}) ∪
              (Set.range feet \ {feet i})) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_four_connected_lean hrootW h_four_connected
    hfeet_injective
    (fun i =>
      D.triad.foot_inside_neighbors_at_most_three_of_lean_and_foot_cross
        D.lean hfeet_injective i (hfoot_cross i))

def RST31LeanTriadData.to_rstLeanTriadData_of_four_connected_lean_cross_singleton
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (D : RST31LeanTriadData G feet ({root} : Set V))
    (h_four_connected : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hinternal_cross :
      forall {i : Fin 3} {v : V},
        v ∈ Walk.InternalVertices (D.triad.leg i) ->
          Exists fun X : Set V =>
            X.ncard <= 1 ∧
              G.neighborSet v ∩ D.triad.vertexSet ⊆
                (G.neighborSet v ∩
                  {u : V | u ∈ (D.triad.leg i).support}) ∪ X)
    (hfoot_cross :
      forall i : Fin 3,
        G.neighborSet (feet i) ∩ D.triad.vertexSet ⊆
          (G.neighborSet (feet i) ∩
            {v : V | v ∈ (D.triad.leg i).support}) ∪
              (Set.range feet \ {feet i})) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_four_connected_lean_cross
    (by simp) h_four_connected hfeet_injective hinternal_cross hfoot_cross

def RST31LeanTriadData.to_rstLeanTriadData_of_four_connected_lean_foot_cross_singleton
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (D : RST31LeanTriadData G feet ({root} : Set V))
    (h_four_connected : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hfoot_cross :
      forall i : Fin 3,
        G.neighborSet (feet i) ∩ D.triad.vertexSet ⊆
          (G.neighborSet (feet i) ∩
            {v : V | v ∈ (D.triad.leg i).support}) ∪
              (Set.range feet \ {feet i})) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_four_connected_lean_foot_cross
    (by simp) h_four_connected hfeet_injective hfoot_cross

def RST31LeanTriadData.to_rstLeanTriadData_of_four_connected_lean_long_legs_singleton
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (D : RST31LeanTriadData G feet ({root} : Set V))
    (h_four_connected : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hlong : forall i : Fin 3, 1 < (D.triad.leg i).length) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_four_connected_lean
    (by simp) h_four_connected hfeet_injective
    (fun i =>
      D.triad.foot_inside_neighbors_at_most_three_of_lean_all_long_legs
        D.lean hfeet_injective hlong i)

def RST31LeanTriadData.to_rstLeanTriadData_of_four_connected_lean_all_legs_length_one_singleton
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (D : RST31LeanTriadData G feet ({root} : Set V))
    (h_four_connected : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hshort : forall i : Fin 3, (D.triad.leg i).length = 1) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_four_connected_lean
    (by simp) h_four_connected hfeet_injective
    (fun i =>
      D.triad.foot_inside_neighbors_at_most_three_of_legs_length_eq_one
        hfeet_injective hshort i)

def RST31LeanTriadData.to_rstLeanTriadData_of_four_connected_lean_no_short_cross_singleton
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {root : V}
    (D : RST31LeanTriadData G feet ({root} : Set V))
    (h_four_connected : IsFourConnected G)
    (hfeet_injective : Function.Injective feet)
    (hno_short_cross :
      forall i : Fin 3,
        (D.triad.leg i).length = 1 ->
          D.triad.ShortFootHasNoCrossNeighbor i) :
    RSTLeanTriadData G feet root :=
  D.to_rstLeanTriadData_of_four_connected_lean
    (by simp) h_four_connected hfeet_injective
    (by
      intro i
      by_cases hlong : 1 < (D.triad.leg i).length
      · exact D.triad.foot_inside_neighbors_at_most_three_of_lean_long_legs
          D.lean hfeet_injective i hlong
      · have hshort : (D.triad.leg i).length = 1 := by
          have hpos := D.triad.leg_length_pos i
          omega
        exact D.triad.foot_inside_neighbors_at_most_three_of_short_leg_no_cross
          D.lean hfeet_injective (hno_short_cross i hshort))

def RST31LeanTriadData.of_flap_complement_subset_feet
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (B : T.Flap)
    (hB_complement : (T.flapVertexSet B)ᶜ ⊆ Set.range feet) :
    RST31LeanTriadData G feet W where
  triad := T
  lean := hlean
  avoids_W := havoid
  complement_connected :=
    T.complement_connected_of_flap_complement_subset_feet B hB_complement

def RST31LeanTriadData.of_subsingleton_flaps
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (B : T.Flap)
    (hsubsingleton : Subsingleton T.Flap) :
    RST31LeanTriadData G feet W where
  triad := T
  lean := hlean
  avoids_W := havoid
  complement_connected := by
    have hnonempty : T.vertexSetᶜ.Nonempty := by
      obtain ⟨x, hxB⟩ := T.flapVertexSet_nonempty B
      exact ⟨x, T.flapVertexSet_subset_complement B hxB⟩
    exact T.complement_connected_of_subsingleton_flaps hnonempty hsubsingleton

def RST31LeanTriadData.of_unique_flap
    {feet : Fin 3 -> V}
    {W : Set V}
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (B : T.Flap)
    (hunique : forall C : T.Flap, C = B) :
    RST31LeanTriadData G feet W :=
  RST31LeanTriadData.of_subsingleton_flaps hlean havoid B
    ⟨fun C D => (hunique C).trans (hunique D).symm⟩

def RST31LeanTriadData.of_blocked_core_unique_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (D : T.Flap)
    {K boundary : Set V}
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ boundary -> Not (G.Adj a b))
    (hfeet_K : forall i : Fin 3, feet i ∉ K)
    (hK_nonempty : K.Nonempty)
    (hboundary_ncard : boundary.ncard <= 3)
    (hother_subset :
      forall C : T.Flap, C ≠ D -> T.flapVertexSet C ⊆ Kᶜ) :
    RST31LeanTriadData G feet W := by
  have hK_complement : Kᶜ ⊆ Set.range feet :=
    hno.core_complement_subset_feet_of_boundary_le_three
      hfeet_injective hclosed hfeet_K hK_nonempty hboundary_ncard
  have hsubsingleton : Subsingleton T.Flap :=
    T.subsingleton_flaps_of_core_complement_subset_feet
      hK_complement hother_subset
  exact RST31LeanTriadData.of_subsingleton_flaps
    hlean havoid D hsubsingleton

def RST31LeanTriadData.of_component_blocked_core_unique_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (D : T.Flap)
    {S : Set V}
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hfeet_C :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C)
    (hboundary :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S).ncard <= 3)
    (hother_subset :
      forall E : T.Flap, E ≠ D ->
        T.flapVertexSet E ⊆ (induceComponentSupport (G := G) C)ᶜ) :
    RST31LeanTriadData G feet W := by
  exact RST31LeanTriadData.of_blocked_core_unique_flap
    (G := G) hno hfeet_injective hlean havoid D
    (induceComponentSupport_closed_with_relativeBoundary (G := G) C)
    hfeet_C (induceComponentSupport_nonempty (G := G) C)
    hboundary hother_subset

def RST31LeanTriadData.of_essential_component_tree_root_pair_paths_unique_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (D : T.Flap)
    (C : (G.induce
      ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent)
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hH_feet : forall i : Fin 3, feet i ∈ H.verts)
    (hapex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i)
    (hpair_path_through_apex :
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (feet i) (feet j) =>
          p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hboundary_inter_H :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ H.verts).ncard <= 3)
    (hother_subset :
      forall E : T.Flap, E ≠ D ->
        T.flapVertexSet E ⊆ (induceComponentSupport (G := G) C)ᶜ) :
    RST31LeanTriadData G feet W := by
  let essential : Set V := {v : V | T.EssentialWithin (T.flapVertexSet D) v}
  have hfeet_C :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C :=
    T.feet_avoid_essential_complement_component D C
  have hboundary_essential :
      relativeVertexBoundary G (induceComponentSupport (G := G) C) essential ⊆
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
    intro v hv
    exact hv.1
  have hboundary :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) essential).ncard <= 3 :=
    T.ncard_le_of_essentialWithin_tree_root_pair_paths
      (X := T.flapVertexSet D)
      (S := relativeVertexBoundary G (induceComponentSupport (G := G) C) essential)
      hboundary_essential hH_tree hH_feet hapex_not_foot
      hpair_path_through_apex hH_subset (by
        simpa [essential] using hboundary_inter_H)
  exact RST31LeanTriadData.of_component_blocked_core_unique_flap
    (G := G) hno hfeet_injective hlean havoid D C hfeet_C
    (by simpa [essential] using hboundary) hother_subset

def RST31LeanTriadData.of_essential_component_tree_root_pair_paths_unique_flap_of_boundaries_essential
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (D : T.Flap)
    (C : (G.induce
      ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent)
    (hD_subset_C : T.flapVertexSet D ⊆ induceComponentSupport (G := G) C)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hH_feet : forall i : Fin 3, feet i ∈ H.verts)
    (hapex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i)
    (hpair_path_through_apex :
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (feet i) (feet j) =>
          p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hboundary_inter_H :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ H.verts).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  exact RST31LeanTriadData.of_essential_component_tree_root_pair_paths_unique_flap
    (G := G) hno hfeet_injective hlean havoid D C hH_tree
    hH_feet hapex_not_foot hpair_path_through_apex hH_subset
    hboundary_inter_H
    (T.other_flap_subset_essential_component_complement_of_boundaries_essential
      hD_subset_C hboundary_essential)

def RST31LeanTriadData.of_essential_component_triad_unique_flap_of_boundaries_essential
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (D : T.Flap)
    (C : (G.induce
      ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent)
    (hD_subset_C : T.flapVertexSet D ⊆ induceComponentSupport (G := G) C)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    (T' : Triad G feet)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hboundary_inter_T' :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ T'.vertexSet).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  let essential : Set V := {v : V | T.EssentialWithin (T.flapVertexSet D) v}
  have hfeet_C :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C :=
    T.feet_avoid_essential_complement_component D C
  have hboundary_essential_core :
      relativeVertexBoundary G (induceComponentSupport (G := G) C) essential ⊆
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} := by
    intro v hv
    exact hv.1
  have hboundary :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) essential).ncard <= 3 :=
    T.ncard_le_of_essentialWithin_witness_triad
      (X := T.flapVertexSet D)
      (S := relativeVertexBoundary G (induceComponentSupport (G := G) C) essential)
      hboundary_essential_core T' hT'_subset (by
        simpa [essential] using hboundary_inter_T')
  exact RST31LeanTriadData.of_component_blocked_core_unique_flap
    (G := G) hno hfeet_injective hlean havoid D C hfeet_C
    (by simpa [essential] using hboundary)
    (T.other_flap_subset_essential_component_complement_of_boundaries_essential
      hD_subset_C hboundary_essential)

def RST31LeanTriadData.of_essential_component_boundary_subset_feet_unique_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (D : T.Flap)
    (C : (G.induce
      ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent)
    (hD_subset_C : T.flapVertexSet D ⊆ induceComponentSupport (G := G) C)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    (hboundary_subset_feet :
      relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ⊆ Set.range feet) :
    RST31LeanTriadData G feet W := by
  let essential : Set V := {v : V | T.EssentialWithin (T.flapVertexSet D) v}
  have hfeet_C :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C :=
    T.feet_avoid_essential_complement_component D C
  have hboundary :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) essential).ncard <= 3 := by
    exact ncard_le_three_of_subset_range_feet hfeet_injective
      (by simpa [essential] using hboundary_subset_feet)
  exact RST31LeanTriadData.of_component_blocked_core_unique_flap
    (G := G) hno hfeet_injective hlean havoid D C hfeet_C hboundary
    (T.other_flap_subset_essential_component_complement_of_boundaries_essential
      hD_subset_C hboundary_essential)

noncomputable def RST31LeanTriadData.of_boundaries_essential_and_component_triad_witness
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (D : T.Flap)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    (hwitness :
      forall C :
        (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent,
        T.flapVertexSet D ⊆ induceComponentSupport (G := G) C ->
          Exists fun T' : Triad G feet =>
            T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ∧
              (relativeVertexBoundary G (induceComponentSupport (G := G) C)
                {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
                  T'.vertexSet).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  classical
  let C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent :=
    Classical.choose (T.exists_essential_component_containing_flap D)
  have hD_subset_C : T.flapVertexSet D ⊆ induceComponentSupport (G := G) C :=
    Classical.choose_spec (T.exists_essential_component_containing_flap D)
  let T' : Triad G feet := Classical.choose (hwitness C hD_subset_C)
  have hT'_spec := Classical.choose_spec (hwitness C hD_subset_C)
  have hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D := hT'_spec.1
  have hboundary_inter_T' :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ T'.vertexSet).ncard <= 3 :=
    hT'_spec.2
  exact RST31LeanTriadData.of_essential_component_triad_unique_flap_of_boundaries_essential
    (G := G) hno hfeet_injective hlean havoid D C hD_subset_C
    hboundary_essential T' hT'_subset hboundary_inter_T'

noncomputable def RST31LeanTriadData.of_boundaries_essential_and_component_boundary_split
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (D : T.Flap)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    (hwitness_nonfeet :
      forall C :
        (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent,
        T.flapVertexSet D ⊆ induceComponentSupport (G := G) C ->
          ¬ (relativeVertexBoundary G (induceComponentSupport (G := G) C)
              {v : V | T.EssentialWithin (T.flapVertexSet D) v} ⊆ Set.range feet) ->
            Exists fun T' : Triad G feet =>
              T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ∧
                (relativeVertexBoundary G (induceComponentSupport (G := G) C)
                  {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
                    T'.vertexSet).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  classical
  let C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent :=
    Classical.choose (T.exists_essential_component_containing_flap D)
  have hD_subset_C : T.flapVertexSet D ⊆ induceComponentSupport (G := G) C :=
    Classical.choose_spec (T.exists_essential_component_containing_flap D)
  by_cases hboundary_subset_feet :
      relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ⊆ Set.range feet
  · exact RST31LeanTriadData.of_essential_component_boundary_subset_feet_unique_flap
      (G := G) hno hfeet_injective hlean havoid D C hD_subset_C
      hboundary_essential hboundary_subset_feet
  · let T' : Triad G feet :=
      Classical.choose (hwitness_nonfeet C hD_subset_C hboundary_subset_feet)
    have hT'_spec :=
      Classical.choose_spec (hwitness_nonfeet C hD_subset_C hboundary_subset_feet)
    exact RST31LeanTriadData.of_essential_component_triad_unique_flap_of_boundaries_essential
      (G := G) hno hfeet_injective hlean havoid D C hD_subset_C
      hboundary_essential T' hT'_spec.1 hT'_spec.2

noncomputable def RST31LeanTriadData.of_boundaries_essential_and_nonfoot_boundary_vertex_witness
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (D : T.Flap)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    (hwitness_nonfoot_vertex :
      forall C :
        (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent,
        T.flapVertexSet D ⊆ induceComponentSupport (G := G) C ->
          forall x : V,
            x ∈ relativeVertexBoundary G (induceComponentSupport (G := G) C)
              {v : V | T.EssentialWithin (T.flapVertexSet D) v} ->
              x ∈ T.vertexSet ->
                x ∉ Set.range feet ->
                  Exists fun T' : Triad G feet =>
                    T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ∧
                      (relativeVertexBoundary G (induceComponentSupport (G := G) C)
                        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
                          T'.vertexSet).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  classical
  refine RST31LeanTriadData.of_boundaries_essential_and_component_boundary_split
        (G := G) hno hfeet_injective hlean havoid D hboundary_essential ?_
  intro C hD_subset_C hboundary_not_subset_feet
  obtain ⟨x, hx_boundary, hxT, hx_not_feet⟩ :=
    T.exists_nonfoot_essential_component_boundary_vertex D C
      hboundary_not_subset_feet
  exact hwitness_nonfoot_vertex C hD_subset_C x hx_boundary hxT hx_not_feet

noncomputable def RST31LeanTriadData.of_distinguished_two_flap_component_triad_witness
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    {B D : T.Flap}
    (havoid : T.AvoidsSet W)
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hflaps_two : forall E : T.Flap, E = B ∨ E = D)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard)
    (hmin :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
            T.vertexSet.ncard <= U.vertexSet.ncard)
    (hwitness :
      forall C :
        (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent,
        T.flapVertexSet D ⊆ induceComponentSupport (G := G) C ->
          Exists fun T' : Triad G feet =>
            T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ∧
              (relativeVertexBoundary G (induceComponentSupport (G := G) C)
                {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
                  T'.vertexSet).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  have hlean : T.Lean :=
    T.lean_of_distinguished_ncard_maximal_minimal hW hmax hmin
  refine RST31LeanTriadData.of_boundaries_essential_and_component_triad_witness
    (G := G) hno hfeet_injective hlean havoid D ?_ hwitness
  intro E hED
  rcases hflaps_two E with hEB | hED'
  · subst E
    exact T.flap_boundary_essentialWithin_of_distinguished_ncard_maximal_other_flap
      hW hDB hmax
  · exact False.elim (hED hED')


end Schematic.Math.GraphTheory
