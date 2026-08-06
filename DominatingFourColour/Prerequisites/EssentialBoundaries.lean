import DominatingFourColour.Prerequisites.FlapWitnesses

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
def RST31LeanTriadData.of_component_essential_boundary_witness
    [Fintype V]
    {feet : Fin 3 -> V}
    {W X S : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (B : T.Flap)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hC_eq_B : induceComponentSupport (G := G) C = T.flapVertexSet B)
    (hboundary_essential :
      relativeVertexBoundary G (induceComponentSupport (G := G) C) S ⊆
        {v : V | T.EssentialWithin X v})
    (T' : Triad G feet)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ X)
    (hboundary_inter_T' :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S ∩
        T'.vertexSet).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  have hfeet_C :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C := by
    intro i hfoot
    have hfootB : feet i ∈ T.flapVertexSet B := by
      simpa [hC_eq_B] using hfoot
    exact (T.flapVertexSet_subset_complement B hfootB) (T.foot_mem_vertexSet i)
  have hC_complement :
      (induceComponentSupport (G := G) C)ᶜ ⊆ Set.range feet :=
    hno.component_complement_subset_feet_of_essential_boundary_witness
      hfeet_injective C hfeet_C T hboundary_essential T' hT'_subset
      hboundary_inter_T'
  exact RST31LeanTriadData.of_flap_complement_subset_feet
    hlean havoid B (by
      simpa [hC_eq_B] using hC_complement)

def RST31LeanTriadData.of_distinguished_ncard_maximal_minimal_boundary_le_three
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (havoid : T.AvoidsSet W)
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard)
    (hmin :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
            T.vertexSet.ncard <= U.vertexSet.ncard)
    (hboundary :
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  have hlean : T.Lean :=
    T.lean_of_distinguished_ncard_maximal_minimal hW hmax hmin
  have hfeet_B :
      forall i : Fin 3, feet i ∉ T.flapVertexSet B := by
    intro i hfootB
    exact (T.flapVertexSet_subset_complement B hfootB) (T.foot_mem_vertexSet i)
  have hB_complement :
      (T.flapVertexSet B)ᶜ ⊆ Set.range feet :=
    hno.component_complement_subset_feet_of_boundary_le_three
      hfeet_injective (S := T.vertexSet) B hfeet_B hboundary
  exact RST31LeanTriadData.of_flap_complement_subset_feet
    hlean havoid B hB_complement

def RST31LeanTriadData.of_distinguished_ncard_maximal_minimal_boundary_le_three_singleton
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (havoid : T.AvoidsSet ({root} : Set V))
    {B : T.Flap}
    (hrootB : root ∈ T.flapVertexSet B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        ({root} : Set V) ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard)
    (hmin :
      forall (U : Triad G feet) (C : U.Flap),
        ({root} : Set V) ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
            T.vertexSet.ncard <= U.vertexSet.ncard)
    (hboundary :
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet).ncard <= 3) :
    RST31LeanTriadData G feet ({root} : Set V) := by
  have hW :
      ({root} : Set V) ⊆ T.flapVertexSet B := by
    simpa using hrootB
  exact RST31LeanTriadData.of_distinguished_ncard_maximal_minimal_boundary_le_three
    (G := G) (W := ({root} : Set V))
    hno hfeet_injective havoid hW hmax hmin hboundary

def RST31LeanTriadData.of_component_essential_boundary_tree_root_pair_paths
    [Fintype V]
    {feet : Fin 3 -> V}
    {W X S : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (B : T.Flap)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hC_eq_B : induceComponentSupport (G := G) C = T.flapVertexSet B)
    (hboundary_essential :
      relativeVertexBoundary G (induceComponentSupport (G := G) C) S ⊆
        {v : V | T.EssentialWithin X v})
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
    (hH_subset : H.verts ⊆ T.vertexSet ∪ X)
    (hboundary_inter_H :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  have hfeet_C :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C := by
    intro i hfoot
    have hfootB : feet i ∈ T.flapVertexSet B := by
      simpa [hC_eq_B] using hfoot
    exact (T.flapVertexSet_subset_complement B hfootB) (T.foot_mem_vertexSet i)
  have hC_complement :
      (induceComponentSupport (G := G) C)ᶜ ⊆ Set.range feet :=
    hno.component_complement_subset_feet_of_essential_boundary_tree_root_pair_paths
      hfeet_injective C hfeet_C T hboundary_essential hH_tree hH_feet
      hapex_not_foot hpair_path_through_apex hH_subset hboundary_inter_H
  exact RST31LeanTriadData.of_flap_complement_subset_feet
    hlean havoid B (by
      simpa [hC_eq_B] using hC_complement)

def RST31LeanTriadData.of_component_essential_boundary_tree_root_delete_unreachable
    [Fintype V]
    {feet : Fin 3 -> V}
    {W X S : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    (B : T.Flap)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hC_eq_B : induceComponentSupport (G := G) C = T.flapVertexSet B)
    (hboundary_essential :
      relativeVertexBoundary G (induceComponentSupport (G := G) C) S ⊆
        {v : V | T.EssentialWithin X v})
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hH_feet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hH_feet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hH_feet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hH_feet j⟩ : H.verts), by exact hfoot_ne_apex j⟩)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ X)
    (hboundary_inter_H :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C) S ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  have hfeet_C :
      forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) C := by
    intro i hfoot
    have hfootB : feet i ∈ T.flapVertexSet B := by
      simpa [hC_eq_B] using hfoot
    exact (T.flapVertexSet_subset_complement B hfootB) (T.foot_mem_vertexSet i)
  have hC_complement :
      (induceComponentSupport (G := G) C)ᶜ ⊆ Set.range feet :=
    hno.component_complement_subset_feet_of_essential_boundary_tree_root_delete_unreachable
      hfeet_injective C hfeet_C T hboundary_essential hH_tree hH_feet
      hfoot_ne_apex hunreachable hH_subset hboundary_inter_H
  exact RST31LeanTriadData.of_flap_complement_subset_feet
    hlean havoid B (by
      simpa [hC_eq_B] using hC_complement)

def RST31LeanTriadData.of_profile_maximal_component_boundary_witness_empty
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (C : (G.induce T.vertexSetᶜ).ConnectedComponent)
    (hC_eq_B : induceComponentSupport (G := G) C = T.flapVertexSet B)
    (T' : Triad G feet)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet)
    (hboundary_inter_T' :
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        T'.vertexSet).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  exact RST31LeanTriadData.of_component_essential_boundary_witness
    (G := G) (W := W) (X := ∅) (S := T.vertexSet)
    hno hfeet_injective hlean havoid B C hC_eq_B (by
      intro v hv
      have hv' :
          v ∈ relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet := by
        simpa [hC_eq_B] using hv
      exact T.flap_boundary_essentialWithin_empty_of_profile_maximal hW hmax hv')
    T' (by
      intro v hv
      exact Or.inl (hT'_subset hv))
    (by
      simpa [hC_eq_B] using hboundary_inter_T')

def RST31LeanTriadData.of_profile_maximal_component_boundary_tree_root_pair_paths_empty
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (C : (G.induce T.vertexSetᶜ).ConnectedComponent)
    (hC_eq_B : induceComponentSupport (G := G) C = T.flapVertexSet B)
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
    (hH_subset : H.verts ⊆ T.vertexSet)
    (hboundary_inter_H :
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  exact RST31LeanTriadData.of_component_essential_boundary_tree_root_pair_paths
    (G := G) (W := W) (X := ∅) (S := T.vertexSet)
    hno hfeet_injective hlean havoid B C hC_eq_B (by
      intro v hv
      have hv' :
          v ∈ relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet := by
        simpa [hC_eq_B] using hv
      exact T.flap_boundary_essentialWithin_empty_of_profile_maximal hW hmax hv')
    hH_tree hH_feet hapex_not_foot hpair_path_through_apex (by
      intro v hv
      exact Or.inl (hH_subset hv))
    (by
      simpa [hC_eq_B] using hboundary_inter_H)

def RST31LeanTriadData.of_profile_maximal_component_boundary_tree_root_delete_unreachable_empty
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    {B : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (C : (G.induce T.vertexSetᶜ).ConnectedComponent)
    (hC_eq_B : induceComponentSupport (G := G) C = T.flapVertexSet B)
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hH_feet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hH_feet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hH_feet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hH_feet j⟩ : H.verts), by exact hfoot_ne_apex j⟩)
    (hH_subset : H.verts ⊆ T.vertexSet)
    (hboundary_inter_H :
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  exact RST31LeanTriadData.of_component_essential_boundary_tree_root_delete_unreachable
    (G := G) (W := W) (X := ∅) (S := T.vertexSet)
    hno hfeet_injective hlean havoid B C hC_eq_B (by
      intro v hv
      have hv' :
          v ∈ relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet := by
        simpa [hC_eq_B] using hv
      exact T.flap_boundary_essentialWithin_empty_of_profile_maximal hW hmax hv')
    hH_tree hH_feet hfoot_ne_apex hunreachable (by
      intro v hv
      exact Or.inl (hH_subset hv))
    (by
      simpa [hC_eq_B] using hboundary_inter_H)

def RST31LeanTriadData.of_profile_maximal_boundary_tree_root_pair_paths_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
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
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  exact RST31LeanTriadData.of_component_essential_boundary_tree_root_pair_paths
    (G := G) (W := W) (X := T.flapVertexSet D) (S := T.vertexSet)
    hno hfeet_injective hlean havoid B B rfl (by
      intro v hv
      exact T.flap_boundary_essentialWithin_of_profile_maximal_other_flap
        hW hDB hmax hv)
    hH_tree hH_feet hapex_not_foot hpair_path_through_apex
    hH_subset
    (by
      simpa using hboundary_inter_H)

def RST31LeanTriadData.of_profile_maximal_boundary_tree_root_delete_unreachable_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hH_feet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hH_feet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hH_feet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hH_feet j⟩ : H.verts), by exact hfoot_ne_apex j⟩)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hboundary_inter_H :
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  exact RST31LeanTriadData.of_component_essential_boundary_tree_root_delete_unreachable
    (G := G) (W := W) (X := T.flapVertexSet D) (S := T.vertexSet)
    hno hfeet_injective hlean havoid B B rfl (by
      intro v hv
      exact T.flap_boundary_essentialWithin_of_profile_maximal_other_flap
        hW hDB hmax hv)
    hH_tree hH_feet hfoot_ne_apex hunreachable
    hH_subset
    (by
      simpa using hboundary_inter_H)

def RST31LeanTriadData.of_profile_maximal_minimal_boundary_tree_root_pair_paths_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (havoid : T.AvoidsSet W)
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
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
              T.flapSizeProfileWith B <= T'.flapSizeProfileWith B')
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
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  have hlean : T.Lean :=
    T.lean_of_profile_maximal_minimal_of_strict_subtriad_profile_not_smaller
      hmax hmin hstrict_not_smaller
  exact RST31LeanTriadData.of_profile_maximal_boundary_tree_root_pair_paths_other_flap
    hno hfeet_injective hlean havoid hW hDB hmax hH_tree hH_feet
    hapex_not_foot hpair_path_through_apex hH_subset hboundary_inter_H

def RST31LeanTriadData.of_profile_maximal_minimal_boundary_tree_root_delete_unreachable_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (havoid : T.AvoidsSet W)
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
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
              T.flapSizeProfileWith B <= T'.flapSizeProfileWith B')
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hH_feet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hH_feet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hH_feet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hH_feet j⟩ : H.verts), by exact hfoot_ne_apex j⟩)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hboundary_inter_H :
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  have hlean : T.Lean :=
    T.lean_of_profile_maximal_minimal_of_strict_subtriad_profile_not_smaller
      hmax hmin hstrict_not_smaller
  exact RST31LeanTriadData.of_profile_maximal_boundary_tree_root_delete_unreachable_other_flap
    hno hfeet_injective hlean havoid hW hDB hmax hH_tree hH_feet
    hfoot_ne_apex hunreachable hH_subset hboundary_inter_H

def RST31LeanTriadData.of_distinguished_ncard_maximal_minimal_boundary_tree_root_pair_paths_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (havoid : T.AvoidsSet W)
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard)
    (hmin :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
            T.vertexSet.ncard <= U.vertexSet.ncard)
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
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  have hlean : T.Lean :=
    T.lean_of_distinguished_ncard_maximal_minimal hW hmax hmin
  exact RST31LeanTriadData.of_component_essential_boundary_tree_root_pair_paths
    (G := G) (W := W) (X := T.flapVertexSet D) (S := T.vertexSet)
    hno hfeet_injective hlean havoid B B rfl (by
      intro v hv
      exact T.flap_boundary_essentialWithin_of_distinguished_ncard_maximal_other_flap
        hW hDB hmax hv)
    hH_tree hH_feet hapex_not_foot hpair_path_through_apex
    hH_subset
    (by
      simpa using hboundary_inter_H)

def RST31LeanTriadData.of_distinguished_ncard_maximal_minimal_boundary_tree_root_delete_unreachable_other_flap
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (havoid : T.AvoidsSet W)
    {B D : T.Flap}
    (hW : W ⊆ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard)
    (hmin :
      forall (U : Triad G feet) (C : U.Flap),
        W ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
            T.vertexSet.ncard <= U.vertexSet.ncard)
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hH_feet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hH_feet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hH_feet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hH_feet j⟩ : H.verts), by exact hfoot_ne_apex j⟩)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hboundary_inter_H :
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet W := by
  have hlean : T.Lean :=
    T.lean_of_distinguished_ncard_maximal_minimal hW hmax hmin
  exact RST31LeanTriadData.of_component_essential_boundary_tree_root_delete_unreachable
    (G := G) (W := W) (X := T.flapVertexSet D) (S := T.vertexSet)
    hno hfeet_injective hlean havoid B B rfl (by
      intro v hv
      exact T.flap_boundary_essentialWithin_of_distinguished_ncard_maximal_other_flap
        hW hDB hmax hv)
    hH_tree hH_feet hfoot_ne_apex hunreachable
    hH_subset
    (by
      simpa using hboundary_inter_H)

def RST31LeanTriadData.of_distinguished_ncard_maximal_minimal_boundary_tree_root_pair_paths_other_flap_singleton
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (havoid : T.AvoidsSet ({root} : Set V))
    {B D : T.Flap}
    (hrootB : root ∈ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        ({root} : Set V) ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard)
    (hmin :
      forall (U : Triad G feet) (C : U.Flap),
        ({root} : Set V) ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
            T.vertexSet.ncard <= U.vertexSet.ncard)
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
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet ({root} : Set V) := by
  have hW :
      ({root} : Set V) ⊆ T.flapVertexSet B := by
    simpa using hrootB
  exact RST31LeanTriadData.of_distinguished_ncard_maximal_minimal_boundary_tree_root_pair_paths_other_flap
    (G := G) (W := ({root} : Set V))
    hno hfeet_injective havoid hW hDB hmax hmin hH_tree hH_feet
    hapex_not_foot hpair_path_through_apex hH_subset hboundary_inter_H

def RST31LeanTriadData.of_distinguished_ncard_maximal_minimal_boundary_tree_root_delete_unreachable_other_flap_singleton
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (havoid : T.AvoidsSet ({root} : Set V))
    {B D : T.Flap}
    (hrootB : root ∈ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        ({root} : Set V) ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard <= (T.flapVertexSet B).ncard)
    (hmin :
      forall (U : Triad G feet) (C : U.Flap),
        ({root} : Set V) ⊆ U.flapVertexSet C ->
          (U.flapVertexSet C).ncard = (T.flapVertexSet B).ncard ->
            T.vertexSet.ncard <= U.vertexSet.ncard)
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hH_feet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hH_feet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hH_feet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hH_feet j⟩ : H.verts), by exact hfoot_ne_apex j⟩)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hboundary_inter_H :
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet ({root} : Set V) := by
  have hW :
      ({root} : Set V) ⊆ T.flapVertexSet B := by
    simpa using hrootB
  exact RST31LeanTriadData.of_distinguished_ncard_maximal_minimal_boundary_tree_root_delete_unreachable_other_flap
    (G := G) (W := ({root} : Set V))
    hno hfeet_injective havoid hW hDB hmax hmin hH_tree hH_feet
    hfoot_ne_apex hunreachable hH_subset hboundary_inter_H

def RST31LeanTriadData.of_profile_maximal_minimal_boundary_tree_root_pair_paths_other_flap_singleton
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (havoid : T.AvoidsSet ({root} : Set V))
    {B D : T.Flap}
    (hrootB : root ∈ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        ({root} : Set V) ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (hmin :
      forall (U : Triad G feet) (C : U.Flap),
        ({root} : Set V) ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C = T.flapSizeProfileWith B ->
            T.vertexSet.ncard <= U.vertexSet.ncard)
    (hstrict_not_smaller :
      forall T' : Triad G feet,
        T'.vertexSet ⊂ T.vertexSet ->
          Exists fun B' : T'.Flap =>
            ({root} : Set V) ⊆ T'.flapVertexSet B' ∧
              T.flapSizeProfileWith B <= T'.flapSizeProfileWith B')
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
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet ({root} : Set V) := by
  have hW :
      ({root} : Set V) ⊆ T.flapVertexSet B := by
    simpa using hrootB
  exact RST31LeanTriadData.of_profile_maximal_minimal_boundary_tree_root_pair_paths_other_flap
    (G := G) (W := ({root} : Set V))
    hno hfeet_injective havoid hW hDB hmax hmin hstrict_not_smaller
    hH_tree hH_feet hapex_not_foot hpair_path_through_apex hH_subset
    hboundary_inter_H

def RST31LeanTriadData.of_profile_maximal_minimal_boundary_tree_root_delete_unreachable_other_flap_singleton
    [Fintype V]
    {feet : Fin 3 -> V}
    {root : V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (havoid : T.AvoidsSet ({root} : Set V))
    {B D : T.Flap}
    (hrootB : root ∈ T.flapVertexSet B)
    (hDB : D ≠ B)
    (hmax :
      forall (U : Triad G feet) (C : U.Flap),
        ({root} : Set V) ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C <= T.flapSizeProfileWith B)
    (hmin :
      forall (U : Triad G feet) (C : U.Flap),
        ({root} : Set V) ⊆ U.flapVertexSet C ->
          U.flapSizeProfileWith C = T.flapSizeProfileWith B ->
            T.vertexSet.ncard <= U.vertexSet.ncard)
    (hstrict_not_smaller :
      forall T' : Triad G feet,
        T'.vertexSet ⊂ T.vertexSet ->
          Exists fun B' : T'.Flap =>
            ({root} : Set V) ⊆ T'.flapVertexSet B' ∧
              T.flapSizeProfileWith B <= T'.flapSizeProfileWith B')
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hH_feet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hH_feet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hH_feet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hH_feet j⟩ : H.verts), by exact hfoot_ne_apex j⟩)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hboundary_inter_H :
      (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩
        H.verts).ncard <= 3) :
    RST31LeanTriadData G feet ({root} : Set V) := by
  have hW :
      ({root} : Set V) ⊆ T.flapVertexSet B := by
    simpa using hrootB
  exact RST31LeanTriadData.of_profile_maximal_minimal_boundary_tree_root_delete_unreachable_other_flap
    (G := G) (W := ({root} : Set V))
    hno hfeet_injective havoid hW hDB hmax hmin hstrict_not_smaller
    hH_tree hH_feet hfoot_ne_apex hunreachable hH_subset hboundary_inter_H


end Schematic.Math.GraphTheory
