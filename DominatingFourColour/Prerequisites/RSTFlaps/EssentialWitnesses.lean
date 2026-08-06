import DominatingFourColour.Prerequisites.RSTFlaps.SteinerTree

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

theorem Triad.ncard_le_of_essentialWithin_witness_triad
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {X S : Set V}
    (hS_essential : S ⊆ {v : V | T.EssentialWithin X v})
    (T' : Triad G feet)
    (hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ X)
    (hS_inter_T' : (S ∩ T'.vertexSet).ncard <= 3) :
    S.ncard <= 3 := by
  have hS_subset_T' : S ⊆ T'.vertexSet := by
    intro v hv
    exact hS_essential hv T' hT'_subset
  have hS_eq : S = S ∩ T'.vertexSet := by
    ext v
    constructor
    · intro hv
      exact ⟨hv, hS_subset_T' hv⟩
    · intro hv
      exact hv.1
  rw [hS_eq]
  exact hS_inter_T'

theorem treePairPaths_of_deleteRoot_unreachable
    {feet : Fin 3 -> V} {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hfeet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hfeet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hfeet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hfeet j⟩ : H.verts), by exact hfoot_ne_apex j⟩) :
    (forall i : Fin 3, (apex : V) ≠ feet i) ∧
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (feet i) (feet j) =>
          p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support := by
  let terminalH : Fin 3 -> H.verts := fun i => ⟨feet i, hfeet i⟩
  constructor
  · intro i h
    exact hfoot_ne_apex i (by
      apply Subtype.ext
      exact h.symm)
  · intro i j hij
    simpa [terminalH] using
      (Subgraph.tree_pair_paths_through_root_of_not_reachable_delete_singleton
        (T := H) (root := apex) (terminal := terminalH)
        hH_tree (by
          intro k
          exact hfoot_ne_apex k) (by
          intro a b hab
          exact hunreachable hab) hij)

theorem Triad.exists_triad_witness_of_tree_root_pair_paths
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {X S : Set V}
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hfeet : forall i : Fin 3, feet i ∈ H.verts)
    (hapex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i)
    (hpair_path_through_apex :
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (feet i) (feet j) =>
          p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ X)
    (hS_inter_H : (S ∩ H.verts).ncard <= 3) :
    Exists fun T' : Triad G feet =>
      T'.vertexSet ⊆ T.vertexSet ∪ X ∧
        (S ∩ T'.vertexSet).ncard <= 3 := by
  obtain ⟨T', _hleg_le, hT'_H⟩ :=
    Triad.exists_of_tree_root_pair_paths
      (G := G) (feet := feet) (H := H) hH_tree hfeet
      hapex_not_foot hpair_path_through_apex
  refine ⟨T', ?_, ?_⟩
  · intro v hv
    exact hH_subset (hT'_H hv)
  · have hinter_subset :
        S ∩ T'.vertexSet ⊆ S ∩ H.verts := by
      intro v hv
      exact ⟨hv.1, hT'_H hv.2⟩
    exact le_trans (Set.ncard_le_ncard hinter_subset) hS_inter_H

theorem Triad.exists_triad_witness_of_tree_root_delete_unreachable
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {X S : Set V}
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hfeet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hfeet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hfeet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hfeet j⟩ : H.verts), by exact hfoot_ne_apex j⟩)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ X)
    (hS_inter_H : (S ∩ H.verts).ncard <= 3) :
    Exists fun T' : Triad G feet =>
      T'.vertexSet ⊆ T.vertexSet ∪ X ∧
        (S ∩ T'.vertexSet).ncard <= 3 := by
  obtain ⟨hapex_not_foot, hpair_path_through_apex⟩ :=
    treePairPaths_of_deleteRoot_unreachable
      hH_tree hfeet hfoot_ne_apex hunreachable
  exact T.exists_triad_witness_of_tree_root_pair_paths
    hH_tree hfeet hapex_not_foot hpair_path_through_apex
    hH_subset hS_inter_H

theorem Triad.exists_essential_component_boundary_triad_witness_of_tree_root_pair_paths
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hfeet : forall i : Fin 3, feet i ∈ H.verts)
    (hapex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i)
    (hpair_path_through_apex :
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (feet i) (feet j) =>
          p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hboundary_inter_H :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ H.verts).ncard <= 3) :
    Exists fun T' : Triad G feet =>
      T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ∧
        (relativeVertexBoundary G (induceComponentSupport (G := G) C)
          {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
            T'.vertexSet).ncard <= 3 := by
  exact T.exists_triad_witness_of_tree_root_pair_paths
    (X := T.flapVertexSet D)
    (S := relativeVertexBoundary G (induceComponentSupport (G := G) C)
      {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    hH_tree hfeet hapex_not_foot hpair_path_through_apex
    hH_subset hboundary_inter_H

theorem Triad.exists_essential_component_boundary_triad_witness_of_tree_root_delete_unreachable
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hfeet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hfeet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hfeet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hfeet j⟩ : H.verts), by exact hfoot_ne_apex j⟩)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D)
    (hboundary_inter_H :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ H.verts).ncard <= 3) :
    Exists fun T' : Triad G feet =>
      T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ∧
        (relativeVertexBoundary G (induceComponentSupport (G := G) C)
          {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
            T'.vertexSet).ncard <= 3 := by
  exact T.exists_triad_witness_of_tree_root_delete_unreachable
    (X := T.flapVertexSet D)
    (S := relativeVertexBoundary G (induceComponentSupport (G := G) C)
      {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    hH_tree hfeet hfoot_ne_apex hunreachable hH_subset hboundary_inter_H

theorem Triad.ncard_le_of_essentialWithin_tree_root_pair_paths
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {X S : Set V}
    (hS_essential : S ⊆ {v : V | T.EssentialWithin X v})
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hfeet : forall i : Fin 3, feet i ∈ H.verts)
    (hapex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i)
    (hpair_path_through_apex :
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (feet i) (feet j) =>
          p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ X)
    (hS_inter_H : (S ∩ H.verts).ncard <= 3) :
    S.ncard <= 3 := by
  obtain ⟨T', _hleg_le, hT'_H⟩ :=
    Triad.exists_of_tree_root_pair_paths
      (G := G) (feet := feet) (H := H) hH_tree hfeet
      hapex_not_foot hpair_path_through_apex
  have hT'_subset : T'.vertexSet ⊆ T.vertexSet ∪ X := by
    intro v hv
    exact hH_subset (hT'_H hv)
  have hinter_subset :
      S ∩ T'.vertexSet ⊆ S ∩ H.verts := by
    intro v hv
    exact ⟨hv.1, hT'_H hv.2⟩
  have hS_inter_T' : (S ∩ T'.vertexSet).ncard <= 3 :=
    le_trans (Set.ncard_le_ncard hinter_subset) hS_inter_H
  exact T.ncard_le_of_essentialWithin_witness_triad
    hS_essential T' hT'_subset hS_inter_T'

theorem Triad.ncard_le_of_essentialWithin_tree_root_delete_unreachable
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {X S : Set V}
    (hS_essential : S ⊆ {v : V | T.EssentialWithin X v})
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hfeet : forall i : Fin 3, feet i ∈ H.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, hfeet i⟩ : H.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
            ⟨(⟨feet i, hfeet i⟩ : H.verts), by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, hfeet j⟩ : H.verts), by exact hfoot_ne_apex j⟩)
    (hH_subset : H.verts ⊆ T.vertexSet ∪ X)
    (hS_inter_H : (S ∩ H.verts).ncard <= 3) :
    S.ncard <= 3 := by
  obtain ⟨hapex_not_foot, hpair_path_through_apex⟩ :=
    treePairPaths_of_deleteRoot_unreachable
      hH_tree hfeet hfoot_ne_apex hunreachable
  exact T.ncard_le_of_essentialWithin_tree_root_pair_paths
    hS_essential hH_tree hfeet hapex_not_foot hpair_path_through_apex
    hH_subset hS_inter_H

theorem ncard_complement_ge_four_of_feet_and_extra
    [Fintype V]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    {K : Set V}
    (hfeet : forall i : Fin 3, feet i ∉ K)
    {x : V}
    (hxK : x ∉ K)
    (hx_not_feet : x ∉ Set.range feet) :
    4 <= Kᶜ.ncard := by
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
  have hle : Q.ncard <= Kᶜ.ncard := Set.ncard_le_ncard hQ_subset
  omega

theorem exists_two_nonfeet_of_ncard_ge_four_and_missing_foot
    [Fintype V]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    {S : Set V}
    (hS_card : 4 <= S.ncard)
    (hmissing : Exists fun i : Fin 3 => feet i ∉ S) :
    Exists fun x : V =>
      Exists fun y : V =>
        x ≠ y ∧ x ∈ S ∧ x ∉ Set.range feet ∧
          y ∈ S ∧ y ∉ Set.range feet := by
  classical
  rcases hmissing with ⟨i, hmissing_i⟩
  let N : Set V := S \ Set.range feet
  let F : Set V := S ∩ Set.range feet
  have hF_card : F.ncard <= 2 := by
    have hF_subset : F ⊆ Set.range feet \ {feet i} := by
      intro x hxF
      exact ⟨hxF.2, by
        intro hx
        have hx_eq : x = feet i := Set.mem_singleton_iff.mp hx
        exact hmissing_i (by simpa [← hx_eq] using hxF.1)⟩
    exact le_trans (Set.ncard_le_ncard hF_subset)
      (ncard_range_fin3_diff_singleton_le_two hfeet_injective i)
  have hN_card : 2 <= N.ncard := by
    by_contra hnot
    have hN_le : N.ncard <= 1 := by omega
    have hS_subset : S ⊆ N ∪ F := by
      intro x hxS
      by_cases hxfeet : x ∈ Set.range feet
      · exact Or.inr ⟨hxS, hxfeet⟩
      · exact Or.inl ⟨hxS, hxfeet⟩
    have hS_le_union : S.ncard <= (N ∪ F).ncard :=
      Set.ncard_le_ncard hS_subset
    have hunion_le : (N ∪ F).ncard <= N.ncard + F.ncard :=
      Set.ncard_union_le N F
    omega
  have hN_one_lt : 1 < N.ncard := by omega
  obtain ⟨x, hxN, y, hyN, hxy⟩ :=
    (Set.one_lt_ncard (s := N)).mp hN_one_lt
  exact ⟨x, y, hxy, hxN.1, hxN.2, hyN.1, hyN.2⟩

theorem exists_nonfoot_ne_of_ncard_ge_four_and_missing_foot
    [Fintype V]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    {S : Set V}
    (hS_card : 4 <= S.ncard)
    (hmissing : Exists fun i : Fin 3 => feet i ∉ S)
    {y : V} :
    Exists fun z : V =>
      z ≠ y ∧ z ∈ S ∧ z ∉ Set.range feet := by
  classical
  obtain ⟨x₁, x₂, hx₁x₂, hx₁S, hx₁_not_feet,
      hx₂S, hx₂_not_feet⟩ :=
    exists_two_nonfeet_of_ncard_ge_four_and_missing_foot
      (feet := feet) hfeet_injective hS_card hmissing
  by_cases hx₁y : x₁ = y
  · exact ⟨x₂, by
      intro hx₂y
      exact hx₁x₂ (hx₁y.trans hx₂y.symm), hx₂S, hx₂_not_feet⟩
  · exact ⟨x₁, hx₁y, hx₁S, hx₁_not_feet⟩

end Schematic.Math.GraphTheory
