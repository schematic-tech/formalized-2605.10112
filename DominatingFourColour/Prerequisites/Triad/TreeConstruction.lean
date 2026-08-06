import DominatingFourColour.Prerequisites.Triad.Structure

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

def Triad.of_tree_rooted_paths
    {feet : Fin 3 -> V}
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hapex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i)
    (leg : forall i : Fin 3, G.Walk (apex : V) (feet i))
    (hleg_le : forall i : Fin 3, (leg i).toSubgraph ≤ H)
    (hleg_isPath : forall i : Fin 3, (leg i).IsPath)
    (hpair_path_through_apex :
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (feet i) (feet j) =>
          p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support) :
    Triad G feet := by
  classical
  let terminal : Fin 3 -> H.verts := fun i =>
    ⟨feet i, Walk.support_subset_of_toSubgraph_le (hleg_le i) (leg i).end_mem_support⟩
  have hterminal_ne : forall i : Fin 3, terminal i ≠ apex := by
    intro i h
    have hval := congrArg (fun x : H.verts => (x : V)) h
    exact hapex_not_foot i hval.symm
  have hpunctured_disjoint :
      forall {i j : Fin 3}, i ≠ j ->
        Disjoint
          {z : V | z ∈ (leg i).support ∧ z ≠ (apex : V)}
          {z : V | z ∈ (leg j).support ∧ z ≠ (apex : V)} := by
    exact
      Subgraph.tree_rooted_paths_punctured_supports_disjoint_of_pair_paths_through_root
        (G := G) (T := H) (root := apex) (terminal := terminal)
        hH_tree leg hleg_le hterminal_ne hleg_isPath (by
          intro i j hij
          obtain ⟨p, hp_le, hp_path, hapex_p⟩ :=
            hpair_path_through_apex hij
          exact ⟨p, by simpa [terminal] using hp_le, hp_path,
            by simpa using hapex_p⟩)
  exact {
    apex := apex
    apex_not_foot := hapex_not_foot
    leg := leg
    leg_isPath := hleg_isPath
    apex_only_common_vertex := by
      intro i j hij
      rw [Set.disjoint_left]
      intro z hzi hzj
      exact Set.disjoint_left.mp (hpunctured_disjoint hij)
        ⟨hzi.1, hzi.2.1⟩ ⟨hzj.1, hzj.2.1⟩
    internal_vertices_avoid_feet := by
      intro i j hfoot
      by_cases hij : i = j
      · subst j
        exact hfoot.2.2 rfl
      · exact Set.disjoint_left.mp (hpunctured_disjoint hij)
          ⟨(leg i).end_mem_support, (hapex_not_foot i).symm⟩
          ⟨hfoot.1, hfoot.2.1⟩
  }

theorem Triad.exists_of_tree_root_pair_paths
    {feet : Fin 3 -> V}
    {H : G.Subgraph}
    [DecidableEq H.verts]
    (hH_tree : H.coe.IsTree)
    {apex : H.verts}
    (hfeet : forall i : Fin 3, feet i ∈ H.verts)
    (hapex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i)
    (hpair_path_through_apex :
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (feet i) (feet j) =>
          p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support) :
    Exists fun T : Triad G feet =>
      (forall i : Fin 3, (T.leg i).toSubgraph ≤ H) ∧
        T.vertexSet ⊆ H.verts := by
  classical
  let leg : forall i : Fin 3, G.Walk (apex : V) (feet i) := fun i =>
    Classical.choose
      (Subgraph.Connected.exists_path_between
        (G := G) hH_tree.connected apex.2 (hfeet i))
  have hleg_isPath : forall i : Fin 3, (leg i).IsPath := by
    intro i
    exact (Classical.choose_spec
      (Subgraph.Connected.exists_path_between
        (G := G) hH_tree.connected apex.2 (hfeet i))).1
  have hleg_le : forall i : Fin 3, (leg i).toSubgraph ≤ H := by
    intro i
    exact (Classical.choose_spec
      (Subgraph.Connected.exists_path_between
        (G := G) hH_tree.connected apex.2 (hfeet i))).2
  let T : Triad G feet :=
    Triad.of_tree_rooted_paths
      (G := G) (H := H) hH_tree hapex_not_foot leg hleg_le
      hleg_isPath hpair_path_through_apex
  refine ⟨T, ?_, ?_⟩
  · intro i
    simpa [T, Triad.of_tree_rooted_paths] using hleg_le i
  · exact T.vertexSet_subset_of_leg_toSubgraph_le (by
      intro i
      simpa [T, Triad.of_tree_rooted_paths] using hleg_le i)

theorem Triad.exists_of_tree_with_three_terminal_leaves
    {feet : Fin 3 -> V}
    {H : G.Subgraph}
    [Fintype H.verts]
    [DecidableEq H.verts]
    [DecidableRel H.coe.Adj]
    [Nontrivial H.verts]
    (hH_tree : H.coe.IsTree)
    (hfeet_injective : Function.Injective feet)
    (hfeet : forall i : Fin 3, feet i ∈ H.verts)
    (hterminal_degree :
      forall i : Fin 3, H.coe.degree (⟨feet i, hfeet i⟩ : H.verts) = 1)
    (hbranch_card_le_one :
      (Finset.univ.filter fun v : H.verts => 3 <= H.coe.degree v).card <= 1) :
    Exists fun T : Triad G feet =>
      (forall i : Fin 3, (T.leg i).toSubgraph ≤ H) ∧
        T.vertexSet ⊆ H.verts := by
  classical
  let terminalH : Fin 3 -> H.verts := fun i => ⟨feet i, hfeet i⟩
  have hterminal_injective : Function.Injective terminalH := by
    intro i j hij
    apply hfeet_injective
    exact congrArg (fun x : H.verts => (x : V)) hij
  obtain ⟨root, hroot_degree, hroot_unique⟩ :=
    Schematic.Math.GraphTheory.IsTree.exists_unique_degree_ge_three_of_three_distinct_degree_one
      (G := H.coe) hH_tree hterminal_injective
      (by
        intro i
        simpa [terminalH] using hterminal_degree i)
      hbranch_card_le_one
  have hterminal_ne_root : forall i : Fin 3, terminalH i ≠ root := by
    intro i h
    have hdegree_one :
        @SimpleGraph.degree H.verts H.coe (terminalH i)
          (Subtype.fintype (Membership.mem (H.coe.neighborSet (terminalH i)))) = 1 := by
      simpa [terminalH,
        Subsingleton.elim
          (Subtype.fintype (Membership.mem (H.coe.neighborSet (terminalH i))))
          (SimpleGraph.Subgraph.coeFiniteAt (terminalH i))] using
        hterminal_degree i
    subst root
    omega
  have hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (H.coe.induce ({root} : Set H.verts)ᶜ).Reachable
            ⟨terminalH i, by exact hterminal_ne_root i⟩
            ⟨terminalH j, by exact hterminal_ne_root j⟩ := by
    exact
      Schematic.Math.GraphTheory.IsTree.not_reachable_delete_singleton_of_unique_degree_ge_three_terminals
        (G := H.coe) hH_tree hterminal_injective
        (by
          intro i
          simpa [terminalH] using hterminal_degree i)
        hroot_unique hterminal_ne_root
  have hpair_path_through_root :
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (feet i) (feet j) =>
          p.toSubgraph ≤ H ∧ p.IsPath ∧ (root : V) ∈ p.support := by
    intro i j hij
    simpa [terminalH] using
      (Subgraph.tree_pair_paths_through_root_of_not_reachable_delete_singleton
        (T := H) (root := root) (terminal := terminalH)
        hH_tree hterminal_ne_root hunreachable hij)
  have hroot_not_foot : forall i : Fin 3, (root : V) ≠ feet i := by
    intro i h
    exact hterminal_ne_root i (by
      apply Subtype.ext
      simpa [terminalH] using h.symm)
  exact Triad.exists_of_tree_root_pair_paths
    (G := G) (feet := feet) (H := H) hH_tree hfeet
    hroot_not_foot hpair_path_through_root

theorem Triad.exists_of_minimal_connected_subgraph_terminal_neighbor_ncard_one
    [Fintype V]
    [DecidableEq V]
    {feet : Fin 3 -> V}
    {C B : G.Subgraph}
    (hBC : B ≤ C)
    (hB_connected : B.coe.Connected)
    (hfeet_injective : Function.Injective feet)
    (hfeet_B : forall i : Fin 3, feet i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ C ->
          B'.coe.Connected ->
            (forall i : Fin 3, feet i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_terminal_neighbor_ncard :
      forall i : Fin 3,
        (B.coe.neighborSet (⟨feet i, hfeet_B i⟩ : B.verts)).ncard = 1) :
    Exists fun T : Triad G feet => T.vertexSet ⊆ B.verts := by
  classical
  obtain ⟨S, hS_tree, hS_spanning⟩ :=
    Connected.exists_spanning_tree_subgraph (G := B.coe) hB_connected
  letI : Fintype S.verts := S.verts.toFinite.fintype
  letI : DecidableRel S.coe.Adj := Classical.decRel _
  let H : G.Subgraph := SimpleGraph.Subgraph.coeSubgraph S
  letI : Fintype H.verts := H.verts.toFinite.fintype
  letI : DecidableRel H.coe.Adj := Classical.decRel _
  have hH_tree : H.coe.IsTree := by
    simpa [H] using Schematic.Math.GraphTheory.Subgraph.coeSubgraph_isTree S hS_tree
  have hfeet_H : forall i : Fin 3, feet i ∈ H.verts := by
    intro i
    change feet i ∈ (SimpleGraph.Subgraph.coeSubgraph S).verts
    exact ⟨(⟨feet i, hfeet_B i⟩ : B.verts),
      hS_spanning (⟨feet i, hfeet_B i⟩ : B.verts), rfl⟩
  let terminalS : Fin 3 -> S.verts := fun i =>
    ⟨(⟨feet i, hfeet_B i⟩ : B.verts),
      hS_spanning (⟨feet i, hfeet_B i⟩ : B.verts)⟩
  have hS_nontrivial : Nontrivial S.verts := by
    let f0 : S.verts := terminalS 0
    let f1 : S.verts := terminalS 1
    refine ⟨⟨f0, f1, ?_⟩⟩
    intro h
    have hfeet : feet 0 = feet 1 := by
      have hval := congrArg (fun x : S.verts => ((x : B.verts) : V)) h
      simpa [f0, f1, terminalS] using hval
    exact (by decide : (0 : Fin 3) ≠ 1) (hfeet_injective hfeet)
  letI : Nontrivial S.verts := hS_nontrivial
  have hH_nontrivial : Nontrivial H.verts := by
    let f0 : H.verts := ⟨feet 0, hfeet_H 0⟩
    let f1 : H.verts := ⟨feet 1, hfeet_H 1⟩
    refine ⟨⟨f0, f1, ?_⟩⟩
    intro h
    have hfeet : feet 0 = feet 1 := congrArg (fun x : H.verts => (x : V)) h
    exact (by decide : (0 : Fin 3) ≠ 1) (hfeet_injective hfeet)
  letI : Nontrivial H.verts := hH_nontrivial
  have hterminal_degree_S :
      forall i : Fin 3, S.coe.degree (terminalS i) = 1 := by
    have hdegree :=
      Subgraph.spanning_tree_terminal_degrees_one_of_subgraph_neighbor_ncard_one
        (B := B) (T := S) hS_tree.connected hS_spanning
        (terminal := fun i : Fin 3 =>
          (⟨feet i, hfeet_B i⟩ : B.verts))
        (by intro i; infer_instance)
        (by intro i; infer_instance)
        hB_terminal_neighbor_ncard
    intro i
    simpa [terminalS] using hdegree i
  have hterminal_degree_S' :
      forall i : Fin 3,
        @SimpleGraph.degree S.verts S.coe (terminalS i)
          (Subtype.fintype (Membership.mem (S.coe.neighborSet (terminalS i)))) = 1 := by
    intro i
    simpa [
      Subsingleton.elim
        (Subtype.fintype (Membership.mem (S.coe.neighborSet (terminalS i))))
        (SimpleGraph.Subgraph.coeFiniteAt (terminalS i))] using
      hterminal_degree_S i
  have hbranch_card_S :=
    Subgraph.minimal_connected_spanning_tree_card_degree_ge_three_le_one_of_three_terminals
      (C := C) (B := B) (T := S) (terminal := feet)
      hBC hfeet_B hB_minimal hS_tree hS_spanning
  have hterminal_injective : Function.Injective terminalS := by
    intro i j hij
    apply hfeet_injective
    have hval := congrArg (fun x : S.verts => ((x : B.verts) : V)) hij
    simpa [terminalS] using hval
  obtain ⟨rootS, hroot_degree, hroot_unique⟩ :=
    Schematic.Math.GraphTheory.IsTree.exists_unique_degree_ge_three_of_three_distinct_degree_one
      (G := S.coe) hS_tree hterminal_injective hterminal_degree_S'
      hbranch_card_S
  have hterminal_ne_root : forall i : Fin 3, terminalS i ≠ rootS := by
    intro i h
    subst rootS
    have hdegree_one := hterminal_degree_S' i
    omega
  have hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (S.coe.induce ({rootS} : Set S.verts)ᶜ).Reachable
            ⟨terminalS i, by exact hterminal_ne_root i⟩
            ⟨terminalS j, by exact hterminal_ne_root j⟩ := by
    exact
      Schematic.Math.GraphTheory.IsTree.not_reachable_delete_singleton_of_unique_degree_ge_three_terminals
        (G := S.coe) hS_tree hterminal_injective hterminal_degree_S'
        hroot_unique hterminal_ne_root
  let rootH : H.verts :=
    ⟨((rootS : B.verts) : V), by
      change ((rootS : B.verts) : V) ∈
        (SimpleGraph.Subgraph.coeSubgraph S).verts
      exact ⟨(rootS : B.verts), rootS.2, rfl⟩⟩
  have hroot_not_foot : forall i : Fin 3, (rootH : V) ≠ feet i := by
    intro i h
    have hroot_terminal : rootS = terminalS i := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [rootH, terminalS] using h
    exact hterminal_ne_root i hroot_terminal.symm
  have hpair_path_through_root :
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (feet i) (feet j) =>
          p.toSubgraph ≤ H ∧ p.IsPath ∧ (rootH : V) ∈ p.support := by
    intro i j hij
    obtain ⟨pB, hpB_le, hpB_path, hroot_pB⟩ :=
      (Subgraph.tree_pair_paths_through_root_of_not_reachable_delete_singleton
        (T := S) (root := rootS) (terminal := terminalS)
        hS_tree hterminal_ne_root hunreachable hij)
    let p : G.Walk (feet i) (feet j) :=
      (pB.map B.hom).copy
        (by simp [terminalS])
        (by simp [terminalS])
    refine ⟨p, ?_, ?_, ?_⟩
    · have hp_map : (pB.map B.hom).toSubgraph ≤ H := by
        rw [SimpleGraph.Walk.toSubgraph_map]
        exact SimpleGraph.Subgraph.map_mono hpB_le
      simpa [p, H] using hp_map
    · exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr
        (SimpleGraph.Walk.map_isPath_of_injective
          SimpleGraph.Subgraph.hom_injective hpB_path)
    · have hroot_map : ((rootS : B.verts) : V) ∈ (pB.map B.hom).support := by
        rw [SimpleGraph.Walk.support_map]
        exact List.mem_map.mpr ⟨rootS, hroot_pB, rfl⟩
      simpa [p, rootH] using hroot_map
  obtain ⟨T, _hleg_le, hT_subset_H⟩ :=
    Triad.exists_of_tree_root_pair_paths
      (G := G) (feet := feet) (H := H) hH_tree hfeet_H
      hroot_not_foot hpair_path_through_root
  exact ⟨T, fun v hv =>
    (SimpleGraph.Subgraph.coeSubgraph_le S).left (hT_subset_H hv)⟩

theorem Triad.exists_of_minimal_connected_subgraph_overgraph_terminal_neighbor_ncard_one
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {C B : G.Subgraph}
    (hBC : B ≤ C)
    (hB_connected : B.coe.Connected)
    (hfeet_injective : Function.Injective feet)
    (hfeet_B : forall i : Fin 3, feet i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ C ->
          B'.coe.Connected ->
            (forall i : Fin 3, feet i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hC_terminal_neighbor_ncard :
      forall i : Fin 3, (C.neighborSet (feet i)).ncard = 1) :
    Exists fun T : Triad G feet => T.vertexSet ⊆ B.verts :=
  Triad.exists_of_minimal_connected_subgraph_terminal_neighbor_ncard_one
    (G := G) hBC hB_connected hfeet_injective hfeet_B hB_minimal
    (Subgraph.connected_subgraph_terminal_neighbor_ncard_one_of_le
      (G := G) hBC hB_connected hfeet_injective hfeet_B
      hC_terminal_neighbor_ncard)

theorem three_pendant_edges_neighborSet_foot_eq_singleton
    {feet x : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hfoot_ne_x : forall i j : Fin 3, feet i ≠ x j)
    (hadj : forall i : Fin 3, G.Adj (x i) (feet i))
    (i : Fin 3) :
    ((⨆ j : Fin 3, (hadj j).toWalk.toSubgraph).neighborSet (feet i)) =
      {x i} := by
  ext y
  constructor
  · intro hy
    simp only [SimpleGraph.Subgraph.neighborSet, SimpleGraph.Subgraph.iSup_adj] at hy
    rcases hy with ⟨j, hyj⟩
    by_cases hji : j = i
    · subst j
      have hxi : x i ≠ feet i := by
        intro h
        exact hfoot_ne_x i i h.symm
      simp [SimpleGraph.Walk.toSubgraph, Sym2.eq, hxi] at hyj
      exact hyj.symm
    · have hfeet_ne : feet j ≠ feet i := by
        intro h
        exact hji (hfeet_injective h)
      have hx_ne : x j ≠ feet i := by
        intro h
        exact hfoot_ne_x i j h.symm
      simp [SimpleGraph.Walk.toSubgraph, Sym2.eq, hx_ne, hfeet_ne] at hyj
  · intro hy
    subst y
    simp only [SimpleGraph.Subgraph.neighborSet, SimpleGraph.Subgraph.iSup_adj]
    refine ⟨i, ?_⟩
    simp [SimpleGraph.Walk.toSubgraph, Sym2.eq]

theorem connected_fragment_with_pendant_edges_neighborSet_foot_eq_singleton
    [DecidableEq V]
    {feet x : Fin 3 -> V}
    (H : G.Subgraph)
    (hfeet_injective : Function.Injective feet)
    (hxH : forall i : Fin 3, x i ∈ H.verts)
    (hfeet_not_H : forall i : Fin 3, feet i ∉ H.verts)
    (hadj : forall i : Fin 3, G.Adj (x i) (feet i))
    (i : Fin 3) :
    (H ⊔ (⨆ j : Fin 3, (hadj j).toWalk.toSubgraph)).neighborSet (feet i) =
      {x i} := by
  have hfoot_ne_x : forall i j : Fin 3, feet i ≠ x j := by
    intro i j h
    exact hfeet_not_H i (by simpa [h] using hxH j)
  rw [SimpleGraph.Subgraph.neighborSet_sup,
    Subgraph.neighborSet_eq_empty_of_not_mem_verts H (hfeet_not_H i),
    three_pendant_edges_neighborSet_foot_eq_singleton
      (G := G) hfeet_injective hfoot_ne_x hadj i]
  simp

theorem connected_fragment_with_pendant_edges_neighborSet_foot_ncard
    [DecidableEq V]
    {feet x : Fin 3 -> V}
    (H : G.Subgraph)
    (hfeet_injective : Function.Injective feet)
    (hxH : forall i : Fin 3, x i ∈ H.verts)
    (hfeet_not_H : forall i : Fin 3, feet i ∉ H.verts)
    (hadj : forall i : Fin 3, G.Adj (x i) (feet i))
    (i : Fin 3) :
    ((H ⊔ (⨆ j : Fin 3, (hadj j).toWalk.toSubgraph)).neighborSet
      (feet i)).ncard = 1 := by
  rw [connected_fragment_with_pendant_edges_neighborSet_foot_eq_singleton
    (G := G) H hfeet_injective hxH hfeet_not_H hadj i]
  simp

theorem connected_fragment_with_pendant_edges_connected
    {feet x : Fin 3 -> V}
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hxH : forall i : Fin 3, x i ∈ H.verts)
    (hadj : forall i : Fin 3, G.Adj (x i) (feet i)) :
    ((H ⊔ (⨆ j : Fin 3, (hadj j).toWalk.toSubgraph)).coe).Connected := by
  classical
  let E : G.Subgraph := ⨆ j : Fin 3, (hadj j).toWalk.toSubgraph
  let C : G.Subgraph := H ⊔ E
  have hH_le_C : H ≤ C := by
    exact le_sup_left
  have hedge_le_C : forall i : Fin 3, (hadj i).toWalk.toSubgraph ≤ C := by
    intro i
    exact le_trans (le_iSup (fun j : Fin 3 => (hadj j).toWalk.toSubgraph) i)
      le_sup_right
  have hwalk_to_H :
      forall {u : V}, u ∈ C.verts ->
        Exists fun a : V =>
          a ∈ H.verts ∧
            Exists fun p : G.Walk u a => p.toSubgraph ≤ C := by
    intro u hu
    have hu' : u ∈ H.verts ∪ E.verts := by simpa [C] using hu
    rcases hu' with huH | huE
    · exact ⟨u, huH, SimpleGraph.Walk.nil, by simp [C, huH]⟩
    · have huE' : u ∈ (⨆ j : Fin 3, (hadj j).toWalk.toSubgraph).verts := by
        simpa [E] using huE
      rw [SimpleGraph.Subgraph.verts_iSup] at huE'
      rcases Set.mem_iUnion.mp huE' with ⟨i, hui⟩
      have hui_support : u ∈ (hadj i).toWalk.support := by
        rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hui
      simp at hui_support
      rcases hui_support with hui | hui
      · subst u
        exact ⟨x i, hxH i, SimpleGraph.Walk.nil, by simp [C, hxH i]⟩
      · subst u
        refine ⟨x i, hxH i, (hadj i).symm.toWalk, ?_⟩
        have hC_adj : C.Adj (x i) (feet i) :=
          (hedge_le_C i).right (by
            simp [SimpleGraph.Walk.toSubgraph])
        simpa [SimpleGraph.Walk.toSubgraph] using
          SimpleGraph.subgraphOfAdj_le_of_adj C (C.adj_symm hC_adj)
  change C.coe.Connected
  rw [← SimpleGraph.Subgraph.connected_iff']
  rw [SimpleGraph.Subgraph.connected_iff_forall_exists_walk_subgraph]
  constructor
  · rcases hH_connected.nonempty with ⟨vH⟩
    exact ⟨(vH : V), hH_le_C.left vH.2⟩
  · intro u v hu hv
    obtain ⟨a, haH, pua, hpua⟩ := hwalk_to_H (by simpa [C] using hu)
    obtain ⟨b, hbH, pvb, hpvb⟩ := hwalk_to_H (by simpa [C] using hv)
    obtain ⟨pab, _hpab_path, hpab⟩ :=
      Subgraph.Connected.exists_path_between (G := G) hH_connected haH hbH
    refine ⟨pua.append (pab.append pvb.reverse), ?_⟩
    rw [SimpleGraph.Walk.toSubgraph_append, SimpleGraph.Walk.toSubgraph_append,
      SimpleGraph.Walk.toSubgraph_reverse]
    exact sup_le hpua (sup_le (le_trans hpab hH_le_C) hpvb)

private theorem exists_triad_of_connected_fragment_adjacent_to_feet
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet x : Fin 3 -> V}
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hfeet_injective : Function.Injective feet)
    (hxH : forall i : Fin 3, x i ∈ H.verts)
    (hfeet_not_H : forall i : Fin 3, feet i ∉ H.verts)
    (hadj : forall i : Fin 3, G.Adj (x i) (feet i)) :
    Exists fun T : Triad G feet =>
      T.vertexSet ⊆
        (H ⊔ (⨆ j : Fin 3, (hadj j).toWalk.toSubgraph)).verts := by
  classical
  let C : G.Subgraph := H ⊔ (⨆ j : Fin 3, (hadj j).toWalk.toSubgraph)
  have hC_connected : C.coe.Connected := by
    simpa [C] using
      connected_fragment_with_pendant_edges_connected
        (G := G) H hH_connected hxH hadj
  have hfeet_C : forall i : Fin 3, feet i ∈ C.verts := by
    intro i
    change feet i ∈ (H ⊔ (⨆ j : Fin 3, (hadj j).toWalk.toSubgraph)).verts
    right
    rw [SimpleGraph.Subgraph.verts_iSup]
    exact Set.mem_iUnion.mpr ⟨i, by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph]
      exact (hadj i).toWalk.end_mem_support⟩
  obtain ⟨B, hBC, hB_connected, hfeet_B, hB_minimal⟩ :=
    Subgraph.Connected.exists_minimal_connected_subgraph_containing
      (G := G) (B := C) hC_connected (terminal := feet) hfeet_C
  obtain ⟨T, hT_subset_B⟩ :=
    Triad.exists_of_minimal_connected_subgraph_overgraph_terminal_neighbor_ncard_one
      (G := G) (feet := feet) (C := C) (B := B)
      hBC hB_connected hfeet_injective hfeet_B hB_minimal
      (by
        intro i
        simpa [C] using
          connected_fragment_with_pendant_edges_neighborSet_foot_ncard
            (G := G) H hfeet_injective hxH hfeet_not_H hadj i)
  exact ⟨T, fun v hv => hBC.1 (hT_subset_B hv)⟩

theorem Triad.exists_of_connected_fragment_adjacent_to_feet
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet x : Fin 3 -> V}
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hfeet_injective : Function.Injective feet)
    (hxH : forall i : Fin 3, x i ∈ H.verts)
    (hfeet_not_H : forall i : Fin 3, feet i ∉ H.verts)
    (hadj : forall i : Fin 3, G.Adj (x i) (feet i)) :
    Nonempty (Triad G feet) := by
  obtain ⟨T, _hsubset⟩ := exists_triad_of_connected_fragment_adjacent_to_feet
    (G := G) H hH_connected hfeet_injective hxH hfeet_not_H hadj
  exact ⟨T⟩

theorem Triad.exists_of_connected_fragment_adjacent_to_feet_subset
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet x : Fin 3 -> V}
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hfeet_injective : Function.Injective feet)
    (hxH : forall i : Fin 3, x i ∈ H.verts)
    (hfeet_not_H : forall i : Fin 3, feet i ∉ H.verts)
    (hadj : forall i : Fin 3, G.Adj (x i) (feet i)) :
    Exists fun T : Triad G feet =>
      T.vertexSet ⊆
        (H ⊔ (⨆ j : Fin 3, (hadj j).toWalk.toSubgraph)).verts :=
  exists_triad_of_connected_fragment_adjacent_to_feet
    (G := G) H hH_connected hfeet_injective hxH hfeet_not_H hadj

theorem connected_fragment_with_pendant_edges_verts_subset
    {feet x : Fin 3 -> V}
    (H : G.Subgraph)
    (hxH : forall i : Fin 3, x i ∈ H.verts)
    (hadj : forall i : Fin 3, G.Adj (x i) (feet i)) :
    (H ⊔ (⨆ j : Fin 3, (hadj j).toWalk.toSubgraph)).verts ⊆
      H.verts ∪ Set.range feet := by
  intro v hv
  rcases hv with hvH | hvE
  · exact Or.inl hvH
  · rw [SimpleGraph.Subgraph.verts_iSup] at hvE
    rcases Set.mem_iUnion.mp hvE with ⟨i, hvi⟩
    rw [SimpleGraph.Walk.mem_verts_toSubgraph] at hvi
    simp at hvi
    rcases hvi with h | h
    · exact Or.inl (by simpa [h] using hxH i)
    · exact Or.inr ⟨i, h.symm⟩

theorem IsFourConnected.exists_triad_of_three_distinct_vertices
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    (hG : IsFourConnected G)
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet) :
    Nonempty (Triad G feet) := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).deleteVerts (Set.range feet)
  have hH_connected : H.coe.Connected := by
    have hconn :=
      isFourConnected_delete_triple_top_connected
        (G := G) hG (feet 0) (feet 1) (feet 2)
    have hrange :
        ({feet 0, feet 1, feet 2} : Set V) = Set.range feet :=
      (fin3_range_eq_insert feet).symm
    rw [hrange] at hconn
    simpa [H] using hconn
  have hfoot_outside :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ ((⊤ : G.Subgraph).deleteVerts (Set.range feet)).verts ∧
            G.Adj u (feet i) := by
    intro i
    have hinside :
        (G.neighborSet (feet i) ∩ Set.range feet).ncard <= 3 := by
      have hsubset :
          G.neighborSet (feet i) ∩ Set.range feet ⊆ Set.range feet :=
        Set.inter_subset_right
      have hcard_le :
          (G.neighborSet (feet i) ∩ Set.range feet).ncard <=
            (Set.range feet).ncard :=
        Set.ncard_le_ncard hsubset
      have hrange_card : (Set.range feet).ncard = 3 :=
        ncard_range_fin3_of_injective hfeet_injective
      omega
    exact exists_neighbor_outside_set_of_degree_atLeast_four_of_inside_neighbors_atMost_three
      (G := G) (S := Set.range feet) (v := feet i)
      (four_connected_minDegree_atLeast_four hG (feet i)) hinside
  let x : Fin 3 -> V := fun i => Classical.choose (hfoot_outside i)
  have hxH : forall i : Fin 3, x i ∈ H.verts := by
    intro i
    change x i ∈ ((⊤ : G.Subgraph).deleteVerts (Set.range feet)).verts
    exact (Classical.choose_spec (hfoot_outside i)).1
  have hfeet_not_H : forall i : Fin 3, feet i ∉ H.verts := by
    intro i hmem
    have hmem' :
        feet i ∈ ((⊤ : G.Subgraph).deleteVerts (Set.range feet)).verts := by
      simp [H] at hmem
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hmem'
    exact hmem'.2 ⟨i, rfl⟩
  have hadj : forall i : Fin 3, G.Adj (x i) (feet i) := by
    intro i
    exact (Classical.choose_spec (hfoot_outside i)).2
  exact Triad.exists_of_connected_fragment_adjacent_to_feet
    (G := G) (feet := feet) (x := x) H hH_connected hfeet_injective
    hxH hfeet_not_H hadj

theorem IsFourConnected.exists_triad_of_triangle
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    (hG : IsFourConnected G)
    {feet : Fin 3 -> V}
    (htriangle : IsTriangle G (feet 0) (feet 1) (feet 2)) :
    Nonempty (Triad G feet) :=
  hG.exists_triad_of_three_distinct_vertices (IsTriangle.injective_fin3 htriangle)

theorem IsFourConnected.delete_root_feet_component_adjacent_to_foot
    [Fintype V]
    [DecidableEq V]
    (hG : IsFourConnected G)
    {feet : Fin 3 -> V}
    {root : V}
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet)
    (C : (G.induce (insert root (Set.range feet))ᶜ).ConnectedComponent)
    (i : Fin 3) :
    Exists fun u : V =>
      u ∈ induceComponentSupport (G := G) C ∧ G.Adj u (feet i) := by
  classical
  let S : Set V := insert root (Set.range feet)
  let K : Set V := induceComponentSupport (G := G) C
  by_contra hno
  let B : Set V := insert root (Set.range feet \ {feet i})
  have hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b) := by
    intro a b ha hbK hbB hab
    by_cases hbS : b ∈ S
    · have hbS' : b = root ∨ b ∈ Set.range feet := by
        simpa [S] using hbS
      have hb_eq_foot : b = feet i := by
        rcases hbS' with hbroot | hbrange
        · exfalso
          exact hbB (by simp [B, hbroot])
        · by_cases hbi : b = feet i
          · exact hbi
          · exfalso
            exact hbB (by
              refine Set.mem_insert_of_mem root ?_
              exact ⟨hbrange, by simpa [Set.mem_singleton_iff] using hbi⟩)
      subst b
      exact hno ⟨a, ha, hab⟩
    · exact hbK
        (by
          have hbA : b ∈ (insert root (Set.range feet))ᶜ := by
            simpa [S] using hbS
          exact induceComponentSupport_mem_of_adj (G := G) C ha hbA hab)
  have hdiff_le : (Set.range feet \ {feet i}).ncard <= 2 := by
    exact ncard_range_fin3_diff_singleton_le_two hfeet_injective i
  have hB_card : B.ncard <= 3 := by
    simpa [B] using
      ncard_insert_range_fin3_diff_singleton_le_three
        hfeet_injective i root
  let Sep : Separation G := Separation.ofCoreAndBoundary (G := G) K B hclosed
  have hfoot_not_K : feet i ∉ K := by
    intro hfootK
    have hfoot_compl :
        feet i ∈ (insert root (Set.range feet))ᶜ :=
      induceComponentSupport_subset (G := G) C hfootK
    exact hfoot_compl (by simp)
  have hfoot_not_B : feet i ∉ B := by
    intro hfootB
    rcases hfootB with hroot | hdiff
    · exact hroot_not_feet ⟨i, hroot⟩
    · exact hdiff.2 rfl
  have hleft_only : (Sep.left \ Sep.right).Nonempty := by
    refine ⟨feet i, ?_, ?_⟩
    · exact hfoot_not_K
    · intro hright
      rcases hright with hK | hB
      · exact hfoot_not_K hK
      · exact hfoot_not_B hB
  have hright_only : (Sep.right \ Sep.left).Nonempty := by
    simpa [Sep] using
      Separation.ofCoreAndBoundary_right_only_nonempty
        (G := G) K B hclosed (induceComponentSupport_nonempty (G := G) C)
  have hproper : Sep.Proper := ⟨hleft_only, hright_only⟩
  have horder : Sep.OrderAtMost 3 := by
    simpa [Sep] using
      Separation.ofCoreAndBoundary_orderAtMost_of_boundary_ncard_le
        (G := G) K B hclosed hB_card
  exact isFourConnected_no_proper_separation_orderAtMost_three
    (G := G) hG Sep hproper horder

theorem IsFourConnected.exists_triad_avoiding_root_of_three_distinct_vertices
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    (hG : IsFourConnected G)
    {feet : Fin 3 -> V}
    {root : V}
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet) :
    Exists fun T : Triad G feet => root ∉ T.vertexSet := by
  classical
  let S : Set V := insert root (Set.range feet)
  have hS_card : S.ncard <= 4 := by
    simpa [S] using ncard_insert_range_fin3_le_four hfeet_injective root
  have hS_compl_nonempty : Sᶜ.Nonempty := by
    by_contra hnone
    have huniv_subset : (Set.univ : Set V) ⊆ S := by
      intro v _hv
      by_contra hvS
      exact hnone ⟨v, hvS⟩
    have hcard_univ : Fintype.card V <= 4 := by
      have hle : (Set.univ : Set V).ncard <= S.ncard :=
        Set.ncard_le_ncard huniv_subset
      rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
      exact le_trans hle hS_card
    have hcard_gt : 4 < Fintype.card V := by
      have hnat : 4 < Nat.card V := hG.1
      rwa [Nat.card_eq_fintype_card] at hnat
    omega
  obtain ⟨z, hzS⟩ := hS_compl_nonempty
  let zA : ((insert root (Set.range feet))ᶜ : Set V) := ⟨z, by
    simpa [S] using hzS⟩
  let C : (G.induce (insert root (Set.range feet))ᶜ).ConnectedComponent :=
    (G.induce (insert root (Set.range feet))ᶜ).connectedComponentMk zA
  let H : G.Subgraph := induceComponentSubgraph (G := G) C
  have hH_connected : H.coe.Connected := by
    exact SimpleGraph.Subgraph.connected_iff'.mp (by
      simpa [H] using induceComponentSubgraph_connected (G := G) C)
  have hcomponent_adj :
      forall i : Fin 3,
        Exists fun u : V =>
          u ∈ induceComponentSupport (G := G) C ∧ G.Adj u (feet i) := by
    intro i
    exact hG.delete_root_feet_component_adjacent_to_foot
      hfeet_injective hroot_not_feet C i
  let x : Fin 3 -> V := fun i => Classical.choose (hcomponent_adj i)
  have hxH : forall i : Fin 3, x i ∈ H.verts := by
    intro i
    rw [show H.verts = induceComponentSupport (G := G) C by
      simp [H]]
    exact (Classical.choose_spec (hcomponent_adj i)).1
  have hfeet_not_H : forall i : Fin 3, feet i ∉ H.verts := by
    intro i hfoot
    have hfootK : feet i ∈ induceComponentSupport (G := G) C := by
      simpa [H] using hfoot
    have hfoot_compl :
        feet i ∈ (insert root (Set.range feet))ᶜ :=
      induceComponentSupport_subset (G := G) C hfootK
    exact hfoot_compl (by simp)
  have hroot_not_H : root ∉ H.verts := by
    intro hrootH
    have hrootK : root ∈ induceComponentSupport (G := G) C := by
      simpa [H] using hrootH
    have hroot_compl :
        root ∈ (insert root (Set.range feet))ᶜ :=
      induceComponentSupport_subset (G := G) C hrootK
    exact hroot_compl (by simp)
  have hadj : forall i : Fin 3, G.Adj (x i) (feet i) := by
    intro i
    exact (Classical.choose_spec (hcomponent_adj i)).2
  obtain ⟨T, hT_subset⟩ :=
    Triad.exists_of_connected_fragment_adjacent_to_feet_subset
      (G := G) (feet := feet) (x := x) H hH_connected hfeet_injective
      hxH hfeet_not_H hadj
  refine ⟨T, ?_⟩
  intro hrootT
  have hroot_fragment := hT_subset hrootT
  have hroot_H_or_feet :
      root ∈ H.verts ∪ Set.range feet :=
    connected_fragment_with_pendant_edges_verts_subset
      (G := G) H hxH hadj hroot_fragment
  rcases hroot_H_or_feet with hrootH | hrootFeet
  · exact hroot_not_H hrootH
  · exact hroot_not_feet hrootFeet

theorem IsFourConnected.exists_triad_avoiding_root_of_triangle
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    (hG : IsFourConnected G)
    {feet : Fin 3 -> V}
    {root : V}
    (htriangle : IsTriangle G (feet 0) (feet 1) (feet 2))
    (hroot_not_feet : root ∉ Set.range feet) :
    Exists fun T : Triad G feet => root ∉ T.vertexSet :=
  hG.exists_triad_avoiding_root_of_three_distinct_vertices
    (IsTriangle.injective_fin3 htriangle) hroot_not_feet

end Schematic.Math.GraphTheory
