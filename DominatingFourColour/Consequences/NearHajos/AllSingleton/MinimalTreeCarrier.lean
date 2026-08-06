import DominatingFourColour.Consequences.NearHajos.AllSingleton.AttachmentPatterns

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem dominating_K5_model_tail_all_singleton_first_branch_small_attachment_carrier_near_hajos
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_card : B.verts.ncard <= 2) :
    NearHajosStrengtheningConclusion G := by
  classical
  obtain ⟨u, v, huB, hvB, hvalues⟩ :=
    fin4_map_into_set_ncard_le_two_has_two_values
      (V := V) (A := B.verts) attach hB_terminal hB_card
  exact
    dominating_K5_model_tail_all_singleton_first_branch_two_value_attachments_near_hajos
      T htail (hB_le.left huB) (hB_le.left hvB) attach hattach hvalues

theorem dominating_K5_model_tail_all_singleton_first_branch_large_minimal_attachment_carrier
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (hno_small :
      Not (Exists fun htail' :
          forall i : Fin 4, BranchIsSingleton T.tailK4 i =>
        Exists fun attach : Fin 4 -> V =>
          Exists fun B : G.Subgraph =>
            (forall i : Fin 4,
              attach i ∈ (T.branch (0 : Fin 5)).verts ∧
                G.Adj (attach i) (htail' i).choose) ∧
              B ≤ T.branch (0 : Fin 5) ∧
                (forall i : Fin 4, attach i ∈ B.verts) ∧
                  B.verts.ncard <= 2)) :
    Exists fun attach : Fin 4 -> V =>
      (forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose) ∧
        Exists fun B : G.Subgraph =>
          B ≤ T.branch (0 : Fin 5) ∧
            B.coe.Connected ∧
              (forall i : Fin 4, attach i ∈ B.verts) ∧
                (forall B' : G.Subgraph,
                  B' ≤ T.branch (0 : Fin 5) ->
                    B'.coe.Connected ->
                      (forall i : Fin 4, attach i ∈ B'.verts) ->
                        B'.verts ⊆ B.verts ->
                          B.verts ⊆ B'.verts) ∧
                  3 <= B.verts.ncard := by
  classical
  obtain ⟨attach, hattach, B, hB_le, hB_connected, hB_terminal, hB_minimal⟩ :=
    dominating_K5_model_tail_all_singleton_first_branch_minimal_attachment_carrier
      T htail
  have hB_large : 3 <= B.verts.ncard := by
    by_contra hlt
    have hB_small : B.verts.ncard <= 2 := by omega
    exact hno_small
      ⟨htail, attach, B, hattach, hB_le, hB_terminal, hB_small⟩
  exact ⟨attach, hattach, B, hB_le, hB_connected, hB_terminal,
    hB_minimal, hB_large⟩

theorem dominating_K5_model_tail_all_singleton_first_branch_large_minimal_attachment_carrier_three_distinct
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (hno_two :
      Not (Exists fun htail' :
          forall i : Fin 4, BranchIsSingleton T.tailK4 i =>
        Exists fun attach : Fin 4 -> V =>
          Exists fun u : V =>
            Exists fun v : V =>
              (forall i : Fin 4,
                attach i ∈ (T.branch (0 : Fin 5)).verts ∧
                  G.Adj (attach i) (htail' i).choose) ∧
                u ∈ (T.branch (0 : Fin 5)).verts ∧
                  v ∈ (T.branch (0 : Fin 5)).verts ∧
                    (forall i : Fin 4, attach i = u ∨ attach i = v)))
    (hno_small :
      Not (Exists fun htail' :
          forall i : Fin 4, BranchIsSingleton T.tailK4 i =>
        Exists fun attach : Fin 4 -> V =>
          Exists fun B : G.Subgraph =>
            (forall i : Fin 4,
              attach i ∈ (T.branch (0 : Fin 5)).verts ∧
                G.Adj (attach i) (htail' i).choose) ∧
              B ≤ T.branch (0 : Fin 5) ∧
                (forall i : Fin 4, attach i ∈ B.verts) ∧
                  B.verts.ncard <= 2)) :
    Exists fun attach : Fin 4 -> V =>
      (forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose) ∧
        3 <= (Set.range attach).ncard ∧
          Exists fun B : G.Subgraph =>
            B ≤ T.branch (0 : Fin 5) ∧
              B.coe.Connected ∧
                (forall i : Fin 4, attach i ∈ B.verts) ∧
                  (forall B' : G.Subgraph,
                    B' ≤ T.branch (0 : Fin 5) ->
                      B'.coe.Connected ->
                        (forall i : Fin 4, attach i ∈ B'.verts) ->
                          B'.verts ⊆ B.verts ->
                            B.verts ⊆ B'.verts) ∧
                    3 <= B.verts.ncard := by
  classical
  obtain ⟨attach, hattach, B, hB_le, hB_connected, hB_terminal,
    hB_minimal, hB_large⟩ :=
    dominating_K5_model_tail_all_singleton_first_branch_large_minimal_attachment_carrier
      T htail hno_small
  have hnot_two_attach :
      Not (Exists fun u : V =>
        Exists fun v : V =>
          u ∈ (T.branch (0 : Fin 5)).verts ∧
            v ∈ (T.branch (0 : Fin 5)).verts ∧
              forall i : Fin 4, attach i = u ∨ attach i = v) := by
    rintro ⟨u, v, hu, hv, hvalues⟩
    exact hno_two ⟨htail, attach, u, v, hattach, hu, hv, hvalues⟩
  have hattach_range_large :
      3 <= (Set.range attach).ncard :=
    fin4_range_ncard_ge_three_of_not_two_values_in_set
      (V := V) (A := (T.branch (0 : Fin 5)).verts)
      attach (fun i => (hattach i).1) hnot_two_attach
  exact ⟨attach, hattach, hattach_range_large, B, hB_le, hB_connected,
    hB_terminal, hB_minimal, hB_large⟩

theorem dominating_K5_model_tail_all_singleton_first_branch_large_minimal_attachment_carrier_three_distinct_indices
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (hno_two :
      Not (Exists fun htail' :
          forall i : Fin 4, BranchIsSingleton T.tailK4 i =>
        Exists fun attach : Fin 4 -> V =>
          Exists fun u : V =>
            Exists fun v : V =>
              (forall i : Fin 4,
                attach i ∈ (T.branch (0 : Fin 5)).verts ∧
                  G.Adj (attach i) (htail' i).choose) ∧
                u ∈ (T.branch (0 : Fin 5)).verts ∧
                  v ∈ (T.branch (0 : Fin 5)).verts ∧
                    (forall i : Fin 4, attach i = u ∨ attach i = v)))
    (hno_small :
      Not (Exists fun htail' :
          forall i : Fin 4, BranchIsSingleton T.tailK4 i =>
        Exists fun attach : Fin 4 -> V =>
          Exists fun B : G.Subgraph =>
            (forall i : Fin 4,
              attach i ∈ (T.branch (0 : Fin 5)).verts ∧
                G.Adj (attach i) (htail' i).choose) ∧
              B ≤ T.branch (0 : Fin 5) ∧
                (forall i : Fin 4, attach i ∈ B.verts) ∧
                  B.verts.ncard <= 2)) :
    Exists fun attach : Fin 4 -> V =>
      (forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose) ∧
        Exists fun i : Fin 4 =>
          Exists fun j : Fin 4 =>
            Exists fun k : Fin 4 =>
              attach i ≠ attach j ∧
                attach i ≠ attach k ∧
                  attach j ≠ attach k ∧
                    Exists fun B : G.Subgraph =>
                      B ≤ T.branch (0 : Fin 5) ∧
                        B.coe.Connected ∧
                          (forall i : Fin 4, attach i ∈ B.verts) ∧
                            (forall B' : G.Subgraph,
                              B' ≤ T.branch (0 : Fin 5) ->
                                B'.coe.Connected ->
                                  (forall i : Fin 4, attach i ∈ B'.verts) ->
                                    B'.verts ⊆ B.verts ->
                                      B.verts ⊆ B'.verts) ∧
                              3 <= B.verts.ncard := by
  classical
  obtain ⟨attach, hattach, hattach_large, B, hB_le, hB_connected,
    hB_terminal, hB_minimal, hB_large⟩ :=
    dominating_K5_model_tail_all_singleton_first_branch_large_minimal_attachment_carrier_three_distinct
      T htail hno_two hno_small
  obtain ⟨i, j, k, hij, hik, hjk⟩ :=
    fin4_exists_three_pairwise_distinct_values_of_range_ncard_ge_three
      attach hattach_large
  exact ⟨attach, hattach, i, j, k, hij, hik, hjk, B, hB_le, hB_connected,
    hB_terminal, hB_minimal, hB_large⟩

theorem dominating_K5_model_tail_all_singleton_first_branch_large_minimal_attachment_tree_carrier
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (hno_two :
      Not (Exists fun htail' :
          forall i : Fin 4, BranchIsSingleton T.tailK4 i =>
        Exists fun attach : Fin 4 -> V =>
          Exists fun u : V =>
            Exists fun v : V =>
              (forall i : Fin 4,
                attach i ∈ (T.branch (0 : Fin 5)).verts ∧
                  G.Adj (attach i) (htail' i).choose) ∧
                u ∈ (T.branch (0 : Fin 5)).verts ∧
                  v ∈ (T.branch (0 : Fin 5)).verts ∧
                    (forall i : Fin 4, attach i = u ∨ attach i = v)))
    (hno_small :
      Not (Exists fun htail' :
          forall i : Fin 4, BranchIsSingleton T.tailK4 i =>
        Exists fun attach : Fin 4 -> V =>
          Exists fun B : G.Subgraph =>
            (forall i : Fin 4,
              attach i ∈ (T.branch (0 : Fin 5)).verts ∧
                G.Adj (attach i) (htail' i).choose) ∧
              B ≤ T.branch (0 : Fin 5) ∧
                (forall i : Fin 4, attach i ∈ B.verts) ∧
                  B.verts.ncard <= 2)) :
    Exists fun attach : Fin 4 -> V =>
      (forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose) ∧
        Exists fun i : Fin 4 =>
          Exists fun j : Fin 4 =>
            Exists fun k : Fin 4 =>
              attach i ≠ attach j ∧
                attach i ≠ attach k ∧
                  attach j ≠ attach k ∧
                    Exists fun B : G.Subgraph =>
                      B ≤ T.branch (0 : Fin 5) ∧
                        B.coe.Connected ∧
                          (forall i : Fin 4, attach i ∈ B.verts) ∧
                            (forall B' : G.Subgraph,
                              B' ≤ T.branch (0 : Fin 5) ->
                                B'.coe.Connected ->
                                  (forall i : Fin 4, attach i ∈ B'.verts) ->
                                    B'.verts ⊆ B.verts ->
                                      B.verts ⊆ B'.verts) ∧
                              3 <= B.verts.ncard ∧
                                Exists fun TB : B.coe.Subgraph =>
                                  TB.coe.IsTree ∧ TB.IsSpanning := by
  classical
  obtain ⟨attach, hattach, i, j, k, hij, hik, hjk, B, hB_le,
    hB_connected, hB_terminal, hB_minimal, hB_large⟩ :=
    dominating_K5_model_tail_all_singleton_first_branch_large_minimal_attachment_carrier_three_distinct_indices
      T htail hno_two hno_small
  obtain ⟨TB, hTB_tree, hTB_spanning, _hTB_terminal⟩ :=
    Subgraph.Connected.exists_spanning_tree_coe_subgraph_containing
      (B := B) hB_connected attach hB_terminal
  exact ⟨attach, hattach, i, j, k, hij, hik, hjk, B, hB_le, hB_connected,
    hB_terminal, hB_minimal, hB_large, TB, hTB_tree, hTB_spanning⟩

theorem dominating_K5_model_tail_all_singleton_first_branch_tree_carrier_root_paths
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (TB : B.coe.Subgraph)
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning)
    {apex : V}
    (hapex : apex ∈ B.verts) :
    Exists fun stem : forall i : Fin 4, G.Walk apex (attach i) =>
      (forall i : Fin 4, (stem i).IsPath) ∧
        (forall i : Fin 4, forall {z : V},
          z ∈ (stem i).support ->
            z ∈ (T.branch (0 : Fin 5)).verts) ∧
          forall i : Fin 4, forall z : V, z ∈ (stem i).support ->
            Exists fun hzB : z ∈ B.verts =>
              (⟨z, hzB⟩ : B.verts) ∈ TB.verts := by
  classical
  obtain ⟨stem, hstem_path, hstem_le_B, hstem_tree_support⟩ :=
    Subgraph.Connected.exists_rooted_paths_in_spanning_coe_subgraph
      (B := B) (T := TB) hTB_tree.connected hTB_spanning hapex
      attach hB_terminal
  refine ⟨stem, hstem_path, ?_, hstem_tree_support⟩
  intro i z hz
  exact hB_le.left
    ((hstem_le_B i).left (by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph]
      exact hz))

theorem tree_bridge_internal_left_stem_yields_path_avoiding_left
    {V : Type u} {G : SimpleGraph V}
    {B : G.Subgraph}
    {TB : B.coe.Subgraph}
    [DecidableEq TB.verts]
    (hTB_tree : TB.coe.IsTree)
    {leftT rightT attachT : TB.verts}
    {p : B.coe.Walk (leftT : B.verts) (rightT : B.verts)}
    {stem : B.coe.Walk (leftT : B.verts) (attachT : B.verts)}
    (hp_le : p.toSubgraph ≤ TB)
    (hstem_le : stem.toSubgraph ≤ TB)
    (hp : p.IsPath)
    (hstem : stem.IsPath)
    (hright_ne_left : rightT ≠ leftT)
    {zT : TB.verts}
    (hz_p : (zT : B.verts) ∈ Walk.InternalVertices p)
    (hz_stem : (zT : B.verts) ∈ stem.support)
    (hz_ne_left : (zT : B.verts) ≠ (leftT : B.verts)) :
    Exists fun r : B.coe.Walk (rightT : B.verts) (attachT : B.verts) =>
      r.toSubgraph ≤ TB ∧ r.IsPath ∧ (leftT : B.verts) ∉ r.support := by
  classical
  have hattach_ne_left : attachT ≠ leftT := by
    intro h
    have hattach_val : (attachT : B.verts) = (leftT : B.verts) :=
      congrArg (fun x : TB.verts => (x : B.verts)) h
    exact
      (Walk.IsPath.end_ne_start_of_mem_support_ne_start
        hstem hz_stem hz_ne_left) hattach_val
  exact
    Subgraph.tree_exists_endpoint_path_avoiding_root_of_rooted_paths_common_nonroot
      (G := B.coe) (T := TB) (root := leftT) (a := rightT)
      (b := attachT) hTB_tree hp_le hstem_le hp hstem hright_ne_left
      hattach_ne_left hz_p.1 hz_stem hz_ne_left

theorem tree_bridge_internal_right_stem_yields_path_avoiding_right
    {V : Type u} {G : SimpleGraph V}
    {B : G.Subgraph}
    {TB : B.coe.Subgraph}
    [DecidableEq TB.verts]
    (hTB_tree : TB.coe.IsTree)
    {leftT rightT attachT : TB.verts}
    {p : B.coe.Walk (leftT : B.verts) (rightT : B.verts)}
    {stem : B.coe.Walk (rightT : B.verts) (attachT : B.verts)}
    (hp_le : p.toSubgraph ≤ TB)
    (hstem_le : stem.toSubgraph ≤ TB)
    (hp : p.IsPath)
    (hstem : stem.IsPath)
    (hleft_ne_right : leftT ≠ rightT)
    {zT : TB.verts}
    (hz_p : (zT : B.verts) ∈ Walk.InternalVertices p)
    (hz_stem : (zT : B.verts) ∈ stem.support)
    (hz_ne_right : (zT : B.verts) ≠ (rightT : B.verts)) :
    Exists fun r : B.coe.Walk (leftT : B.verts) (attachT : B.verts) =>
      r.toSubgraph ≤ TB ∧ r.IsPath ∧ (rightT : B.verts) ∉ r.support := by
  classical
  have hattach_ne_right : attachT ≠ rightT := by
    intro h
    have hattach_val : (attachT : B.verts) = (rightT : B.verts) :=
      congrArg (fun x : TB.verts => (x : B.verts)) h
    exact
      (Walk.IsPath.end_ne_start_of_mem_support_ne_start
        hstem hz_stem hz_ne_right) hattach_val
  have hp_rev : p.reverse.toSubgraph ≤ TB := by
    simpa [SimpleGraph.Walk.toSubgraph_reverse] using hp_le
  have hz_p_rev : (zT : B.verts) ∈ Walk.InternalVertices p.reverse := by
    exact (Walk.mem_internalVertices_reverse_iff p).mpr hz_p
  exact
    Subgraph.tree_exists_endpoint_path_avoiding_root_of_rooted_paths_common_nonroot
      (G := B.coe) (T := TB) (root := rightT) (a := leftT)
      (b := attachT) hTB_tree hp_rev hstem_le hp.reverse hstem
      hleft_ne_right hattach_ne_right hz_p_rev.1 hz_stem hz_ne_right

theorem dominating_K5_model_tail_all_singleton_first_branch_minimal_tree_nonterminal_degree_ne_one
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (TB : B.coe.Subgraph)
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning)
    {v : V}
    (hvB : v ∈ B.verts)
    [Fintype (TB.coe.neighborSet
      (⟨(⟨v, hvB⟩ : B.verts), hTB_spanning (⟨v, hvB⟩ : B.verts)⟩ : TB.verts))]
    (hv_not_attach : forall i : Fin 4, attach i ≠ v) :
    TB.coe.degree
        (⟨(⟨v, hvB⟩ : B.verts), hTB_spanning (⟨v, hvB⟩ : B.verts)⟩ : TB.verts) ≠ 1 := by
  exact
    Subgraph.minimal_connected_spanning_tree_nonterminal_degree_ne_one
      (C := T.branch (0 : Fin 5)) (B := B) (terminal := attach)
      hB_le hB_terminal hB_minimal hTB_tree.connected hTB_spanning hvB
      hv_not_attach

theorem dominating_K5_model_tail_all_singleton_first_branch_minimal_tree_leaf_mem_attachment_range
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (TB : B.coe.Subgraph)
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning)
    {v : V}
    (hvB : v ∈ B.verts)
    [Fintype (TB.coe.neighborSet
      (⟨(⟨v, hvB⟩ : B.verts), hTB_spanning (⟨v, hvB⟩ : B.verts)⟩ : TB.verts))]
    (hdegree :
      TB.coe.degree
        (⟨(⟨v, hvB⟩ : B.verts), hTB_spanning (⟨v, hvB⟩ : B.verts)⟩ : TB.verts) = 1) :
    v ∈ Set.range attach := by
  exact
    Subgraph.minimal_connected_spanning_tree_leaf_mem_terminal_range
      (C := T.branch (0 : Fin 5)) (B := B) (terminal := attach)
      hB_le hB_terminal hB_minimal hTB_tree.connected hTB_spanning hvB
      hdegree

theorem dominating_K5_model_tail_all_singleton_first_branch_minimal_tree_exists_two_attachment_leaves
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableRel TB.coe.Adj]
    [Nontrivial TB.verts]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    Exists fun uT : TB.verts =>
      Exists fun vT : TB.verts =>
        uT ≠ vT ∧
          TB.coe.degree uT = 1 ∧
            TB.coe.degree vT = 1 ∧
              ((uT : B.verts) : V) ∈ Set.range attach ∧
                ((vT : B.verts) : V) ∈ Set.range attach := by
  exact
    Subgraph.minimal_connected_spanning_tree_exists_two_terminal_leaves
      (C := T.branch (0 : Fin 5)) (B := B) (terminal := attach)
      hB_le hB_terminal hB_minimal hTB_tree hTB_spanning

theorem dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_exists_two_attachment_leaves
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_large : 3 <= B.verts.ncard)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableEq TB.verts]
    [DecidableRel TB.coe.Adj]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    Exists fun uT : TB.verts =>
      Exists fun vT : TB.verts =>
        uT ≠ vT ∧
          TB.coe.degree uT = 1 ∧
            TB.coe.degree vT = 1 ∧
              ((uT : B.verts) : V) ∈ Set.range attach ∧
                ((vT : B.verts) : V) ∈ Set.range attach := by
  classical
  letI : Nontrivial TB.verts :=
    Subgraph.spanning_subgraph_nontrivial_of_ncard_ge_three
      (G := G) hTB_spanning hB_large
  exact
    dominating_K5_model_tail_all_singleton_first_branch_minimal_tree_exists_two_attachment_leaves
      T attach B hB_le hB_terminal hB_minimal TB hTB_tree hTB_spanning

theorem dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_exists_attachment_leaf_bridge_path
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_large : 3 <= B.verts.ncard)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableEq TB.verts]
    [DecidableRel TB.coe.Adj]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    Exists fun left : V =>
      Exists fun right : V =>
        Exists fun p : G.Walk left right =>
          left ∈ (T.branch (0 : Fin 5)).verts ∧
            right ∈ (T.branch (0 : Fin 5)).verts ∧
              left ≠ right ∧
                p.IsPath ∧
                  (forall {z : V},
                    z ∈ Walk.InternalVertices p ->
                      z ∈ (T.branch (0 : Fin 5)).verts) ∧
                    left ∈ Set.range attach ∧
                      right ∈ Set.range attach := by
  classical
  obtain ⟨uT, vT, huv, _hu_degree, _hv_degree, hu_range, hv_range⟩ :=
    dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_exists_two_attachment_leaves
      T attach B hB_le hB_terminal hB_minimal hB_large TB hTB_tree hTB_spanning
  let left : V := ((uT : B.verts) : V)
  let right : V := ((vT : B.verts) : V)
  have hleftB : left ∈ B.verts := (uT : B.verts).2
  have hrightB : right ∈ B.verts := (vT : B.verts).2
  have hleft_ne_right : left ≠ right := by
    intro h
    exact huv (by
      apply Subtype.ext
      apply Subtype.ext
      exact h)
  obtain ⟨p, hp, hp_le, _hp_support, hp_internal⟩ :=
    Subgraph.Connected.exists_path_between_in_spanning_coe_subgraph_internal_subset
      (B := B) (T := TB) hTB_tree.connected hTB_spanning hleftB hrightB
  refine ⟨left, right, p, hB_le.left hleftB, hB_le.left hrightB,
    hleft_ne_right, hp, ?_, by simpa [left] using hu_range,
    by simpa [right] using hv_range⟩
  intro z hz
  obtain ⟨hzB, _hzT⟩ := hp_internal z hz
  exact hB_le.left hzB

theorem dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_exists_attachment_leaf_bridge_path_with_indices
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_large : 3 <= B.verts.ncard)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableEq TB.verts]
    [DecidableRel TB.coe.Adj]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    Exists fun left : V =>
      Exists fun right : V =>
        Exists fun p : G.Walk left right =>
          Exists fun i : Fin 4 =>
            Exists fun j : Fin 4 =>
              left ∈ (T.branch (0 : Fin 5)).verts ∧
                right ∈ (T.branch (0 : Fin 5)).verts ∧
                  left ≠ right ∧
                    p.IsPath ∧
                      (forall {z : V},
                        z ∈ Walk.InternalVertices p ->
                          z ∈ (T.branch (0 : Fin 5)).verts) ∧
                        left = attach i ∧
                          right = attach j ∧
                            G.Adj left (htail i).choose ∧
                              G.Adj right (htail j).choose ∧ i ≠ j := by
  classical
  obtain ⟨left, right, p, hleft_mem, hright_mem, hleft_ne_right, hp,
    hp_internal, hleft_range, hright_range⟩ :=
    dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_exists_attachment_leaf_bridge_path
      T attach B hB_le hB_terminal hB_minimal hB_large TB hTB_tree hTB_spanning
  rcases hleft_range with ⟨i, rfl⟩
  rcases hright_range with ⟨j, rfl⟩
  have hij : i ≠ j := by
    intro hij
    exact hleft_ne_right (by simp [hij])
  refine ⟨attach i, attach j, p, i, j, hleft_mem, hright_mem,
    hleft_ne_right, hp, hp_internal, rfl, rfl, ?_, ?_, hij⟩
  · exact (hattach i).2
  · exact (hattach j).2

theorem dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_exists_attachment_leaf_bridge_path_with_indices_and_degrees
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_large : 3 <= B.verts.ncard)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableEq TB.verts]
    [DecidableRel TB.coe.Adj]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    Exists fun leftT : TB.verts =>
      Exists fun rightT : TB.verts =>
        Exists fun p : G.Walk ((leftT : B.verts) : V) ((rightT : B.verts) : V) =>
          Exists fun i : Fin 4 =>
            Exists fun j : Fin 4 =>
              leftT ≠ rightT ∧
                TB.coe.degree leftT = 1 ∧
                  TB.coe.degree rightT = 1 ∧
                    p.IsPath ∧
                      (forall {z : V},
                        z ∈ Walk.InternalVertices p ->
                          z ∈ (T.branch (0 : Fin 5)).verts) ∧
                        ((leftT : B.verts) : V) = attach i ∧
                          ((rightT : B.verts) : V) = attach j ∧
                            G.Adj ((leftT : B.verts) : V) (htail i).choose ∧
                              G.Adj ((rightT : B.verts) : V) (htail j).choose ∧ i ≠ j := by
  classical
  obtain ⟨leftT, rightT, hleft_ne_right, hleft_degree, hright_degree,
    hleft_range, hright_range⟩ :=
    dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_exists_two_attachment_leaves
      T attach B hB_le hB_terminal hB_minimal hB_large TB hTB_tree hTB_spanning
  let left : V := ((leftT : B.verts) : V)
  let right : V := ((rightT : B.verts) : V)
  have hleftB : left ∈ B.verts := (leftT : B.verts).2
  have hrightB : right ∈ B.verts := (rightT : B.verts).2
  obtain ⟨p, hp, _hp_le, _hp_support, hp_internal⟩ :=
    Subgraph.Connected.exists_path_between_in_spanning_coe_subgraph_internal_subset
      (B := B) (T := TB) hTB_tree.connected hTB_spanning hleftB hrightB
  rcases hleft_range with ⟨i, hleft_eq⟩
  rcases hright_range with ⟨j, hright_eq⟩
  have hij : i ≠ j := by
    intro hij
    exact hleft_ne_right (by
      apply Subtype.ext
      apply Subtype.ext
      calc
        ((leftT : B.verts) : V) = attach i := hleft_eq.symm
        _ = attach j := by rw [hij]
        _ = ((rightT : B.verts) : V) := hright_eq)
  refine ⟨leftT, rightT, p, i, j, hleft_ne_right, hleft_degree,
    hright_degree, hp, ?_, hleft_eq.symm, hright_eq.symm, ?_, ?_, hij⟩
  · intro z hz
    obtain ⟨hzB, _hzT⟩ := hp_internal z hz
    exact hB_le.left hzB
  · simpa [hleft_eq] using (hattach i).2
  · simpa [hright_eq] using (hattach j).2

theorem dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_exists_attachment_leaf_bridge_coe_path_with_indices_and_degrees
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (htail : forall i : Fin 4, BranchIsSingleton T.tailK4 i)
    (attach : Fin 4 -> V)
    (hattach :
      forall i : Fin 4,
        attach i ∈ (T.branch (0 : Fin 5)).verts ∧
          G.Adj (attach i) (htail i).choose)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_large : 3 <= B.verts.ncard)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableEq TB.verts]
    [DecidableRel TB.coe.Adj]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    Exists fun leftT : TB.verts =>
      Exists fun rightT : TB.verts =>
        Exists fun pB : B.coe.Walk (leftT : B.verts) (rightT : B.verts) =>
          Exists fun i : Fin 4 =>
            Exists fun j : Fin 4 =>
              leftT ≠ rightT ∧
                TB.coe.degree leftT = 1 ∧
                  TB.coe.degree rightT = 1 ∧
                    pB.IsPath ∧
                      pB.toSubgraph ≤ TB ∧
                        ((leftT : B.verts) : V) = attach i ∧
                          ((rightT : B.verts) : V) = attach j ∧
                            G.Adj ((leftT : B.verts) : V) (htail i).choose ∧
                              G.Adj ((rightT : B.verts) : V) (htail j).choose ∧ i ≠ j := by
  classical
  obtain ⟨leftT, rightT, hleft_ne_right, hleft_degree, hright_degree,
    hleft_range, hright_range⟩ :=
    dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_exists_two_attachment_leaves
      T attach B hB_le hB_terminal hB_minimal hB_large TB hTB_tree hTB_spanning
  let left : V := ((leftT : B.verts) : V)
  let right : V := ((rightT : B.verts) : V)
  have hleftB : left ∈ B.verts := (leftT : B.verts).2
  have hrightB : right ∈ B.verts := (rightT : B.verts).2
  obtain ⟨pB, hpB, hpB_le⟩ :=
    Subgraph.Connected.exists_coe_path_between_in_spanning_coe_subgraph
      (B := B) (T := TB) hTB_tree.connected hTB_spanning hleftB hrightB
  rcases hleft_range with ⟨i, hleft_eq⟩
  rcases hright_range with ⟨j, hright_eq⟩
  have hij : i ≠ j := by
    intro hij
    exact hleft_ne_right (by
      apply Subtype.ext
      apply Subtype.ext
      calc
        ((leftT : B.verts) : V) = attach i := hleft_eq.symm
        _ = attach j := by rw [hij]
        _ = ((rightT : B.verts) : V) := hright_eq)
  refine ⟨leftT, rightT, pB, i, j, hleft_ne_right, hleft_degree,
    hright_degree, hpB, hpB_le, hleft_eq.symm, hright_eq.symm, ?_, ?_, hij⟩
  · simpa [hleft_eq] using (hattach i).2
  · simpa [hright_eq] using (hattach j).2

theorem dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_card_branch_vertices_le_two
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_large : 3 <= B.verts.ncard)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableRel TB.coe.Adj]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    (Finset.univ.filter fun vT : TB.verts => 3 <= TB.coe.degree vT).card <= 2 := by
  classical
  letI : Nontrivial TB.verts :=
    Subgraph.spanning_subgraph_nontrivial_of_ncard_ge_three
      (G := G) hTB_spanning hB_large
  exact
    Subgraph.minimal_connected_spanning_tree_card_degree_ge_three_le_two_of_four_terminals
      (C := T.branch (0 : Fin 5)) (B := B) (terminal := attach)
      hB_le hB_terminal hB_minimal hTB_tree hTB_spanning

theorem dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_branch_vertex_cases
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_large : 3 <= B.verts.ncard)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableEq TB.verts]
    [DecidableRel TB.coe.Adj]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    let branchVerts : Finset TB.verts :=
      Finset.univ.filter fun vT : TB.verts => 3 <= TB.coe.degree vT
    branchVerts = ∅ ∨
      (Exists fun center : TB.verts => branchVerts = {center}) ∨
        Exists fun left : TB.verts =>
          Exists fun right : TB.verts => left ≠ right ∧ branchVerts = {left, right} := by
  classical
  intro branchVerts
  exact finset_card_le_two_cases branchVerts
    (by
      simpa [branchVerts] using
        dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_card_branch_vertices_le_two
          T attach B hB_le hB_terminal hB_minimal hB_large TB hTB_tree hTB_spanning)

theorem DominatingK5Model.first_branch_large_minimal_tree_exists_two_attachment_leaves
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_large : 3 <= B.verts.ncard)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableEq TB.verts]
    [DecidableRel TB.coe.Adj]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    Exists fun uT : TB.verts =>
      Exists fun vT : TB.verts =>
        uT ≠ vT ∧
          TB.coe.degree uT = 1 ∧
            TB.coe.degree vT = 1 ∧
              ((uT : B.verts) : V) ∈ Set.range attach ∧
                ((vT : B.verts) : V) ∈ Set.range attach := by
  exact
    dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_exists_two_attachment_leaves
      T attach B hB_le hB_terminal hB_minimal hB_large TB hTB_tree
      hTB_spanning

theorem DominatingK5Model.first_branch_large_minimal_tree_exists_attachment_leaf_bridge_coe_path_with_indices_and_degrees
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_large : 3 <= B.verts.ncard)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableEq TB.verts]
    [DecidableRel TB.coe.Adj]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    Exists fun leftT : TB.verts =>
      Exists fun rightT : TB.verts =>
        Exists fun pB : B.coe.Walk (leftT : B.verts) (rightT : B.verts) =>
          Exists fun i : Fin 4 =>
            Exists fun j : Fin 4 =>
              leftT ≠ rightT ∧
                TB.coe.degree leftT = 1 ∧
                  TB.coe.degree rightT = 1 ∧
                    pB.IsPath ∧
                      pB.toSubgraph ≤ TB ∧
                        ((leftT : B.verts) : V) = attach i ∧
                          ((rightT : B.verts) : V) = attach j ∧ i ≠ j := by
  classical
  obtain ⟨leftT, rightT, hleft_ne_right, hleft_degree, hright_degree,
    hleft_range, hright_range⟩ :=
    T.first_branch_large_minimal_tree_exists_two_attachment_leaves
      attach B hB_le hB_terminal hB_minimal hB_large TB hTB_tree
      hTB_spanning
  let left : V := ((leftT : B.verts) : V)
  let right : V := ((rightT : B.verts) : V)
  have hleftB : left ∈ B.verts := (leftT : B.verts).2
  have hrightB : right ∈ B.verts := (rightT : B.verts).2
  obtain ⟨pB, hpB, hpB_le⟩ :=
    Subgraph.Connected.exists_coe_path_between_in_spanning_coe_subgraph
      (B := B) (T := TB) hTB_tree.connected hTB_spanning hleftB hrightB
  rcases hleft_range with ⟨i, hleft_eq⟩
  rcases hright_range with ⟨j, hright_eq⟩
  have hij : i ≠ j := by
    intro hij
    exact hleft_ne_right (by
      apply Subtype.ext
      apply Subtype.ext
      calc
        ((leftT : B.verts) : V) = attach i := hleft_eq.symm
        _ = attach j := by rw [hij]
        _ = ((rightT : B.verts) : V) := hright_eq)
  exact ⟨leftT, rightT, pB, i, j, hleft_ne_right, hleft_degree,
    hright_degree, hpB, hpB_le, hleft_eq.symm, hright_eq.symm, hij⟩

theorem DominatingK5Model.first_branch_large_minimal_tree_card_branch_vertices_le_two
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_large : 3 <= B.verts.ncard)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableRel TB.coe.Adj]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    (Finset.univ.filter fun vT : TB.verts => 3 <= TB.coe.degree vT).card <= 2 := by
  exact
    dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_card_branch_vertices_le_two
      T attach B hB_le hB_terminal hB_minimal hB_large TB hTB_tree
      hTB_spanning

theorem DominatingK5Model.first_branch_large_minimal_tree_branch_vertex_cases
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : DominatingK5Model G)
    (attach : Fin 4 -> V)
    (B : G.Subgraph)
    (hB_le : B ≤ T.branch (0 : Fin 5))
    (hB_terminal : forall i : Fin 4, attach i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ T.branch (0 : Fin 5) ->
          B'.coe.Connected ->
            (forall i : Fin 4, attach i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    (hB_large : 3 <= B.verts.ncard)
    (TB : B.coe.Subgraph)
    [Fintype TB.verts]
    [DecidableEq TB.verts]
    [DecidableRel TB.coe.Adj]
    (hTB_tree : TB.coe.IsTree)
    (hTB_spanning : TB.IsSpanning) :
    let branchVerts : Finset TB.verts :=
      Finset.univ.filter fun vT : TB.verts => 3 <= TB.coe.degree vT
    branchVerts = ∅ ∨
      (Exists fun center : TB.verts => branchVerts = {center}) ∨
        Exists fun left : TB.verts =>
          Exists fun right : TB.verts => left ≠ right ∧ branchVerts = {left, right} := by
  classical
  intro branchVerts
  simpa [branchVerts] using
    dominating_K5_model_tail_all_singleton_first_branch_large_minimal_tree_branch_vertex_cases
      T attach B hB_le hB_terminal hB_minimal hB_large TB hTB_tree
      hTB_spanning

end Schematic.Math.GraphTheory
