import DominatingFourColour.Consequences.NearHajos.PathCarrier.Data

set_option maxHeartbeats 800000

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

namespace PathCarrier

set_option maxHeartbeats 0 in
theorem prepare
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G) :
    NearHajosStrengtheningConclusion G ∨ Nonempty (LargePathCarrier D) := by
  classical
  obtain ⟨Ktail, attachTail, hattachTail,
    hKtail_branch_not_first,
    hKtail_internal_not_first, Btail,
    hBtail_le, hBtail_connected,
    hBtail_terminal, hBtail_minimal,
    TBtail, hTBtail_tree,
    hTBtail_spanning⟩ :=
    D.model.exists_tail_k4UnsplitSubdivisionData_first_branch_minimal_attachment_tree_carrier
  letI : DecidableEq Btail.verts := Classical.decEq _
  letI : Fintype TBtail.verts := TBtail.verts.toFinite.fintype
  letI : DecidableEq TBtail.verts := Classical.decEq _
  letI : DecidableRel TBtail.coe.Adj := Classical.decRel _
  have _h_tail_three_distinct_indices_of_no_two_value :
      Not (Exists fun u : V =>
        Exists fun v : V =>
          u ∈ Btail.verts ∧ v ∈ Btail.verts ∧
            forall i : Fin 4,
              attachTail i = u ∨ attachTail i = v) ->
        Exists fun i : Fin 4 =>
          Exists fun j : Fin 4 =>
            Exists fun k : Fin 4 =>
              attachTail i ≠ attachTail j ∧
                attachTail i ≠ attachTail k ∧
                  attachTail j ≠ attachTail k := by
    intro hno_two
    have hrange_large :
        3 <= (Set.range attachTail).ncard :=
      fin4_range_ncard_ge_three_of_not_two_values_in_set
        (V := V) (A := Btail.verts) attachTail
        hBtail_terminal hno_two
    exact
      fin4_exists_three_pairwise_distinct_values_of_range_ncard_ge_three
        attachTail hrange_large
  by_cases hrooted_tail :
      Exists fun apexB : Btail.verts =>
        forall {a b : Fin 4}, a ≠ b ->
          Exists fun p :
            Btail.coe.Walk
              (⟨attachTail a,
                hBtail_terminal a⟩ : Btail.verts)
              (⟨attachTail b,
                hBtail_terminal b⟩ : Btail.verts) =>
            p.toSubgraph ≤ TBtail ∧ p.IsPath ∧
              apexB ∈ p.support
  · rcases hrooted_tail with ⟨apexB, hpair_through_apex⟩
    exact Or.inl
      (Ktail.carrier_rooted_attachment_spanning_tree_all_pairs_through_root_near_hajos_with_two_incident_unsplit_edges
        Btail
        (by
          intro i hmem
          exact hKtail_branch_not_first i
            (hBtail_le.left hmem))
        (by
          intro i j hij z hz hmem
          exact hKtail_internal_not_first hij hz
            (hBtail_le.left hmem))
        attachTail hBtail_terminal TBtail
        hTBtail_tree hTBtail_spanning apexB
        (by
          intro i
          exact (hattachTail i).2)
        (by
          intro a b hab
          exact hpair_through_apex hab))
  · have _h_tail_large_leaf_bridge_data :=
      fun hnot_small : Not (Btail.verts.ncard <= 2) =>
        by
          have hBtail_large : 3 <= Btail.verts.ncard := by
            omega
          exact
            D.model.first_branch_large_minimal_tree_exists_attachment_leaf_bridge_coe_path_with_indices_and_degrees
              attachTail Btail hBtail_le hBtail_terminal
              hBtail_minimal hBtail_large TBtail hTBtail_tree
              hTBtail_spanning
    have _h_tail_large_non_two_bridge_ordering_setup :
        Not (Btail.verts.ncard <= 2) ->
          Not (Exists fun u : V =>
            Exists fun v : V =>
              u ∈ Btail.verts ∧ v ∈ Btail.verts ∧
                forall i : Fin 4,
                  attachTail i = u ∨ attachTail i = v) ->
            Exists fun leftT₀ : TBtail.verts =>
              Exists fun rightT₀ : TBtail.verts =>
                Exists fun pB₀ :
                  Btail.coe.Walk
                    (leftT₀ : Btail.verts)
                    (rightT₀ : Btail.verts) =>
                  Exists fun i₀ : Fin 4 =>
                    Exists fun j₀ : Fin 4 =>
                      Exists fun σ₀ : Fin 4 ↪ Fin 4 =>
                        leftT₀ ≠ rightT₀ ∧
                          TBtail.coe.degree leftT₀ = 1 ∧
                            TBtail.coe.degree rightT₀ = 1 ∧
                              pB₀.IsPath ∧
                                pB₀.toSubgraph ≤ TBtail ∧
                              ((leftT₀ : Btail.verts) : V) =
                                attachTail i₀ ∧
                                ((rightT₀ : Btail.verts) : V) =
                                  attachTail j₀ ∧
                                  i₀ ≠ j₀ ∧
                                    ((leftT₀ : Btail.verts) : V) ∈
                                      (D.model.branch (0 : Fin 5)).verts ∧
                                      ((rightT₀ : Btail.verts) : V) ∈
                                        (D.model.branch (0 : Fin 5)).verts ∧
                                        ((leftT₀ : Btail.verts) : V) ≠
                                          ((rightT₀ : Btail.verts) : V) ∧
                                          attachTail i₀ ≠ attachTail j₀ ∧
                                            σ₀ (0 : Fin 4) = i₀ ∧
                                              σ₀ (2 : Fin 4) = j₀ ∧
                                                attachTail (σ₀ (1 : Fin 4)) ≠
                                                  attachTail j₀ ∧
                                                  attachTail (σ₀ (3 : Fin 4)) ≠
                                                    attachTail i₀ ∧
                                                    (σ₀ (1 : Fin 4) ≠ i₀ ∧
                                                      σ₀ (1 : Fin 4) ≠ j₀ ∧
                                                        σ₀ (3 : Fin 4) ≠ i₀ ∧
                                                          σ₀ (3 : Fin 4) ≠ j₀ ∧
                                                            σ₀ (1 : Fin 4) ≠ σ₀ (3 : Fin 4)) ∧
                                                      (forall a : Fin 4,
                                                        attachTail (σ₀ a) ∈
                                                          (D.model.branch (0 : Fin 5)).verts ∧
                                                          G.Adj (attachTail (σ₀ a))
                                                            (Ktail.model.branchVertex (σ₀ a))) ∧
                                                        (forall a : Fin 4,
                                                          attachTail (σ₀ a) ∈ Btail.verts) ∧
                                                          ((leftT₀ : Btail.verts) : V) =
                                                            attachTail (σ₀ (0 : Fin 4)) ∧
                                                            ((rightT₀ : Btail.verts) : V) =
                                                              attachTail (σ₀ (2 : Fin 4)) ∧
                                                              attachTail (σ₀ (1 : Fin 4)) ≠
                                                                ((rightT₀ : Btail.verts) : V) ∧
                                                                attachTail (σ₀ (3 : Fin 4)) ≠
                                                                  ((leftT₀ : Btail.verts) : V) := by
      intro hnot_small hno_two
      obtain ⟨leftT₀, rightT₀, pB₀, i₀, j₀,
        hleftT₀_ne_rightT₀, _hleftT₀_degree,
        _hrightT₀_degree, hpB₀, hpB₀_le_TB,
        hleft₀_eq, hright₀_eq, hi₀j₀⟩ :=
        _h_tail_large_leaf_bridge_data hnot_small
      have hleftT₀_degree_for_coeFiniteAt :
          @SimpleGraph.degree TBtail.verts TBtail.coe leftT₀
            (SimpleGraph.Subgraph.coeFiniteAt leftT₀) = 1 := by
        simpa [Subsingleton.elim
          (Subtype.fintype
            (Membership.mem (TBtail.coe.neighborSet leftT₀)))
          (SimpleGraph.Subgraph.coeFiniteAt leftT₀)] using
          _hleftT₀_degree
      have hrightT₀_degree_for_coeFiniteAt :
          @SimpleGraph.degree TBtail.verts TBtail.coe rightT₀
            (SimpleGraph.Subgraph.coeFiniteAt rightT₀) = 1 := by
        simpa [Subsingleton.elim
          (Subtype.fintype
            (Membership.mem (TBtail.coe.neighborSet rightT₀)))
          (SimpleGraph.Subgraph.coeFiniteAt rightT₀)] using
          _hrightT₀_degree
      let left₀ : V := ((leftT₀ : Btail.verts) : V)
      let right₀ : V := ((rightT₀ : Btail.verts) : V)
      have hleft₀_mem :
          left₀ ∈ (D.model.branch (0 : Fin 5)).verts := by
        exact hBtail_le.left (leftT₀ : Btail.verts).2
      have hright₀_mem :
          right₀ ∈ (D.model.branch (0 : Fin 5)).verts := by
        exact hBtail_le.left (rightT₀ : Btail.verts).2
      have hleft₀_ne_right₀ : left₀ ≠ right₀ := by
        intro h
        exact hleftT₀_ne_rightT₀ (by
          apply Subtype.ext
          apply Subtype.ext
          exact h)
      have hattach_i₀_ne_j₀ :
          attachTail i₀ ≠ attachTail j₀ := by
        intro hsame
        exact hleft₀_ne_right₀ (by
          calc
            left₀ = attachTail i₀ := hleft₀_eq
            _ = attachTail j₀ := hsame
            _ = right₀ := hright₀_eq.symm)
      obtain ⟨p, q, r, hpq, hpr, hqr⟩ :=
        _h_tail_three_distinct_indices_of_no_two_value hno_two
      have hthird_i₀j₀ :
          Exists fun k' : Fin 4 =>
            attachTail k' ≠ attachTail i₀ ∧
              attachTail k' ≠ attachTail j₀ :=
        fin4_exists_third_value_of_three_pairwise_distinct
          attachTail hpq hpr hqr
      obtain ⟨σ₀, hσ₀_zero, hσ₀_two,
        hσ₀_one_avoids_right,
        hσ₀_three_avoids_left⟩ :=
        fin4_exists_embedding_zero_two_cross_avoiding_values
          attachTail hi₀j₀ hattach_i₀_ne_j₀
          hthird_i₀j₀
      have hσ₀_remaining_ne :=
        fin4_embedding_zero_two_remaining_ne
          hσ₀_zero hσ₀_two
      refine ⟨leftT₀, rightT₀, pB₀, i₀, j₀, σ₀,
        hleftT₀_ne_rightT₀,
        hleftT₀_degree_for_coeFiniteAt,
        hrightT₀_degree_for_coeFiniteAt, hpB₀, hpB₀_le_TB,
        hleft₀_eq, hright₀_eq, hi₀j₀,
        hleft₀_mem, hright₀_mem, hleft₀_ne_right₀,
        hattach_i₀_ne_j₀, hσ₀_zero, hσ₀_two,
        hσ₀_one_avoids_right,
        hσ₀_three_avoids_left, hσ₀_remaining_ne,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro a
        exact hattachTail (σ₀ a)
      · intro a
        exact hBtail_terminal (σ₀ a)
      · simpa [hσ₀_zero] using hleft₀_eq
      · simpa [hσ₀_two] using hright₀_eq
      · intro hsame
        exact hσ₀_one_avoids_right (hsame.trans hright₀_eq)
      · intro hsame
        exact hσ₀_three_avoids_left (hsame.trans hleft₀_eq)
    have _h_tail_large_non_two_root_paths_setup :
        Not (Btail.verts.ncard <= 2) ->
          Not (Exists fun u : V =>
            Exists fun v : V =>
              u ∈ Btail.verts ∧ v ∈ Btail.verts ∧
                forall i : Fin 4,
                  attachTail i = u ∨ attachTail i = v) ->
            Exists fun leftT₀ : TBtail.verts =>
              Exists fun rightT₀ : TBtail.verts =>
                Exists fun pB₀ :
                  Btail.coe.Walk
                    (leftT₀ : Btail.verts)
                    (rightT₀ : Btail.verts) =>
                  Exists fun σ₀ : Fin 4 ↪ Fin 4 =>
                    Exists fun stemLeftB₀ :
                      forall a : Fin 4,
                        Btail.coe.Walk
                          (leftT₀ : Btail.verts)
                          (⟨attachTail (σ₀ a),
                            hBtail_terminal (σ₀ a)⟩ :
                              Btail.verts) =>
                      Exists fun stemRightB₀ :
                        forall a : Fin 4,
                          Btail.coe.Walk
                            (rightT₀ : Btail.verts)
                            (⟨attachTail (σ₀ a),
                              hBtail_terminal (σ₀ a)⟩ :
                                Btail.verts) =>
                        ((leftT₀ : Btail.verts) : V) ≠
                          ((rightT₀ : Btail.verts) : V) ∧
                          pB₀.IsPath ∧
                            pB₀.toSubgraph ≤ TBtail ∧
                              ((leftT₀ : Btail.verts) : V) =
                                attachTail (σ₀ (0 : Fin 4)) ∧
                                ((rightT₀ : Btail.verts) : V) =
                                  attachTail (σ₀ (2 : Fin 4)) ∧
                                  attachTail (σ₀ (1 : Fin 4)) ≠
                                    ((rightT₀ : Btail.verts) : V) ∧
                                    attachTail (σ₀ (3 : Fin 4)) ≠
                                      ((leftT₀ : Btail.verts) : V) ∧
                                      (forall a : Fin 4,
                                        (stemLeftB₀ a).IsPath) ∧
                                        (forall a : Fin 4,
                                          (stemLeftB₀ a).toSubgraph ≤
                                            TBtail) ∧
                                          (forall a : Fin 4,
                                            (stemRightB₀ a).IsPath) ∧
                                            (forall a : Fin 4,
                                              (stemRightB₀ a).toSubgraph ≤
                                                TBtail) ∧
                                              (forall {z : Btail.verts},
                                                z ∈ (stemLeftB₀ (1 : Fin 4)).support ->
                                                  z ≠ (leftT₀ : Btail.verts) ->
                                                    z ≠ (rightT₀ : Btail.verts)) ∧
                                                (forall {z : Btail.verts},
                                                  z ∈ (stemRightB₀ (3 : Fin 4)).support ->
                                                    z ≠ (rightT₀ : Btail.verts) ->
                                                      z ≠ (leftT₀ : Btail.verts)) := by
      intro hnot_small hno_two
      obtain ⟨leftT₀, rightT₀, pB₀, _i₀, _j₀, σ₀,
        _hleftT₀_ne_rightT₀, hleftT₀_degree,
        hrightT₀_degree, hpB₀, hpB₀_le_TB,
        _hleft₀_eq, _hright₀_eq, _hi₀j₀,
        _hleft₀_mem, _hright₀_mem, hleft₀_ne_right₀,
        _hattach_i₀_ne_j₀, _hσ₀_zero, _hσ₀_two,
        _hσ₀_one_avoids_right,
        _hσ₀_three_avoids_left, _hσ₀_remaining_ne,
        _hattachσ₀, _hBtail_terminalσ₀,
        hleft₀_eq_attachσ₀_zero,
        hright₀_eq_attachσ₀_two,
        hattachσ₀_one_ne_right,
        hattachσ₀_three_ne_left⟩ :=
        _h_tail_large_non_two_bridge_ordering_setup
          hnot_small hno_two
      obtain ⟨stemLeftB₀, hstemLeftB₀_path,
        hstemLeftB₀_le_TB⟩ :=
        Subgraph.Connected.exists_coe_rooted_paths_in_spanning_coe_subgraph
          (B := Btail) (T := TBtail)
          hTBtail_tree.connected hTBtail_spanning
          (leftT₀ : Btail.verts).2
          (fun a : Fin 4 => attachTail (σ₀ a))
          (fun a : Fin 4 => hBtail_terminal (σ₀ a))
      obtain ⟨stemRightB₀, hstemRightB₀_path,
        hstemRightB₀_le_TB⟩ :=
        Subgraph.Connected.exists_coe_rooted_paths_in_spanning_coe_subgraph
          (B := Btail) (T := TBtail)
          hTBtail_tree.connected hTBtail_spanning
          (rightT₀ : Btail.verts).2
          (fun a : Fin 4 => attachTail (σ₀ a))
          (fun a : Fin 4 => hBtail_terminal (σ₀ a))
      have hleftT₀_degree_for_coeFiniteAt :
          @SimpleGraph.degree TBtail.verts TBtail.coe leftT₀
            (SimpleGraph.Subgraph.coeFiniteAt leftT₀) = 1 := by
        simpa [Subsingleton.elim
          (Subtype.fintype
            (Membership.mem (TBtail.coe.neighborSet leftT₀)))
          (SimpleGraph.Subgraph.coeFiniteAt leftT₀)] using
          hleftT₀_degree
      have hrightT₀_degree_for_coeFiniteAt :
          @SimpleGraph.degree TBtail.verts TBtail.coe rightT₀
            (SimpleGraph.Subgraph.coeFiniteAt rightT₀) = 1 := by
        simpa [Subsingleton.elim
          (Subtype.fintype
            (Membership.mem (TBtail.coe.neighborSet rightT₀)))
          (SimpleGraph.Subgraph.coeFiniteAt rightT₀)] using
          hrightT₀_degree
      have hrightT₀_not_left_stem_one :
          (rightT₀ : Btail.verts) ∉
            (stemLeftB₀ (1 : Fin 4)).support := by
        exact
          Subgraph.Walk.IsPath.tree_leaf_not_mem_support_of_ne_endpoints
            (G := G) (B := Btail) (T := TBtail)
            (hstemLeftB₀_path (1 : Fin 4))
            (hstemLeftB₀_le_TB (1 : Fin 4))
            hrightT₀_degree_for_coeFiniteAt
            (by
              intro h
              exact hleft₀_ne_right₀ (by
                have hval :=
                  congrArg (fun x : Btail.verts => (x : V)) h
                simpa using hval.symm))
            (by
              intro h
              exact hattachσ₀_one_ne_right (by
                have hval :=
                  congrArg (fun x : Btail.verts => (x : V)) h
                simpa using hval.symm))
      have hleftT₀_not_right_stem_three :
          (leftT₀ : Btail.verts) ∉
            (stemRightB₀ (3 : Fin 4)).support := by
        exact
          Subgraph.Walk.IsPath.tree_leaf_not_mem_support_of_ne_endpoints
            (G := G) (B := Btail) (T := TBtail)
            (hstemRightB₀_path (3 : Fin 4))
            (hstemRightB₀_le_TB (3 : Fin 4))
            hleftT₀_degree_for_coeFiniteAt
            (by
              intro h
              exact hleft₀_ne_right₀ (by
                have hval :=
                  congrArg (fun x : Btail.verts => (x : V)) h
                simpa using hval))
            (by
              intro h
              exact hattachσ₀_three_ne_left (by
                have hval :=
                  congrArg (fun x : Btail.verts => (x : V)) h
                simpa using hval.symm))
      have hstemLeftB₀_avoids_right :
          forall {z : Btail.verts},
            z ∈ (stemLeftB₀ (1 : Fin 4)).support ->
              z ≠ (leftT₀ : Btail.verts) ->
                z ≠ (rightT₀ : Btail.verts) := by
        intro z hz _hz_ne_left hz_right
        exact hrightT₀_not_left_stem_one
          (by simpa [hz_right] using hz)
      have hstemRightB₀_avoids_left :
          forall {z : Btail.verts},
            z ∈ (stemRightB₀ (3 : Fin 4)).support ->
              z ≠ (rightT₀ : Btail.verts) ->
                z ≠ (leftT₀ : Btail.verts) := by
        intro z hz _hz_ne_right hz_left
        exact hleftT₀_not_right_stem_three
          (by simpa [hz_left] using hz)
      exact ⟨leftT₀, rightT₀, pB₀, σ₀,
        stemLeftB₀, stemRightB₀,
        hleft₀_ne_right₀, hpB₀, hpB₀_le_TB,
        hleft₀_eq_attachσ₀_zero,
        hright₀_eq_attachσ₀_two,
        hattachσ₀_one_ne_right,
        hattachσ₀_three_ne_left,
          hstemLeftB₀_path, hstemLeftB₀_le_TB,
          hstemRightB₀_path, hstemRightB₀_le_TB,
          hstemLeftB₀_avoids_right,
          hstemRightB₀_avoids_left⟩
    by_cases hBtail_small : Btail.verts.ncard <= 2
    · obtain ⟨u, v, huB, hvB, hvalues⟩ :=
        fin4_map_into_set_ncard_le_two_has_two_values
          (V := V) (A := Btail.verts) attachTail
          hBtail_terminal hBtail_small
      exact Or.inl
        (Ktail.carrier_two_value_attachment_near_hajos_with_two_incident_unsplit_edges
          Btail hBtail_connected huB hvB
          (by
            intro i hmem
            exact hKtail_branch_not_first i
              (hBtail_le.left hmem))
          (by
            intro i j hij z hz hmem
            exact hKtail_internal_not_first hij hz
              (hBtail_le.left hmem))
          attachTail
          (by
            intro i
            exact ⟨hBtail_terminal i,
              (hattachTail i).2⟩)
          hvalues)
    · by_cases htwo :
        Exists fun u : V =>
          Exists fun v : V =>
            u ∈ Btail.verts ∧ v ∈ Btail.verts ∧
              forall i : Fin 4,
                attachTail i = u ∨ attachTail i = v
      · rcases htwo with ⟨u, v, huB, hvB, hvalues⟩
        exact Or.inl
          (Ktail.carrier_two_value_attachment_near_hajos_with_two_incident_unsplit_edges
            Btail hBtail_connected huB hvB
            (by
              intro i hmem
              exact hKtail_branch_not_first i
                (hBtail_le.left hmem))
            (by
              intro i j hij z hz hmem
              exact hKtail_internal_not_first hij hz
                (hBtail_le.left hmem))
            attachTail
            (by
              intro i
              exact ⟨hBtail_terminal i,
                (hattachTail i).2⟩)
            hvalues)
      · obtain ⟨leftT₀, rightT₀, pB₀, σ₀,
          stemLeftB₀, stemRightB₀,
          hleft₀_ne_right₀, hpB₀, hpB₀_le_TB,
          hleft₀_eq_attachσ₀_zero,
          hright₀_eq_attachσ₀_two,
          hattachσ₀_one_ne_right,
          hattachσ₀_three_ne_left,
          hstemLeftB₀_path, hstemLeftB₀_le_TB,
          hstemRightB₀_path, hstemRightB₀_le_TB,
          hstemLeftB₀_avoids_right,
          hstemRightB₀_avoids_left⟩ :=
          _h_tail_large_non_two_root_paths_setup
            hBtail_small htwo
        exact Or.inr ⟨{
          Ktail := Ktail
          attachTail := attachTail
          hattachTail := hattachTail
          hKtail_branch_not_first := hKtail_branch_not_first
          hKtail_internal_not_first := hKtail_internal_not_first
          Btail := Btail
          hBtail_le := hBtail_le
          hBtail_terminal := hBtail_terminal
          TBtail := TBtail
          hTBtail_tree := hTBtail_tree
          hTBtail_spanning := hTBtail_spanning
          leftT := leftT₀
          rightT := rightT₀
          bridge := pB₀
          order := σ₀
          leftStem := stemLeftB₀
          rightStem := stemRightB₀
          left_ne_right := hleft₀_ne_right₀
          bridge_isPath := hpB₀
          bridge_le := hpB₀_le_TB
          left_eq_zero := hleft₀_eq_attachσ₀_zero
          right_eq_two := hright₀_eq_attachσ₀_two
          one_ne_right := hattachσ₀_one_ne_right
          three_ne_left := hattachσ₀_three_ne_left
          leftStem_isPath := hstemLeftB₀_path
          leftStem_le := hstemLeftB₀_le_TB
          rightStem_isPath := hstemRightB₀_path
          rightStem_le := hstemRightB₀_le_TB
          leftStem_avoids_right := hstemLeftB₀_avoids_right
          rightStem_avoids_left := hstemRightB₀_avoids_left
        }⟩

end PathCarrier

end Schematic.Math.GraphTheory
