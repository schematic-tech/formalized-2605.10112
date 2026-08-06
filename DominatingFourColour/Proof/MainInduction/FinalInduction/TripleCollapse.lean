import DominatingFourColour.Proof.MainInduction.FinalInduction.PairSeparators
import DominatingFourColour.Proof.MainInduction.TripleQuotients

/-! Assemble and colour the final triple-separator collapse data. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem TripleSeparatorCollapseInductionData.toColorableData
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    {S : Separation G} {x y z : V}
    (hproper : S.Proper)
    (D : TripleSeparatorCollapseInductionData (G := G) S x y z) :
    TripleSeparatorCollapseColorableData (G := G) S x y z := by
  classical
  letI : Fintype S.right := S.right.toFinite.fintype
  have hright_card_lt : Fintype.card S.right < Fintype.card V := by
    have hnat := S.natCard_right_lt_of_proper hproper
    simpa [Nat.card_eq_fintype_card] using hnat
  refine {
    hxy := D.hxy
    hxz := D.hxz
    hyz := D.hyz
    hseparator := D.hseparator
    right_colorable := ?_
    xy_collapse_colorable := ?_
    xz_collapse_colorable := ?_
    yz_collapse_colorable := ?_
    xyz_collapse_colorable := ?_
  }
  · rcases D.right_no_model with ⟨Lright, hno_Lright⟩
    rcases hIH S.rightWithSeparatorClique hright_card_lt Lright with
      hcolor | hmodel
    · exact hcolor
    · exact False.elim (hno_Lright hmodel)
  · intro rx ry Hxy hHxy_connected C
    have hrx_mem : rx ∈ Hxy.verts := by simp [Hxy]
    have hry_mem : ry ∈ Hxy.verts := by simp [Hxy]
    have hrx_ne_ry : rx ≠ ry := by
      intro h
      exact D.hxy (congrArg (fun r : S.right => (r : V)) h)
    have hC_card_right : Fintype.card C.Target < Fintype.card S.right := by
      simpa [C] using
        GraphContraction.collapseSubgraph_target_card_lt
          S.rightWithSeparatorClique Hxy hHxy_connected hrx_mem hry_mem hrx_ne_ry
    have hC_card : Fintype.card C.Target < Fintype.card V :=
      lt_trans hC_card_right hright_card_lt
    rcases D.xy_no_model with ⟨Lxy, hno_Lxy⟩
    rcases hIH C.graph hC_card Lxy with hcolor | hmodel
    · exact hcolor
    · exact False.elim (hno_Lxy hmodel)
  · intro rx rz Hxz hHxz_connected C
    have hrx_mem : rx ∈ Hxz.verts := by simp [Hxz]
    have hrz_mem : rz ∈ Hxz.verts := by simp [Hxz]
    have hrx_ne_rz : rx ≠ rz := by
      intro h
      exact D.hxz (congrArg (fun r : S.right => (r : V)) h)
    have hC_card_right : Fintype.card C.Target < Fintype.card S.right := by
      simpa [C] using
        GraphContraction.collapseSubgraph_target_card_lt
          S.rightWithSeparatorClique Hxz hHxz_connected hrx_mem hrz_mem hrx_ne_rz
    have hC_card : Fintype.card C.Target < Fintype.card V :=
      lt_trans hC_card_right hright_card_lt
    rcases D.xz_no_model with ⟨Lxz, hno_Lxz⟩
    rcases hIH C.graph hC_card Lxz with hcolor | hmodel
    · exact hcolor
    · exact False.elim (hno_Lxz hmodel)
  · intro ry rz Hyz hHyz_connected C
    have hry_mem : ry ∈ Hyz.verts := by simp [Hyz]
    have hrz_mem : rz ∈ Hyz.verts := by simp [Hyz]
    have hry_ne_rz : ry ≠ rz := by
      intro h
      exact D.hyz (congrArg (fun r : S.right => (r : V)) h)
    have hC_card_right : Fintype.card C.Target < Fintype.card S.right := by
      simpa [C] using
        GraphContraction.collapseSubgraph_target_card_lt
          S.rightWithSeparatorClique Hyz hHyz_connected hry_mem hrz_mem hry_ne_rz
    have hC_card : Fintype.card C.Target < Fintype.card V :=
      lt_trans hC_card_right hright_card_lt
    rcases D.yz_no_model with ⟨Lyz, hno_Lyz⟩
    rcases hIH C.graph hC_card Lyz with hcolor | hmodel
    · exact hcolor
    · exact False.elim (hno_Lyz hmodel)
  · intro rx ry rz Hxyz hHxyz_connected C
    have hrx_mem : rx ∈ Hxyz.verts := by simp [Hxyz]
    have hry_mem : ry ∈ Hxyz.verts := by simp [Hxyz]
    have hrx_ne_ry : rx ≠ ry := by
      intro h
      exact D.hxy (congrArg (fun r : S.right => (r : V)) h)
    have hC_card_right : Fintype.card C.Target < Fintype.card S.right := by
      simpa [C] using
        GraphContraction.collapseSubgraph_target_card_lt
          S.rightWithSeparatorClique Hxyz hHxyz_connected
          hrx_mem hry_mem hrx_ne_ry
    have hC_card : Fintype.card C.Target < Fintype.card V :=
      lt_trans hC_card_right hright_card_lt
    rcases D.xyz_no_model with ⟨Lxyz, hno_Lxyz⟩
    rcases hIH C.graph hC_card Lxyz with hcolor | hmodel
    · exact hcolor
    · exact False.elim (hno_Lxyz hmodel)

theorem exists_triple_separator_collapse_induction_data_of_minimal_pair_left_nonclique
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hvertex_minimal_pair :
      forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    (Asep : Separation G)
    (hAsep_proper : Asep.Proper)
    (hAsep_order : Asep.OrderAtMost 3)
    (hAsep_left :
      (OrderedClique.pair v1 v2 edge).vertexSet ⊆ Asep.left)
    (hAsep_minimal :
      forall T : Separation G,
        PairLeftSmallNoncliqueSeparation G edge T ->
          Asep.left.ncard <= T.left.ncard)
    (htriple :
      Exists fun x : V =>
        Exists fun y : V =>
          Exists fun z : V =>
            x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
              Asep.separator = ({x, y, z} : Set V)) :
      Exists fun x : V =>
        Exists fun y : V =>
          Exists fun z : V =>
            TripleSeparatorCollapseInductionData (G := G) Asep x y z := by
    classical
  rcases htriple with ⟨x, y, z, hxy, hxz, hyz, hseparator⟩
  have hthree_connected : IsThreeConnected G :=
    three_connected_of_pair_induction_hypotheses
      (G := G) hIH hnot_four_colorable edge hno_model_pair hvertex_minimal_pair
  have hmin_degree_pair : forall v : V, 4 <= G.degree v :=
    fun v =>
      degree_atLeast_four_of_not_colorable_four_of_delete_vertex_colorable
        (G := G) v hnot_four_colorable (hvertex_minimal_pair v)
  have hAsep_left_only_large :
      2 <= (Asep.left \ Asep.right).ncard :=
    Asep.left_only_ncard_ge_two_of_min_degree_four_orderAtMost_three
      hmin_degree_pair hAsep_proper hAsep_order
  obtain ⟨root, hroot_left_only, hroot_ne_v1, hroot_prefer_v2⟩ :=
    Asep.exists_left_only_ne_prefer_of_two_left_only
      v1 v2 hAsep_left_only_large edge.ne'
  have hroot_left : root ∈ Asep.left := hroot_left_only.1
  have hroot_not_right : root ∉ Asep.right := hroot_left_only.2
  have hv1_left : v1 ∈ Asep.left :=
    hAsep_left (by simp [OrderedClique.vertexSet])
  have hroot_degree : 3 <= G.degree root := by
    have hdeg := hmin_degree_pair root
    omega
  have hdup_three_connected :
      IsThreeConnected (duplicateVertexGraph G root) :=
    duplicateVertexGraph_three_connected
      (G := G) hthree_connected hroot_degree
  have hleft_dup_inj :
      Function.Injective
        (vertexTriple (some v1) (some root) (none : Option V)) := by
    exact vertexTriple_injective
      (by
        intro h
        exact hroot_ne_v1 (Option.some.inj h).symm)
      (by simp)
      (by simp)
  have hright_dup_inj :
      Function.Injective (vertexTriple (some x) (some y) (some z)) := by
    exact vertexTriple_injective
      (by
        intro h
        exact hxy (Option.some.inj h))
      (by
        intro h
        exact hxz (Option.some.inj h))
      (by
        intro h
        exact hyz (Option.some.inj h))
  have hv2_left : v2 ∈ Asep.left :=
    hAsep_left (by simp [OrderedClique.vertexSet])
  suffices hfolded_kntw :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
            Exists fun F : FoldedDuplicateLinkageDataInSet G Asep.left root v1 X Y Z =>
              ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ∧
                F.toLinkage.pathYZ.IsChordless ∧
                  (G.induce F.deletedPathSet).Connected by
    rcases hfolded_kntw with
      ⟨X, Y, Z, F, hXYZ, hpathYZ_chordless, hdeleted_connected⟩
    have hleft_cover :
        forall b : V, b ∈ Asep.left ->
          b ∈ F.pathXComponentCore.verts ∨
            b ∈ F.toLinkage.pathYZ.support :=
      F.left_cover_of_deletedPathSet_connected hdeleted_connected
    have hpairwise : X ≠ Y ∧ X ≠ Z ∧ Y ≠ Z :=
      pairwise_ne_of_triple_set_eq hxy hxz hyz hXYZ
    have hseparatorXYZ : Asep.separator = ({X, Y, Z} : Set V) :=
      hseparator.trans hXYZ.symm
    have hY_adjacent_core :
        Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h Y :=
      F.endpointY_adjacent_core_of_minimal_pair_left_nonclique
        hnot_four_colorable edge hvertex_minimal_pair Asep hthree_connected
        hAsep_proper hAsep_left_only_large hAsep_left hAsep_minimal
        hseparatorXYZ hpairwise.2.2 hpathYZ_chordless hleft_cover
    have hZ_adjacent_core :
        Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h Z :=
      F.endpointZ_adjacent_core_of_minimal_pair_left_nonclique
        hnot_four_colorable edge hvertex_minimal_pair Asep hthree_connected
        hAsep_proper hAsep_left_only_large hAsep_left hAsep_minimal
        hseparatorXYZ hpairwise.2.2 hpathYZ_chordless hleft_cover
    exact ⟨X, Y, Z,
      F.tripleSeparatorCollapseInductionData_of_componentCore_kntw_connected
        hpairwise.1 hpairwise.2.1 hpairwise.2.2 hseparatorXYZ
        hmin_degree_pair hpathYZ_chordless hdeleted_connected
        hY_adjacent_core hZ_adjacent_core edge hno_model_pair hv2_left⟩
  /-
  Remaining source-paper core:

  * finite vertex Menger in the duplicated graph, using `hdup_three_connected`,
    `hleft_dup_inj`, and `hright_dup_inj`, to get an initial folded linkage;
  * the KNTW/Tutte rerouting/minimality argument for the optimized folded
    certificate.  In the code shape below, KNTW must provide the stable
    non-attachment boundary vertex for each noncore component and prove that
    for the consecutive core-attachment interval around it, the path-boundary
    of the corresponding `CC_i` is contained in the closed interval.
    The checked background bridge then turns this into connectedness of
    `G[Asep.left - V(P_yz)]`.
  -/
  suffices hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
          (vertexTriple (some v1) (some root) (none : Option V))
          (vertexTriple (some x) (some y) (some z)) by
    have hstable :
        forall X Y Z : V,
          forall F : FoldedDuplicateLinkageDataInSet G Asep.left root v1 X Y Z,
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ->
              F.toLinkage.pathYZ.IsChordless ->
                (forall X' Y' Z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G Asep.left root v1 X' Y' Z',
                    ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                      F'.pathXComponentCore.verts.ncard <=
                        F.pathXComponentCore.verts.ncard) ->
                  (forall X' Y' Z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G Asep.left root v1 X' Y' Z',
                    ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                      F'.pathXComponentCore.verts.ncard =
                        F.pathXComponentCore.verts.ncard ->
                            F.toLinkage.pathYZ.length <=
                              F'.toLinkage.pathYZ.length) ->
                    forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
                      Exists fun b : V =>
                        b ∈ F.noncorePathBoundaryOfSet
                            (F.noncoreComponent hc) ∧
                          b ∉ F.pathYZCoreAttachmentSet ∧
                            forall u v : V,
                              u ∈ F.pathYZCoreAttachmentSet ->
                                v ∈ F.pathYZCoreAttachmentSet ->
                                  b ∈ Walk.OpenSupportInterval
                                      F.toLinkage.pathYZ u v ->
                                    (forall a : V,
                                      a ∈ Walk.OpenSupportInterval
                                          F.toLinkage.pathYZ u v ->
                                        a ∉ F.pathYZCoreAttachmentSet) ->
                                      F.noncorePathBoundaryOfSet
                                          (F.noncoreComponentsAttachedToOpenInterval
                                            u v) ⊆
                                        Walk.SupportInterval
                                          F.toLinkage.pathYZ u v := by
      intro X Y Z F hXYZ _hpathYZ_chordless hmax _hmin
      have hseparatorXYZ : Asep.separator = ({X, Y, Z} : Set V) :=
        hseparator.trans hXYZ.symm
      exact
        F.optimized_nonattachment_boundary_stable
          hthree_connected hseparatorXYZ
          (by
            intro F'
            exact hmax X Y Z F' hXYZ)
    exact
      HasThreeVertexLinkage.exists_connected_foldedDuplicateInSeparation_of_optimized_nonattachment_boundary_stable
        (G := G) Asep hthree_connected hroot_left hroot_not_right hv1_left
        hseparator hlink hstable
  exact
    IsThreeConnected.hasThreeVertexLinkage_fin3_triples
      hdup_three_connected hleft_dup_inj hright_dup_inj

theorem exists_triple_separator_collapse_colorable_data_of_minimal_pair_left_nonclique
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hvertex_minimal_pair :
      forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    (Asep : Separation G)
    (hAsep_proper : Asep.Proper)
    (hAsep_order : Asep.OrderAtMost 3)
    (hAsep_left :
      (OrderedClique.pair v1 v2 edge).vertexSet ⊆ Asep.left)
    (hAsep_minimal :
      forall T : Separation G,
        PairLeftSmallNoncliqueSeparation G edge T ->
          Asep.left.ncard <= T.left.ncard)
    (htriple :
      Exists fun x : V =>
        Exists fun y : V =>
          Exists fun z : V =>
            x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
              Asep.separator = ({x, y, z} : Set V)) :
    Exists fun x : V =>
      Exists fun y : V =>
        Exists fun z : V =>
          TripleSeparatorCollapseColorableData (G := G) Asep x y z := by
  classical
  obtain ⟨x, y, z, D⟩ :=
    exists_triple_separator_collapse_induction_data_of_minimal_pair_left_nonclique
      (G := G) hIH hnot_four_colorable edge hno_model_pair
      hvertex_minimal_pair Asep hAsep_proper hAsep_order
      hAsep_left hAsep_minimal htriple
  exact ⟨x, y, z,
    D.toColorableData (G := G) hIH hAsep_proper⟩

theorem colorable_of_minimal_pair_left_triple_nonclique_separation
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (hnot_four_colorable : Not (G.Colorable 4))
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hvertex_minimal_pair :
      forall v : V, (G.induce ({v} : Set V)ᶜ).Colorable 4)
    (Asep : Separation G)
    (hAsep_proper : Asep.Proper)
    (hAsep_order : Asep.OrderAtMost 3)
    (hAsep_left :
      (OrderedClique.pair v1 v2 edge).vertexSet ⊆ Asep.left)
    (hAsep_minimal :
      forall T : Separation G,
        PairLeftSmallNoncliqueSeparation G edge T ->
          Asep.left.ncard <= T.left.ncard)
    (hAsep_left_colorable : (G.induce Asep.left).Colorable 4)
    (htriple :
      Exists fun x : V =>
        Exists fun y : V =>
          Exists fun z : V =>
            x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
              Asep.separator = ({x, y, z} : Set V)) :
    G.Colorable 4 := by
  classical
  obtain ⟨x, y, z, hdata⟩ :=
    exists_triple_separator_collapse_colorable_data_of_minimal_pair_left_nonclique
      (G := G) hIH hnot_four_colorable edge hno_model_pair
      hvertex_minimal_pair Asep hAsep_proper hAsep_order
      hAsep_left hAsep_minimal htriple
  rcases hAsep_left_colorable with ⟨left_coloring⟩
  exact
    colorable_of_triple_separation_collapse_colorable_by_color_cases
      (G := G) Asep hdata.hxy hdata.hxz hdata.hyz
      hdata.hseparator left_coloring hdata.right_colorable
      hdata.xy_collapse_colorable hdata.xz_collapse_colorable
      hdata.yz_collapse_colorable hdata.xyz_collapse_colorable

end Schematic.Math.GraphTheory
