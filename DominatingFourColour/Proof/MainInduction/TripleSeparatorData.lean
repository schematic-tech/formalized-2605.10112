import DominatingFourColour.Proof.MainInduction.ReroutingCollapse
import DominatingFourColour.Proof.MainInduction.TripleContractions

/-! Induction data produced by triple-separator collapse certificates. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

structure TripleSeparatorCollapseColorableData
    (S : Separation G) (x y z : V) : Prop where
  hxy : x ≠ y
  hxz : x ≠ z
  hyz : y ≠ z
  hseparator : S.separator = ({x, y, z} : Set V)
  right_colorable : S.rightWithSeparatorClique.Colorable 4
  xy_collapse_colorable :
    (S.rightTripleXYContraction hxy hseparator).graph.Colorable 4
  xz_collapse_colorable :
    (S.rightTripleXZContraction hxz hseparator).graph.Colorable 4
  yz_collapse_colorable :
    (S.rightTripleYZContraction hyz hseparator).graph.Colorable 4
  xyz_collapse_colorable :
    (S.rightTripleXYZContraction hxy hxz hseparator).graph.Colorable 4

structure TripleSeparatorCollapseInductionData
    (S : Separation G) (x y z : V) where
  hxy : x ≠ y
  hxz : x ≠ z
  hyz : y ≠ z
  hseparator : S.separator = ({x, y, z} : Set V)
  right_no_model :
    Exists fun L : OrderedClique S.rightWithSeparatorClique =>
      Not (CompatibleDominatingK5Model L)
  xy_no_model :
    Exists fun L : OrderedClique
        (S.rightTripleXYContraction hxy hseparator).graph =>
      Not (CompatibleDominatingK5Model L)
  xz_no_model :
    Exists fun L : OrderedClique
        (S.rightTripleXZContraction hxz hseparator).graph =>
      Not (CompatibleDominatingK5Model L)
  yz_no_model :
    Exists fun L : OrderedClique
        (S.rightTripleYZContraction hyz hseparator).graph =>
      Not (CompatibleDominatingK5Model L)
  xyz_no_model :
    Exists fun L : OrderedClique
        (S.rightTripleXYZContraction hxy hxz hseparator).graph =>
      Not (CompatibleDominatingK5Model L)

theorem tripleSeparatorCollapseInductionData_of_right_xy_no_model
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hno_xy :
      Not (CompatibleDominatingK5Model
        (S.rightTripleXYOrderedClique hxy hseparator))) :
    TripleSeparatorCollapseInductionData (G := G) S x y z := by
  classical
  refine {
    hxy := hxy
    hxz := hxz
    hyz := hyz
    hseparator := hseparator
    right_no_model := ⟨S.rightTripleXYOrderedClique hxy hseparator, hno_xy⟩
    xy_no_model := ?_
    xz_no_model := ?_
    yz_no_model := ?_
    xyz_no_model := ?_
  }
  · let rx := S.rightTripleX hseparator
    let ry := S.rightTripleY hseparator
    let hxy_right := S.rightTripleXYAdj hxy hseparator
    let C := S.rightTripleXYContraction hxy hseparator
    let Hxy := GraphContraction.inducedPairSubgraph
      S.rightWithSeparatorClique rx ry
    let hHxy_connected : Hxy.coe.Connected :=
      GraphContraction.inducedPairSubgraph_connected hxy_right
    obtain ⟨Lq, _himage, _hfirst, hno_Lq⟩ :=
      exists_collapse_pair_image_no_compatible_model_of_first_mem
      (G := S.rightWithSeparatorClique)
      (edge := hxy_right)
      Hxy hHxy_connected
      (by simp [Hxy, rx, ry])
      (by
        simpa [Separation.rightTripleXYOrderedClique] using hno_xy)
    exact ⟨Lq, by simpa [C, Separation.rightTripleXYContraction] using hno_Lq⟩
  · let rx := S.rightTripleX hseparator
    let ry := S.rightTripleY hseparator
    let rz := S.rightTripleZ hseparator
    let hxz_right := S.rightTripleXZAdj hxz hseparator
    let C := S.rightTripleXZContraction hxz hseparator
    let Hxz := GraphContraction.inducedPairSubgraph
      S.rightWithSeparatorClique rx rz
    let hHxz_connected : Hxz.coe.Connected :=
      GraphContraction.inducedPairSubgraph_connected hxz_right
    obtain ⟨Lq, _himage, _hfirst, hno_Lq⟩ :=
      exists_collapse_pair_image_no_compatible_model_of_first_mem
      (G := S.rightWithSeparatorClique)
      (edge := S.rightTripleXYAdj hxy hseparator)
      Hxz hHxz_connected
      (by simp [Hxz, rx, rz])
      (by
        simpa [Separation.rightTripleXYOrderedClique, ry] using hno_xy)
    exact ⟨Lq, by simpa [C, Separation.rightTripleXZContraction] using hno_Lq⟩
  · let rx := S.rightTripleX hseparator
    let ry := S.rightTripleY hseparator
    let rz := S.rightTripleZ hseparator
    let hyz_right := S.rightTripleYZAdj hyz hseparator
    let C := S.rightTripleYZContraction hyz hseparator
    let Hyz := GraphContraction.inducedPairSubgraph
      S.rightWithSeparatorClique ry rz
    let hHyz_connected : Hyz.coe.Connected :=
      GraphContraction.inducedPairSubgraph_connected hyz_right
    have edge_xy : S.rightWithSeparatorClique.Adj rx ry :=
      S.rightTripleXYAdj hxy hseparator
    obtain ⟨Lq, _himage, _hsecond, hno_Lq⟩ :=
      exists_collapse_pair_image_no_compatible_model_of_second_neighbor
      (G := S.rightWithSeparatorClique)
      edge_xy Hyz hHyz_connected
      (by simp [Hyz])
      (by
        intro a ha
        have ha_pair : a = ry ∨ a = rz := by
          have : a ∈ ({ry, rz} : Set S.right) := by
            simpa [Hyz] using ha
          simpa using this
        rcases ha_pair with rfl | rfl
        · exact edge_xy
        · exact S.rightTripleXZAdj hxz hseparator)
      (by
        simpa [Separation.rightTripleXYOrderedClique, rx] using hno_xy)
    exact ⟨Lq, by simpa [C, Separation.rightTripleYZContraction] using hno_Lq⟩
  · let rx := S.rightTripleX hseparator
    let ry := S.rightTripleY hseparator
    let rz := S.rightTripleZ hseparator
    let hxy_right := S.rightTripleXYAdj hxy hseparator
    let hxz_right := S.rightTripleXZAdj hxz hseparator
    let C := S.rightTripleXYZContraction hxy hxz hseparator
    let Hxyz := GraphContraction.inducedTripleSubgraph
      S.rightWithSeparatorClique rx ry rz
    let hHxyz_connected : Hxyz.coe.Connected :=
      GraphContraction.inducedTripleSubgraph_connected hxy_right hxz_right
    obtain ⟨Lq, _himage, _hfirst, hno_Lq⟩ :=
      exists_collapse_pair_image_no_compatible_model_of_first_mem
      (G := S.rightWithSeparatorClique)
      (edge := hxy_right)
      Hxyz hHxyz_connected
      (by simp [Hxyz, rx, ry, rz])
      (by
        simpa [Separation.rightTripleXYOrderedClique] using hno_xy)
    exact ⟨Lq, by simpa [C, Separation.rightTripleXYZContraction] using hno_Lq⟩

theorem tripleSeparatorCollapseInductionData_of_right_xz_no_model
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hno_xz :
      Not (CompatibleDominatingK5Model
        (S.rightTripleXZOrderedClique hxz hseparator))) :
    TripleSeparatorCollapseInductionData (G := G) S x y z := by
  classical
  have hseparator_xzy : S.separator = ({x, z, y} : Set V) := by
    rw [hseparator]
    ext v
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hno_xz' :
      Not (CompatibleDominatingK5Model
        (S.rightTripleXYOrderedClique hxz hseparator_xzy)) := by
    simpa [Separation.rightTripleXYOrderedClique,
      Separation.rightTripleXZOrderedClique] using hno_xz
  let D := tripleSeparatorCollapseInductionData_of_right_xy_no_model
    (G := G) S hxz hxy hyz.symm hseparator_xzy hno_xz'
  refine {
    hxy := hxy
    hxz := hxz
    hyz := hyz
    hseparator := hseparator
    right_no_model := D.right_no_model
    xy_no_model := ?_
    xz_no_model := ?_
    yz_no_model := ?_
    xyz_no_model := ?_
  }
  · simpa [D, hseparator_xzy] using D.xz_no_model
  · simpa [D, hseparator_xzy] using D.xy_no_model
  · let ry := S.rightTripleY hseparator
    let rz := S.rightTripleZ hseparator
    let hyz_right := S.rightTripleYZAdj hyz hseparator
    let C := S.rightTripleYZContraction hyz hseparator
    let ryD := S.rightTripleY hseparator_xzy
    let rzD := S.rightTripleZ hseparator_xzy
    have hryD : ryD = rz := Subtype.ext (by rfl)
    have hrzD : rzD = ry := Subtype.ext (by rfl)
    let Hyz := GraphContraction.inducedPairSubgraph
      S.rightWithSeparatorClique ry rz
    let hHyz_connected : Hyz.coe.Connected :=
      GraphContraction.inducedPairSubgraph_connected hyz_right
    let HD := GraphContraction.inducedPairSubgraph
      S.rightWithSeparatorClique ryD rzD
    have hHD : HD = Hyz := by
      simpa [HD, Hyz, hryD, hrzD] using
        GraphContraction.inducedPairSubgraph_comm
          S.rightWithSeparatorClique rz ry
    let P : (K : S.rightWithSeparatorClique.Subgraph) ->
        K.coe.Connected -> Prop := fun K hK_connected =>
      let CD := GraphContraction.collapseSubgraph
        S.rightWithSeparatorClique K hK_connected
      Exists fun L : OrderedClique CD.graph =>
        Not (CompatibleDominatingK5Model L)
    let hHD_connected : HD.coe.Connected := hHD.symm ▸ hHyz_connected
    have hD : P HD hHD_connected := by
      simpa [P, D, HD, ryD, rzD, GraphContraction.collapseEdge] using
        D.yz_no_model
    simpa [P, C, Hyz, hHyz_connected,
      Separation.rightTripleYZContraction, GraphContraction.collapseEdge] using
      GraphContraction.connectedSubgraphProperty_congr P hHD hD
  · let rx := S.rightTripleX hseparator
    let ry := S.rightTripleY hseparator
    let rz := S.rightTripleZ hseparator
    let hxy_right := S.rightTripleXYAdj hxy hseparator
    let hxz_right := S.rightTripleXZAdj hxz hseparator
    let C := S.rightTripleXYZContraction hxy hxz hseparator
    let rxD := S.rightTripleX hseparator_xzy
    let ryD := S.rightTripleY hseparator_xzy
    let rzD := S.rightTripleZ hseparator_xzy
    have hrxD : rxD = rx := Subtype.ext (by rfl)
    have hryD : ryD = rz := Subtype.ext (by rfl)
    have hrzD : rzD = ry := Subtype.ext (by rfl)
    let Hxyz := GraphContraction.inducedTripleSubgraph
      S.rightWithSeparatorClique rx ry rz
    let hHxyz_connected : Hxyz.coe.Connected :=
      GraphContraction.inducedTripleSubgraph_connected hxy_right hxz_right
    let HD := GraphContraction.inducedTripleSubgraph
      S.rightWithSeparatorClique rxD ryD rzD
    have hHD : HD = Hxyz := by
      simpa [HD, Hxyz, hrxD, hryD, hrzD] using
        GraphContraction.inducedTripleSubgraph_swap_right
          S.rightWithSeparatorClique rx rz ry
    let P : (K : S.rightWithSeparatorClique.Subgraph) ->
        K.coe.Connected -> Prop := fun K hK_connected =>
      let CD := GraphContraction.collapseSubgraph
        S.rightWithSeparatorClique K hK_connected
      Exists fun L : OrderedClique CD.graph =>
        Not (CompatibleDominatingK5Model L)
    let hHD_connected : HD.coe.Connected := hHD.symm ▸ hHxyz_connected
    have hD : P HD hHD_connected := by
      simpa [P, D, HD, rxD, ryD, rzD,
        GraphContraction.collapseTriple] using D.xyz_no_model
    simpa [P, C, Hxyz, hHxyz_connected,
      Separation.rightTripleXYZContraction,
      GraphContraction.collapseTriple] using
      GraphContraction.connectedSubgraphProperty_congr P hHD hD

theorem MinimalYZReroutingCertificate.tripleSeparatorCollapseInductionData_of_original_pair_core_or_y
    {S : Separation G} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_y : v2 ∈ R.core.verts ∨ v2 = y) :
    TripleSeparatorCollapseInductionData (G := G) S x y z :=
  tripleSeparatorCollapseInductionData_of_right_xy_no_model
    (G := G) S hxy hxz hyz hseparator
    (R.rightWithSeparatorClique_pair_xy_no_model_of_original_pair_core_or_y
      hxy hxz hyz hseparator edge hno_model_pair hv2_core_or_y)

theorem MinimalYZReroutingCertificate.tripleSeparatorCollapseInductionData_of_original_pair_core_or_z
    {S : Separation G} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_z : v2 ∈ R.core.verts ∨ v2 = z) :
    TripleSeparatorCollapseInductionData (G := G) S x y z :=
  tripleSeparatorCollapseInductionData_of_right_xz_no_model
    (G := G) S hxy hxz hyz hseparator
    (R.rightWithSeparatorClique_pair_xz_no_model_of_original_pair_core_or_z
      hxy hxz hyz hseparator edge hno_model_pair hv2_core_or_z)

theorem MinimalYZReroutingCertificate.tripleSeparatorCollapseInductionData_of_original_pair_core_or_endpoint
    {S : Separation G} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_endpoint : v2 ∈ R.core.verts ∨ v2 = y ∨ v2 = z) :
    TripleSeparatorCollapseInductionData (G := G) S x y z := by
  rcases hv2_core_or_endpoint with hv2_core | hv2_y | hv2_z
  · exact R.tripleSeparatorCollapseInductionData_of_original_pair_core_or_y
      hxy hxz hyz hseparator edge hno_model_pair (Or.inl hv2_core)
  · exact R.tripleSeparatorCollapseInductionData_of_original_pair_core_or_y
      hxy hxz hyz hseparator edge hno_model_pair (Or.inr hv2_y)
  · exact R.tripleSeparatorCollapseInductionData_of_original_pair_core_or_z
      hxy hxz hyz hseparator edge hno_model_pair (Or.inr hv2_z)

theorem MinimalYZReroutingCertificate.tripleSeparatorCollapseInductionData_of_original_pair_core_or_path
    {S : Separation G} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_path : v2 ∈ R.core.verts ∨ v2 ∈ R.pathYZ.support) :
    TripleSeparatorCollapseInductionData (G := G) S x y z := by
  rcases hv2_core_or_path with hv2_core | hv2_path
  · exact R.tripleSeparatorCollapseInductionData_of_original_pair_core_or_endpoint
      hxy hxz hyz hseparator edge hno_model_pair (Or.inl hv2_core)
  · by_cases hv2_z : v2 = z
    · exact R.tripleSeparatorCollapseInductionData_of_original_pair_core_or_endpoint
        hxy hxz hyz hseparator edge hno_model_pair
        (Or.inr (Or.inr hv2_z))
    · exact tripleSeparatorCollapseInductionData_of_right_xy_no_model
        (G := G) S hxy hxz hyz hseparator
        (R.rightWithSeparatorClique_pair_xy_no_model_of_original_pair_core_or_path_not_z
          hxy hxz hyz hseparator edge hno_model_pair
          (Or.inr ⟨hv2_path, hv2_z⟩))

theorem exists_triple_separator_collapse_induction_data_of_certificate
    {S : Separation G} {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hcert :
      Exists fun x : V =>
        Exists fun y : V =>
          Exists fun z : V =>
            Exists fun R : MinimalYZReroutingCertificate G S.left v1 x y z =>
              x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
                S.separator = ({x, y, z} : Set V) ∧
                  (v2 ∈ R.core.verts ∨ v2 = y ∨ v2 = z)) :
      Exists fun x : V =>
        Exists fun y : V =>
          Exists fun z : V =>
            TripleSeparatorCollapseInductionData (G := G) S x y z := by
  rcases hcert with
    ⟨x, y, z, R, hxy, hxz, hyz, hseparator, hv2_core_or_endpoint⟩
  exact ⟨x, y, z,
    R.tripleSeparatorCollapseInductionData_of_original_pair_core_or_endpoint
      hxy hxz hyz hseparator edge hno_model_pair hv2_core_or_endpoint⟩

theorem exists_triple_separator_collapse_induction_data_of_core_or_path_certificate
    {S : Separation G} {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hcert :
      Exists fun x : V =>
        Exists fun y : V =>
          Exists fun z : V =>
            Exists fun R : MinimalYZReroutingCertificate G S.left v1 x y z =>
              x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
                S.separator = ({x, y, z} : Set V) ∧
                  (v2 ∈ R.core.verts ∨ v2 ∈ R.pathYZ.support)) :
    Exists fun x : V =>
      Exists fun y : V =>
        Exists fun z : V =>
          TripleSeparatorCollapseInductionData (G := G) S x y z := by
  rcases hcert with
    ⟨x, y, z, R, hxy, hxz, hyz, hseparator, hv2_core_or_path⟩
  exact ⟨x, y, z,
    R.tripleSeparatorCollapseInductionData_of_original_pair_core_or_path
      hxy hxz hyz hseparator edge hno_model_pair hv2_core_or_path⟩

theorem FoldedDuplicateLinkageDataInSet.tripleSeparatorCollapseInductionData_of_componentCore
    [DecidableEq V]
    {S : Separation G} {root v1 v2 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hpathYZ_vertices_adjacent_core :
      forall a : V, a ∈ F.toLinkage.pathYZ.support ->
        Exists fun h : V =>
          h ∈ F.pathXComponentCore.verts ∧ G.Adj h a)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
      (hv2_core_or_endpoint :
        v2 ∈ F.pathXComponentCore.verts ∨ v2 = y ∨ v2 = z) :
      TripleSeparatorCollapseInductionData (G := G) S x y z := by
  let R : MinimalYZReroutingCertificate G S.left v1 x y z :=
    MinimalYZReroutingCertificate.ofFoldedLinkageInSetAndComponentCore
      F hpathYZ_chordless hpathYZ_vertices_adjacent_core
  exact R.tripleSeparatorCollapseInductionData_of_original_pair_core_or_endpoint
    hxy hxz hyz hseparator edge hno_model_pair (by
      simpa [R, MinimalYZReroutingCertificate.ofFoldedLinkageInSetAndComponentCore,
        MinimalYZReroutingCertificate.ofFoldedLinkageAndCore] using hv2_core_or_endpoint)

theorem FoldedDuplicateLinkageDataInSet.tripleSeparatorCollapseInductionData_of_componentCore_or_path
    [DecidableEq V]
    {S : Separation G} {root v1 v2 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hpathYZ_vertices_adjacent_core :
      forall a : V, a ∈ F.toLinkage.pathYZ.support ->
        Exists fun h : V =>
          h ∈ F.pathXComponentCore.verts ∧ G.Adj h a)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_path :
      v2 ∈ F.pathXComponentCore.verts ∨
        v2 ∈ F.toLinkage.pathYZ.support) :
    TripleSeparatorCollapseInductionData (G := G) S x y z := by
  let R : MinimalYZReroutingCertificate G S.left v1 x y z :=
    MinimalYZReroutingCertificate.ofFoldedLinkageInSetAndComponentCore
      F hpathYZ_chordless hpathYZ_vertices_adjacent_core
  exact R.tripleSeparatorCollapseInductionData_of_original_pair_core_or_path
    hxy hxz hyz hseparator edge hno_model_pair (by
      simpa [R, MinimalYZReroutingCertificate.ofFoldedLinkageInSetAndComponentCore,
        MinimalYZReroutingCertificate.ofFoldedLinkageAndCore] using hv2_core_or_path)

theorem FoldedDuplicateLinkageDataInSet.tripleSeparatorCollapseInductionData_of_componentCore_root_prefer
    [DecidableEq V]
    {S : Separation G} {root v1 v2 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hpathYZ_vertices_adjacent_core :
      forall a : V, a ∈ F.toLinkage.pathYZ.support ->
        Exists fun h : V =>
          h ∈ F.pathXComponentCore.verts ∧ G.Adj h a)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_left : v2 ∈ S.left)
    (hroot_prefer : v2 ∈ S.left \ S.right -> root = v2)
    (hroot_pathYZ : root ∈ F.toLinkage.pathYZ.support) :
    TripleSeparatorCollapseInductionData (G := G) S x y z := by
  exact F.tripleSeparatorCollapseInductionData_of_componentCore_or_path
    hxy hxz hyz hseparator hpathYZ_chordless
    hpathYZ_vertices_adjacent_core edge hno_model_pair
    (F.mem_pathXComponentCore_or_pathYZ_of_root_prefer
      hseparator hv2_left hroot_prefer hroot_pathYZ)

theorem FoldedDuplicateLinkageDataInSet.tripleSeparatorCollapseInductionData_of_componentCore_kntw_cover
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {S : Separation G} {root v1 v2 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hmin_degree : forall v : V, 4 <= G.degree v)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hleft_cover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hy_adjacent_core :
      Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h y)
    (hz_adjacent_core :
      Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h z)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_left : v2 ∈ S.left) :
    TripleSeparatorCollapseInductionData (G := G) S x y z := by
  have hpathYZ_adjacent_core :
      forall a : V, a ∈ F.toLinkage.pathYZ.support ->
        Exists fun h : V =>
          h ∈ F.pathXComponentCore.verts ∧ G.Adj h a :=
    F.pathYZ_vertices_adjacent_pathXComponentCore_of_left_cover
      hseparator hmin_degree hpathYZ_chordless hleft_cover
      hy_adjacent_core hz_adjacent_core
  exact F.tripleSeparatorCollapseInductionData_of_componentCore_or_path
    hxy hxz hyz hseparator hpathYZ_chordless hpathYZ_adjacent_core
    edge hno_model_pair
    (F.mem_pathXComponentCore_or_pathYZ_of_left_cover hleft_cover hv2_left)

theorem FoldedDuplicateLinkageDataInSet.tripleSeparatorCollapseInductionData_of_componentCore_kntw_connected
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {S : Separation G} {root v1 v2 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hmin_degree : forall v : V, 4 <= G.degree v)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hdeleted_connected : (G.induce F.deletedPathSet).Connected)
    (hy_adjacent_core :
      Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h y)
    (hz_adjacent_core :
      Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h z)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_left : v2 ∈ S.left) :
    TripleSeparatorCollapseInductionData (G := G) S x y z :=
  F.tripleSeparatorCollapseInductionData_of_componentCore_kntw_cover
    hxy hxz hyz hseparator hmin_degree hpathYZ_chordless
    (F.left_cover_of_deletedPathSet_connected hdeleted_connected)
    hy_adjacent_core hz_adjacent_core edge hno_model_pair hv2_left

theorem HasThreeVertexLinkage.exists_tripleSeparatorCollapseInductionData_of_foldedDuplicate_kntw
    [DecidableEq V]
    {S : Separation G} {root v1 v2 x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z)))
    (hpathYZ_chordless :
      let P := hlink.foldedDuplicateInSeparation
        (G := G) S hroot_left hroot_not_right hv1_left hseparator
      P.2.2.2.2.toLinkage.pathYZ.IsChordless)
    (hpathYZ_vertices_adjacent_core :
      let P := hlink.foldedDuplicateInSeparation
        (G := G) S hroot_left hroot_not_right hv1_left hseparator
      forall a : V, a ∈ P.2.2.2.2.toLinkage.pathYZ.support ->
        Exists fun h : V =>
          h ∈ P.2.2.2.2.pathXComponentCore.verts ∧ G.Adj h a)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_left : v2 ∈ S.left)
    (hroot_prefer : v2 ∈ S.left \ S.right -> root = v2) :
    Exists fun X : V =>
      Exists fun Y : V =>
        Exists fun Z : V =>
          TripleSeparatorCollapseInductionData (G := G) S X Y Z := by
  classical
  let P := hlink.foldedDuplicateInSeparation
    (G := G) S hroot_left hroot_not_right hv1_left hseparator
  have hroot_pathYZ :
      root ∈ P.2.2.2.2.toLinkage.pathYZ.support := by
    simpa [P] using
      hlink.foldedDuplicateInSeparation_root_mem_pathYZ
        (G := G) S hroot_left hroot_not_right hv1_left hseparator
  have hchord : P.2.2.2.2.toLinkage.pathYZ.IsChordless := by
    simpa [P] using hpathYZ_chordless
  have hadj :
      forall a : V, a ∈ P.2.2.2.2.toLinkage.pathYZ.support ->
        Exists fun h : V =>
          h ∈ P.2.2.2.2.pathXComponentCore.verts ∧ G.Adj h a := by
    simpa [P] using hpathYZ_vertices_adjacent_core
  rcases P with ⟨X, Y, Z, hpack⟩
  rcases hpack with ⟨hXYZ_lift, F⟩
  have hXYZ : ({X, Y, Z} : Set V) = ({x, y, z} : Set V) := hXYZ_lift.down
  have hpairwise :
      X ≠ Y ∧ X ≠ Z ∧ Y ≠ Z :=
    pairwise_ne_of_triple_set_eq hxy hxz hyz hXYZ
  have hseparatorXYZ : S.separator = ({X, Y, Z} : Set V) := by
    rw [hseparator, ← hXYZ]
  exact ⟨X, Y, Z,
    F.tripleSeparatorCollapseInductionData_of_componentCore_root_prefer
      hpairwise.1 hpairwise.2.1 hpairwise.2.2 hseparatorXYZ
      hchord hadj edge hno_model_pair hv2_left hroot_prefer hroot_pathYZ⟩

theorem HasThreeVertexLinkage.exists_tripleSeparatorCollapseInductionData_of_foldedDuplicate_kntw_cover
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {S : Separation G} {root v1 v2 x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hmin_degree : forall v : V, 4 <= G.degree v)
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z)))
    (hpathYZ_chordless :
      let P := hlink.foldedDuplicateInSeparation
        (G := G) S hroot_left hroot_not_right hv1_left hseparator
      P.2.2.2.2.toLinkage.pathYZ.IsChordless)
    (hleft_cover :
      let P := hlink.foldedDuplicateInSeparation
        (G := G) S hroot_left hroot_not_right hv1_left hseparator
      forall b : V, b ∈ S.left ->
        b ∈ P.2.2.2.2.pathXComponentCore.verts ∨
          b ∈ P.2.2.2.2.toLinkage.pathYZ.support)
    (hy_adjacent_core :
      let P := hlink.foldedDuplicateInSeparation
        (G := G) S hroot_left hroot_not_right hv1_left hseparator
      Exists fun h : V =>
        h ∈ P.2.2.2.2.pathXComponentCore.verts ∧ G.Adj h P.2.1)
    (hz_adjacent_core :
      let P := hlink.foldedDuplicateInSeparation
        (G := G) S hroot_left hroot_not_right hv1_left hseparator
      Exists fun h : V =>
        h ∈ P.2.2.2.2.pathXComponentCore.verts ∧ G.Adj h P.2.2.1)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_left : v2 ∈ S.left)
    (hroot_prefer : v2 ∈ S.left \ S.right -> root = v2) :
    Exists fun X : V =>
      Exists fun Y : V =>
        Exists fun Z : V =>
          TripleSeparatorCollapseInductionData (G := G) S X Y Z := by
  classical
  let P := hlink.foldedDuplicateInSeparation
    (G := G) S hroot_left hroot_not_right hv1_left hseparator
  have hseparatorP :
      S.separator = ({P.1, P.2.1, P.2.2.1} : Set V) := by
    exact hseparator.trans P.2.2.2.1.down.symm
  have hpathYZ_adjacent_core :
      forall a : V, a ∈ P.2.2.2.2.toLinkage.pathYZ.support ->
        Exists fun h : V =>
          h ∈ P.2.2.2.2.pathXComponentCore.verts ∧ G.Adj h a := by
    simpa [P] using
      P.2.2.2.2.pathYZ_vertices_adjacent_pathXComponentCore_of_left_cover
        hseparatorP hmin_degree
        (by simpa [P] using hpathYZ_chordless)
        (by simpa [P] using hleft_cover)
        (by simpa [P] using hy_adjacent_core)
        (by simpa [P] using hz_adjacent_core)
  exact
    HasThreeVertexLinkage.exists_tripleSeparatorCollapseInductionData_of_foldedDuplicate_kntw
      (G := G) (S := S) (root := root) (v1 := v1) (v2 := v2)
      (x := x) (y := y) (z := z)
      hxy hxz hyz hseparator hroot_left hroot_not_right hv1_left
      hlink hpathYZ_chordless hpathYZ_adjacent_core edge hno_model_pair
      hv2_left hroot_prefer


end Schematic.Math.GraphTheory
