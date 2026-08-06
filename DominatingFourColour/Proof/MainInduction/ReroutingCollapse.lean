import DominatingFourColour.Proof.MainInduction.TripleContractions
import DominatingFourColour.Proof.MainInduction.SeparationColoring

/-! Rerouting-certificate collapses and model transport. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem MinimalYZReroutingCertificate.second_path_collapse_no_model_of_core_pair_no_model
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z)
    (edge_core_y :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map y))
    (hno_pair :
      Not (CompatibleDominatingK5Model
        (.pair (R.coreCollapse.map v1) (R.coreCollapse.map y) edge_core_y))) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map y) (R.coreCollapse.map z) :=
      R.pathYZInCoreCollapse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath
        (R.pathYZInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    Exists fun Lq : OrderedClique D.graph =>
      OrderedCliqueContractionImage D
        (.pair (R.coreCollapse.map v1) (R.coreCollapse.map y) edge_core_y) Lq ∧
        Lq.second? = some (none : D.Target) ∧
          Not (CompatibleDominatingK5Model Lq) := by
  intro P H2 hH2_connected D
  exact exists_collapse_pair_image_no_compatible_model_of_second_neighbor
    (G := R.coreCollapse.graph)
    edge_core_y H2 hH2_connected
    (by simp [H2, P])
    (by
      intro a ha
      exact R.pathYZInCoreCollapse_dropLast_neighbor_first hyz a (by
        simpa [P, H2] using ha))
    hno_pair

theorem MinimalYZReroutingCertificate.second_path_collapse_pair_no_model_of_core_pair_no_model
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z)
    (edge_core_y :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map y))
    (hno_pair :
      Not (CompatibleDominatingK5Model
        (.pair (R.coreCollapse.map v1) (R.coreCollapse.map y) edge_core_y))) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map y) (R.coreCollapse.map z) :=
      R.pathYZInCoreCollapse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath
        (R.pathYZInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    forall edgeD :
      D.graph.Adj
        (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map y)),
      Not (CompatibleDominatingK5Model
        (.pair (D.map (R.coreCollapse.map v1))
          (D.map (R.coreCollapse.map y)) edgeD)) := by
  intro P H2 hH2_connected D edgeD
  exact collapse_pair_no_compatible_model_of_second_neighbor
    (G := R.coreCollapse.graph)
    edge_core_y H2 hH2_connected
    (by simp [H2, P])
    (by
      intro a ha
      exact R.pathYZInCoreCollapse_dropLast_neighbor_first hyz a (by
        simpa [P, H2] using ha))
    hno_pair edgeD

private theorem coreCollapse_pair_endpoint_no_model_of_original_pair
    {A : Set V} {v1 v2 x y z w : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_w : v2 ∈ R.core.verts ∨ v2 = w)
    (edge_core_w :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map w)) :
    Not (CompatibleDominatingK5Model
      (.pair (R.coreCollapse.map v1) (R.coreCollapse.map w) edge_core_w)) := by
  classical
  have hv1_map := R.coreCollapse_map_v1
  rcases hv2_core_or_w with hv2_core | hv2_eq_w
  · have hv2_map :
        R.coreCollapse.map v2 = (none : R.coreCollapse.Target) := by
      simpa [MinimalYZReroutingCertificate.coreCollapse] using
        GraphContraction.collapseSubgraph_map_eq_none_of_mem
          G R.core R.core_connected hv2_core
    let Lsingle : OrderedClique R.coreCollapse.graph :=
      .single (R.coreCollapse.map v1)
    have hno_single :
        Not (CompatibleDominatingK5Model Lsingle) := by
      intro hmodel
      have himage :
          OrderedCliqueContractionImage R.coreCollapse
            (.pair v1 v2 edge) Lsingle := by
        exact OrderedCliqueContractionImage.pair_collapsed edge (by
          rw [hv1_map, hv2_map])
      have hfirst :
          Lsingle.first? =
            some (none : R.coreCollapse.Target) := by
          change some (R.coreCollapse.map v1) = some (none : R.coreCollapse.Target)
          exact congrArg some hv1_map
      exact hno_model_pair
        (contraction_lifts_first_branch_of_collapse
          (G := G) (L := .pair v1 v2 edge)
          (H1 := R.core) R.core_connected
          (Lq := Lsingle)
          (by
            simpa [MinimalYZReroutingCertificate.coreCollapse] using himage)
          (by
            simpa [MinimalYZReroutingCertificate.coreCollapse] using hfirst)
          (by
            simpa [MinimalYZReroutingCertificate.coreCollapse] using hmodel))
    exact no_compatible_model_of_initialSegment
      (G := R.coreCollapse.graph)
      (L := Lsingle)
      (L' := .pair (R.coreCollapse.map v1) (R.coreCollapse.map w) edge_core_w)
      (by simp [OrderedClique.InitialSegment, Lsingle])
      hno_single
  · have edge_w : G.Adj v1 w := by
      simpa [hv2_eq_w] using edge
    have hno_model_pair_w :
        Not (CompatibleDominatingK5Model (.pair v1 w edge_w)) := by
      subst w
      simpa using hno_model_pair
    intro hmodel
    have himage :
        OrderedCliqueContractionImage R.coreCollapse
          (.pair v1 w edge_w)
          (.pair (R.coreCollapse.map v1) (R.coreCollapse.map w) edge_core_w) := by
      exact OrderedCliqueContractionImage.pair_uncollapsed edge_w edge_core_w
    have hfirst :
        (.pair (R.coreCollapse.map v1) (R.coreCollapse.map w) edge_core_w :
          OrderedClique R.coreCollapse.graph).first? =
          some (none : R.coreCollapse.Target) := by
      change some (R.coreCollapse.map v1) = some (none : R.coreCollapse.Target)
      exact congrArg some hv1_map
    exact hno_model_pair_w
      (contraction_lifts_first_branch_of_collapse
        (G := G) (L := .pair v1 w edge_w)
        (H1 := R.core) R.core_connected
        (Lq := .pair (R.coreCollapse.map v1) (R.coreCollapse.map w) edge_core_w)
        (by
          simpa [MinimalYZReroutingCertificate.coreCollapse] using himage)
        (by
          simpa [MinimalYZReroutingCertificate.coreCollapse] using hfirst)
        (by
          simpa [MinimalYZReroutingCertificate.coreCollapse] using hmodel))

theorem MinimalYZReroutingCertificate.coreCollapse_pair_y_no_model_of_original_pair
    {A : Set V} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_y : v2 ∈ R.core.verts ∨ v2 = y)
    (edge_core_y :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map y)) :
    Not (CompatibleDominatingK5Model
      (.pair (R.coreCollapse.map v1) (R.coreCollapse.map y) edge_core_y)) :=
  coreCollapse_pair_endpoint_no_model_of_original_pair
    R edge hno_model_pair hv2_core_or_y edge_core_y

theorem MinimalYZReroutingCertificate.second_path_collapse_no_model_of_original_pair_core_or_y
    {A : Set V} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_y : v2 ∈ R.core.verts ∨ v2 = y) :
    Exists fun edge_core_y :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map y) =>
        let P : R.coreCollapse.graph.Walk
            (R.coreCollapse.map y) (R.coreCollapse.map z) :=
          R.pathYZInCoreCollapse
        let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
        let hH2_connected : H2.coe.Connected :=
          (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
            R.pathYZInCoreCollapse_isPath
            (R.pathYZInCoreCollapse_not_nil hyz)).1
        let D : GraphContraction R.coreCollapse.graph :=
          GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
        Exists fun Lq : OrderedClique D.graph =>
          OrderedCliqueContractionImage D
            (.pair (R.coreCollapse.map v1) (R.coreCollapse.map y) edge_core_y) Lq ∧
          Lq.second? = some (none : D.Target) ∧
            Not (CompatibleDominatingK5Model Lq) := by
  classical
  let edge_core_y := R.coreCollapse_adj_v1_y
  refine ⟨edge_core_y, ?_⟩
  exact R.second_path_collapse_no_model_of_core_pair_no_model hyz edge_core_y
    (R.coreCollapse_pair_y_no_model_of_original_pair
      edge hno_model_pair hv2_core_or_y edge_core_y)

theorem MinimalYZReroutingCertificate.second_path_collapse_pair_no_model_of_original_pair_core_or_y
    {A : Set V} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_y : v2 ∈ R.core.verts ∨ v2 = y) :
    Exists fun _edge_core_y :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map y) =>
        let P : R.coreCollapse.graph.Walk
            (R.coreCollapse.map y) (R.coreCollapse.map z) :=
          R.pathYZInCoreCollapse
        let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
        let hH2_connected : H2.coe.Connected :=
          (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
            R.pathYZInCoreCollapse_isPath
            (R.pathYZInCoreCollapse_not_nil hyz)).1
        let D : GraphContraction R.coreCollapse.graph :=
          GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
        forall edgeD :
          D.graph.Adj
            (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map y)),
          Not (CompatibleDominatingK5Model
            (.pair (D.map (R.coreCollapse.map v1))
              (D.map (R.coreCollapse.map y)) edgeD)) := by
  classical
  let edge_core_y := R.coreCollapse_adj_v1_y
  refine ⟨edge_core_y, ?_⟩
  exact R.second_path_collapse_pair_no_model_of_core_pair_no_model hyz edge_core_y
    (R.coreCollapse_pair_y_no_model_of_original_pair
      edge hno_model_pair hv2_core_or_y edge_core_y)

theorem MinimalYZReroutingCertificate.second_path_collapse_pair_no_model_of_original_pair_core_or_path_not_z
    {A : Set V} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_path_not_z :
      v2 ∈ R.core.verts ∨ (v2 ∈ R.pathYZ.support ∧ v2 ≠ z)) :
    Exists fun _edge_core_y :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map y) =>
        let P : R.coreCollapse.graph.Walk
            (R.coreCollapse.map y) (R.coreCollapse.map z) :=
          R.pathYZInCoreCollapse
        let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
        let hH2_connected : H2.coe.Connected :=
          (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
            R.pathYZInCoreCollapse_isPath
            (R.pathYZInCoreCollapse_not_nil hyz)).1
        let D : GraphContraction R.coreCollapse.graph :=
          GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
        forall edgeD :
          D.graph.Adj
            (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map y)),
          Not (CompatibleDominatingK5Model
            (.pair (D.map (R.coreCollapse.map v1))
              (D.map (R.coreCollapse.map y)) edgeD)) := by
  classical
  rcases hv2_core_or_path_not_z with hv2_core | hv2_path_not_z
  · exact R.second_path_collapse_pair_no_model_of_original_pair_core_or_y
      hyz edge hno_model_pair (Or.inl hv2_core)
  · rcases hv2_path_not_z with ⟨hv2_path, hv2_ne_z⟩
    let edge_core_y := R.coreCollapse_adj_v1_y
    refine ⟨edge_core_y, ?_⟩
    intro P H2 hH2_connected D edgeD
    have hv2_H2 : R.coreCollapse.map v2 ∈ H2.verts := by
      simpa [P, H2] using
        R.coreCollapse_map_mem_pathYZInCoreCollapse_dropLast hyz hv2_path hv2_ne_z
    have hy_H2 : R.coreCollapse.map y ∈ H2.verts := by
      simp [P, H2]
    have hv2_not_core : v2 ∉ R.core.verts := by
      intro hv2_core
      exact Set.disjoint_left.mp R.pathYZ_disjoint_core hv2_path hv2_core
    have hv1_map_none := R.coreCollapse_map_v1
    have hmap_ne :
        R.coreCollapse.map v1 ≠ R.coreCollapse.map v2 := by
      intro hsame
      have hcases :
          (v1 ∈ R.core.verts ∧ v2 ∈ R.core.verts) ∨
            (v1 = v2 ∧ v1 ∉ R.core.verts ∧ v2 ∉ R.core.verts) := by
        simpa [MinimalYZReroutingCertificate.coreCollapse] using
          (GraphContraction.collapseSubgraph_map_eq_iff
            G R.core R.core_connected (v := v1) (w := v2)).mp hsame
      rcases hcases with hboth | hout
      · exact hv2_not_core hboth.2
      · exact hout.2.1 R.v1_mem_core
    have edge_core_v2 :
        R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map v2) := by
      rcases R.coreCollapse.map_adj edge with hsame | hadj
      · exact False.elim (hmap_ne hsame)
      · exact hadj
    have hno_pair_core_v2 :
        Not (CompatibleDominatingK5Model
          (.pair (R.coreCollapse.map v1) (R.coreCollapse.map v2) edge_core_v2)) := by
      intro hmodel
      have himage :
          OrderedCliqueContractionImage R.coreCollapse
            (.pair v1 v2 edge)
            (.pair (R.coreCollapse.map v1) (R.coreCollapse.map v2) edge_core_v2) := by
        exact OrderedCliqueContractionImage.pair_uncollapsed edge edge_core_v2
      have hfirst :
          (.pair (R.coreCollapse.map v1) (R.coreCollapse.map v2) edge_core_v2 :
            OrderedClique R.coreCollapse.graph).first? =
            some (none : R.coreCollapse.Target) := by
        change some (R.coreCollapse.map v1) = some (none : R.coreCollapse.Target)
        exact congrArg some hv1_map_none
      exact hno_model_pair
        (contraction_lifts_first_branch_of_collapse
          (G := G) (L := .pair v1 v2 edge)
          (H1 := R.core) R.core_connected
          (Lq := .pair (R.coreCollapse.map v1) (R.coreCollapse.map v2) edge_core_v2)
          (by
            simpa [MinimalYZReroutingCertificate.coreCollapse] using himage)
          (by
            simpa [MinimalYZReroutingCertificate.coreCollapse] using hfirst)
          (by
            simpa [MinimalYZReroutingCertificate.coreCollapse] using hmodel))

    have hpair_no_v2 :
        forall edgeD :
          D.graph.Adj
            (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map v2)),
          Not (CompatibleDominatingK5Model
            (.pair (D.map (R.coreCollapse.map v1))
              (D.map (R.coreCollapse.map v2)) edgeD)) := by
      exact collapse_pair_no_compatible_model_of_second_neighbor
        (G := R.coreCollapse.graph)
        edge_core_v2 H2 hH2_connected hv2_H2
        (by
          intro a ha
          exact R.pathYZInCoreCollapse_dropLast_neighbor_first hyz a (by
            simpa [P, H2] using ha))
        hno_pair_core_v2
    have hv2_D_none :
        D.map (R.coreCollapse.map v2) = (none : D.Target) := by
      simpa [D] using
        GraphContraction.collapseSubgraph_map_eq_none_of_mem
          R.coreCollapse.graph H2 hH2_connected hv2_H2
    have hy_D_none :
        D.map (R.coreCollapse.map y) = (none : D.Target) := by
      simpa [D] using
        GraphContraction.collapseSubgraph_map_eq_none_of_mem
          R.coreCollapse.graph H2 hH2_connected hy_H2
    have edgeD_v2 :
        D.graph.Adj
          (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map v2)) := by
      simpa [hv2_D_none, hy_D_none] using edgeD
    have hno := hpair_no_v2 edgeD_v2
    intro hmodel
    exact hno (by
      simpa [hv2_D_none, hy_D_none] using hmodel)

theorem MinimalYZReroutingCertificate.coreCollapse_pair_z_no_model_of_original_pair
    {A : Set V} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_z : v2 ∈ R.core.verts ∨ v2 = z)
    (edge_core_z :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map z)) :
    Not (CompatibleDominatingK5Model
      (.pair (R.coreCollapse.map v1) (R.coreCollapse.map z) edge_core_z)) :=
  coreCollapse_pair_endpoint_no_model_of_original_pair
    R edge hno_model_pair hv2_core_or_z edge_core_z

theorem MinimalYZReroutingCertificate.second_path_reverse_collapse_no_model_of_core_pair_no_model
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z)
    (edge_core_z :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map z))
    (hno_pair :
      Not (CompatibleDominatingK5Model
        (.pair (R.coreCollapse.map v1) (R.coreCollapse.map z) edge_core_z))) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map z) (R.coreCollapse.map y) :=
      R.pathYZInCoreCollapse.reverse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath.reverse
        (R.pathZYInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    Exists fun Lq : OrderedClique D.graph =>
      OrderedCliqueContractionImage D
        (.pair (R.coreCollapse.map v1) (R.coreCollapse.map z) edge_core_z) Lq ∧
        Lq.second? = some (none : D.Target) ∧
          Not (CompatibleDominatingK5Model Lq) := by
  intro P H2 hH2_connected D
  exact exists_collapse_pair_image_no_compatible_model_of_second_neighbor
    (G := R.coreCollapse.graph)
    edge_core_z H2 hH2_connected
    (by simp [H2, P])
    (by
      intro a ha
      exact R.pathZYInCoreCollapse_dropLast_neighbor_first hyz a (by
        simpa [P, H2] using ha))
    hno_pair

theorem MinimalYZReroutingCertificate.second_path_reverse_collapse_pair_no_model_of_core_pair_no_model
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z)
    (edge_core_z :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map z))
    (hno_pair :
      Not (CompatibleDominatingK5Model
        (.pair (R.coreCollapse.map v1) (R.coreCollapse.map z) edge_core_z))) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map z) (R.coreCollapse.map y) :=
      R.pathYZInCoreCollapse.reverse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath.reverse
        (R.pathZYInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    forall edgeD :
      D.graph.Adj
        (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map z)),
      Not (CompatibleDominatingK5Model
        (.pair (D.map (R.coreCollapse.map v1))
          (D.map (R.coreCollapse.map z)) edgeD)) := by
  intro P H2 hH2_connected D edgeD
  exact collapse_pair_no_compatible_model_of_second_neighbor
    (G := R.coreCollapse.graph)
    edge_core_z H2 hH2_connected
    (by simp [H2, P])
    (by
      intro a ha
      exact R.pathZYInCoreCollapse_dropLast_neighbor_first hyz a (by
        simpa [P, H2] using ha))
    hno_pair edgeD

theorem MinimalYZReroutingCertificate.second_path_reverse_collapse_no_model_of_original_pair_core_or_z
    {A : Set V} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_z : v2 ∈ R.core.verts ∨ v2 = z) :
    Exists fun edge_core_z :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map z) =>
        let P : R.coreCollapse.graph.Walk
            (R.coreCollapse.map z) (R.coreCollapse.map y) :=
          R.pathYZInCoreCollapse.reverse
        let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
        let hH2_connected : H2.coe.Connected :=
          (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
            R.pathYZInCoreCollapse_isPath.reverse
            (R.pathZYInCoreCollapse_not_nil hyz)).1
        let D : GraphContraction R.coreCollapse.graph :=
          GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
        Exists fun Lq : OrderedClique D.graph =>
          OrderedCliqueContractionImage D
            (.pair (R.coreCollapse.map v1) (R.coreCollapse.map z) edge_core_z) Lq ∧
          Lq.second? = some (none : D.Target) ∧
            Not (CompatibleDominatingK5Model Lq) := by
  classical
  let edge_core_z := R.coreCollapse_adj_v1_z
  refine ⟨edge_core_z, ?_⟩
  exact R.second_path_reverse_collapse_no_model_of_core_pair_no_model hyz edge_core_z
    (R.coreCollapse_pair_z_no_model_of_original_pair
      edge hno_model_pair hv2_core_or_z edge_core_z)

theorem MinimalYZReroutingCertificate.second_path_reverse_collapse_pair_no_model_of_original_pair_core_or_z
    {A : Set V} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z)
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_z : v2 ∈ R.core.verts ∨ v2 = z) :
    Exists fun _edge_core_z :
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map z) =>
        let P : R.coreCollapse.graph.Walk
            (R.coreCollapse.map z) (R.coreCollapse.map y) :=
          R.pathYZInCoreCollapse.reverse
        let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
        let hH2_connected : H2.coe.Connected :=
          (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
            R.pathYZInCoreCollapse_isPath.reverse
            (R.pathZYInCoreCollapse_not_nil hyz)).1
        let D : GraphContraction R.coreCollapse.graph :=
          GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
        forall edgeD :
          D.graph.Adj
            (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map z)),
          Not (CompatibleDominatingK5Model
            (.pair (D.map (R.coreCollapse.map v1))
              (D.map (R.coreCollapse.map z)) edgeD)) := by
  classical
  let edge_core_z := R.coreCollapse_adj_v1_z
  refine ⟨edge_core_z, ?_⟩
  exact R.second_path_reverse_collapse_pair_no_model_of_core_pair_no_model hyz edge_core_z
    (R.coreCollapse_pair_z_no_model_of_original_pair
      edge hno_model_pair hv2_core_or_z edge_core_z)

private noncomputable def rightWithSeparatorCliqueCollapseHom
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (D : GraphContraction R.coreCollapse.graph)
    (hf_inj : Function.Injective
      (fun r : S.right => D.map (R.coreCollapse.map (r : V))))
    (hDyz : D.graph.Adj
      (D.map (R.coreCollapse.map y)) (D.map (R.coreCollapse.map z))) :
    S.rightWithSeparatorClique →g D.graph := by
  classical
  let f : S.right -> D.Target := fun r => D.map (R.coreCollapse.map (r : V))
  let rx := S.rightTripleX hseparator
  let ry := S.rightTripleY hseparator
  let rz := S.rightTripleZ hseparator
  have hx_map_v1 := R.coreCollapse_map_x_eq_map_v1
  have hCxy := R.coreCollapse_adj_x_y
  have hCxz := R.coreCollapse_adj_x_z
  have hDxy :
      D.graph.Adj (f rx) (f ry) := by
    rcases D.map_adj hCxy with hsame | hadj
    · have hrxy : rx = ry := hf_inj (by simpa [f, rx, ry] using hsame)
      exact False.elim (hxy (congrArg (fun r : S.right => (r : V)) hrxy))
    · simpa [f, rx, ry] using hadj
  have hDxz :
      D.graph.Adj (f rx) (f rz) := by
    rcases D.map_adj hCxz with hsame | hadj
    · have hrxz : rx = rz := hf_inj (by simpa [f, rx, rz] using hsame)
      exact False.elim (hxz (congrArg (fun r : S.right => (r : V)) hrxz))
    · simpa [f, rx, rz] using hadj
  have hDyz' : D.graph.Adj (f ry) (f rz) := by
    simpa [f, ry, rz] using hDyz
  refine ⟨f, ?_⟩
  intro a b hab
  rcases hab with hab | hsep
  · have hC_adj : R.coreCollapse.graph.Adj
        (R.coreCollapse.map (a : V)) (R.coreCollapse.map (b : V)) := by
      rcases R.coreCollapse.map_adj hab with hsame | hadj
      · have hcore_inj :
            Function.Injective (fun r : S.right => R.coreCollapse.map (r : V)) := by
          simpa [MinimalYZReroutingCertificate.coreCollapse] using
            R.collapse_core_injective_on_right_of_triple_separator hseparator
        have hab_eq : a = b := hcore_inj hsame
        exact False.elim (hab.ne hab_eq)
      · exact hadj
    rcases D.map_adj hC_adj with hsame | hadj
    · exact False.elim (hab.ne (hf_inj (by simpa [f] using hsame)))
    · exact hadj
  · rcases hsep with ⟨ha_left, hb_left, hab_ne⟩
    have ha_sep : (a : V) ∈ S.separator := ⟨ha_left, a.2⟩
    have hb_sep : (b : V) ∈ S.separator := ⟨hb_left, b.2⟩
    have ha_tri : (a : V) = x ∨ (a : V) = y ∨ (a : V) = z := by
      have : (a : V) ∈ ({x, y, z} : Set V) := by
        simpa [hseparator] using ha_sep
      simpa [Set.mem_insert_iff] using this
    have hb_tri : (b : V) = x ∨ (b : V) = y ∨ (b : V) = z := by
      have : (b : V) ∈ ({x, y, z} : Set V) := by
        simpa [hseparator] using hb_sep
      simpa [Set.mem_insert_iff] using this
    rcases ha_tri with ha_x | ha_y | ha_z <;>
      rcases hb_tri with hb_x | hb_y | hb_z
    · exact False.elim (hab_ne (Subtype.ext (ha_x.trans hb_x.symm)))
    · simpa [f, rx, ry, ha_x, hb_y] using hDxy
    · simpa [f, rx, rz, ha_x, hb_z] using hDxz
    · simpa [f, rx, ry, ha_y, hb_x] using hDxy.symm
    · exact False.elim (hab_ne (Subtype.ext (ha_y.trans hb_y.symm)))
    · simpa [f, ry, rz, ha_y, hb_z] using hDyz'
    · simpa [f, rx, rz, ha_z, hb_x] using hDxz.symm
    · simpa [f, ry, rz, ha_z, hb_y] using hDyz'.symm
    · exact False.elim (hab_ne (Subtype.ext (ha_z.trans hb_z.symm)))

noncomputable def MinimalYZReroutingCertificate.rightWithSeparatorCliqueSecondCollapseHom
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map y) (R.coreCollapse.map z) :=
      R.pathYZInCoreCollapse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath
        (R.pathYZInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    S.rightWithSeparatorClique →g D.graph := by
  classical
  intro P H2 hH2_connected D
  apply rightWithSeparatorCliqueCollapseHom R hxy hxz hseparator D
  · simpa [P, H2, D] using
      R.secondCollapse_injective_on_right_of_triple_separator hseparator hyz
  · simpa [P, H2, D] using
      R.collapse_pathYZInCoreCollapse_dropLast_adj_yz hyz

theorem MinimalYZReroutingCertificate.rightWithSeparatorCliqueSecondCollapseHom_injective
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map y) (R.coreCollapse.map z) :=
      R.pathYZInCoreCollapse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath
        (R.pathYZInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    Function.Injective
      (R.rightWithSeparatorCliqueSecondCollapseHom hxy hxz hyz hseparator :
        S.rightWithSeparatorClique →g D.graph) := by
  intro P H2 hH2_connected D
  simpa [MinimalYZReroutingCertificate.rightWithSeparatorCliqueSecondCollapseHom]
    using R.secondCollapse_injective_on_right_of_triple_separator hseparator hyz

noncomputable def Separation.rightTripleXYOrderedClique
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    OrderedClique S.rightWithSeparatorClique :=
  .pair (S.rightTripleX hseparator) (S.rightTripleY hseparator)
    (S.rightTripleXYAdj hxy hseparator)

noncomputable def Separation.rightTripleXZOrderedClique
    (S : Separation G)
    {x y z : V}
    (hxz : x ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    OrderedClique S.rightWithSeparatorClique :=
  .pair (S.rightTripleX hseparator) (S.rightTripleZ hseparator)
    (S.rightTripleXZAdj hxz hseparator)

private theorem rightWithSeparatorClique_pair_xy_no_model_of_second_collapse_pair_no_model
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hpair_no :
      let P : R.coreCollapse.graph.Walk
          (R.coreCollapse.map y) (R.coreCollapse.map z) :=
        R.pathYZInCoreCollapse
      let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
      let hH2_connected : H2.coe.Connected :=
        (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
          R.pathYZInCoreCollapse_isPath
          (R.pathYZInCoreCollapse_not_nil hyz)).1
      let D : GraphContraction R.coreCollapse.graph :=
        GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
      forall edgeD :
        D.graph.Adj
          (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map y)),
        Not (CompatibleDominatingK5Model
          (.pair (D.map (R.coreCollapse.map v1))
            (D.map (R.coreCollapse.map y)) edgeD))) :
    Not (CompatibleDominatingK5Model
      (S.rightTripleXYOrderedClique hxy hseparator)) := by
  classical
  let P : R.coreCollapse.graph.Walk
      (R.coreCollapse.map y) (R.coreCollapse.map z) :=
    R.pathYZInCoreCollapse
  let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
  let hH2_connected : H2.coe.Connected :=
    (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
      R.pathYZInCoreCollapse_isPath
      (R.pathYZInCoreCollapse_not_nil hyz)).1
  let D : GraphContraction R.coreCollapse.graph :=
    GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
  let hom : S.rightWithSeparatorClique →g D.graph := by
    simpa [P, H2, D] using
      R.rightWithSeparatorCliqueSecondCollapseHom hxy hxz hyz hseparator
  have hhom_inj : Function.Injective hom := by
    simpa [P, H2, D, hom] using
      R.rightWithSeparatorCliqueSecondCollapseHom_injective hxy hxz hyz hseparator
  let rx := S.rightTripleX hseparator
  let ry := S.rightTripleY hseparator
  have edge_side : S.rightWithSeparatorClique.Adj rx ry :=
    S.rightTripleXYAdj hxy hseparator
  let Lside : OrderedClique S.rightWithSeparatorClique := .pair rx ry edge_side
  have hpair_no' :
      forall edgeD :
        D.graph.Adj
          (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map y)),
        Not (CompatibleDominatingK5Model
          (.pair (D.map (R.coreCollapse.map v1))
            (D.map (R.coreCollapse.map y)) edgeD)) := by
    simpa [P, H2, D] using hpair_no
  have hx_map_v1 := R.coreCollapse_map_x_eq_map_v1
  have edgeD :
      D.graph.Adj
        (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map y)) := by
    have h := hom.map_adj edge_side
    simpa [hom, MinimalYZReroutingCertificate.rightWithSeparatorCliqueSecondCollapseHom,
      rightWithSeparatorCliqueCollapseHom,
      P, H2, D, rx, ry, hx_map_v1] using h
  have hno_Lside : Not (CompatibleDominatingK5Model Lside) :=
    not_compatible_of_map_not_compatible Lside hom hhom_inj (by
    simpa [Lside, OrderedClique.map, hom,
      MinimalYZReroutingCertificate.rightWithSeparatorCliqueSecondCollapseHom,
      rightWithSeparatorCliqueCollapseHom,
        P, H2, D, rx, ry, hx_map_v1] using hpair_no' edgeD)
  simpa [Separation.rightTripleXYOrderedClique, Lside, rx, ry] using hno_Lside

theorem MinimalYZReroutingCertificate.rightWithSeparatorClique_pair_xy_no_model_of_original_pair_core_or_y
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
    Not (CompatibleDominatingK5Model
      (S.rightTripleXYOrderedClique hxy hseparator)) := by
  obtain ⟨_edge_core_y, hpair_no⟩ :=
    R.second_path_collapse_pair_no_model_of_original_pair_core_or_y
      hyz edge hno_model_pair hv2_core_or_y
  exact rightWithSeparatorClique_pair_xy_no_model_of_second_collapse_pair_no_model
    R hxy hxz hyz hseparator hpair_no

theorem MinimalYZReroutingCertificate.rightWithSeparatorClique_pair_xy_no_model_of_original_pair_core_or_path_not_z
    {S : Separation G} {v1 v2 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (edge : G.Adj v1 v2)
    (hno_model_pair :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge)))
    (hv2_core_or_path_not_z :
      v2 ∈ R.core.verts ∨ (v2 ∈ R.pathYZ.support ∧ v2 ≠ z)) :
    Not (CompatibleDominatingK5Model
      (S.rightTripleXYOrderedClique hxy hseparator)) := by
  obtain ⟨_edge_core_y, hpair_no⟩ :=
    R.second_path_collapse_pair_no_model_of_original_pair_core_or_path_not_z
      hyz edge hno_model_pair hv2_core_or_path_not_z
  exact rightWithSeparatorClique_pair_xy_no_model_of_second_collapse_pair_no_model
    R hxy hxz hyz hseparator hpair_no

noncomputable def MinimalYZReroutingCertificate.rightWithSeparatorCliqueSecondReverseCollapseHom
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map z) (R.coreCollapse.map y) :=
      R.pathYZInCoreCollapse.reverse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath.reverse
        (R.pathZYInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    S.rightWithSeparatorClique →g D.graph := by
  classical
  intro P H2 hH2_connected D
  apply rightWithSeparatorCliqueCollapseHom R hxy hxz hseparator D
  · simpa [P, H2, D] using
      R.secondReverseCollapse_injective_on_right_of_triple_separator hseparator hyz
  · simpa [P, H2, D] using
      (R.collapse_pathZYInCoreCollapse_dropLast_adj_zy hyz).symm

theorem MinimalYZReroutingCertificate.rightWithSeparatorCliqueSecondReverseCollapseHom_injective
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map z) (R.coreCollapse.map y) :=
      R.pathYZInCoreCollapse.reverse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath.reverse
        (R.pathZYInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    Function.Injective
      (R.rightWithSeparatorCliqueSecondReverseCollapseHom hxy hxz hyz hseparator :
        S.rightWithSeparatorClique →g D.graph) := by
  intro P H2 hH2_connected D
  simpa [MinimalYZReroutingCertificate.rightWithSeparatorCliqueSecondReverseCollapseHom]
    using R.secondReverseCollapse_injective_on_right_of_triple_separator hseparator hyz

theorem MinimalYZReroutingCertificate.rightWithSeparatorClique_pair_xz_no_model_of_original_pair_core_or_z
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
    Not (CompatibleDominatingK5Model
      (S.rightTripleXZOrderedClique hxz hseparator)) := by
  classical
  let P : R.coreCollapse.graph.Walk
      (R.coreCollapse.map z) (R.coreCollapse.map y) :=
    R.pathYZInCoreCollapse.reverse
  let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
  let hH2_connected : H2.coe.Connected :=
    (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
      R.pathYZInCoreCollapse_isPath.reverse
      (R.pathZYInCoreCollapse_not_nil hyz)).1
  let D : GraphContraction R.coreCollapse.graph :=
    GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
  let hom : S.rightWithSeparatorClique →g D.graph := by
    simpa [P, H2, D] using
      R.rightWithSeparatorCliqueSecondReverseCollapseHom hxy hxz hyz hseparator
  have hhom_inj : Function.Injective hom := by
    simpa [P, H2, D, hom] using
      R.rightWithSeparatorCliqueSecondReverseCollapseHom_injective hxy hxz hyz hseparator
  let rx := S.rightTripleX hseparator
  let rz := S.rightTripleZ hseparator
  have edge_side : S.rightWithSeparatorClique.Adj rx rz :=
    S.rightTripleXZAdj hxz hseparator
  let Lside : OrderedClique S.rightWithSeparatorClique := .pair rx rz edge_side
  obtain ⟨_edge_core_z, hpair_no⟩ :=
    R.second_path_reverse_collapse_pair_no_model_of_original_pair_core_or_z
      hyz edge hno_model_pair hv2_core_or_z
  have hpair_no' :
      forall edgeD :
        D.graph.Adj
          (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map z)),
        Not (CompatibleDominatingK5Model
          (.pair (D.map (R.coreCollapse.map v1))
            (D.map (R.coreCollapse.map z)) edgeD)) := by
    simpa [P, H2, D] using hpair_no
  have hx_map_v1 := R.coreCollapse_map_x_eq_map_v1
  have edgeD :
      D.graph.Adj
        (D.map (R.coreCollapse.map v1)) (D.map (R.coreCollapse.map z)) := by
    have h := hom.map_adj edge_side
    simpa [hom, MinimalYZReroutingCertificate.rightWithSeparatorCliqueSecondReverseCollapseHom,
      rightWithSeparatorCliqueCollapseHom,
      P, H2, D, rx, rz, hx_map_v1] using h
  have hno_Lside : Not (CompatibleDominatingK5Model Lside) :=
    not_compatible_of_map_not_compatible Lside hom hhom_inj (by
    simpa [Lside, OrderedClique.map, hom,
      MinimalYZReroutingCertificate.rightWithSeparatorCliqueSecondReverseCollapseHom,
      rightWithSeparatorCliqueCollapseHom,
      P, H2, D, rx, rz, hx_map_v1] using hpair_no' edgeD)
  simpa [Separation.rightTripleXZOrderedClique, Lside, rx, rz] using hno_Lside


end Schematic.Math.GraphTheory
