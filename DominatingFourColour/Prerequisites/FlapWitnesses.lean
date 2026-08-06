import DominatingFourColour.Prerequisites.TriadDataConversions

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}
structure RST31OtherFlapTreeWitness
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B D : T.Flap) where
  H : G.Subgraph
  tree : H.coe.IsTree
  feet_mem : forall i : Fin 3, feet i ∈ H.verts
  apex : H.verts
  foot_ne_apex :
    forall i : Fin 3, (⟨feet i, feet_mem i⟩ : H.verts) ≠ apex
  unreachable :
    forall {i j : Fin 3}, i ≠ j ->
      ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
          ⟨(⟨feet i, feet_mem i⟩ : H.verts), by exact foot_ne_apex i⟩
          ⟨(⟨feet j, feet_mem j⟩ : H.verts), by exact foot_ne_apex j⟩
  verts_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D
  boundary_inter_ncard_le :
    (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩ H.verts).ncard <= 3

structure RST31OtherFlapPairPathsWitness
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B D : T.Flap) where
  H : G.Subgraph
  tree : H.coe.IsTree
  feet_mem : forall i : Fin 3, feet i ∈ H.verts
  apex : H.verts
  apex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i
  pair_path_through_apex :
    forall {i j : Fin 3}, i ≠ j ->
      Exists fun p : G.Walk (feet i) (feet j) =>
        p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support
  verts_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D
  boundary_inter_ncard_le :
    (relativeVertexBoundary G (T.flapVertexSet B) T.vertexSet ∩ H.verts).ncard <= 3

structure RST31OtherFlapBlockedCoreWitness
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap) where
  core : Set V
  boundary : Set V
  closed :
    forall {a b : V}, a ∈ core -> b ∉ core -> b ∉ boundary -> Not (G.Adj a b)
  feet_not_mem : forall i : Fin 3, feet i ∉ core
  core_nonempty : core.Nonempty
  boundary_ncard_le : boundary.ncard <= 3
  other_flap_subset_compl :
    forall C : T.Flap, C ≠ D -> T.flapVertexSet C ⊆ coreᶜ

structure RST31OtherFlapComponentWitness
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap) where
  separator : Set V
  component : (G.induce separatorᶜ).ConnectedComponent
  feet_not_mem :
    forall i : Fin 3, feet i ∉ induceComponentSupport (G := G) component
  boundary_ncard_le :
    (relativeVertexBoundary G (induceComponentSupport (G := G) component)
      separator).ncard <= 3
  other_flap_subset_compl :
    forall C : T.Flap, C ≠ D ->
      T.flapVertexSet C ⊆ (induceComponentSupport (G := G) component)ᶜ

structure RST31OtherFlapEssentialComponentPairPathsWitness
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap) where
  component :
    (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent
  H : G.Subgraph
  tree : H.coe.IsTree
  apex : H.verts
  feet_mem : forall i : Fin 3, feet i ∈ H.verts
  apex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i
  pair_path_through_apex :
    forall {i j : Fin 3}, i ≠ j ->
      Exists fun p : G.Walk (feet i) (feet j) =>
        p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support
  verts_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D
  boundary_inter_ncard_le :
    (relativeVertexBoundary G (induceComponentSupport (G := G) component)
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ H.verts).ncard <= 3
  other_flap_subset_compl :
    forall C : T.Flap, C ≠ D ->
      T.flapVertexSet C ⊆ (induceComponentSupport (G := G) component)ᶜ

structure RST31OtherFlapEssentialBoundaryPairPathsWitness
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap) where
  component :
    (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent
  flap_subset_component :
    T.flapVertexSet D ⊆ induceComponentSupport (G := G) component
  boundary_essential :
    forall E : T.Flap, E ≠ D ->
      relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
        {v : V | T.EssentialWithin (T.flapVertexSet D) v}
  H : G.Subgraph
  tree : H.coe.IsTree
  apex : H.verts
  feet_mem : forall i : Fin 3, feet i ∈ H.verts
  apex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i
  pair_path_through_apex :
    forall {i j : Fin 3}, i ≠ j ->
      Exists fun p : G.Walk (feet i) (feet j) =>
        p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support
  verts_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D
  boundary_inter_ncard_le :
    (relativeVertexBoundary G (induceComponentSupport (G := G) component)
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ H.verts).ncard <= 3

structure RST31OtherFlapEssentialBoundaryCorePairPathsWitness
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (D : T.Flap) where
  component :
    (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent
  flap_subset_component :
    T.flapVertexSet D ⊆ induceComponentSupport (G := G) component
  H : G.Subgraph
  tree : H.coe.IsTree
  apex : H.verts
  feet_mem : forall i : Fin 3, feet i ∈ H.verts
  apex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i
  pair_path_through_apex :
    forall {i j : Fin 3}, i ≠ j ->
      Exists fun p : G.Walk (feet i) (feet j) =>
        p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support
  verts_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D
  boundary_inter_ncard_le :
    (relativeVertexBoundary G (induceComponentSupport (G := G) component)
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ H.verts).ncard <= 3

structure RST31EssentialComponentBoundaryPairPathsWitness
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    (C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent) where
  H : G.Subgraph
  tree : H.coe.IsTree
  apex : H.verts
  feet_mem : forall i : Fin 3, feet i ∈ H.verts
  apex_not_foot : forall i : Fin 3, (apex : V) ≠ feet i
  pair_path_through_apex :
    forall {i j : Fin 3}, i ≠ j ->
      Exists fun p : G.Walk (feet i) (feet j) =>
        p.toSubgraph ≤ H ∧ p.IsPath ∧ (apex : V) ∈ p.support
  verts_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D
  boundary_inter_ncard_le :
    (relativeVertexBoundary G (induceComponentSupport (G := G) C)
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ H.verts).ncard <= 3

structure RST31EssentialComponentBoundaryTreeWitness
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    (C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent) where
  H : G.Subgraph
  tree : H.coe.IsTree
  apex : H.verts
  feet_mem : forall i : Fin 3, feet i ∈ H.verts
  foot_ne_apex :
    forall i : Fin 3, (⟨feet i, feet_mem i⟩ : H.verts) ≠ apex
  unreachable :
    forall {i j : Fin 3}, i ≠ j ->
      ¬ (H.coe.induce ({apex} : Set H.verts)ᶜ).Reachable
          ⟨(⟨feet i, feet_mem i⟩ : H.verts), by exact foot_ne_apex i⟩
          ⟨(⟨feet j, feet_mem j⟩ : H.verts), by exact foot_ne_apex j⟩
  verts_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D
  boundary_inter_ncard_le :
    (relativeVertexBoundary G (induceComponentSupport (G := G) C)
      {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ H.verts).ncard <= 3

def RST31OtherFlapComponentWitness.toBlockedCoreWitness
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    (W : RST31OtherFlapComponentWitness (G := G) T D) :
    RST31OtherFlapBlockedCoreWitness (G := G) T D where
  core := induceComponentSupport (G := G) W.component
  boundary := relativeVertexBoundary G (induceComponentSupport (G := G) W.component)
    W.separator
  closed := induceComponentSupport_closed_with_relativeBoundary (G := G) W.component
  feet_not_mem := W.feet_not_mem
  core_nonempty := induceComponentSupport_nonempty (G := G) W.component
  boundary_ncard_le := W.boundary_ncard_le
  other_flap_subset_compl := W.other_flap_subset_compl

noncomputable def RST31OtherFlapEssentialComponentPairPathsWitness.toRST31LeanTriadData
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    {D : T.Flap}
    (Y : RST31OtherFlapEssentialComponentPairPathsWitness (G := G) T D) :
    RST31LeanTriadData G feet W := by
  classical
  letI : DecidableEq Y.H.verts := Classical.decEq Y.H.verts
  exact RST31LeanTriadData.of_essential_component_tree_root_pair_paths_unique_flap
    (G := G) hno hfeet_injective hlean havoid D Y.component Y.tree
    Y.feet_mem Y.apex_not_foot Y.pair_path_through_apex Y.verts_subset
    Y.boundary_inter_ncard_le Y.other_flap_subset_compl

noncomputable def RST31OtherFlapEssentialBoundaryPairPathsWitness.toRST31LeanTriadData
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    {D : T.Flap}
    (Y : RST31OtherFlapEssentialBoundaryPairPathsWitness (G := G) T D) :
    RST31LeanTriadData G feet W := by
  classical
  letI : DecidableEq Y.H.verts := Classical.decEq Y.H.verts
  exact
    RST31LeanTriadData.of_essential_component_tree_root_pair_paths_unique_flap_of_boundaries_essential
      (G := G) hno hfeet_injective hlean havoid D Y.component
      Y.flap_subset_component Y.boundary_essential Y.tree
      Y.feet_mem Y.apex_not_foot Y.pair_path_through_apex Y.verts_subset
      Y.boundary_inter_ncard_le

noncomputable def RST31OtherFlapEssentialBoundaryCorePairPathsWitness.toRST31LeanTriadData
    [Fintype V]
    {feet : Fin 3 -> V}
    {W : Set V}
    (hno : RST31NoSeparation G feet)
    (hfeet_injective : Function.Injective feet)
    {T : Triad G feet}
    (hlean : T.Lean)
    (havoid : T.AvoidsSet W)
    {D : T.Flap}
    (Y : RST31OtherFlapEssentialBoundaryCorePairPathsWitness (G := G) T D)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v}) :
    RST31LeanTriadData G feet W := by
  classical
  letI : DecidableEq Y.H.verts := Classical.decEq Y.H.verts
  exact
    RST31LeanTriadData.of_essential_component_tree_root_pair_paths_unique_flap_of_boundaries_essential
      (G := G) hno hfeet_injective hlean havoid D Y.component
      Y.flap_subset_component hboundary_essential Y.tree
      Y.feet_mem Y.apex_not_foot Y.pair_path_through_apex Y.verts_subset
      Y.boundary_inter_ncard_le

def RST31OtherFlapTreeWitness.toPairPathsWitness
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {B D : T.Flap}
    (W : RST31OtherFlapTreeWitness (G := G) T B D)
    [DecidableEq W.H.verts] :
    RST31OtherFlapPairPathsWitness (G := G) T B D := by
  obtain ⟨hapex, hpairs⟩ := treePairPaths_of_deleteRoot_unreachable
    W.tree W.feet_mem W.foot_ne_apex W.unreachable
  exact {
    H := W.H
    tree := W.tree
    feet_mem := W.feet_mem
    apex := W.apex
    apex_not_foot := hapex
    pair_path_through_apex := hpairs
    verts_subset := W.verts_subset
    boundary_inter_ncard_le := W.boundary_inter_ncard_le }

def RST31EssentialComponentBoundaryTreeWitness.toPairPathsWitness
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (W : RST31EssentialComponentBoundaryTreeWitness (G := G) (D := D) T C)
    [DecidableEq W.H.verts] :
    RST31EssentialComponentBoundaryPairPathsWitness (G := G) (D := D) T C := by
  obtain ⟨hapex, hpairs⟩ := treePairPaths_of_deleteRoot_unreachable
    W.tree W.feet_mem W.foot_ne_apex W.unreachable
  exact {
    H := W.H
    tree := W.tree
    feet_mem := W.feet_mem
    apex := W.apex
    apex_not_foot := hapex
    pair_path_through_apex := hpairs
    verts_subset := W.verts_subset
    boundary_inter_ncard_le := W.boundary_inter_ncard_le }

def RST31EssentialBoundarySteinerTree.toComponentBoundaryTreeWitness
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    (apex : Z.treeInG.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, Z.feet_mem_treeInG i⟩ : Z.treeInG.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (Z.treeInG.coe.induce ({apex} : Set Z.treeInG.verts)ᶜ).Reachable
            ⟨(⟨feet i, Z.feet_mem_treeInG i⟩ : Z.treeInG.verts),
              by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, Z.feet_mem_treeInG j⟩ : Z.treeInG.verts),
              by exact hfoot_ne_apex j⟩) :
    RST31EssentialComponentBoundaryTreeWitness (G := G) (D := D) T C where
  H := Z.treeInG
  tree := Z.treeInG_isTree
  apex := apex
  feet_mem := Z.feet_mem_treeInG
  foot_ne_apex := hfoot_ne_apex
  unreachable := hunreachable
  verts_subset := Z.treeInG_verts_subset
  boundary_inter_ncard_le := Z.boundary_inter_treeInG_ncard_le

def RST31EssentialBoundarySteinerTree.toComponentBoundaryPairPathsWitness
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    [DecidableEq Z.treeInG.verts]
    (apex : Z.treeInG.verts)
    (hfoot_ne_apex :
      forall i : Fin 3, (⟨feet i, Z.feet_mem_treeInG i⟩ : Z.treeInG.verts) ≠ apex)
    (hunreachable :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (Z.treeInG.coe.induce ({apex} : Set Z.treeInG.verts)ᶜ).Reachable
            ⟨(⟨feet i, Z.feet_mem_treeInG i⟩ : Z.treeInG.verts),
              by exact hfoot_ne_apex i⟩
            ⟨(⟨feet j, Z.feet_mem_treeInG j⟩ : Z.treeInG.verts),
              by exact hfoot_ne_apex j⟩) :
    RST31EssentialComponentBoundaryPairPathsWitness (G := G) (D := D) T C := by
  obtain ⟨hapex, hpairs⟩ := treePairPaths_of_deleteRoot_unreachable
    Z.treeInG_isTree Z.feet_mem_treeInG hfoot_ne_apex hunreachable
  exact {
    H := Z.treeInG
    tree := Z.treeInG_isTree
    feet_mem := Z.feet_mem_treeInG
    apex := apex
    apex_not_foot := hapex
    pair_path_through_apex := hpairs
    verts_subset := Z.treeInG_verts_subset
    boundary_inter_ncard_le := Z.boundary_inter_treeInG_ncard_le }

noncomputable def RST31EssentialBoundarySteinerTree.toComponentBoundaryTreeWitnessOfTerminalDegrees
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    [Fintype Z.treeSubgraph.verts]
    [DecidableRel Z.treeSubgraph.coe.Adj]
    (hfeet_injective : Function.Injective feet)
    {root : Z.treeSubgraph.verts}
    (hroot_degree : 3 <= Z.treeSubgraph.coe.degree root)
    (hroot_unique :
      forall z : Z.treeSubgraph.verts,
        3 <= Z.treeSubgraph.coe.degree z -> z = root)
    (hterminal_degree :
      forall i : Fin 3, Z.treeSubgraph.coe.degree (Z.terminalTree i) = 1) :
    RST31EssentialComponentBoundaryTreeWitness (G := G) (D := D) T C := by
  classical
  letI : DecidableEq Z.treeSubgraph.verts := Classical.decEq _
  letI : DecidableEq Z.treeInG.verts := Classical.decEq _
  exact Z.toComponentBoundaryTreeWitness (Z.treeVertexInG root)
    (by
      intro i h
      have hval : ((Z.treeVertexInG root : Z.treeInG.verts) : V) = feet i := by
        exact (congrArg (fun x : Z.treeInG.verts => (x : V)) h.symm)
      exact (Z.treeVertexInG_not_foot_of_degree_ge_three
        hroot_degree hterminal_degree i) hval)
    (by
      intro i j hij
      exact Z.unreachable_treeInG_of_terminal_degrees
        hfeet_injective hroot_degree hroot_unique hterminal_degree hij)

noncomputable def RST31EssentialBoundarySteinerTree.toComponentBoundaryPairPathsWitnessOfTerminalDegrees
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    [Fintype Z.treeSubgraph.verts]
    [DecidableRel Z.treeSubgraph.coe.Adj]
    (hfeet_injective : Function.Injective feet)
    {root : Z.treeSubgraph.verts}
    (hroot_degree : 3 <= Z.treeSubgraph.coe.degree root)
    (hroot_unique :
      forall z : Z.treeSubgraph.verts,
        3 <= Z.treeSubgraph.coe.degree z -> z = root)
    (hterminal_degree :
      forall i : Fin 3, Z.treeSubgraph.coe.degree (Z.terminalTree i) = 1) :
    RST31EssentialComponentBoundaryPairPathsWitness (G := G) (D := D) T C := by
  classical
  letI : DecidableEq Z.treeSubgraph.verts := Classical.decEq _
  letI : DecidableEq Z.treeInG.verts := Classical.decEq _
  exact Z.toComponentBoundaryPairPathsWitness (Z.treeVertexInG root)
    (by
      intro i h
      have hval : ((Z.treeVertexInG root : Z.treeInG.verts) : V) = feet i := by
        exact (congrArg (fun x : Z.treeInG.verts => (x : V)) h.symm)
      exact (Z.treeVertexInG_not_foot_of_degree_ge_three
        hroot_degree hterminal_degree i) hval)
    (by
      intro i j hij
      exact Z.unreachable_treeInG_of_terminal_degrees
        hfeet_injective hroot_degree hroot_unique hterminal_degree hij)

theorem RST31EssentialBoundarySteinerTree.exists_component_boundary_tree_witness_of_connector_neighbor_ncard_one
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    [Fintype Z.treeSubgraph.verts]
    [DecidableRel Z.treeSubgraph.coe.Adj]
    (hfeet_injective : Function.Injective feet)
    (hY_terminal_neighbor_ncard :
      forall i : Fin 3, (Y.H.neighborSet (feet i)).ncard = 1) :
    Nonempty (RST31EssentialComponentBoundaryTreeWitness (G := G) (D := D) T C) := by
  classical
  let hterminal_degree :=
    Z.terminal_degrees_one_of_B_neighbor_ncard_one hfeet_injective
      (Z.B_terminal_neighbor_ncard_one_of_connector_neighbor_ncard_one
        hfeet_injective hY_terminal_neighbor_ncard)
  obtain ⟨root, hroot_degree, hroot_unique⟩ :=
    Z.exists_unique_branch_of_terminal_degrees hfeet_injective hterminal_degree
  exact ⟨Z.toComponentBoundaryTreeWitnessOfTerminalDegrees
    hfeet_injective hroot_degree hroot_unique hterminal_degree⟩

theorem RST31EssentialBoundarySteinerTree.exists_component_boundary_pair_paths_witness_of_connector_neighbor_ncard_one
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    [Fintype Z.treeSubgraph.verts]
    [DecidableRel Z.treeSubgraph.coe.Adj]
    (hfeet_injective : Function.Injective feet)
    (hY_terminal_neighbor_ncard :
      forall i : Fin 3, (Y.H.neighborSet (feet i)).ncard = 1) :
    Nonempty (RST31EssentialComponentBoundaryPairPathsWitness (G := G) (D := D) T C) := by
  classical
  obtain ⟨W⟩ :=
    Z.exists_component_boundary_tree_witness_of_connector_neighbor_ncard_one
      hfeet_injective hY_terminal_neighbor_ncard
  letI : DecidableEq W.H.verts := Classical.decEq _
  exact ⟨W.toPairPathsWitness⟩

theorem RST31EssentialBoundaryConnector.exists_component_boundary_tree_witness_of_terminal_neighbor_ncard_one
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C)
    (hfeet_injective : Function.Injective feet)
    (hY_terminal_neighbor_ncard :
      forall i : Fin 3, (Y.H.neighborSet (feet i)).ncard = 1) :
    Nonempty (RST31EssentialComponentBoundaryTreeWitness (G := G) (D := D) T C) := by
  classical
  obtain ⟨Z⟩ := Y.exists_steiner_tree
  letI : Fintype Z.treeSubgraph.verts := Z.treeSubgraph.verts.toFinite.fintype
  exact Z.exists_component_boundary_tree_witness_of_connector_neighbor_ncard_one
    hfeet_injective hY_terminal_neighbor_ncard

theorem RST31EssentialBoundaryConnector.exists_component_boundary_pair_paths_witness_of_terminal_neighbor_ncard_one
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C)
    (hfeet_injective : Function.Injective feet)
    (hY_terminal_neighbor_ncard :
      forall i : Fin 3, (Y.H.neighborSet (feet i)).ncard = 1) :
    Nonempty (RST31EssentialComponentBoundaryPairPathsWitness (G := G) (D := D) T C) := by
  classical
  obtain ⟨W⟩ :=
    Y.exists_component_boundary_tree_witness_of_terminal_neighbor_ncard_one
      hfeet_injective hY_terminal_neighbor_ncard
  letI : DecidableEq W.H.verts := Classical.decEq _
  exact ⟨W.toPairPathsWitness⟩

theorem RST31EssentialBoundaryAttachment.exists_component_boundary_pair_paths_witness_of_other_branches_avoid
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C)
    (hfeet_injective : Function.Injective feet)
    (hother :
      forall i j : Fin 3, j ≠ i -> feet i ∉ (A.branchSubgraph j).verts) :
    Nonempty (RST31EssentialComponentBoundaryPairPathsWitness (G := G) (D := D) T C) := by
  classical
  exact A.toConnector.exists_component_boundary_pair_paths_witness_of_terminal_neighbor_ncard_one
    hfeet_injective (by
      intro i
      simpa [RST31EssentialBoundaryAttachment.toConnector] using
        A.connector_neighborSet_foot_ncard_of_other_branches_avoid i
          (hother i))

theorem Triad.exists_essential_component_boundary_triad_witness_of_nonfoot_boundary
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (hD_subset_C : T.flapVertexSet D ⊆ induceComponentSupport (G := G) C)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    {x : V}
    (hx_boundary :
      x ∈ relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    (hx_not_feet : x ∉ Set.range feet) :
    Exists fun T' : Triad G feet =>
      T'.vertexSet ⊆ T.vertexSet ∪ T.flapVertexSet D ∧
        (relativeVertexBoundary G (induceComponentSupport (G := G) C)
          {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
            T'.vertexSet).ncard <= 3 := by
  classical
  obtain ⟨A, hother⟩ :=
    T.exists_essential_boundary_attachment_to_nonfoot_boundary
      hfeet_injective hD_subset_C hboundary_essential hx_boundary hx_not_feet
  obtain ⟨Y⟩ :=
    A.exists_component_boundary_pair_paths_witness_of_other_branches_avoid
      hfeet_injective hother
  letI : DecidableEq Y.H.verts := Classical.decEq Y.H.verts
  exact T.exists_essential_component_boundary_triad_witness_of_tree_root_pair_paths
    (C := C) Y.tree Y.feet_mem Y.apex_not_foot
    Y.pair_path_through_apex Y.verts_subset Y.boundary_inter_ncard_le

noncomputable def RST31LeanTriadData.of_boundaries_essential_and_nonfoot_boundary
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
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
          {v : V | T.EssentialWithin (T.flapVertexSet D) v}) :
    RST31LeanTriadData G feet W := by
  classical
  refine RST31LeanTriadData.of_boundaries_essential_and_nonfoot_boundary_vertex_witness
    (G := G) hno hfeet_injective hlean havoid D hboundary_essential ?_
  intro C hD_subset_C x hx_boundary _hxT hx_not_feet
  exact T.exists_essential_component_boundary_triad_witness_of_nonfoot_boundary
    hfeet_injective hD_subset_C hboundary_essential hx_boundary hx_not_feet


end Schematic.Math.GraphTheory
