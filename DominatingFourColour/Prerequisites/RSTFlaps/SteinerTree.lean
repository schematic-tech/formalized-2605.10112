import DominatingFourColour.Prerequisites.RSTFlaps.BoundaryAttachments

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

structure RST31EssentialBoundarySteinerTree
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C)
    where
  B : G.Subgraph
  B_le_connector : B ≤ Y.H
  B_connected : B.coe.Connected
  feet_mem_B : forall i : Fin 3, feet i ∈ B.verts
  B_minimal :
    forall B' : G.Subgraph,
      B' ≤ Y.H ->
        B'.coe.Connected ->
          (forall i : Fin 3, feet i ∈ B'.verts) ->
            B'.verts ⊆ B.verts ->
              B.verts ⊆ B'.verts
  treeSubgraph : B.coe.Subgraph
  tree : treeSubgraph.coe.IsTree
  tree_spanning : treeSubgraph.IsSpanning
  boundary_inter_B_ncard_le :
    (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ B.verts).ncard <= 3

theorem RST31EssentialBoundaryConnector.exists_steiner_tree
    [Fintype V]
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C) :
    Nonempty (RST31EssentialBoundarySteinerTree (G := G) Y) := by
  classical
  obtain ⟨B, hB_le, hB_connected, hfeet_B, hB_minimal⟩ :=
    Subgraph.Connected.exists_minimal_connected_subgraph_containing
      (G := G) (B := Y.H) Y.connected (terminal := feet) Y.feet_mem
  obtain ⟨S, hS_tree, hS_spanning⟩ :=
    Connected.exists_spanning_tree_subgraph (G := B.coe) hB_connected
  have hboundary_inter_B :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C)
          {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ B.verts).ncard <= 3 := by
    have hsubset :
        relativeVertexBoundary G (induceComponentSupport (G := G) C)
            {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ B.verts ⊆
          relativeVertexBoundary G (induceComponentSupport (G := G) C)
            {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ Y.H.verts := by
      intro v hv
      exact ⟨hv.1, hB_le.left hv.2⟩
    exact le_trans (Set.ncard_le_ncard hsubset) Y.boundary_inter_ncard_le
  exact ⟨{
    B := B
    B_le_connector := hB_le
    B_connected := hB_connected
    feet_mem_B := hfeet_B
    B_minimal := hB_minimal
    treeSubgraph := S
    tree := hS_tree
    tree_spanning := hS_spanning
    boundary_inter_B_ncard_le := hboundary_inter_B
  }⟩

def RST31EssentialBoundarySteinerTree.treeInG
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y) :
    G.Subgraph :=
  SimpleGraph.Subgraph.coeSubgraph Z.treeSubgraph

theorem RST31EssentialBoundarySteinerTree.treeInG_isTree
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y) :
    Z.treeInG.coe.IsTree :=
  Schematic.Math.GraphTheory.Subgraph.coeSubgraph_isTree Z.treeSubgraph Z.tree

theorem RST31EssentialBoundarySteinerTree.treeInG_le_B
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y) :
    Z.treeInG ≤ Z.B :=
  SimpleGraph.Subgraph.coeSubgraph_le Z.treeSubgraph

theorem RST31EssentialBoundarySteinerTree.treeInG_le_connector
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y) :
    Z.treeInG ≤ Y.H :=
  le_trans Z.treeInG_le_B Z.B_le_connector

theorem RST31EssentialBoundarySteinerTree.treeInG_verts_eq_B
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y) :
    Z.treeInG.verts = Z.B.verts := by
  ext v
  constructor
  · intro hv
    exact Z.treeInG_le_B.left hv
  · intro hv
    let vB : Z.B.verts := ⟨v, hv⟩
    have hv_tree : vB ∈ Z.treeSubgraph.verts := Z.tree_spanning vB
    change v ∈ (SimpleGraph.Subgraph.coeSubgraph Z.treeSubgraph).verts
    exact ⟨vB, hv_tree, rfl⟩

theorem RST31EssentialBoundarySteinerTree.feet_mem_treeInG
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    (i : Fin 3) :
    feet i ∈ Z.treeInG.verts := by
  rw [Z.treeInG_verts_eq_B]
  exact Z.feet_mem_B i

theorem RST31EssentialBoundarySteinerTree.treeInG_verts_subset
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y) :
    Z.treeInG.verts ⊆ T.vertexSet ∪ T.flapVertexSet D := by
  intro v hv
  exact Y.verts_subset (Z.treeInG_le_connector.left hv)

theorem RST31EssentialBoundarySteinerTree.boundary_inter_treeInG_ncard_le
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y) :
    (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
      Z.treeInG.verts).ncard <= 3 := by
  rw [Z.treeInG_verts_eq_B]
  exact Z.boundary_inter_B_ncard_le

theorem RST31EssentialBoundarySteinerTree.treeSubgraph_nontrivial
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    (hfeet_injective : Function.Injective feet) :
    Nontrivial Z.treeSubgraph.verts := by
  let f0B : Z.B.verts := ⟨feet 0, Z.feet_mem_B 0⟩
  let f1B : Z.B.verts := ⟨feet 1, Z.feet_mem_B 1⟩
  let f0T : Z.treeSubgraph.verts := ⟨f0B, Z.tree_spanning f0B⟩
  let f1T : Z.treeSubgraph.verts := ⟨f1B, Z.tree_spanning f1B⟩
  refine ⟨⟨f0T, f1T, ?_⟩⟩
  intro h
  have hfeet : feet 0 = feet 1 := by
    have hval := congrArg (fun x : Z.treeSubgraph.verts => ((x : Z.B.verts) : V)) h
    simpa [f0T, f1T, f0B, f1B] using hval
  exact (by decide : (0 : Fin 3) ≠ 1) (hfeet_injective hfeet)

theorem RST31EssentialBoundarySteinerTree.B_nontrivial
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    (hfeet_injective : Function.Injective feet) :
    Nontrivial Z.B.verts := by
  let f0B : Z.B.verts := ⟨feet 0, Z.feet_mem_B 0⟩
  let f1B : Z.B.verts := ⟨feet 1, Z.feet_mem_B 1⟩
  refine ⟨⟨f0B, f1B, ?_⟩⟩
  intro h
  have hfeet : feet 0 = feet 1 := by
    have hval := congrArg (fun x : Z.B.verts => (x : V)) h
    simpa [f0B, f1B] using hval
  exact (by decide : (0 : Fin 3) ≠ 1) (hfeet_injective hfeet)

def RST31EssentialBoundarySteinerTree.terminalTree
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    (i : Fin 3) :
    Z.treeSubgraph.verts :=
  ⟨(⟨feet i, Z.feet_mem_B i⟩ : Z.B.verts),
    Z.tree_spanning (⟨feet i, Z.feet_mem_B i⟩ : Z.B.verts)⟩

theorem RST31EssentialBoundarySteinerTree.terminalTree_injective
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    (hfeet_injective : Function.Injective feet) :
    Function.Injective Z.terminalTree := by
  intro i j hij
  apply hfeet_injective
  have hval := congrArg (fun x : Z.treeSubgraph.verts => ((x : Z.B.verts) : V)) hij
  simpa [RST31EssentialBoundarySteinerTree.terminalTree] using hval

noncomputable def RST31EssentialBoundarySteinerTree.treeVertexInG
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    (v : Z.treeSubgraph.verts) :
    Z.treeInG.verts :=
  (Schematic.Math.GraphTheory.Subgraph.coeSubgraphCoeIso Z.treeSubgraph) v

@[simp]
theorem RST31EssentialBoundarySteinerTree.treeVertexInG_val
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    (v : Z.treeSubgraph.verts) :
    ((Z.treeVertexInG v : Z.treeInG.verts) : V) = ((v : Z.B.verts) : V) := by
  rfl

@[simp]
theorem RST31EssentialBoundarySteinerTree.treeVertexInG_terminalTree
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    (i : Fin 3) :
    Z.treeVertexInG (Z.terminalTree i) =
      (⟨feet i, Z.feet_mem_treeInG i⟩ : Z.treeInG.verts) := by
  apply Subtype.ext
  change ((Z.treeVertexInG (Z.terminalTree i) : Z.treeInG.verts) : V) = feet i
  simp [RST31EssentialBoundarySteinerTree.terminalTree]

theorem RST31EssentialBoundarySteinerTree.treeVertexInG_not_foot_of_degree_ge_three
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
    {root : Z.treeSubgraph.verts}
    (hroot_degree : 3 <= Z.treeSubgraph.coe.degree root)
    (hterminal_degree :
      forall i : Fin 3, Z.treeSubgraph.coe.degree (Z.terminalTree i) = 1)
    (i : Fin 3) :
    ((Z.treeVertexInG root : Z.treeInG.verts) : V) ≠ feet i := by
  intro hroot_foot
  have hroot_eq_terminal : root = Z.terminalTree i := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [RST31EssentialBoundarySteinerTree.treeVertexInG] using hroot_foot
  have hdegree_one : Z.treeSubgraph.coe.degree root = 1 := by
    rw [hroot_eq_terminal]
    exact hterminal_degree i
  omega

theorem RST31EssentialBoundarySteinerTree.exists_two_terminal_leaves
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
    (hfeet_injective : Function.Injective feet) :
    Exists fun uT : Z.treeSubgraph.verts =>
      Exists fun vT : Z.treeSubgraph.verts =>
        uT ≠ vT ∧
          Z.treeSubgraph.coe.degree uT = 1 ∧
            Z.treeSubgraph.coe.degree vT = 1 ∧
              ((uT : Z.B.verts) : V) ∈ Set.range feet ∧
                ((vT : Z.B.verts) : V) ∈ Set.range feet := by
  classical
  letI : Nontrivial Z.treeSubgraph.verts := Z.treeSubgraph_nontrivial hfeet_injective
  exact
    Subgraph.minimal_connected_spanning_tree_exists_two_terminal_leaves
      (C := Y.H) (B := Z.B) (T := Z.treeSubgraph) (terminal := feet)
      Z.B_le_connector Z.feet_mem_B Z.B_minimal Z.tree Z.tree_spanning

theorem RST31EssentialBoundarySteinerTree.branch_vertices_card_le_one
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
    (hfeet_injective : Function.Injective feet) :
    (Finset.univ.filter
      fun vT : Z.treeSubgraph.verts => 3 <= Z.treeSubgraph.coe.degree vT).card <= 1 := by
  classical
  letI : Nontrivial Z.treeSubgraph.verts := Z.treeSubgraph_nontrivial hfeet_injective
  exact
    Subgraph.minimal_connected_spanning_tree_card_degree_ge_three_le_one_of_three_terminals
      (C := Y.H) (B := Z.B) (T := Z.treeSubgraph) (terminal := feet)
      Z.B_le_connector Z.feet_mem_B Z.B_minimal Z.tree Z.tree_spanning

theorem RST31EssentialBoundarySteinerTree.terminal_degrees_one_of_B_neighbor_ncard_one
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
    (hB_terminal_neighbor_ncard :
      forall i : Fin 3,
        (Z.B.coe.neighborSet (⟨feet i, Z.feet_mem_B i⟩ : Z.B.verts)).ncard = 1) :
    forall i : Fin 3,
      Z.treeSubgraph.coe.degree (Z.terminalTree i) = 1 := by
  classical
  letI : Nontrivial Z.treeSubgraph.verts := Z.treeSubgraph_nontrivial hfeet_injective
  have hdegree :=
    Subgraph.spanning_tree_terminal_degrees_one_of_subgraph_neighbor_ncard_one
      (B := Z.B) (T := Z.treeSubgraph)
      Z.tree.connected Z.tree_spanning
      (terminal := fun i : Fin 3 => (⟨feet i, Z.feet_mem_B i⟩ : Z.B.verts))
      (by intro i; infer_instance)
      (by intro i; infer_instance)
      hB_terminal_neighbor_ncard
  intro i
  simpa [RST31EssentialBoundarySteinerTree.terminalTree] using hdegree i

theorem RST31EssentialBoundarySteinerTree.B_terminal_neighbor_ncard_one_of_connector_neighbor_ncard_one
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    {Y : RST31EssentialBoundaryConnector (G := G) (D := D) T C}
    (Z : RST31EssentialBoundarySteinerTree (G := G) Y)
    (hfeet_injective : Function.Injective feet)
    (hY_terminal_neighbor_ncard :
      forall i : Fin 3, (Y.H.neighborSet (feet i)).ncard = 1) :
    forall i : Fin 3,
      (Z.B.coe.neighborSet (⟨feet i, Z.feet_mem_B i⟩ : Z.B.verts)).ncard = 1 := by
  classical
  letI : Nontrivial Z.B.verts := Z.B_nontrivial hfeet_injective
  intro i
  let vB : Z.B.verts := ⟨feet i, Z.feet_mem_B i⟩
  have hpos_coe : 0 < Z.B.coe.degree vB :=
    Z.B_connected.preconnected.degree_pos_of_nontrivial vB
  have hcoe_degree :
      Z.B.coe.degree vB = Z.B.degree (feet i) := by
    simp [vB]
  have hpos : 0 < Z.B.degree (feet i) := by
    rwa [hcoe_degree] at hpos_coe
  have hYdegree_ncard :
      (Y.H.neighborSet (feet i)).ncard = Y.H.degree (feet i) := by
    simp [SimpleGraph.Subgraph.degree, Set.ncard_eq_toFinset_card']
  have hYdegree : Y.H.degree (feet i) = 1 := by
    rw [← hYdegree_ncard]
    exact hY_terminal_neighbor_ncard i
  have hle : Z.B.degree (feet i) <= Y.H.degree (feet i) :=
    SimpleGraph.Subgraph.degree_le' Z.B Y.H Z.B_le_connector (feet i)
  have hBdegree : Z.B.degree (feet i) = 1 := by
    rw [hYdegree] at hle
    omega
  have hBdegree_ncard :
      (Z.B.neighborSet (feet i)).ncard = Z.B.degree (feet i) := by
    simp [SimpleGraph.Subgraph.degree, Set.ncard_eq_toFinset_card']
  have hcoe_ncard :
      (Z.B.coe.neighborSet vB).ncard =
        (Z.B.neighborSet (feet i)).ncard := by
    rw [← Set.fintypeCard_eq_ncard, ← Set.fintypeCard_eq_ncard]
    exact Fintype.card_congr (SimpleGraph.Subgraph.coeNeighborSetEquiv vB)
  rw [hcoe_ncard, hBdegree_ncard, hBdegree]

theorem RST31EssentialBoundarySteinerTree.exists_unique_branch_of_terminal_degrees
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
    (hterminal_degree :
      forall i : Fin 3, Z.treeSubgraph.coe.degree (Z.terminalTree i) = 1) :
    Exists fun root : Z.treeSubgraph.verts =>
      3 <= Z.treeSubgraph.coe.degree root ∧
        forall z : Z.treeSubgraph.verts,
          3 <= Z.treeSubgraph.coe.degree z -> z = root := by
  classical
  letI : Nontrivial Z.treeSubgraph.verts := Z.treeSubgraph_nontrivial hfeet_injective
  exact
    Schematic.Math.GraphTheory.IsTree.exists_unique_degree_ge_three_of_three_distinct_degree_one
      (G := Z.treeSubgraph.coe) Z.tree (Z.terminalTree_injective hfeet_injective)
      hterminal_degree
      (Z.branch_vertices_card_le_one hfeet_injective)

theorem RST31EssentialBoundarySteinerTree.exists_unique_branch_of_B_neighbor_ncard_one
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
    (hB_terminal_neighbor_ncard :
      forall i : Fin 3,
        (Z.B.coe.neighborSet (⟨feet i, Z.feet_mem_B i⟩ : Z.B.verts)).ncard = 1) :
    Exists fun root : Z.treeSubgraph.verts =>
      3 <= Z.treeSubgraph.coe.degree root ∧
        forall z : Z.treeSubgraph.verts,
          3 <= Z.treeSubgraph.coe.degree z -> z = root := by
  exact Z.exists_unique_branch_of_terminal_degrees hfeet_injective
    (Z.terminal_degrees_one_of_B_neighbor_ncard_one hfeet_injective
      hB_terminal_neighbor_ncard)

theorem RST31EssentialBoundarySteinerTree.exists_unique_branch_of_connector_neighbor_ncard_one
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
    Exists fun root : Z.treeSubgraph.verts =>
      3 <= Z.treeSubgraph.coe.degree root ∧
        forall z : Z.treeSubgraph.verts,
          3 <= Z.treeSubgraph.coe.degree z -> z = root := by
  exact Z.exists_unique_branch_of_B_neighbor_ncard_one hfeet_injective
    (Z.B_terminal_neighbor_ncard_one_of_connector_neighbor_ncard_one
      hfeet_injective hY_terminal_neighbor_ncard)

theorem RST31EssentialBoundarySteinerTree.unreachable_treeInG_of_terminal_degrees
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
    [DecidableEq Z.treeSubgraph.verts]
    [DecidableRel Z.treeSubgraph.coe.Adj]
    [DecidableEq Z.treeInG.verts]
    [DecidableRel Z.treeInG.coe.Adj]
    (hfeet_injective : Function.Injective feet)
    {root : Z.treeSubgraph.verts}
    (hroot_degree : 3 <= Z.treeSubgraph.coe.degree root)
    (hroot_unique :
      forall z : Z.treeSubgraph.verts,
        3 <= Z.treeSubgraph.coe.degree z -> z = root)
    (hterminal_degree :
      forall i : Fin 3, Z.treeSubgraph.coe.degree (Z.terminalTree i) = 1) :
    forall {i j : Fin 3}, i ≠ j ->
      ¬ (Z.treeInG.coe.induce
          ({Z.treeVertexInG root} : Set Z.treeInG.verts)ᶜ).Reachable
          ⟨(⟨feet i, Z.feet_mem_treeInG i⟩ : Z.treeInG.verts), by
            intro h
            have heq :
                (⟨feet i, Z.feet_mem_treeInG i⟩ : Z.treeInG.verts) =
                  Z.treeVertexInG root := by
              simpa using h
            have hval : ((Z.treeVertexInG root : Z.treeInG.verts) : V) = feet i := by
              exact (congrArg (fun x : Z.treeInG.verts => (x : V)) heq).symm
            exact (Z.treeVertexInG_not_foot_of_degree_ge_three
              hroot_degree hterminal_degree i) hval⟩
          ⟨(⟨feet j, Z.feet_mem_treeInG j⟩ : Z.treeInG.verts), by
            intro h
            have heq :
                (⟨feet j, Z.feet_mem_treeInG j⟩ : Z.treeInG.verts) =
                  Z.treeVertexInG root := by
              simpa using h
            have hval : ((Z.treeVertexInG root : Z.treeInG.verts) : V) = feet j := by
              exact (congrArg (fun x : Z.treeInG.verts => (x : V)) heq).symm
            exact (Z.treeVertexInG_not_foot_of_degree_ge_three
              hroot_degree hterminal_degree j) hval⟩ := by
  classical
  let e := Schematic.Math.GraphTheory.Subgraph.coeSubgraphCoeIso Z.treeSubgraph
  have hterminal_ne_root :
      forall i : Fin 3, Z.terminalTree i ≠ root := by
    intro i hi
    have hval : ((Z.treeVertexInG root : Z.treeInG.verts) : V) = feet i := by
      rw [← hi]
      simp [RST31EssentialBoundarySteinerTree.terminalTree]
    exact (Z.treeVertexInG_not_foot_of_degree_ge_three
      hroot_degree hterminal_degree i) hval
  have hunreachable_tree :
      forall {i j : Fin 3}, i ≠ j ->
        ¬ (Z.treeSubgraph.coe.induce ({root} : Set Z.treeSubgraph.verts)ᶜ).Reachable
            ⟨Z.terminalTree i, by exact hterminal_ne_root i⟩
            ⟨Z.terminalTree j, by exact hterminal_ne_root j⟩ :=
    Schematic.Math.GraphTheory.IsTree.not_reachable_delete_singleton_of_unique_degree_ge_three_terminals
      (G := Z.treeSubgraph.coe) Z.tree
      (Z.terminalTree_injective hfeet_injective) hterminal_degree
      hroot_unique hterminal_ne_root
  intro i j hij hreach
  let eDel := Iso.induceComplSingleton e root
  have hreach_image :
      (Z.treeInG.coe.induce ({Z.treeVertexInG root} : Set Z.treeInG.verts)ᶜ).Reachable
        (eDel ⟨Z.terminalTree i, by exact hterminal_ne_root i⟩)
        (eDel ⟨Z.terminalTree j, by exact hterminal_ne_root j⟩) := by
    simpa [eDel, e, RST31EssentialBoundarySteinerTree.treeVertexInG] using hreach
  have hreach_tree :
      (Z.treeSubgraph.coe.induce ({root} : Set Z.treeSubgraph.verts)ᶜ).Reachable
        ⟨Z.terminalTree i, by exact hterminal_ne_root i⟩
        ⟨Z.terminalTree j, by exact hterminal_ne_root j⟩ := by
    exact (SimpleGraph.Iso.reachable_iff (φ := eDel)).mp hreach_image
  exact hunreachable_tree hij hreach_tree

end Schematic.Math.GraphTheory
