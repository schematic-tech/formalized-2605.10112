import DominatingFourColour.Prerequisites.RSTFlaps.EssentialWithin

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

structure RST31EssentialBoundaryAttachment
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    (C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent)
    where
  boundaryVertex : Fin 3 -> V
  componentVertex : Fin 3 -> V
  path : forall i : Fin 3, G.Walk (feet i) (boundaryVertex i)
  boundary_mem :
    forall i : Fin 3,
      boundaryVertex i ∈ relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v}
  component_mem :
    forall i : Fin 3, componentVertex i ∈ induceComponentSupport (G := G) C
  component_subset :
    forall i : Fin 3, componentVertex i ∈ T.vertexSet ∪ T.flapVertexSet D
  component_verts_subset :
    induceComponentSupport (G := G) C ⊆ T.vertexSet ∪ T.flapVertexSet D
  adj :
    forall i : Fin 3, G.Adj (componentVertex i) (boundaryVertex i)
  path_isPath : forall i : Fin 3, (path i).IsPath
  path_le_carrier : forall i : Fin 3, (path i).toSubgraph ≤ T.carrier
  path_first_boundary :
    forall i : Fin 3, forall z : V, z ∈ (path i).support ->
      z ∈ relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ->
        z = boundaryVertex i

theorem RST31EssentialBoundaryAttachment.componentVertex_not_foot
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C)
    (i j : Fin 3) :
    A.componentVertex i ≠ feet j := by
  intro h
  exact T.foot_not_mem_essential_component_support D C j (by
    simpa [h] using A.component_mem i)

theorem RST31EssentialBoundaryAttachment.foot_not_mem_component_subgraph
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (_A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C)
    (i : Fin 3) :
    feet i ∉ (induceComponentSubgraph (G := G) C).verts := by
  intro h
  exact T.foot_not_mem_essential_component_support D C i (by
    simpa [induceComponentSubgraph] using h)

theorem Triad.exists_essential_boundary_attachment
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (hD_subset_C : T.flapVertexSet D ⊆ induceComponentSupport (G := G) C)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    (hboundary_nonempty :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v}).Nonempty) :
    Nonempty (RST31EssentialBoundaryAttachment (G := G) (D := D) T C) := by
  classical
  let R : Set V :=
    relativeVertexBoundary G (induceComponentSupport (G := G) C)
      {v : V | T.EssentialWithin (T.flapVertexSet D) v}
  have hR_nonempty : R.Nonempty := by
    simpa [R] using hboundary_nonempty
  have hR_subset : R ⊆ T.vertexSet := by
    intro v hv
    exact T.essential_component_boundary_subset_vertexSet D C (by
      simpa [R] using hv)
  have hpaths :
      forall i : Fin 3,
        Exists fun x : V =>
          Exists fun _hxR : x ∈ R =>
            Exists fun p : G.Walk (feet i) x =>
              p.IsPath ∧ p.toSubgraph ≤ T.carrier ∧
                forall z : V, z ∈ p.support -> z ∈ R -> z = x := by
    intro i
    exact T.exists_carrier_path_to_first_mem hR_nonempty hR_subset i
  choose x hxR p hp using hpaths
  have hneighbors :
      forall i : Fin 3,
        Exists fun y : V =>
          y ∈ induceComponentSupport (G := G) C ∧
            y ∈ T.vertexSet ∪ T.flapVertexSet D ∧ G.Adj y (x i) := by
    intro i
    exact T.exists_component_neighbor_in_vertexSet_union_flap_of_essential_boundary
      hD_subset_C hboundary_essential (by simpa [R] using hxR i)
  choose y hy using hneighbors
  refine ⟨{
    boundaryVertex := x
    componentVertex := y
    path := p
    boundary_mem := ?_
    component_mem := ?_
    component_subset := ?_
    component_verts_subset := ?_
    adj := ?_
    path_isPath := ?_
    path_le_carrier := ?_
    path_first_boundary := ?_
  }⟩
  · intro i
    simpa [R] using hxR i
  · intro i
    exact (hy i).1
  · intro i
    exact (hy i).2.1
  · exact T.essential_component_subset_vertexSet_union_flap_of_boundaries_essential
      hD_subset_C hboundary_essential
  · intro i
    exact (hy i).2.2
  · intro i
    exact (hp i).1
  · intro i
    exact (hp i).2.1
  · intro i z hz hzR
    exact (hp i).2.2 z hz (by simpa [R] using hzR)

theorem ncard_le_three_of_subset_fin3_range
    {f : Fin 3 -> V}
    {S : Set V}
    (hS : S ⊆ Set.range f) :
    S.ncard <= 3 := by
  have hcard : S.ncard <= (Set.range f).ncard :=
    Set.ncard_le_ncard hS
  have hrange : (Set.range f).ncard <= 3 := by
    have hle :
        (f '' (Set.univ : Set (Fin 3))).ncard <=
          (Set.univ : Set (Fin 3)).ncard :=
      Set.ncard_image_le (f := f) (s := (Set.univ : Set (Fin 3)))
    simpa [Set.image_univ] using hle
  exact le_trans hcard hrange

def RST31EssentialBoundaryAttachment.branchSubgraph
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C)
    (i : Fin 3) :
    G.Subgraph :=
  (A.path i).toSubgraph ⊔ (A.adj i).toWalk.toSubgraph

theorem RST31EssentialBoundaryAttachment.branch_connected
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C)
    (i : Fin 3) :
    (A.branchSubgraph i).Connected := by
  have hinter :
      ((A.path i).toSubgraph ⊓ (A.adj i).toWalk.toSubgraph).verts.Nonempty := by
    refine ⟨A.boundaryVertex i, ?_⟩
    simp
  exact SimpleGraph.Subgraph.connected_sup
    (A.path i).toSubgraph_connected.preconnected
    (A.adj i).toWalk.toSubgraph_connected.preconnected
    hinter

theorem RST31EssentialBoundaryAttachment.branch_neighborSet_foot_ncard
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C)
    (i : Fin 3) :
    ((A.branchSubgraph i).neighborSet (feet i)).ncard = 1 := by
  classical
  by_cases hnil : (A.path i).Nil
  · have hb : A.boundaryVertex i = feet i :=
      (SimpleGraph.Walk.Nil.eq hnil).symm
    have hpath_eq :
        (A.path i).toSubgraph.neighborSet (feet i) = ∅ :=
      Walk.Nil.toSubgraph_neighborSet_eq_empty hnil
    have hedge_eq :
        (A.adj i).toWalk.toSubgraph.neighborSet (feet i) =
          {A.componentVertex i} := by
      simp [hb]
    rw [RST31EssentialBoundaryAttachment.branchSubgraph,
      Subgraph.neighborSet_sup_eq_union, hpath_eq, hedge_eq]
    simp
  · have hneq : feet i ≠ A.boundaryVertex i :=
      Walk.IsPath.start_ne_end_of_not_nil (A.path_isPath i) hnil
    have hpath_neighbor :
        (A.path i).toSubgraph.neighborSet (feet i) = {(A.path i).snd} :=
      (A.path_isPath i).neighborSet_toSubgraph_startpoint hnil
    have hfoot_not_edge_verts :
        feet i ∉ (A.adj i).toWalk.toSubgraph.verts := by
      intro hv
      simp [SimpleGraph.Walk.toSubgraph] at hv
      rcases hv with hcomp | hbound
      · exact A.componentVertex_not_foot i i hcomp.symm
      · exact hneq hbound
    have hedge_empty :
        (A.adj i).toWalk.toSubgraph.neighborSet (feet i) = ∅ :=
      Subgraph.neighborSet_eq_empty_of_not_mem_verts _ hfoot_not_edge_verts
    rw [RST31EssentialBoundaryAttachment.branchSubgraph,
      Subgraph.neighborSet_sup_eq_union, hpath_neighbor, hedge_empty]
    simp

theorem Triad.exists_essential_boundary_attachment_to_nonfoot_boundary
    [DecidableEq V]
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
    Exists fun A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C =>
      forall i j : Fin 3, j ≠ i -> feet i ∉ (A.branchSubgraph j).verts := by
  classical
  let R : Set V :=
    relativeVertexBoundary G (induceComponentSupport (G := G) C)
      {v : V | T.EssentialWithin (T.flapVertexSet D) v}
  have hR_subset : R ⊆ T.vertexSet := by
    intro v hv
    exact T.essential_component_boundary_subset_vertexSet D C (by
      simpa [R] using hv)
  have hxR : x ∈ R := by
    simpa [R] using hx_boundary
  have hpaths :
      forall i : Fin 3,
        Exists fun z : V =>
          Exists fun _hzR : z ∈ R =>
            Exists fun p : G.Walk (feet i) z =>
              p.IsPath ∧ p.toSubgraph ≤ T.carrier ∧
                (forall w : V, w ∈ p.support -> w ∈ R -> w = z) ∧
                  forall j : Fin 3, j ≠ i -> feet j ∉ p.support := by
    intro i
    exact T.exists_carrier_path_to_first_mem_of_nonfoot_target
      hfeet_injective hR_subset hxR hx_not_feet i
  choose z hzR p hp using hpaths
  have hneighbors :
      forall i : Fin 3,
        Exists fun y : V =>
          y ∈ induceComponentSupport (G := G) C ∧
            y ∈ T.vertexSet ∪ T.flapVertexSet D ∧ G.Adj y (z i) := by
    intro i
    exact T.exists_component_neighbor_in_vertexSet_union_flap_of_essential_boundary
      hD_subset_C hboundary_essential (by simpa [R] using hzR i)
  choose y hy using hneighbors
  let A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C := {
    boundaryVertex := z
    componentVertex := y
    path := p
    boundary_mem := by
      intro i
      simpa [R] using hzR i
    component_mem := by
      intro i
      exact (hy i).1
    component_subset := by
      intro i
      exact (hy i).2.1
    component_verts_subset :=
      T.essential_component_subset_vertexSet_union_flap_of_boundaries_essential
        hD_subset_C hboundary_essential
    adj := by
      intro i
      exact (hy i).2.2
    path_isPath := by
      intro i
      exact (hp i).1
    path_le_carrier := by
      intro i
      exact (hp i).2.1
    path_first_boundary := by
      intro i w hw hwR
      exact (hp i).2.2.1 w hw (by simpa [R] using hwR)
  }
  refine ⟨A, ?_⟩
  intro i j hji hmem
  have hcases :
      feet i = A.componentVertex j ∨ feet i ∈ (A.path j).support := by
    simpa [A, RST31EssentialBoundaryAttachment.branchSubgraph,
      SimpleGraph.Subgraph.verts_sup] using hmem
  rcases hcases with hcomp | hpath
  · exact A.componentVertex_not_foot j i hcomp.symm
  · exact (hp j).2.2.2 i (fun hij => hji hij.symm) hpath

def RST31EssentialBoundaryAttachment.connectorSubgraph
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C) :
    G.Subgraph :=
  (((induceComponentSubgraph (G := G) C ⊔ A.branchSubgraph 0) ⊔
      A.branchSubgraph 1) ⊔ A.branchSubgraph 2)

theorem RST31EssentialBoundaryAttachment.connector_connected
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C) :
    A.connectorSubgraph.Connected := by
  let H0 : G.Subgraph := induceComponentSubgraph (G := G) C
  let H1 : G.Subgraph := H0 ⊔ A.branchSubgraph 0
  let H2 : G.Subgraph := H1 ⊔ A.branchSubgraph 1
  have h0 : H0.Connected := by
    simpa [H0] using induceComponentSubgraph_connected (G := G) C
  have hinter1 : (H0 ⊓ A.branchSubgraph 0).verts.Nonempty := by
    refine ⟨A.componentVertex 0, ?_⟩
    simp [H0, RST31EssentialBoundaryAttachment.branchSubgraph, A.component_mem]
  have h1 : H1.Connected := by
    simpa [H1] using
      SimpleGraph.Subgraph.connected_sup h0.preconnected
        (A.branch_connected 0).preconnected hinter1
  have hinter2 : (H1 ⊓ A.branchSubgraph 1).verts.Nonempty := by
    refine ⟨A.componentVertex 1, ?_⟩
    simp [H1, H0, RST31EssentialBoundaryAttachment.branchSubgraph, A.component_mem]
  have h2 : H2.Connected := by
    simpa [H2] using
      SimpleGraph.Subgraph.connected_sup h1.preconnected
        (A.branch_connected 1).preconnected hinter2
  have hinter3 : (H2 ⊓ A.branchSubgraph 2).verts.Nonempty := by
    refine ⟨A.componentVertex 2, ?_⟩
    simp [H2, H1, H0, RST31EssentialBoundaryAttachment.branchSubgraph, A.component_mem]
  simpa [RST31EssentialBoundaryAttachment.connectorSubgraph, H2, H1, H0] using
    SimpleGraph.Subgraph.connected_sup h2.preconnected
      (A.branch_connected 2).preconnected hinter3

theorem RST31EssentialBoundaryAttachment.feet_mem_connector
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C)
    (i : Fin 3) :
    feet i ∈ A.connectorSubgraph.verts := by
  fin_cases i <;>
    simp [RST31EssentialBoundaryAttachment.connectorSubgraph,
      RST31EssentialBoundaryAttachment.branchSubgraph]

theorem RST31EssentialBoundaryAttachment.connector_neighborSet_foot_ncard_of_other_branches_avoid
    [Fintype V]
    [DecidableRel G.Adj]
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C)
    (i : Fin 3)
    (hother :
      forall j : Fin 3, j ≠ i -> feet i ∉ (A.branchSubgraph j).verts) :
    (A.connectorSubgraph.neighborSet (feet i)).ncard = 1 := by
  classical
  have hC_empty :
      (induceComponentSubgraph (G := G) C).neighborSet (feet i) = ∅ :=
    Subgraph.neighborSet_eq_empty_of_not_mem_verts _
      (A.foot_not_mem_component_subgraph i)
  fin_cases i
  · have h1_empty :
        (A.branchSubgraph 1).neighborSet (feet 0) = ∅ :=
      Subgraph.neighborSet_eq_empty_of_not_mem_verts _
        (hother 1 (by decide))
    have h2_empty :
        (A.branchSubgraph 2).neighborSet (feet 0) = ∅ :=
      Subgraph.neighborSet_eq_empty_of_not_mem_verts _
        (hother 2 (by decide))
    rw [RST31EssentialBoundaryAttachment.connectorSubgraph]
    rw [Subgraph.neighborSet_sup_eq_union]
    rw [Subgraph.neighborSet_sup_eq_union]
    rw [Subgraph.neighborSet_sup_eq_union]
    rw [hC_empty]
    rw [show (A.branchSubgraph 1).neighborSet
        (feet ((fun i => i) ⟨0, by omega⟩)) = ∅ by
      simpa using h1_empty]
    rw [show (A.branchSubgraph 2).neighborSet
        (feet ((fun i => i) ⟨0, by omega⟩)) = ∅ by
      simpa using h2_empty]
    simpa [Set.union_assoc] using A.branch_neighborSet_foot_ncard 0
  · have h0_empty :
        (A.branchSubgraph 0).neighborSet (feet 1) = ∅ :=
      Subgraph.neighborSet_eq_empty_of_not_mem_verts _
        (hother 0 (by decide))
    have h2_empty :
        (A.branchSubgraph 2).neighborSet (feet 1) = ∅ :=
      Subgraph.neighborSet_eq_empty_of_not_mem_verts _
        (hother 2 (by decide))
    rw [RST31EssentialBoundaryAttachment.connectorSubgraph]
    rw [Subgraph.neighborSet_sup_eq_union]
    rw [Subgraph.neighborSet_sup_eq_union]
    rw [Subgraph.neighborSet_sup_eq_union]
    rw [hC_empty]
    rw [show (A.branchSubgraph 0).neighborSet
        (feet ((fun i => i) ⟨1, by omega⟩)) = ∅ by
      simpa using h0_empty]
    rw [show (A.branchSubgraph 2).neighborSet
        (feet ((fun i => i) ⟨1, by omega⟩)) = ∅ by
      simpa using h2_empty]
    simpa [Set.union_assoc] using A.branch_neighborSet_foot_ncard 1
  · have h0_empty :
        (A.branchSubgraph 0).neighborSet (feet 2) = ∅ :=
      Subgraph.neighborSet_eq_empty_of_not_mem_verts _
        (hother 0 (by decide))
    have h1_empty :
        (A.branchSubgraph 1).neighborSet (feet 2) = ∅ :=
      Subgraph.neighborSet_eq_empty_of_not_mem_verts _
        (hother 1 (by decide))
    rw [RST31EssentialBoundaryAttachment.connectorSubgraph]
    rw [Subgraph.neighborSet_sup_eq_union]
    rw [Subgraph.neighborSet_sup_eq_union]
    rw [Subgraph.neighborSet_sup_eq_union]
    rw [hC_empty]
    rw [show (A.branchSubgraph 0).neighborSet
        (feet ((fun i => i) ⟨2, by omega⟩)) = ∅ by
      simpa using h0_empty]
    rw [show (A.branchSubgraph 1).neighborSet
        (feet ((fun i => i) ⟨2, by omega⟩)) = ∅ by
      simpa using h1_empty]
    simpa [Set.union_assoc] using A.branch_neighborSet_foot_ncard 2

theorem RST31EssentialBoundaryAttachment.connector_verts_subset
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C) :
    A.connectorSubgraph.verts ⊆ T.vertexSet ∪ T.flapVertexSet D := by
  intro v hv
  have hv_cases :
      v ∈ (induceComponentSubgraph (G := G) C).verts ∨
        v ∈ (A.branchSubgraph 0).verts ∨
          v ∈ (A.branchSubgraph 1).verts ∨
            v ∈ (A.branchSubgraph 2).verts := by
    simpa [RST31EssentialBoundaryAttachment.connectorSubgraph,
      SimpleGraph.Subgraph.verts_sup, Set.union_assoc] using hv
  rcases hv_cases with hvC | hv_cases
  · exact A.component_verts_subset (by
      simpa using hvC)
  rcases hv_cases with hv0 | hv_cases
  · have hv0_cases :
        v = A.componentVertex 0 ∨ v ∈ (A.path 0).support := by
        simpa [RST31EssentialBoundaryAttachment.branchSubgraph,
          SimpleGraph.Subgraph.verts_sup] using hv0
    rcases hv0_cases with rfl | hvp
    · exact A.component_subset 0
    · exact Or.inl (by
        rw [T.vertexSet_eq_carrier_verts]
        exact (A.path_le_carrier 0).left (by
          rw [SimpleGraph.Walk.mem_verts_toSubgraph]
          exact hvp))
  rcases hv_cases with hv1 | hv2
  · have hv1_cases :
        v = A.componentVertex 1 ∨ v ∈ (A.path 1).support := by
        simpa [RST31EssentialBoundaryAttachment.branchSubgraph,
          SimpleGraph.Subgraph.verts_sup] using hv1
    rcases hv1_cases with rfl | hvp
    · exact A.component_subset 1
    · exact Or.inl (by
        rw [T.vertexSet_eq_carrier_verts]
        exact (A.path_le_carrier 1).left (by
          rw [SimpleGraph.Walk.mem_verts_toSubgraph]
          exact hvp))
  · have hv2_cases :
        v = A.componentVertex 2 ∨ v ∈ (A.path 2).support := by
        simpa [RST31EssentialBoundaryAttachment.branchSubgraph,
          SimpleGraph.Subgraph.verts_sup] using hv2
    rcases hv2_cases with rfl | hvp
    · exact A.component_subset 2
    · exact Or.inl (by
        rw [T.vertexSet_eq_carrier_verts]
        exact (A.path_le_carrier 2).left (by
          rw [SimpleGraph.Walk.mem_verts_toSubgraph]
          exact hvp))

theorem RST31EssentialBoundaryAttachment.boundary_inter_connector_subset_range
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C) :
    relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
      A.connectorSubgraph.verts ⊆ Set.range A.boundaryVertex := by
  intro v hv
  have hv_boundary := hv.1
  have hv_cases :
      v ∈ (induceComponentSubgraph (G := G) C).verts ∨
        v ∈ (A.branchSubgraph 0).verts ∨
          v ∈ (A.branchSubgraph 1).verts ∨
            v ∈ (A.branchSubgraph 2).verts := by
    simpa [RST31EssentialBoundaryAttachment.connectorSubgraph,
      SimpleGraph.Subgraph.verts_sup, Set.union_assoc] using hv.2
  rcases hv_cases with hvC | hv_cases
  · have hvK : v ∈ induceComponentSupport (G := G) C := by simpa using hvC
    have hv_not_essential :
        v ∈ ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ : Set V) :=
      induceComponentSupport_subset (G := G) C hvK
    exact False.elim (hv_not_essential hv_boundary.1)
  rcases hv_cases with hv0 | hv_cases
  · have hv0_cases :
        v = A.componentVertex 0 ∨ v ∈ (A.path 0).support := by
        simpa [RST31EssentialBoundaryAttachment.branchSubgraph,
          SimpleGraph.Subgraph.verts_sup] using hv0
    rcases hv0_cases with rfl | hsupport
    · have hv_not_essential :
          A.componentVertex 0 ∈
            ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ : Set V) :=
        induceComponentSupport_subset (G := G) C (A.component_mem 0)
      exact False.elim (hv_not_essential hv_boundary.1)
    · refine ⟨0, ?_⟩
      exact (A.path_first_boundary 0 v hsupport hv_boundary).symm
  rcases hv_cases with hv1 | hv2
  · have hv1_cases :
        v = A.componentVertex 1 ∨ v ∈ (A.path 1).support := by
        simpa [RST31EssentialBoundaryAttachment.branchSubgraph,
          SimpleGraph.Subgraph.verts_sup] using hv1
    rcases hv1_cases with rfl | hsupport
    · have hv_not_essential :
          A.componentVertex 1 ∈
            ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ : Set V) :=
        induceComponentSupport_subset (G := G) C (A.component_mem 1)
      exact False.elim (hv_not_essential hv_boundary.1)
    · refine ⟨1, ?_⟩
      exact (A.path_first_boundary 1 v hsupport hv_boundary).symm
  · have hv2_cases :
        v = A.componentVertex 2 ∨ v ∈ (A.path 2).support := by
        simpa [RST31EssentialBoundaryAttachment.branchSubgraph,
          SimpleGraph.Subgraph.verts_sup] using hv2
    rcases hv2_cases with rfl | hsupport
    · have hv_not_essential :
          A.componentVertex 2 ∈
            ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ : Set V) :=
        induceComponentSupport_subset (G := G) C (A.component_mem 2)
      exact False.elim (hv_not_essential hv_boundary.1)
    · refine ⟨2, ?_⟩
      exact (A.path_first_boundary 2 v hsupport hv_boundary).symm

theorem RST31EssentialBoundaryAttachment.boundary_inter_connector_ncard_le
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C) :
    (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩
      A.connectorSubgraph.verts).ncard <= 3 :=
  ncard_le_three_of_subset_fin3_range
    A.boundary_inter_connector_subset_range

structure RST31EssentialBoundaryConnector
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    (C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent)
    where
  H : G.Subgraph
  connected : H.Connected
  feet_mem : forall i : Fin 3, feet i ∈ H.verts
  verts_subset : H.verts ⊆ T.vertexSet ∪ T.flapVertexSet D
  boundary_inter_ncard_le :
    (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v} ∩ H.verts).ncard <= 3

def RST31EssentialBoundaryAttachment.toConnector
    {feet : Fin 3 -> V}
    {T : Triad G feet}
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (A : RST31EssentialBoundaryAttachment (G := G) (D := D) T C) :
    RST31EssentialBoundaryConnector (G := G) (D := D) T C where
  H := A.connectorSubgraph
  connected := A.connector_connected
  feet_mem := A.feet_mem_connector
  verts_subset := A.connector_verts_subset
  boundary_inter_ncard_le := A.boundary_inter_connector_ncard_le

theorem Triad.exists_essential_boundary_connector
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {D : T.Flap}
    {C :
      (G.induce ({v : V | T.EssentialWithin (T.flapVertexSet D) v}ᶜ)).ConnectedComponent}
    (hD_subset_C : T.flapVertexSet D ⊆ induceComponentSupport (G := G) C)
    (hboundary_essential :
      forall E : T.Flap, E ≠ D ->
        relativeVertexBoundary G (T.flapVertexSet E) T.vertexSet ⊆
          {v : V | T.EssentialWithin (T.flapVertexSet D) v})
    (hboundary_nonempty :
      (relativeVertexBoundary G (induceComponentSupport (G := G) C)
        {v : V | T.EssentialWithin (T.flapVertexSet D) v}).Nonempty) :
    Nonempty (RST31EssentialBoundaryConnector (G := G) (D := D) T C) := by
  obtain ⟨A⟩ :=
    T.exists_essential_boundary_attachment
      hD_subset_C hboundary_essential hboundary_nonempty
  exact ⟨A.toConnector⟩

end Schematic.Math.GraphTheory
