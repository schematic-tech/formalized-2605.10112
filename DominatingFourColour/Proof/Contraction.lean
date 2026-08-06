import DominatingFourColour.Basic
import Schematic.Math.GraphTheory.Contractions

/-!
Formalization of Lemma `contraction` in the paper.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u
universe w

variable {V : Type u} {G : SimpleGraph V}

def MinorModel.ofContraction
    {W : Type w} {H : SimpleGraph W}
    (C : GraphContraction G)
    (M : MinorModel H C.graph) :
    MinorModel H G where
  branch x := C.PreimageSubgraph (M.branch x)
  connected x := GraphContraction.preimageSubgraph_connected (C := C) (M.connected x)
  nonempty x := by
    obtain ⟨y, hy⟩ := M.nonempty x
    obtain ⟨v, hv⟩ := C.surjective y
    exact ⟨v, by
      rw [GraphContraction.mem_preimageSubgraph_verts, hv]
      exact hy⟩
  vertex_disjoint := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro v hvx hvy
    have hmx : C.map v ∈ (M.branch x).verts := by
      simpa [GraphContraction.mem_preimageSubgraph_verts] using hvx
    have hmy : C.map v ∈ (M.branch y).verts := by
      simpa [GraphContraction.mem_preimageSubgraph_verts] using hvy
    exact (Set.disjoint_left.mp (M.vertex_disjoint x y hxy) hmx) hmy
  edge_realized := by
    intro x y hxy
    obtain ⟨a, b, ha, hb, hab⟩ := M.edge_realized hxy
    obtain ⟨v, w, hv, hw, hvw⟩ := C.edge_lift hab
    exact ⟨v, w, by
      rw [GraphContraction.mem_preimageSubgraph_verts, hv]
      exact ha, by
      rw [GraphContraction.mem_preimageSubgraph_verts, hw]
      exact hb, hvw⟩

theorem containsMinor_lift_of_contraction
    {W : Type w} {H : SimpleGraph W}
    (C : GraphContraction G)
    (h : ContainsMinor H C.graph) :
    ContainsMinor H G := by
  rcases h with ⟨M⟩
  exact ⟨M.ofContraction C⟩

theorem compatible_quotient_contains_K5_minor_lift
    (C : GraphContraction G)
    {Lq : OrderedClique C.graph}
    (h : CompatibleDominatingK5Model Lq) :
    ContainsMinor K5Graph G := by
  rcases h with ⟨T, _hT⟩
  exact containsMinor_lift_of_contraction C T.contains_completeGraph_minor

private theorem DominatingModel.branchIndex_eq_map_of_branch_verts
    {t : Nat}
    (C : GraphContraction G)
    (T : DominatingModel G t)
    (Tq : DominatingModel C.graph t)
    (hbranch : forall i v,
      v ∈ (T.branch i).verts ↔ C.map v ∈ (Tq.branch i).verts)
    (v : V) :
    T.branchIndex v = Tq.branchIndex (C.map v) := by
  classical
  by_cases hmem : Exists fun i : Fin t => C.map v ∈ (Tq.branch i).verts
  · let i : Fin t := hmem.choose
    have hiq : C.map v ∈ (Tq.branch i).verts := hmem.choose_spec
    rw [T.branchIndex_eq_add_one_of_mem ((hbranch i v).2 hiq),
      Tq.branchIndex_eq_add_one_of_mem hiq]
  · rw [T.branchIndex_eq_zero_of_forall_not_mem (fun i hi =>
        hmem ⟨i, (hbranch i v).1 hi⟩),
      Tq.branchIndex_eq_zero_of_forall_not_mem (fun i hi => hmem ⟨i, hi⟩)]

private def DominatingModel.ofContractionWithDominates
    {t : Nat}
    (C : GraphContraction G)
    (Tq : DominatingModel C.graph t)
    (hdominates :
      forall i j : Fin t,
        i < j ->
          forall v : V,
            v ∈ (C.PreimageSubgraph (Tq.branch j)).verts ->
              Exists fun u : V =>
                u ∈ (C.PreimageSubgraph (Tq.branch i)).verts ∧ G.Adj u v) :
    DominatingModel G t where
  branch i := C.PreimageSubgraph (Tq.branch i)
  connected i :=
    GraphContraction.preimageSubgraph_connected (C := C) (Tq.connected i)
  vertex_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro v hvi hvj
    have hqi : C.map v ∈ (Tq.branch i).verts := by
      simpa [GraphContraction.mem_preimageSubgraph_verts] using hvi
    have hqj : C.map v ∈ (Tq.branch j).verts := by
      simpa [GraphContraction.mem_preimageSubgraph_verts] using hvj
    exact Set.disjoint_left.mp (Tq.vertex_disjoint i j hij) hqi hqj
  dominates := hdominates

def DominatingModel.ofContractionAvoidingLateFiber
    {t : Nat}
    (C : GraphContraction G)
    (Tq : DominatingModel C.graph t)
    (H : G.Subgraph)
    (y : C.Target)
    (hC : C.OnlyContractsSubgraphTo H y)
    (hy_late : forall j : Fin t, 0 < (j : Nat) -> y ∉ (Tq.branch j).verts) :
    DominatingModel G t :=
  DominatingModel.ofContractionWithDominates C Tq (by
    intro i j hij v hv
    have hz : C.map v ∈ (Tq.branch j).verts := by
      simpa [GraphContraction.mem_preimageSubgraph_verts] using hv
    have hj_pos : 0 < (j : Nat) := lt_of_le_of_lt (Nat.zero_le _) hij
    have hv_ne_y : C.map v ≠ y := by
      intro hvy
      exact hy_late j hj_pos (by simpa [hvy] using hz)
    obtain ⟨x, hx, hxz⟩ := Tq.dominates i j hij (C.map v) hz
    obtain ⟨a, b, ha, hb, hab⟩ := C.edge_lift hxz
    have hb_eq_v : b = v :=
      GraphContraction.eq_of_onlyContractsSubgraphTo_of_map_eq hC hv_ne_y hb
    exact ⟨a, by
      rw [GraphContraction.mem_preimageSubgraph_verts, ha]
      exact hx, by
      simpa [hb_eq_v] using hab⟩)

theorem DominatingModel.branchIndex_ofContractionAvoidingLateFiber
    {t : Nat}
    (C : GraphContraction G)
    (Tq : DominatingModel C.graph t)
    (H : G.Subgraph)
    (y : C.Target)
    (hC : C.OnlyContractsSubgraphTo H y)
    (hy_late : forall j : Fin t, 0 < (j : Nat) -> y ∉ (Tq.branch j).verts)
    (v : V) :
    (Tq.ofContractionAvoidingLateFiber C H y hC hy_late).branchIndex v =
      Tq.branchIndex (C.map v) := by
  apply DominatingModel.branchIndex_eq_map_of_branch_verts C _ Tq
  intro i w
  simp [DominatingModel.ofContractionAvoidingLateFiber,
    DominatingModel.ofContractionWithDominates,
    GraphContraction.mem_preimageSubgraph_verts]

def DominatingModel.ofContractionSingletonBranchFibers
    {t : Nat}
    (C : GraphContraction G)
    (Tq : DominatingModel C.graph t)
    (hsingle :
      forall j : Fin t,
        forall y : C.Target,
          y ∈ (Tq.branch j).verts ->
            forall v w : V, C.map v = y -> C.map w = y -> v = w) :
    DominatingModel G t :=
  DominatingModel.ofContractionWithDominates C Tq (by
    intro i j hij v hv
    have hz : C.map v ∈ (Tq.branch j).verts := by
      simpa [GraphContraction.mem_preimageSubgraph_verts] using hv
    obtain ⟨z, hz_branch, hzz⟩ := Tq.dominates i j hij (C.map v) hz
    obtain ⟨a, b, ha, hb, hab⟩ := C.edge_lift hzz
    have hb_eq_v : b = v := hsingle j (C.map v) hz b v hb rfl
    exact ⟨a, by
      rw [GraphContraction.mem_preimageSubgraph_verts, ha]
      exact hz_branch, by
      simpa [hb_eq_v] using hab⟩)

theorem DominatingModel.branchIndex_ofContractionSingletonBranchFibers
    {t : Nat}
    (C : GraphContraction G)
    (Tq : DominatingModel C.graph t)
    (hsingle :
      forall j : Fin t,
        forall y : C.Target,
          y ∈ (Tq.branch j).verts ->
            forall v w : V, C.map v = y -> C.map w = y -> v = w)
    (v : V) :
    (Tq.ofContractionSingletonBranchFibers C hsingle).branchIndex v =
      Tq.branchIndex (C.map v) := by
  apply DominatingModel.branchIndex_eq_map_of_branch_verts C _ Tq
  intro i w
  simp [DominatingModel.ofContractionSingletonBranchFibers,
    DominatingModel.ofContractionWithDominates,
    GraphContraction.mem_preimageSubgraph_verts]

def DominatingK5Model.ofContractionSecondNeighbor
    (C : GraphContraction G)
    (Tq : DominatingK5Model C.graph)
    (H : G.Subgraph)
    (y : C.Target)
    (hC : C.OnlyContractsSubgraphTo H y)
    (hy_late : forall j : Fin 5, 1 < (j : Nat) -> y ∉ (Tq.branch j).verts)
    (x : V)
    (hx0_of_second :
      y ∈ (Tq.branch (1 : Fin 5)).verts ->
        C.map x ∈ (Tq.branch (0 : Fin 5)).verts)
    (hH_neighbor : forall v : V, v ∈ H.verts -> G.Adj x v) :
    DominatingK5Model G :=
  DominatingModel.ofContractionWithDominates C Tq (by
    intro i j hij v hv
    have hz : C.map v ∈ (Tq.branch j).verts := by
      simpa [GraphContraction.mem_preimageSubgraph_verts] using hv
    by_cases hvy : C.map v = y
    · have hvH : v ∈ H.verts := by
        rw [hC.1]
        exact hvy
      have hyj : y ∈ (Tq.branch j).verts := by
        simpa [hvy] using hz
      fin_cases i <;> fin_cases j <;> simp at hij
      · exact ⟨x, by
          rw [GraphContraction.mem_preimageSubgraph_verts]
          exact hx0_of_second hyj, hH_neighbor v hvH⟩
      all_goals
        exact False.elim (hy_late _ (by decide) hyj)
    · obtain ⟨z, hz_branch, hzz⟩ := Tq.dominates i j hij (C.map v) hz
      obtain ⟨a, b, ha, hb, hab⟩ := C.edge_lift hzz
      have hb_eq_v : b = v :=
        GraphContraction.eq_of_onlyContractsSubgraphTo_of_map_eq hC hvy hb
      exact ⟨a, by
        rw [GraphContraction.mem_preimageSubgraph_verts, ha]
        exact hz_branch, by
        simpa [hb_eq_v] using hab⟩)

theorem DominatingK5Model.branchIndex_ofContractionSecondNeighbor
    (C : GraphContraction G)
    (Tq : DominatingK5Model C.graph)
    (H : G.Subgraph)
    (y : C.Target)
    (hC : C.OnlyContractsSubgraphTo H y)
    (hy_late : forall j : Fin 5, 1 < (j : Nat) -> y ∉ (Tq.branch j).verts)
    (x : V)
    (hx0_of_second :
      y ∈ (Tq.branch (1 : Fin 5)).verts ->
        C.map x ∈ (Tq.branch (0 : Fin 5)).verts)
    (hH_neighbor : forall v : V, v ∈ H.verts -> G.Adj x v)
    (v : V) :
    (Tq.ofContractionSecondNeighbor C H y hC hy_late x hx0_of_second hH_neighbor).branchIndex v =
      Tq.branchIndex (C.map v) := by
  apply DominatingModel.branchIndex_eq_map_of_branch_verts C _ Tq
  intro i w
  simp [DominatingK5Model.ofContractionSecondNeighbor,
    DominatingModel.ofContractionWithDominates,
    GraphContraction.mem_preimageSubgraph_verts]

inductive OrderedCliqueContractionImage
    (C : GraphContraction G) :
    OrderedClique G -> OrderedClique C.graph -> Prop where
  | nil : OrderedCliqueContractionImage C .nil .nil
  | single (v : V) :
      OrderedCliqueContractionImage C (.single v) (.single (C.map v))
  | pair_uncollapsed {v1 v2 : V} (edge : G.Adj v1 v2)
      (edgeq : C.graph.Adj (C.map v1) (C.map v2)) :
      OrderedCliqueContractionImage C
        (.pair v1 v2 edge) (.pair (C.map v1) (C.map v2) edgeq)
  | pair_collapsed {v1 v2 : V} (edge : G.Adj v1 v2)
      (hcollapse : C.map v1 = C.map v2) :
      OrderedCliqueContractionImage C (.pair v1 v2 edge) (.single (C.map v1))

theorem LCompatible.of_contraction_image
    {C : GraphContraction G}
    {L : OrderedClique G}
    {Lq : OrderedClique C.graph}
    {T : DominatingK5Model G}
    {Tq : DominatingK5Model C.graph}
    (himage : OrderedCliqueContractionImage C L Lq)
    (hidx : forall v : V, T.branchIndex v = Tq.branchIndex (C.map v)) :
    LCompatible Lq Tq -> LCompatible L T := by
  intro hcompat
  cases himage with
  | nil =>
      exact trivial
  | single v =>
      simpa [LCompatible, hidx v] using hcompat
  | pair_uncollapsed edge edgeq =>
      simp [LCompatible, hidx] at hcompat ⊢
      exact hcompat
  | pair_collapsed edge hcollapse =>
      simp [LCompatible, hidx, hcollapse] at hcompat ⊢
      omega

theorem not_mem_late_branch_of_compatible_first
    {Lq : OrderedClique G}
    {T : DominatingK5Model G}
    {y : V}
    (hfirst : Lq.first? = some y)
    (hcompat : LCompatible Lq T) :
    forall j : Fin 5, 0 < (j : Nat) -> y ∉ (T.branch j).verts := by
  intro j hj hy
  have hidx := T.branchIndex_eq_add_one_of_mem hy
  cases Lq with
  | nil =>
      simp [OrderedClique.first?] at hfirst
  | single v =>
      simp [OrderedClique.first?] at hfirst
      subst v
      simp [LCompatible] at hcompat
      omega
  | pair v1 v2 edge =>
      simp [OrderedClique.first?] at hfirst
      subst v1
      simp [LCompatible] at hcompat
      omega

theorem not_mem_after_second_branch_of_compatible_second
    {Lq : OrderedClique G}
    {T : DominatingK5Model G}
    {y : V}
    (hsecond : Lq.second? = some y)
    (hcompat : LCompatible Lq T) :
    forall j : Fin 5, 1 < (j : Nat) -> y ∉ (T.branch j).verts := by
  intro j hj hy
  have hidx := T.branchIndex_eq_add_one_of_mem hy
  cases Lq with
  | nil =>
      simp [OrderedClique.second?] at hsecond
  | single v =>
      simp [OrderedClique.second?] at hsecond
  | pair v1 v2 edge =>
      simp [OrderedClique.second?] at hsecond
      subst v2
      simp [LCompatible] at hcompat
      omega

theorem deletion_lifts_dominating_model
    (A : Set V) :
    HasDominatingKModel (G.induce A) 5 -> HasDominatingKModel G 5 := by
  rintro ⟨T⟩
  exact ⟨T.ofInduce⟩

theorem deletion_lifts_nil_compatible_model
    (A : Set V)
    (LA : OrderedClique (G.induce A)) :
    CompatibleDominatingK5Model LA -> CompatibleDominatingK5Model (OrderedClique.nil : OrderedClique G) := by
  rintro ⟨T, _hT⟩
  exact ⟨T.ofInduce, trivial⟩

def OrderedCliqueDeletionRestriction
    (A : Set V)
    (L : OrderedClique G)
    (LA : OrderedClique (G.induce A)) : Prop :=
  match L with
  | .nil => LA = .nil
  | .single v =>
      (Exists fun hv : v ∈ A => LA = .single ⟨v, hv⟩) ∨
        (v ∉ A ∧ LA = .nil)
  | .pair v1 v2 edge =>
      (Exists fun hv1 : v1 ∈ A =>
        Exists fun hv2 : v2 ∈ A =>
          LA = .pair ⟨v1, hv1⟩ ⟨v2, hv2⟩ edge) ∨
      (Exists fun hv1 : v1 ∈ A =>
        v2 ∉ A ∧ LA = .single ⟨v1, hv1⟩) ∨
      (v1 ∉ A ∧
        Exists fun hv2 : v2 ∈ A => LA = .single ⟨v2, hv2⟩) ∨
      (v1 ∉ A ∧ v2 ∉ A ∧ LA = .nil)

noncomputable def OrderedClique.restrictToSet
    (A : Set V)
    (L : OrderedClique G) :
    OrderedClique (G.induce A) := by
  classical
  cases L with
  | nil =>
      exact .nil
  | single v =>
      by_cases hv : v ∈ A
      · exact .single ⟨v, hv⟩
      · exact .nil
  | pair v1 v2 edge =>
      by_cases hv1 : v1 ∈ A
      · by_cases hv2 : v2 ∈ A
        · exact .pair ⟨v1, hv1⟩ ⟨v2, hv2⟩ edge
        · exact .single ⟨v1, hv1⟩
      · by_cases hv2 : v2 ∈ A
        · exact .single ⟨v2, hv2⟩
        · exact .nil

theorem OrderedCliqueDeletionRestriction.restrictToSet
    (A : Set V)
    (L : OrderedClique G) :
    OrderedCliqueDeletionRestriction (G := G) A L (L.restrictToSet A) := by
  classical
  cases L with
  | nil =>
      simp [OrderedClique.restrictToSet, OrderedCliqueDeletionRestriction]
  | single v =>
      by_cases hv : v ∈ A
      · exact Or.inl ⟨hv, by simp [OrderedClique.restrictToSet, hv]⟩
      · exact Or.inr ⟨hv, by simp [OrderedClique.restrictToSet, hv]⟩
  | pair v1 v2 edge =>
      by_cases hv1 : v1 ∈ A
      · by_cases hv2 : v2 ∈ A
        · exact Or.inl ⟨hv1, hv2, by simp [OrderedClique.restrictToSet, hv1, hv2]⟩
        · exact Or.inr (Or.inl ⟨hv1, hv2, by
            simp [OrderedClique.restrictToSet, hv1, hv2]⟩)
      · by_cases hv2 : v2 ∈ A
        · exact Or.inr (Or.inr (Or.inl ⟨hv1, hv2, by
            simp [OrderedClique.restrictToSet, hv1, hv2]⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hv1, hv2, by
            simp [OrderedClique.restrictToSet, hv1, hv2]⟩))

theorem contraction_lifts_first_branch
    (L : OrderedClique G)
    (C : GraphContraction G)
    (Lq : OrderedClique C.graph)
    (H1 : G.Subgraph)
    (y : C.Target)
    (hcontracts : C.OnlyContractsSubgraphTo H1 y)
    (himage : OrderedCliqueContractionImage C L Lq)
    (hfirst : Lq.first? = some y) :
    CompatibleDominatingK5Model Lq -> CompatibleDominatingK5Model L := by
  rintro ⟨Tq, hTq⟩
  let hy_late : forall j : Fin 5, 0 < (j : Nat) -> y ∉ (Tq.branch j).verts :=
    not_mem_late_branch_of_compatible_first hfirst hTq
  let T : DominatingK5Model G :=
    Tq.ofContractionAvoidingLateFiber C H1 y hcontracts hy_late
  refine ⟨T, ?_⟩
  exact LCompatible.of_contraction_image himage (by
    intro v
    exact Tq.branchIndex_ofContractionAvoidingLateFiber C H1 y hcontracts hy_late v) hTq

theorem contraction_lifts_first_branch_of_collapse
    (L : OrderedClique G)
    (H1 : G.Subgraph)
    (hH1_connected : H1.coe.Connected)
    (Lq : OrderedClique (GraphContraction.collapseSubgraph G H1 hH1_connected).graph)
    (himage :
      OrderedCliqueContractionImage
        (GraphContraction.collapseSubgraph G H1 hH1_connected) L Lq)
    (hfirst :
      Lq.first? =
        some (none :
          (GraphContraction.collapseSubgraph G H1 hH1_connected).Target)) :
    CompatibleDominatingK5Model Lq -> CompatibleDominatingK5Model L :=
  contraction_lifts_first_branch
    (G := G) L (GraphContraction.collapseSubgraph G H1 hH1_connected) Lq H1 none
    (GraphContraction.collapseSubgraph_onlyContractsSubgraphTo G H1 hH1_connected)
    himage hfirst

theorem exists_collapse_pair_image_no_compatible_model_of_first_mem
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hv1H : v1 ∈ H.verts)
    (hno_model :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge))) :
    let C : GraphContraction G := GraphContraction.collapseSubgraph G H hH_connected
    Exists fun Lq : OrderedClique C.graph =>
      OrderedCliqueContractionImage C (.pair v1 v2 edge) Lq ∧
        Lq.first? = some (none : C.Target) ∧
          Not (CompatibleDominatingK5Model Lq) := by
  classical
  intro C
  have hv1_map : C.map v1 = (none : C.Target) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_none_of_mem
        G H hH_connected hv1H
  by_cases hv2H : v2 ∈ H.verts
  · have hv2_map : C.map v2 = (none : C.Target) := by
      simpa [C] using
        GraphContraction.collapseSubgraph_map_eq_none_of_mem
          G H hH_connected hv2H
    let Lq : OrderedClique C.graph := .single (C.map v1)
    have himage :
        OrderedCliqueContractionImage C (.pair v1 v2 edge) Lq := by
      exact OrderedCliqueContractionImage.pair_collapsed edge
        (by rw [hv1_map, hv2_map])
    have hfirst : Lq.first? = some (none : C.Target) := by
      change some (C.map v1) = some (none : C.Target)
      exact congrArg some hv1_map
    refine ⟨Lq, himage, hfirst, ?_⟩
    intro hmodel
    exact hno_model
      (contraction_lifts_first_branch_of_collapse
        (G := G) (L := .pair v1 v2 edge)
        (H1 := H) hH_connected (Lq := Lq)
        (by simpa [C] using himage)
        (by simpa [C] using hfirst)
        (by simpa [C] using hmodel))
  · have hv2_map :
        C.map v2 =
          some (⟨v2, hv2H⟩ : {v : V // v ∉ H.verts}) := by
      simpa [C] using
        GraphContraction.collapseSubgraph_map_eq_some_of_not_mem
          G H hH_connected hv2H
    have hmap_ne : C.map v1 ≠ C.map v2 := by
      rw [hv1_map, hv2_map]
      simp
    have edgeq : C.graph.Adj (C.map v1) (C.map v2) := by
      rcases C.map_adj edge with hsame | hadj
      · exact False.elim (hmap_ne hsame)
      · exact hadj
    let Lq : OrderedClique C.graph := .pair (C.map v1) (C.map v2) edgeq
    have himage :
        OrderedCliqueContractionImage C (.pair v1 v2 edge) Lq := by
      exact OrderedCliqueContractionImage.pair_uncollapsed edge edgeq
    have hfirst : Lq.first? = some (none : C.Target) := by
      change some (C.map v1) = some (none : C.Target)
      exact congrArg some hv1_map
    refine ⟨Lq, himage, hfirst, ?_⟩
    intro hmodel
    exact hno_model
      (contraction_lifts_first_branch_of_collapse
        (G := G) (L := .pair v1 v2 edge)
        (H1 := H) hH_connected (Lq := Lq)
        (by simpa [C] using himage)
        (by simpa [C] using hfirst)
        (by simpa [C] using hmodel))

theorem contraction_lifts_second_neighborhood_branch
    (L : OrderedClique G)
    (C : GraphContraction G)
    (Lq : OrderedClique C.graph)
    (H2 : G.Subgraph)
    (y : C.Target)
    (x : V)
    (hcontracts : C.OnlyContractsSubgraphTo H2 y)
    (himage : OrderedCliqueContractionImage C L Lq)
    (hsecond : Lq.second? = some y)
    (hx_first_branch_of_second :
      forall Tq : DominatingK5Model C.graph,
        LCompatible Lq Tq ->
          y ∈ (Tq.branch (1 : Fin 5)).verts ->
            C.map x ∈ (Tq.branch (0 : Fin 5)).verts)
    (hH2_in_neighborhood_of_first : forall v : V, v ∈ H2.verts -> G.Adj x v) :
    CompatibleDominatingK5Model Lq -> CompatibleDominatingK5Model L := by
  rintro ⟨Tq, hTq⟩
  let hy_late : forall j : Fin 5, 1 < (j : Nat) -> y ∉ (Tq.branch j).verts :=
    not_mem_after_second_branch_of_compatible_second hsecond hTq
  let hx0_of_second :
      y ∈ (Tq.branch (1 : Fin 5)).verts ->
        C.map x ∈ (Tq.branch (0 : Fin 5)).verts :=
    hx_first_branch_of_second Tq hTq
  let T : DominatingK5Model G :=
    Tq.ofContractionSecondNeighbor C H2 y hcontracts hy_late x hx0_of_second
      hH2_in_neighborhood_of_first
  refine ⟨T, ?_⟩
  exact LCompatible.of_contraction_image himage (by
    intro v
    exact Tq.branchIndex_ofContractionSecondNeighbor C H2 y hcontracts hy_late x hx0_of_second
      hH2_in_neighborhood_of_first v) hTq

theorem contraction_lifts_second_neighborhood_branch_of_collapse
    (L : OrderedClique G)
    (H2 : G.Subgraph)
    (hH2_connected : H2.coe.Connected)
    (Lq : OrderedClique (GraphContraction.collapseSubgraph G H2 hH2_connected).graph)
    (x : V)
    (himage :
      OrderedCliqueContractionImage
        (GraphContraction.collapseSubgraph G H2 hH2_connected) L Lq)
    (hsecond :
      Lq.second? =
        some (none :
          (GraphContraction.collapseSubgraph G H2 hH2_connected).Target))
    (hx_first_branch_of_second :
      forall Tq : DominatingK5Model
          (GraphContraction.collapseSubgraph G H2 hH2_connected).graph,
        LCompatible Lq Tq ->
          (none :
            (GraphContraction.collapseSubgraph G H2 hH2_connected).Target) ∈
              (Tq.branch (1 : Fin 5)).verts ->
          (GraphContraction.collapseSubgraph G H2 hH2_connected).map x ∈
            (Tq.branch (0 : Fin 5)).verts)
    (hH2_in_neighborhood_of_first : forall v : V, v ∈ H2.verts -> G.Adj x v) :
    CompatibleDominatingK5Model Lq -> CompatibleDominatingK5Model L :=
  contraction_lifts_second_neighborhood_branch
    (G := G) L (GraphContraction.collapseSubgraph G H2 hH2_connected) Lq H2 none x
    (GraphContraction.collapseSubgraph_onlyContractsSubgraphTo G H2 hH2_connected)
    himage hsecond hx_first_branch_of_second hH2_in_neighborhood_of_first

theorem contraction_lifts_compatible_of_singleton_branch_fibers
    (L : OrderedClique G)
    (C : GraphContraction G)
    (Lq : OrderedClique C.graph)
    (himage : OrderedCliqueContractionImage C L Lq)
    (hsingle :
      forall Tq : DominatingK5Model C.graph,
        LCompatible Lq Tq ->
          forall j : Fin 5,
            forall y : C.Target,
              y ∈ (Tq.branch j).verts ->
                forall v w : V, C.map v = y -> C.map w = y -> v = w) :
    CompatibleDominatingK5Model Lq -> CompatibleDominatingK5Model L := by
  rintro ⟨Tq, hTq⟩
  let T : DominatingK5Model G :=
    Tq.ofContractionSingletonBranchFibers C (hsingle Tq hTq)
  refine ⟨T, ?_⟩
  exact LCompatible.of_contraction_image himage (by
    intro v
    exact Tq.branchIndex_ofContractionSingletonBranchFibers C
      (hsingle Tq hTq) v) hTq

theorem deletion_lifts_compatible_model
    (L : OrderedClique G)
    (A : Set V)
    (LA : OrderedClique (G.induce A))
    (hLA : OrderedCliqueDeletionRestriction (G := G) A L LA) :
    CompatibleDominatingK5Model LA -> CompatibleDominatingK5Model L := by
  rintro ⟨T, hT⟩
  refine ⟨T.ofInduce, ?_⟩
  cases L with
  | nil =>
      exact trivial
  | single v =>
      rcases hLA with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
      · simpa [LCompatible, T.branchIndex_ofInduce_of_mem hv] using hT
      · simp [LCompatible, T.branchIndex_ofInduce_of_not_mem hv]
  | pair v1 v2 edge =>
      rcases hLA with
        ⟨hv1, hv2, rfl⟩ |
        (⟨hv1, hv2_not, rfl⟩ |
        (⟨hv1_not, hv2, rfl⟩ |
        ⟨hv1_not, hv2_not, rfl⟩))
      · simpa [LCompatible, T.branchIndex_ofInduce_of_mem hv1,
          T.branchIndex_ofInduce_of_mem hv2] using hT
      · have hidx2 : T.ofInduce.branchIndex v2 = 0 :=
          T.branchIndex_ofInduce_of_not_mem hv2_not
        have hidx1 : T.ofInduce.branchIndex v1 = T.branchIndex ⟨v1, hv1⟩ :=
          T.branchIndex_ofInduce_of_mem hv1
        simp [LCompatible, hidx1, hidx2] at hT ⊢
        exact hT
      · have hidx1 : T.ofInduce.branchIndex v1 = 0 :=
          T.branchIndex_ofInduce_of_not_mem hv1_not
        have hidx2 : T.ofInduce.branchIndex v2 = T.branchIndex ⟨v2, hv2⟩ :=
          T.branchIndex_ofInduce_of_mem hv2
        simp [LCompatible, hidx1, hidx2] at hT ⊢
        omega
      · have hidx1 : T.ofInduce.branchIndex v1 = 0 :=
          T.branchIndex_ofInduce_of_not_mem hv1_not
        have hidx2 : T.ofInduce.branchIndex v2 = 0 :=
          T.branchIndex_ofInduce_of_not_mem hv2_not
        simp [LCompatible, hidx1, hidx2]

theorem compatible_model_of_initial_segment
    {L L' : OrderedClique G}
    (hinit : L.InitialSegment L') :
    CompatibleDominatingK5Model L' -> CompatibleDominatingK5Model L := by
  rintro ⟨T, hT⟩
  refine ⟨T, ?_⟩
  cases L <;> cases L' <;> simp [OrderedClique.InitialSegment, LCompatible] at hinit hT ⊢
  · subst hinit
    exact hT
  · subst hinit
    exact hT.1
  · rcases hinit with ⟨rfl, rfl⟩
    exact hT

/-!
MI integration extras: no-compatible-model contraction transfers used by the
completed main-induction proof.
-/

theorem DominatingModel.mem_branch_of_branchIndex_eq_add_one
    {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t) {i : Fin t} {v : V}
    (hidx : T.branchIndex v = (i : Nat) + 1) :
    v ∈ (T.branch i).verts := by
  classical
  unfold DominatingModel.branchIndex at hidx
  by_cases hmem : Exists fun j : Fin t => v ∈ (T.branch j).verts
  · simp [hmem] at hidx
    have hnat : (hmem.choose : Nat) = (i : Nat) := by omega
    have hchoose : hmem.choose = i := Fin.ext hnat
    simpa [hchoose] using hmem.choose_spec
  · simp [hmem] at hidx

theorem LCompatible.first_mem_branch_zero_of_pair_second_mem
    {G : SimpleGraph V}
    {a b : V} {edge : G.Adj a b}
    {T : DominatingK5Model G}
    (hcompat : LCompatible (.pair a b edge) T)
    (hb : b ∈ (T.branch (1 : Fin 5)).verts) :
    a ∈ (T.branch (0 : Fin 5)).verts := by
  have hbidx : T.branchIndex b = 2 := by
    simpa using T.branchIndex_eq_add_one_of_mem (i := (1 : Fin 5)) hb
  have haidx : T.branchIndex a = 1 := hcompat.2.2 hbidx
  exact T.mem_branch_of_branchIndex_eq_add_one (i := (0 : Fin 5)) (by
    simpa using haidx)

theorem no_compatible_model_of_initialSegment
    {G : SimpleGraph V} {L L' : OrderedClique G}
    (h_segment : L.InitialSegment L')
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    Not (CompatibleDominatingK5Model L') := by
  intro hmodel
  exact hno_model (CompatibleDominatingK5Model.of_initialSegment h_segment hmodel)

theorem exists_collapse_image_no_compatible_model_of_first_mem
    (L : OrderedClique G)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    {v : V}
    (hfirst_L : L.first? = some v)
    (hvH : v ∈ H.verts)
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    let C : GraphContraction G := GraphContraction.collapseSubgraph G H hH_connected
    Exists fun Lq : OrderedClique C.graph =>
      OrderedCliqueContractionImage C L Lq ∧
        Lq.first? = some (none : C.Target) ∧
          Not (CompatibleDominatingK5Model Lq) := by
  classical
  intro C
  cases L with
  | nil =>
      simp [OrderedClique.first?] at hfirst_L
  | single a =>
      simp [OrderedClique.first?] at hfirst_L
      subst a
      have hv_map : C.map v = (none : C.Target) := by
        simpa [C] using
          GraphContraction.collapseSubgraph_map_eq_none_of_mem
            G H hH_connected hvH
      let Lq : OrderedClique C.graph := .single (C.map v)
      have himage : OrderedCliqueContractionImage C (.single v) Lq :=
        OrderedCliqueContractionImage.single v
      have hfirst : Lq.first? = some (none : C.Target) := by
        change some (C.map v) = some (none : C.Target)
        exact congrArg some hv_map
      refine ⟨Lq, himage, hfirst, ?_⟩
      intro hmodel
      exact hno_model
        (contraction_lifts_first_branch_of_collapse
          (G := G) (L := .single v) (H1 := H) hH_connected
          (Lq := Lq)
          (by simpa [C] using himage)
          (by simpa [C] using hfirst)
          (by simpa [C] using hmodel))
  | pair a b edge =>
      simp [OrderedClique.first?] at hfirst_L
      subst a
      have hv_map : C.map v = (none : C.Target) := by
        simpa [C] using
          GraphContraction.collapseSubgraph_map_eq_none_of_mem
            G H hH_connected hvH
      by_cases hbH : b ∈ H.verts
      · have hb_map : C.map b = (none : C.Target) := by
          simpa [C] using
            GraphContraction.collapseSubgraph_map_eq_none_of_mem
              G H hH_connected hbH
        let Lq : OrderedClique C.graph := .single (C.map v)
        have himage :
            OrderedCliqueContractionImage C (.pair v b edge) Lq := by
          exact OrderedCliqueContractionImage.pair_collapsed edge
            (by rw [hv_map, hb_map])
        have hfirst : Lq.first? = some (none : C.Target) := by
          change some (C.map v) = some (none : C.Target)
          exact congrArg some hv_map
        refine ⟨Lq, himage, hfirst, ?_⟩
        intro hmodel
        exact hno_model
          (contraction_lifts_first_branch_of_collapse
            (G := G) (L := .pair v b edge) (H1 := H) hH_connected
            (Lq := Lq)
            (by simpa [C] using himage)
            (by simpa [C] using hfirst)
            (by simpa [C] using hmodel))
      · have hb_map :
            C.map b =
              some (⟨b, hbH⟩ : {v : V // v ∉ H.verts}) := by
          simpa [C] using
            GraphContraction.collapseSubgraph_map_eq_some_of_not_mem
              G H hH_connected hbH
        have hmap_ne : C.map v ≠ C.map b := by
          rw [hv_map, hb_map]
          simp
        have edgeq : C.graph.Adj (C.map v) (C.map b) := by
          rcases C.map_adj edge with hsame | hadj
          · exact False.elim (hmap_ne hsame)
          · exact hadj
        let Lq : OrderedClique C.graph := .pair (C.map v) (C.map b) edgeq
        have himage :
            OrderedCliqueContractionImage C (.pair v b edge) Lq :=
          OrderedCliqueContractionImage.pair_uncollapsed edge edgeq
        have hfirst : Lq.first? = some (none : C.Target) := by
          change some (C.map v) = some (none : C.Target)
          exact congrArg some hv_map
        refine ⟨Lq, himage, hfirst, ?_⟩
        intro hmodel
        exact hno_model
          (contraction_lifts_first_branch_of_collapse
            (G := G) (L := .pair v b edge) (H1 := H) hH_connected
            (Lq := Lq)
            (by simpa [C] using himage)
            (by simpa [C] using hfirst)
            (by simpa [C] using hmodel))

private theorem collapse_pair_no_compatible_model_of_second_neighbor_aux
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (H2 : G.Subgraph)
    (hH2_connected : H2.coe.Connected)
    (hv2H : v2 ∈ H2.verts)
    (hH2_in_neighborhood_of_first :
      forall v : V, v ∈ H2.verts -> G.Adj v1 v)
    (hno_model :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge))) :
    let C : GraphContraction G :=
      GraphContraction.collapseSubgraph G H2 hH2_connected
    forall edgeq : C.graph.Adj (C.map v1) (C.map v2),
      Not (CompatibleDominatingK5Model
        (.pair (C.map v1) (C.map v2) edgeq)) := by
  intro C edgeq hmodel
  have hv2_map : C.map v2 = (none : C.Target) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_none_of_mem
        G H2 hH2_connected hv2H
  have himage :
      OrderedCliqueContractionImage C
        (.pair v1 v2 edge) (.pair (C.map v1) (C.map v2) edgeq) := by
    exact OrderedCliqueContractionImage.pair_uncollapsed edge edgeq
  have hsecond :
      (.pair (C.map v1) (C.map v2) edgeq : OrderedClique C.graph).second? =
        some (none : C.Target) := by
    change some (C.map v2) = some (none : C.Target)
    exact congrArg some hv2_map
  exact hno_model
    (contraction_lifts_second_neighborhood_branch_of_collapse
      (G := G) (L := .pair v1 v2 edge)
      (H2 := H2) hH2_connected
      (Lq := .pair (C.map v1) (C.map v2) edgeq) v1
      (by simpa [C] using himage)
      (by simpa [C] using hsecond)
      (by
        intro Tq hcompat hnone_mem
        have hsecond_mem : C.map v2 ∈ (Tq.branch (1 : Fin 5)).verts := by
          simpa [hv2_map] using hnone_mem
        exact
          LCompatible.first_mem_branch_zero_of_pair_second_mem
            (edge := edgeq) hcompat hsecond_mem)
      hH2_in_neighborhood_of_first
      (by simpa [C] using hmodel))

theorem exists_collapse_pair_image_no_compatible_model_of_second_neighbor
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (H2 : G.Subgraph)
    (hH2_connected : H2.coe.Connected)
    (hv2H : v2 ∈ H2.verts)
    (hH2_in_neighborhood_of_first :
      forall v : V, v ∈ H2.verts -> G.Adj v1 v)
    (hno_model :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge))) :
    let C : GraphContraction G := GraphContraction.collapseSubgraph G H2 hH2_connected
    Exists fun Lq : OrderedClique C.graph =>
      OrderedCliqueContractionImage C (.pair v1 v2 edge) Lq ∧
        Lq.second? = some (none : C.Target) ∧
          Not (CompatibleDominatingK5Model Lq) := by
  classical
  intro C
  have hv1_not_H : v1 ∉ H2.verts := by
    intro hv1H
    exact (hH2_in_neighborhood_of_first v1 hv1H).ne rfl
  have hv1_map :
      C.map v1 =
        some (⟨v1, hv1_not_H⟩ : {v : V // v ∉ H2.verts}) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_some_of_not_mem
        G H2 hH2_connected hv1_not_H
  have hv2_map : C.map v2 = (none : C.Target) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_none_of_mem
        G H2 hH2_connected hv2H
  have hmap_ne : C.map v1 ≠ C.map v2 := by
    rw [hv1_map, hv2_map]
    simp
  have edgeq : C.graph.Adj (C.map v1) (C.map v2) := by
    rcases C.map_adj edge with hsame | hadj
    · exact False.elim (hmap_ne hsame)
    · exact hadj
  let Lq : OrderedClique C.graph := .pair (C.map v1) (C.map v2) edgeq
  have himage :
      OrderedCliqueContractionImage C (.pair v1 v2 edge) Lq := by
    exact OrderedCliqueContractionImage.pair_uncollapsed edge edgeq
  have hsecond : Lq.second? = some (none : C.Target) := by
    change some (C.map v2) = some (none : C.Target)
    exact congrArg some hv2_map
  exact ⟨Lq, himage, hsecond,
    collapse_pair_no_compatible_model_of_second_neighbor_aux
      edge H2 hH2_connected hv2H hH2_in_neighborhood_of_first
      hno_model edgeq⟩

theorem collapse_pair_no_compatible_model_of_second_neighbor
    {v1 v2 : V}
    (edge : G.Adj v1 v2)
    (H2 : G.Subgraph)
    (hH2_connected : H2.coe.Connected)
    (hv2H : v2 ∈ H2.verts)
    (hH2_in_neighborhood_of_first :
      forall v : V, v ∈ H2.verts -> G.Adj v1 v)
    (hno_model :
      Not (CompatibleDominatingK5Model (.pair v1 v2 edge))) :
    let C : GraphContraction G := GraphContraction.collapseSubgraph G H2 hH2_connected
    forall edgeq : C.graph.Adj (C.map v1) (C.map v2),
      Not (CompatibleDominatingK5Model (.pair (C.map v1) (C.map v2) edgeq)) := by
  exact collapse_pair_no_compatible_model_of_second_neighbor_aux
    edge H2 hH2_connected hv2H hH2_in_neighborhood_of_first hno_model


end Schematic.Math.GraphTheory
