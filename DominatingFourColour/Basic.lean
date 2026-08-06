import Mathlib.Data.Fin.Tuple.Embedding
import Schematic.Math.GraphTheory.Separations
import Schematic.Math.GraphTheory.Subdivisions

/-!
Paper-specific definitions: dominating complete-graph models and ordered
cliques of length at most two.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

structure DominatingModel (G : SimpleGraph V) (t : Nat) where
  branch : Fin t -> G.Subgraph
  connected : forall i : Fin t, (branch i).coe.Connected
  vertex_disjoint :
    forall i j : Fin t, i ≠ j -> Disjoint (branch i).verts (branch j).verts
  dominates :
    forall i j : Fin t,
      i < j ->
      forall v : V,
        v ∈ (branch j).verts ->
        Exists fun u : V => u ∈ (branch i).verts ∧ G.Adj u v

theorem DominatingModel.branchVertex_injective_of_index_injective
    {G : SimpleGraph V} {t : Nat} {ι : Type*}
    (T : DominatingModel G t)
    (index : ι -> Fin t)
    (hindex : Function.Injective index)
    (vertex : ι -> V)
    (hvertex : forall i : ι, vertex i ∈ (T.branch (index i)).verts) :
    Function.Injective vertex := by
  intro i j hij
  by_contra hne
  exact Set.disjoint_left.mp
    (T.vertex_disjoint (index i) (index j) (hindex.ne hne))
    (hvertex i) (by simpa [hij] using hvertex j)

theorem DominatingModel.branchVertex_injective
    {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t)
    (vertex : Fin t -> V)
    (hvertex : forall i : Fin t, vertex i ∈ (T.branch i).verts) :
    Function.Injective vertex :=
  T.branchVertex_injective_of_index_injective
    (fun i => i) (fun _ _ hij => hij) vertex hvertex

def DominatingModel.branchVertexEmbedding
    {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t)
    (vertex : Fin t -> V)
    (hvertex : forall i : Fin t, vertex i ∈ (T.branch i).verts) :
    Fin t ↪ V :=
  ⟨vertex, T.branchVertex_injective vertex hvertex⟩

@[simp] theorem DominatingModel.branchVertexEmbedding_apply
    {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t)
    (vertex : Fin t -> V)
    (hvertex : forall i : Fin t, vertex i ∈ (T.branch i).verts)
    (i : Fin t) :
    T.branchVertexEmbedding vertex hvertex i = vertex i := rfl

abbrev DominatingK4Model (G : SimpleGraph V) : Type u :=
  DominatingModel G 4

abbrev DominatingK5Model (G : SimpleGraph V) : Type u :=
  DominatingModel G 5

def HasDominatingKModel (G : SimpleGraph V) (t : Nat) : Prop :=
  Nonempty (DominatingModel G t)

def HasNoDominatingKModel (G : SimpleGraph V) (t : Nat) : Prop :=
  Not (HasDominatingKModel G t)

def DominatingModel.toMinorModel {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t) :
    MinorModel (CompleteGraphOn t) G where
  branch := T.branch
  connected := T.connected
  nonempty := by
    intro i
    obtain ⟨v⟩ := (T.connected i).nonempty
    exact ⟨v, v.2⟩
  vertex_disjoint := T.vertex_disjoint
  edge_realized := by
    intro i j hij
    have hne : i ≠ j := by
      simpa [CompleteGraphOn] using hij
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨v, hv⟩ := (T.connected j).nonempty
      obtain ⟨u, hu, huv⟩ := T.dominates i j hlt v hv
      exact ⟨u, v, hu, hv, huv⟩
    · obtain ⟨v, hv⟩ := (T.connected i).nonempty
      obtain ⟨u, hu, huv⟩ := T.dominates j i hgt v hv
      exact ⟨v, u, hv, hu, huv.symm⟩

theorem DominatingModel.contains_completeGraph_minor {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t) :
    ContainsMinor (CompleteGraphOn t) G :=
  ⟨T.toMinorModel⟩

theorem DominatingModel.card_le
    {G : SimpleGraph V} [Fintype V] {t : Nat}
    (T : DominatingModel G t) :
    t <= Fintype.card V := by
  have hcard :
      Fintype.card (Fin t) <= Fintype.card V :=
    card_le_of_containsMinor T.contains_completeGraph_minor
  simpa using hcard

theorem DominatingK5Model.card_ge_five
    {G : SimpleGraph V} [Fintype V]
    (T : DominatingK5Model G) :
    5 <= Fintype.card V :=
  T.card_le

/-- Restrict a dominating model along an order embedding of its branch indices.

The order condition is essential: unlike an ordinary complete-graph minor model,
the domination condition remembers the order of the branch sets. -/
def DominatingModel.reindex
    {G : SimpleGraph V} {s t : Nat}
    (T : DominatingModel G t) (e : Fin s ↪o Fin t) :
    DominatingModel G s where
  branch i := T.branch (e i)
  connected i := T.connected (e i)
  vertex_disjoint i j hij :=
    T.vertex_disjoint (e i) (e j) (e.injective.ne hij)
  dominates i j hij := T.dominates (e i) (e j) (e.lt_iff_lt.mpr hij)

@[simp] theorem DominatingModel.reindex_branch
    {G : SimpleGraph V} {s t : Nat}
    (T : DominatingModel G t) (e : Fin s ↪o Fin t) (i : Fin s) :
    (T.reindex e).branch i = T.branch (e i) := rfl

def DominatingK5Model.tailK4
    {G : SimpleGraph V}
    (T : DominatingK5Model G) :
    DominatingK4Model G :=
  T.reindex (Fin.succOrderEmb 4)

@[simp] theorem DominatingK5Model.tailK4_branch
    {G : SimpleGraph V}
    (T : DominatingK5Model G) (i : Fin 4) :
    T.tailK4.branch i = T.branch (Fin.succ i) :=
  rfl

/-- Every branch of the tail model is disjoint from the omitted first branch. -/
theorem DominatingK5Model.tailK4_branch_disjoint_first
    {G : SimpleGraph V}
    (T : DominatingK5Model G) (i : Fin 4) :
    Disjoint (T.tailK4.branch i).verts
      (T.branch (0 : Fin 5)).verts := by
  simpa [DominatingK5Model.tailK4] using
    T.vertex_disjoint (Fin.succ i) (0 : Fin 5) (by simp)

theorem DominatingK5Model.adj_from_singleton_left
    {G : SimpleGraph V}
    (T : DominatingK5Model G) {i j : Fin 5} (hij : i < j)
    {u v : V}
    (hi : (T.branch i).verts = {u})
    (hv : v ∈ (T.branch j).verts) :
    G.Adj u v := by
  obtain ⟨u', hu', hu'v⟩ := T.dominates i j hij v hv
  have hu'_eq : u' = u := Set.mem_singleton_iff.mp (by simpa [hi] using hu')
  simpa [hu'_eq] using hu'v

theorem DominatingK5Model.tailK4_contains_K4_minor
    {G : SimpleGraph V}
    (T : DominatingK5Model G) :
    ContainsMinor K4Graph G :=
  T.tailK4.contains_completeGraph_minor

theorem DominatingK5Model.tailK4_contains_weak_K4_subdivision
    {G : SimpleGraph V}
    (T : DominatingK5Model G) :
    ContainsWeakSubdivision K4Graph G :=
  k4_minor_contains_k4_subdivision T.tailK4_contains_K4_minor

def DominatingModel.ofCliqueEmbedding {G : SimpleGraph V} {t : Nat}
    (e : Fin t ↪ V)
    (h_adj : forall i j : Fin t, i ≠ j -> G.Adj (e i) (e j)) :
    DominatingModel G t where
  branch := fun i => G.singletonSubgraph (e i)
  connected := by
    intro i
    exact SimpleGraph.Connected.of_subsingleton
  vertex_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rw [SimpleGraph.singletonSubgraph_verts] at hxi hxj
    exact hij (e.injective (hxi.symm.trans hxj))
  dominates := by
    intro i j hij v hv
    rw [SimpleGraph.singletonSubgraph_verts] at hv
    refine ⟨e i, by simp, ?_⟩
    rw [hv]
    exact h_adj i j (ne_of_lt hij)

def DominatingModel.ofCompleteEmbedding {G : SimpleGraph V} {t : Nat}
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v)
    (e : Fin t ↪ V) :
    DominatingModel G t :=
  DominatingModel.ofCliqueEmbedding e fun i j hij =>
    h_complete (e i) (e j) (fun heq => hij (e.injective heq))

theorem hasDominatingKModel_of_cliqueEmbedding
    {G : SimpleGraph V} {t : Nat}
    (e : Fin t ↪ V)
    (h_adj : forall i j : Fin t, i ≠ j -> G.Adj (e i) (e j)) :
    HasDominatingKModel G t :=
  ⟨DominatingModel.ofCliqueEmbedding e h_adj⟩

def DominatingModel.map
    {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} {t : Nat}
    (f : G →g H)
    (hf : Function.Injective f)
    (T : DominatingModel G t) :
    DominatingModel H t where
  branch i := (T.branch i).map f
  connected := by
    intro i
    rw [SimpleGraph.connected_iff]
    constructor
    · intro x y
      rcases x with ⟨x, hx⟩
      rcases y with ⟨y, hy⟩
      simp only [SimpleGraph.Subgraph.map_verts, Set.mem_image] at hx hy
      rcases hx with ⟨x₀, hx₀, rfl⟩
      rcases hy with ⟨y₀, hy₀, rfl⟩
      let F : (T.branch i).coe →g ((T.branch i).map f).coe :=
        ⟨fun z => ⟨f z, by exact ⟨z, z.2, rfl⟩⟩, by
          intro a b hab
          exact ⟨a, b, hab, rfl, rfl⟩⟩
      exact ((T.connected i) ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩).map F
    · obtain ⟨x, hx⟩ := (T.connected i).nonempty
      exact ⟨⟨f x, by exact ⟨x, hx, rfl⟩⟩⟩
  vertex_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hx hy
    simp only [SimpleGraph.Subgraph.map_verts, Set.mem_image] at hx hy
    rcases hx with ⟨x₀, hx₀, hx₀_eq⟩
    rcases hy with ⟨y₀, hy₀, hy₀_eq⟩
    have hxy : x₀ = y₀ := hf (hx₀_eq.trans hy₀_eq.symm)
    exact (Set.disjoint_left.mp (T.vertex_disjoint i j hij) hx₀) (by simpa [hxy] using hy₀)
  dominates := by
    intro i j hij x hx
    simp only [SimpleGraph.Subgraph.map_verts, Set.mem_image] at hx
    rcases hx with ⟨x₀, hx₀, rfl⟩
    obtain ⟨u₀, hu₀, hu₀x₀⟩ := T.dominates i j hij x₀ hx₀
    exact ⟨f u₀, ⟨u₀, hu₀, rfl⟩, f.map_adj hu₀x₀⟩

def inducedSubgraphHom {G : SimpleGraph V} (A : Set V) :
    G.induce A →g G :=
  ⟨Subtype.val, by
    intro v w hvw
    exact hvw⟩

def DominatingModel.ofInduce
    {G : SimpleGraph V} {t : Nat} {A : Set V}
    (T : DominatingModel (G.induce A) t) :
    DominatingModel G t :=
  T.map (inducedSubgraphHom A) Subtype.val_injective

def DominatingModel.ofConnectedComponent
    {G : SimpleGraph V} {t : Nat}
    (C : G.ConnectedComponent)
    (T : DominatingModel C.toSimpleGraph t) :
    DominatingModel G t :=
  T.map C.toSimpleGraph_hom Subtype.val_injective

def BranchIsSingleton {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t) (i : Fin t) : Prop :=
  Exists fun v : V => (T.branch i).verts = {v}

theorem BranchIsSingleton.choose_mem
    {G : SimpleGraph V} {t : Nat} {T : DominatingModel G t} {i : Fin t}
    (h : BranchIsSingleton T i) :
    h.choose ∈ (T.branch i).verts :=
  h.choose_spec.symm.subset (Set.mem_singleton h.choose)

theorem BranchIsSingleton.eq_choose_of_mem
    {G : SimpleGraph V} {t : Nat} {T : DominatingModel G t} {i : Fin t}
    (h : BranchIsSingleton T i) {v : V} (hv : v ∈ (T.branch i).verts) :
    v = h.choose :=
  Set.mem_singleton_iff.mp (h.choose_spec.subset hv)

theorem BranchIsSingleton.choose_adj_of_lt
    {G : SimpleGraph V} {t : Nat} {T : DominatingModel G t}
    {i j : Fin t}
    (h : BranchIsSingleton T i) (hij : i < j)
    {v : V} (hv : v ∈ (T.branch j).verts) :
    G.Adj h.choose v := by
  obtain ⟨u, hu, huv⟩ := T.dominates i j hij v hv
  simpa [h.eq_choose_of_mem hu] using huv

/-- The canonical clique embedding selected by singleton branch sets. -/
noncomputable def DominatingModel.singletonBranchEmbedding
    {G : SimpleGraph V} {t : Nat} (T : DominatingModel G t)
    (hsingle : ∀ i : Fin t, BranchIsSingleton T i) : Fin t ↪ V :=
  T.branchVertexEmbedding (fun i => (hsingle i).choose)
    (fun i => (hsingle i).choose_mem)

@[simp] theorem DominatingModel.singletonBranchEmbedding_apply
    {G : SimpleGraph V} {t : Nat} (T : DominatingModel G t)
    (hsingle : ∀ i : Fin t, BranchIsSingleton T i) (i : Fin t) :
    T.singletonBranchEmbedding hsingle i = (hsingle i).choose :=
  rfl

theorem DominatingModel.singletonBranchEmbedding_adj
    {G : SimpleGraph V} {t : Nat} (T : DominatingModel G t)
    (hsingle : ∀ i : Fin t, BranchIsSingleton T i)
    {i j : Fin t} (hij : i ≠ j) :
    G.Adj (T.singletonBranchEmbedding hsingle i)
      (T.singletonBranchEmbedding hsingle j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simpa using
      (hsingle i).choose_adj_of_lt hlt (hsingle j).choose_mem
  · simpa using
      ((hsingle j).choose_adj_of_lt hgt (hsingle i).choose_mem).symm

@[simp] theorem DominatingModel.branchIsSingleton_reindex
    {G : SimpleGraph V} {s t : Nat} (T : DominatingModel G t)
    (e : Fin s ↪o Fin t) (i : Fin s) :
    BranchIsSingleton (T.reindex e) i ↔ BranchIsSingleton T (e i) :=
  Iff.rfl

/-- The vertices supplied by earlier branch sets give distinct neighbors of any
vertex in a later branch set.  Keeping the embedding itself available avoids
rebuilding this finite-choice argument in every degree application. -/
theorem DominatingModel.exists_earlierBranchNeighborEmbedding
    {G : SimpleGraph V} {t : Nat} [Fintype V] [DecidableRel G.Adj]
    (T : DominatingModel G t) (i : Fin t) {v : V}
    (hv : v ∈ (T.branch i).verts) :
    Exists fun e : Fin i.val ↪ G.neighborSet v =>
      forall k : Fin i.val,
        (e k : V) ∈
          (T.branch (Fin.castLE (Nat.le_of_lt i.isLt) k)).verts := by
  classical
  let earlier : Fin i.val ↪o Fin t :=
    Fin.castLEOrderEmb (Nat.le_of_lt i.isLt)
  have hearlier_lt (k : Fin i.val) : earlier k < i := by
    change k.val < i.val
    exact k.isLt
  choose neighbor hneighbor using fun k : Fin i.val =>
    T.dominates (earlier k) i (hearlier_lt k) v hv
  let e : Fin i.val ↪ G.neighborSet v :=
    ⟨fun k => ⟨neighbor k, (hneighbor k).2.symm⟩, by
      intro k l hkl
      by_contra hne
      have hindex_ne : earlier k ≠ earlier l := fun h => hne (earlier.injective h)
      have hvalue : neighbor k = neighbor l := congrArg Subtype.val hkl
      exact Set.disjoint_left.mp
        (T.vertex_disjoint (earlier k) (earlier l) hindex_ne)
        (hneighbor k).1 (by simpa [hvalue] using (hneighbor l).1)⟩
  refine ⟨e, ?_⟩
  intro k
  exact (hneighbor k).1

/-- A vertex in branch `i` has at least `i` neighbors, one in each earlier
branch. -/
theorem DominatingModel.branch_vertex_degree_ge_index
    {G : SimpleGraph V} {t : Nat} [Fintype V] [DecidableRel G.Adj]
    (T : DominatingModel G t) (i : Fin t) {v : V}
    (hv : v ∈ (T.branch i).verts) :
    i.val ≤ G.degree v := by
  obtain ⟨e, _he⟩ := T.exists_earlierBranchNeighborEmbedding i hv
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  simpa using Fintype.card_le_of_injective e e.injective

/-- An additional neighbor in branch `j`, with `i ≤ j`, is distinct from
the neighbors supplied by all branches before `i`. -/
theorem DominatingModel.branch_vertex_degree_ge_succ_index_of_adjacent_branch
    {G : SimpleGraph V} {t : Nat} [Fintype V] [DecidableRel G.Adj]
    (T : DominatingModel G t) (i j : Fin t) (hij : i ≤ j)
    {v w : V} (hv : v ∈ (T.branch i).verts)
    (hw : w ∈ (T.branch j).verts) (hvw : G.Adj v w) :
    i.val + 1 ≤ G.degree v := by
  classical
  obtain ⟨e, he⟩ := T.exists_earlierBranchNeighborEmbedding i hv
  have hw_not_range : (⟨w, hvw⟩ : G.neighborSet v) ∉ Set.range e := by
    rintro ⟨k, hk⟩
    have hvalue : w = (e k : V) := (congrArg Subtype.val hk).symm
    have hearlier_lt :
        Fin.castLE (Nat.le_of_lt i.isLt) k < j :=
      lt_of_lt_of_le (by
        change k.val < i.val
        exact k.isLt) hij
    exact Set.disjoint_left.mp
      (T.vertex_disjoint j (Fin.castLE (Nat.le_of_lt i.isLt) k)
        (ne_of_gt hearlier_lt)) hw (by simpa [hvalue] using he k)
  let neighbors : Fin (i.val + 1) → G.neighborSet v :=
    Fin.snoc e ⟨w, hvw⟩
  have hneighbors : Function.Injective neighbors :=
    Fin.snoc_injective_of_injective e.injective hw_not_range
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  simpa using Fintype.card_le_of_injective neighbors hneighbors

/-- If no vertex has degree above the number of earlier branch sets, then that
branch set cannot contain an internal edge and hence, by connectedness, is a
singleton. -/
theorem DominatingModel.branch_isSingleton_of_degree_le_index
    {G : SimpleGraph V} {t : Nat} [Fintype V] [DecidableRel G.Adj]
    (T : DominatingModel G t) (i : Fin t)
    (hdegree : forall v : V, G.degree v ≤ i.val) :
    BranchIsSingleton T i := by
  classical
  obtain ⟨v, hv⟩ := (T.connected i).nonempty
  refine ⟨v, ?_⟩
  ext w
  constructor
  · intro hw
    by_contra hw_ne
    let vv : (T.branch i).verts := ⟨v, hv⟩
    let ww : (T.branch i).verts := ⟨w, hw⟩
    have hvw_ne : vv ≠ ww := by
      intro h
      exact hw_ne (Set.mem_singleton_iff.mpr (congrArg Subtype.val h).symm)
    obtain ⟨z, hz_adj⟩ :=
      ((T.connected i) vv ww).nonempty_neighborSet_left hvw_ne
    have hlarge : i.val + 1 ≤ G.degree v :=
      T.branch_vertex_degree_ge_succ_index_of_adjacent_branch i i le_rfl
        hv z.2 ((T.branch i).adj_sub hz_adj)
    exact Nat.not_succ_le_self i.val (hlarge.trans (hdegree v))
  · intro hw
    simpa only [Set.mem_singleton_iff] using hw.symm ▸ hv

theorem DominatingModel.exists_pair_mem_branch_of_not_singleton
    {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t) (i : Fin t)
    (hnot_singleton : Not (BranchIsSingleton T i)) :
    Exists fun x : V =>
      Exists fun y : V =>
        x ∈ (T.branch i).verts ∧ y ∈ (T.branch i).verts ∧ x ≠ y := by
  classical
  obtain ⟨x, hx⟩ := (T.connected i).nonempty
  by_contra hno_pair
  have hsubsingleton :
      forall y : V, y ∈ (T.branch i).verts -> y = x := by
    intro y hy
    by_contra hyx
    exact hno_pair ⟨y, x, hy, hx, hyx⟩
  exact hnot_singleton ⟨x, by
    ext y
    constructor
    · intro hy
      exact Set.mem_singleton_iff.mpr (hsubsingleton y hy)
    · intro hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      simpa [hyx] using hx⟩

theorem DominatingModel.exists_path_in_branch_of_not_singleton
    {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t) (i : Fin t)
    (hnot_singleton : Not (BranchIsSingleton T i)) :
    Exists fun x : V =>
      Exists fun y : V =>
        Exists fun p : G.Walk x y =>
          x ∈ (T.branch i).verts ∧
            y ∈ (T.branch i).verts ∧
              x ≠ y ∧ p.IsPath ∧ p.toSubgraph ≤ T.branch i := by
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    T.exists_pair_mem_branch_of_not_singleton i hnot_singleton
  obtain ⟨p, hp, hp_le⟩ :=
    Subgraph.Connected.exists_path_between (T.connected i) hx hy
  exact ⟨x, y, p, hx, hy, hxy, hp, hp_le⟩

theorem DominatingModel.exists_not_singleton_of_not_all_singleton
    {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t)
    (hnot_all : Not (forall i : Fin t, BranchIsSingleton T i)) :
    Exists fun i : Fin t => Not (BranchIsSingleton T i) := by
  classical
  by_contra hnone
  exact hnot_all (by
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩)

theorem DominatingModel.exists_branch_path_of_not_all_singleton
    {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t)
    (hnot_all : Not (forall i : Fin t, BranchIsSingleton T i)) :
    Exists fun i : Fin t =>
      Exists fun x : V =>
        Exists fun y : V =>
          Exists fun p : G.Walk x y =>
            x ∈ (T.branch i).verts ∧
              y ∈ (T.branch i).verts ∧
                x ≠ y ∧ p.IsPath ∧ p.toSubgraph ≤ T.branch i := by
  obtain ⟨i, hi⟩ := T.exists_not_singleton_of_not_all_singleton hnot_all
  exact ⟨i, T.exists_path_in_branch_of_not_singleton i hi⟩

noncomputable def DominatingModel.branchIndex
    {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t) (v : V) : Nat := by
  classical
  exact
    if h : Exists fun i : Fin t => v ∈ (T.branch i).verts then
      (h.choose : Nat) + 1
    else
      0

theorem DominatingModel.branchIndex_eq_add_one_of_mem
    {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t) {i : Fin t} {v : V}
    (hv : v ∈ (T.branch i).verts) :
    T.branchIndex v = (i : Nat) + 1 := by
  classical
  let h_exists : Exists fun j : Fin t => v ∈ (T.branch j).verts := ⟨i, hv⟩
  have hchoose : h_exists.choose = i := by
    by_contra hne
    have hdis := T.vertex_disjoint h_exists.choose i hne
    exact (Set.disjoint_left.mp hdis h_exists.choose_spec) hv
  rw [DominatingModel.branchIndex]
  simp only [dif_pos h_exists]
  rw [hchoose]

theorem DominatingModel.branchIndex_eq_zero_of_forall_not_mem
    {G : SimpleGraph V} {t : Nat}
    (T : DominatingModel G t) {v : V}
    (hv : forall i : Fin t, v ∉ (T.branch i).verts) :
    T.branchIndex v = 0 := by
  classical
  have hnot : Not (Exists fun i : Fin t => v ∈ (T.branch i).verts) := by
    intro h
    exact hv h.choose h.choose_spec
  rw [DominatingModel.branchIndex]
  simp [hnot]

theorem DominatingModel.branchIndex_map
    {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W} {t : Nat}
    (T : DominatingModel G t)
    (f : G →g H)
    (hf : Function.Injective f)
    (v : V) :
    (T.map f hf).branchIndex (f v) = T.branchIndex v := by
  classical
  by_cases hmem : Exists fun i : Fin t => v ∈ (T.branch i).verts
  · let i : Fin t := hmem.choose
    have hi : v ∈ (T.branch i).verts := hmem.choose_spec
    have hlift : f v ∈ ((T.map f hf).branch i).verts := by
      exact ⟨v, hi, rfl⟩
    rw [(T.map f hf).branchIndex_eq_add_one_of_mem hlift,
      T.branchIndex_eq_add_one_of_mem hi]
  · have hbase : T.branchIndex v = 0 := by
      exact T.branchIndex_eq_zero_of_forall_not_mem (by
        intro i hi
        exact hmem ⟨i, hi⟩)
    have hmap : (T.map f hf).branchIndex (f v) = 0 := by
      exact (T.map f hf).branchIndex_eq_zero_of_forall_not_mem (by
        intro i hi
        simp only [DominatingModel.map, SimpleGraph.Subgraph.map_verts,
          Set.mem_image] at hi
        rcases hi with ⟨x, hx, hxv⟩
        have hx_eq : x = v := hf hxv
        exact hmem ⟨i, by simpa [hx_eq] using hx⟩)
    rw [hmap, hbase]

theorem DominatingModel.branchIndex_ofInduce_of_mem
    {G : SimpleGraph V} {t : Nat} {A : Set V}
    (T : DominatingModel (G.induce A) t)
    {v : V}
    (hv : v ∈ A) :
    T.ofInduce.branchIndex v = T.branchIndex ⟨v, hv⟩ := by
  classical
  by_cases hmem : Exists fun i : Fin t => ⟨v, hv⟩ ∈ (T.branch i).verts
  · let i : Fin t := hmem.choose
    have hi : ⟨v, hv⟩ ∈ (T.branch i).verts := hmem.choose_spec
    have h_lift : v ∈ (T.ofInduce.branch i).verts := by
      exact ⟨⟨v, hv⟩, hi, rfl⟩
    rw [T.ofInduce.branchIndex_eq_add_one_of_mem h_lift,
      T.branchIndex_eq_add_one_of_mem hi]
  · have hbase : T.branchIndex ⟨v, hv⟩ = 0 := by
      exact T.branchIndex_eq_zero_of_forall_not_mem (by
        intro i hi
        exact hmem ⟨i, hi⟩)
    have hlift : T.ofInduce.branchIndex v = 0 := by
      exact T.ofInduce.branchIndex_eq_zero_of_forall_not_mem (by
        intro i hi
        simp only [DominatingModel.ofInduce, DominatingModel.map,
          SimpleGraph.Subgraph.map_verts,
          Set.mem_image] at hi
        rcases hi with ⟨x, hx, hxv⟩
        have hx_eq : x = ⟨v, hv⟩ := Subtype.ext hxv
        exact hmem ⟨i, by simpa [hx_eq] using hx⟩)
    rw [hlift, hbase]

theorem DominatingModel.branchIndex_ofInduce_of_not_mem
    {G : SimpleGraph V} {t : Nat} {A : Set V}
    (T : DominatingModel (G.induce A) t)
    {v : V}
    (hv : v ∉ A) :
    T.ofInduce.branchIndex v = 0 := by
  classical
  exact T.ofInduce.branchIndex_eq_zero_of_forall_not_mem (by
    intro i hi
    simp only [DominatingModel.ofInduce, DominatingModel.map,
      SimpleGraph.Subgraph.map_verts,
      Set.mem_image] at hi
    rcases hi with ⟨x, _hx, hxv⟩
    exact hv (by rw [← hxv]; exact x.2))

inductive OrderedClique (G : SimpleGraph V) : Type u where
  | nil : OrderedClique G
  | single (v1 : V) : OrderedClique G
  | pair (v1 v2 : V) (edge : G.Adj v1 v2) : OrderedClique G

namespace OrderedClique

variable {G : SimpleGraph V}

def length : OrderedClique G -> Nat
  | nil => 0
  | single _ => 1
  | pair _ _ _ => 2

def first? : OrderedClique G -> Option V
  | nil => none
  | single v1 => some v1
  | pair v1 _ _ => some v1

def second? : OrderedClique G -> Option V
  | nil => none
  | single _ => none
  | pair _ v2 _ => some v2

def vertexSet : OrderedClique G -> Set V
  | nil => ∅
  | single v1 => {v1}
  | pair v1 v2 _ => {v1, v2}

def map {W : Type v} {H : SimpleGraph W}
    (f : G →g H) : OrderedClique G -> OrderedClique H
  | nil => nil
  | single v1 => single (f v1)
  | pair v1 v2 edge => pair (f v1) (f v2) (f.map_adj edge)

def InitialSegment : OrderedClique G -> OrderedClique G -> Prop
  | nil, _ => True
  | single v, single w => v = w
  | single v, pair w _ _ => v = w
  | pair v1 v2 _, pair w1 w2 _ => v1 = w1 ∧ v2 = w2
  | _, _ => False

theorem vertexSet_isClique (L : OrderedClique G) :
    G.IsClique L.vertexSet := by
  intro a ha b hb hab
  cases L with
  | nil =>
      simp [vertexSet] at ha
  | single v =>
      simp [vertexSet] at ha hb
      exact False.elim (hab (ha.trans hb.symm))
  | pair v1 v2 edge =>
      simp [vertexSet] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact edge
      · exact edge.symm
      · exact False.elim (hab rfl)

theorem vertexSet_subset_left_or_subset_right
    (S : Separation G)
    (L : OrderedClique G) :
    L.vertexSet ⊆ S.left ∨ L.vertexSet ⊆ S.right := by
  cases L with
  | nil =>
      exact Or.inl (by intro v hv; simp [vertexSet] at hv)
  | single v =>
      rcases S.mem_left_or_right v with hv_left | hv_right
      · exact Or.inl (by intro x hx; simpa [vertexSet] using hx ▸ hv_left)
      · exact Or.inr (by intro x hx; simpa [vertexSet] using hx ▸ hv_right)
    | pair v1 v2 edge =>
        rcases S.mem_left_or_right v1 with hv1_left | hv1_right
        · by_cases hv2_left : v2 ∈ S.left
          · exact Or.inl (by
              intro x hx
              have hx_cases : x = v1 ∨ x = v2 := by
                simpa [vertexSet] using hx
              rcases hx_cases with rfl | rfl
              · exact hv1_left
              · exact hv2_left)
          · have hv2_right : v2 ∈ S.right := S.mem_right_of_not_mem_left hv2_left
            have hv1_right : v1 ∈ S.right := by
              by_contra hv1_not_right
              exact S.no_cross hv1_left hv1_not_right hv2_right hv2_left edge
            exact Or.inr (by
              intro x hx
              have hx_cases : x = v1 ∨ x = v2 := by
                simpa [vertexSet] using hx
              rcases hx_cases with rfl | rfl
              · exact hv1_right
              · exact hv2_right)
        · by_cases hv2_right : v2 ∈ S.right
          · exact Or.inr (by
              intro x hx
              have hx_cases : x = v1 ∨ x = v2 := by
                simpa [vertexSet] using hx
              rcases hx_cases with rfl | rfl
              · exact hv1_right
              · exact hv2_right)
          · have hv2_left : v2 ∈ S.left := S.mem_left_of_not_mem_right hv2_right
            have hv1_left : v1 ∈ S.left := by
              by_contra hv1_not_left
              exact S.no_cross hv2_left hv2_right hv1_right hv1_not_left edge.symm
            exact Or.inl (by
              intro x hx
              have hx_cases : x = v1 ∨ x = v2 := by
                simpa [vertexSet] using hx
              rcases hx_cases with rfl | rfl
              · exact hv1_left
              · exact hv2_left)

theorem initialSegment_refl (L : OrderedClique G) :
    L.InitialSegment L := by
  cases L <;> simp [InitialSegment]

theorem length_le_of_initialSegment {L L' : OrderedClique G}
    (h : L.InitialSegment L') :
    L.length <= L'.length := by
  cases L <;> cases L' <;> simp [InitialSegment, length] at h ⊢

theorem length_eq_of_pair_initialSegment {v1 v2 : V} {edge : G.Adj v1 v2}
    {L' : OrderedClique G}
    (h : (OrderedClique.pair v1 v2 edge).InitialSegment L') :
    L'.length = 2 := by
  cases L' <;> simp [InitialSegment, length] at h ⊢

end OrderedClique

def LCompatible {G : SimpleGraph V}
    (L : OrderedClique G) (T : DominatingK5Model G) : Prop :=
  match L with
  | .nil => True
  | .single v1 => T.branchIndex v1 <= 1
  | .pair v1 v2 _ =>
      T.branchIndex v1 <= 1 ∧
        T.branchIndex v2 <= 2 ∧
          (T.branchIndex v2 = 2 -> T.branchIndex v1 = 1)

def CompatibleDominatingK5Model {G : SimpleGraph V} (L : OrderedClique G) : Prop :=
  Exists fun T : DominatingK5Model G => LCompatible L T

theorem LCompatible.map
    {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    (L : OrderedClique G)
    (f : G →g H)
    (hf : Function.Injective f)
    {T : DominatingK5Model G}
    (hT : LCompatible L T) :
    LCompatible (L.map f) (T.map f hf) := by
  cases L with
  | nil =>
      simp [OrderedClique.map, LCompatible]
  | single v =>
      simpa [OrderedClique.map, LCompatible, T.branchIndex_map f hf v] using hT
  | pair v1 v2 edge =>
      simpa [OrderedClique.map, LCompatible,
        T.branchIndex_map f hf v1, T.branchIndex_map f hf v2] using hT

theorem CompatibleDominatingK5Model.map
    {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    (L : OrderedClique G)
    (f : G →g H)
    (hf : Function.Injective f) :
    CompatibleDominatingK5Model L ->
      CompatibleDominatingK5Model (L.map f) := by
  rintro ⟨T, hT⟩
  exact ⟨T.map f hf, LCompatible.map L f hf hT⟩

theorem not_compatible_of_map_not_compatible
    {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    (L : OrderedClique G)
    (f : G →g H)
    (hf : Function.Injective f)
    (hno_map : Not (CompatibleDominatingK5Model (L.map f))) :
    Not (CompatibleDominatingK5Model L) := by
  intro hmodel
  exact hno_map (hmodel.map L f hf)

theorem LCompatible.of_initialSegment
    {G : SimpleGraph V} {L L' : OrderedClique G} {T : DominatingK5Model G}
    (h_segment : L.InitialSegment L')
    (h_compatible : LCompatible L' T) :
    LCompatible L T := by
  cases L with
  | nil =>
      simp [LCompatible]
  | single v =>
      cases L' with
      | nil =>
          simp [OrderedClique.InitialSegment] at h_segment
      | single w =>
          simp [OrderedClique.InitialSegment, LCompatible] at h_segment h_compatible ⊢
          subst w
          exact h_compatible
      | pair w z edge =>
          simp [OrderedClique.InitialSegment, LCompatible] at h_segment h_compatible ⊢
          subst w
          exact h_compatible.1
  | pair v w edge =>
      cases L' with
      | nil =>
          simp [OrderedClique.InitialSegment] at h_segment
      | single z =>
          simp [OrderedClique.InitialSegment] at h_segment
      | pair a b edge' =>
          simp [OrderedClique.InitialSegment, LCompatible] at h_segment h_compatible ⊢
          rcases h_segment with ⟨rfl, rfl⟩
          exact h_compatible

theorem CompatibleDominatingK5Model.of_initialSegment
    {G : SimpleGraph V} {L L' : OrderedClique G}
    (h_segment : L.InitialSegment L')
    (h_model : CompatibleDominatingK5Model L') :
    CompatibleDominatingK5Model L := by
  rcases h_model with ⟨T, hT⟩
  exact ⟨T, LCompatible.of_initialSegment h_segment hT⟩

theorem compatible_dominating_K5_model_nil_of_cliqueEmbedding
    {G : SimpleGraph V}
    (e : Fin 5 ↪ V)
    (h_adj : forall i j : Fin 5, i ≠ j -> G.Adj (e i) (e j)) :
    CompatibleDominatingK5Model (OrderedClique.nil : OrderedClique G) :=
  ⟨DominatingModel.ofCliqueEmbedding e h_adj, by simp [LCompatible]⟩

theorem compatible_dominating_K5_model_nil_of_complete_card_ge_five
    {G : SimpleGraph V} [Fintype V]
    (h_card : 5 <= Fintype.card V)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v) :
    CompatibleDominatingK5Model (OrderedClique.nil : OrderedClique G) := by
  classical
  obtain ⟨e⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin 5) (β := V) (by simpa using h_card)
  exact ⟨DominatingModel.ofCompleteEmbedding h_complete e, by simp [LCompatible]⟩

theorem compatible_dominating_K5_model_single_of_complete_card_ge_five
    {G : SimpleGraph V} [Fintype V]
    (h_card : 5 <= Fintype.card V)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v)
    (v1 : V) :
    CompatibleDominatingK5Model (OrderedClique.single v1 : OrderedClique G) := by
  classical
  letI : Fintype {x : V // x ≠ v1} := Fintype.ofFinite _
  have h_compl_card : 4 <= Fintype.card {x : V // x ≠ v1} := by
    have hcard : Fintype.card {x : V // x ≠ v1} = Fintype.card V - 1 := by
      simp
    rw [hcard]
    omega
  obtain ⟨e4_sub⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin 4) (β := {x : V // x ≠ v1}) h_compl_card
  let e4 : Fin 4 ↪ V :=
    e4_sub.trans (Function.Embedding.subtype fun x : V => x ≠ v1)
  have hv1_not_range : v1 ∉ Set.range e4 := by
    rintro ⟨i, hi⟩
    exact (e4_sub i).2 hi
  let e : Fin 5 ↪ V := Fin.Embedding.cons e4 hv1_not_range
  let T : DominatingK5Model G := DominatingModel.ofCompleteEmbedding h_complete e
  refine ⟨T, ?_⟩
  have hv1_mem : v1 ∈ (T.branch (0 : Fin 5)).verts := by
    change v1 ∈ (G.singletonSubgraph (e (0 : Fin 5))).verts
    rw [SimpleGraph.singletonSubgraph_verts]
    simp [e]
  have hidx : T.branchIndex v1 = 1 := by
    simpa using T.branchIndex_eq_add_one_of_mem (i := (0 : Fin 5)) hv1_mem
  simpa [LCompatible] using (le_of_eq hidx)

theorem compatible_dominating_K5_model_pair_of_complete_card_ge_five
    {G : SimpleGraph V} [Fintype V]
    (h_card : 5 <= Fintype.card V)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v)
    {v1 v2 : V} (edge : G.Adj v1 v2) :
    CompatibleDominatingK5Model (OrderedClique.pair v1 v2 edge : OrderedClique G) := by
  classical
  let P : V -> Prop := fun x => x = v1 ∨ x = v2
  letI : Fintype {x : V // P x} := Fintype.ofFinite _
  letI : Fintype {x : V // ¬ P x} := Fintype.ofFinite _
  have hP_card : Fintype.card {x : V // P x} = 2 := by
    rw [Fintype.card_of_subtype ({v1, v2} : Finset V)]
    · exact Finset.card_pair edge.ne
    · intro x
      simp [P]
  have h_compl_card : 3 <= Fintype.card {x : V // ¬ P x} := by
    rw [Fintype.card_subtype_compl P, hP_card]
    omega
  obtain ⟨e3_sub⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin 3) (β := {x : V // ¬ P x}) h_compl_card
  let e3 : Fin 3 ↪ V :=
    e3_sub.trans (Function.Embedding.subtype fun x : V => ¬ P x)
  have hv2_not_range : v2 ∉ Set.range e3 := by
    rintro ⟨i, hi⟩
    exact (e3_sub i).2 (Or.inr hi)
  let e4 : Fin 4 ↪ V := Fin.Embedding.cons e3 hv2_not_range
  have hv1_not_range : v1 ∉ Set.range e4 := by
    rintro ⟨i, hi⟩
    fin_cases i <;> simp [e4, e3] at hi
    · exact edge.ne hi.symm
    · exact (e3_sub 0).2 (Or.inl hi)
    · exact (e3_sub 1).2 (Or.inl hi)
    · exact (e3_sub 2).2 (Or.inl hi)
  let e : Fin 5 ↪ V := Fin.Embedding.cons e4 hv1_not_range
  let T : DominatingK5Model G := DominatingModel.ofCompleteEmbedding h_complete e
  refine ⟨T, ?_⟩
  have hv1_mem : v1 ∈ (T.branch (0 : Fin 5)).verts := by
    change v1 ∈ (G.singletonSubgraph (e (0 : Fin 5))).verts
    rw [SimpleGraph.singletonSubgraph_verts]
    simp [e]
  have hv2_mem : v2 ∈ (T.branch (1 : Fin 5)).verts := by
    change v2 ∈ (G.singletonSubgraph (e (1 : Fin 5))).verts
    rw [SimpleGraph.singletonSubgraph_verts]
    simp [e, e4]
  have hidx1 : T.branchIndex v1 = 1 := by
    simpa using T.branchIndex_eq_add_one_of_mem (i := (0 : Fin 5)) hv1_mem
  have hidx2 : T.branchIndex v2 = 2 := by
    simpa using T.branchIndex_eq_add_one_of_mem (i := (1 : Fin 5)) hv2_mem
  simp [LCompatible, hidx1, hidx2]

theorem compatible_dominating_K5_model_of_complete_card_ge_five
    {G : SimpleGraph V} [Fintype V]
    (h_card : 5 <= Fintype.card V)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v)
    (L : OrderedClique G) :
    CompatibleDominatingK5Model L := by
  cases L with
  | nil =>
      exact compatible_dominating_K5_model_nil_of_complete_card_ge_five h_card h_complete
  | single v1 =>
      exact compatible_dominating_K5_model_single_of_complete_card_ge_five h_card h_complete v1
  | pair v1 v2 edge =>
      exact compatible_dominating_K5_model_pair_of_complete_card_ge_five h_card h_complete edge

end Schematic.Math.GraphTheory
