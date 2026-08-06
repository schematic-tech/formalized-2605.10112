import DominatingFourColour.Consequences.Singletons
import Mathlib.Data.Fin.Tuple.Basic

/-!
Formalization of examples and comparison statements from the introduction.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

private theorem dominating_K5_has_adjacent_degree_atLeast_four
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : DominatingK5Model G) :
    Exists fun p : V =>
      Exists fun q : V => G.Adj p q ∧ 4 <= G.degree p ∧ 4 <= G.degree q := by
  obtain ⟨q, hq⟩ := (T.connected (4 : Fin 5)).nonempty
  obtain ⟨p, hp, hpq⟩ :=
    T.dominates (3 : Fin 5) (4 : Fin 5) (by decide) q hq
  exact ⟨p, q, hpq,
    T.branch_vertex_degree_ge_succ_index_of_adjacent_branch
      (3 : Fin 5) (4 : Fin 5) (by decide) hp hq hpq,
    T.branch_vertex_degree_ge_index (4 : Fin 5) hq⟩

private theorem dominating_K5_last_branch_singleton_of_max_degree_four
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmax : forall v : V, G.degree v <= 4)
    (T : DominatingK5Model G) :
    BranchIsSingleton T (4 : Fin 5) := by
  exact T.branch_isSingleton_of_degree_le_index (4 : Fin 5) hmax

private theorem dominating_K4_has_adjacent_degree_atLeast_three
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : DominatingK4Model G) :
    Exists fun p : V =>
      Exists fun q : V => G.Adj p q ∧ 3 <= G.degree p ∧ 3 <= G.degree q := by
  obtain ⟨q, hq⟩ := (T.connected (3 : Fin 4)).nonempty
  obtain ⟨p, hp, hpq⟩ :=
    T.dominates (2 : Fin 4) (3 : Fin 4) (by decide) q hq
  exact ⟨p, q, hpq,
    T.branch_vertex_degree_ge_succ_index_of_adjacent_branch
      (2 : Fin 4) (3 : Fin 4) (by decide) hp hq hpq,
    T.branch_vertex_degree_ge_index (3 : Fin 4) hq⟩

abbrev OneSubdivisionCompleteGraph (n : Nat) : Type :=
  Fin n ⊕ {e : Sym2 (Fin n) // e ∉ Sym2.diagSet}

def oneSubdivisionCompleteGraph (n : Nat) : SimpleGraph (OneSubdivisionCompleteGraph n) where
  Adj
    | Sum.inl v, Sum.inr e => v ∈ (e : Sym2 (Fin n))
    | Sum.inr e, Sum.inl v => v ∈ (e : Sym2 (Fin n))
    | _, _ => False
  symm := by
    rintro (v | e) (w | f) h <;> simp_all
  loopless := ⟨by
    rintro (v | e) h <;> simp_all⟩

private theorem oneSubdivisionCompleteGraph_subdivision_degree_le_two
    (n : Nat)
    (e : {e : Sym2 (Fin n) // e ∉ Sym2.diagSet})
    [Fintype ((oneSubdivisionCompleteGraph n).neighborSet (Sum.inr e))] :
    (oneSubdivisionCompleteGraph n).degree (Sum.inr e) <= 2 := by
  classical
  let G := oneSubdivisionCompleteGraph n
  let f : G.neighborSet (Sum.inr e) -> {v : Fin n // v ∈ (e : Sym2 (Fin n)).toFinset} :=
    fun
      | ⟨Sum.inl v, hv⟩ => ⟨v, by simpa [G, oneSubdivisionCompleteGraph] using hv⟩
      | ⟨Sum.inr _, hv⟩ => False.elim (by
          simp [G, oneSubdivisionCompleteGraph] at hv)
  have hf : Function.Injective f := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    cases x with
    | inl xv =>
        cases y with
        | inl yv =>
            apply Subtype.ext
            simpa [f] using congrArg Subtype.val hxy
        | inr _ =>
            exact False.elim (by
              simp [G, oneSubdivisionCompleteGraph] at hy)
    | inr _ =>
        exact False.elim (by
          simp [G, oneSubdivisionCompleteGraph] at hx)
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  refine (Fintype.card_le_of_injective f hf).trans ?_
  calc
    Fintype.card {v : Fin n // v ∈ (e : Sym2 (Fin n)).toFinset}
        = ((e : Sym2 (Fin n)).toFinset).card := by
            rw [Fintype.card_subtype]
            congr 1
            ext v
            simp
    _ <= 2 := by
      by_cases hdiag : (e : Sym2 (Fin n)).IsDiag
      · rw [Sym2.card_toFinset_of_isDiag _ hdiag]
        decide
      · rw [Sym2.card_toFinset_of_not_isDiag _ hdiag]

theorem one_subdivision_complete_graph_has_no_dominating_K4
      (n : Nat) :
      HasNoDominatingKModel (oneSubdivisionCompleteGraph n) 4 := by
  classical
  rintro ⟨T⟩
  obtain ⟨p, q, hpq, hp_degree, hq_degree⟩ :=
    dominating_K4_has_adjacent_degree_atLeast_three (oneSubdivisionCompleteGraph n) T
  cases p with
  | inl pv =>
      cases q with
      | inl qv =>
          simp [oneSubdivisionCompleteGraph] at hpq
      | inr qe =>
          have hle := oneSubdivisionCompleteGraph_subdivision_degree_le_two n qe
          exact Nat.not_succ_le_self 2 (le_trans hq_degree hle)
  | inr pe =>
      have hle := oneSubdivisionCompleteGraph_subdivision_degree_le_two n pe
      exact Nat.not_succ_le_self 2 (le_trans hp_degree hle)

theorem max_degree_three_has_no_dominating_K5
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmax : MaxDegreeAtMost G 3) :
    HasNoDominatingKModel G 5 := by
  rintro ⟨T⟩
  obtain ⟨v, hv⟩ := (T.connected (4 : Fin 5)).nonempty
  have hdeg : 4 ≤ G.degree v :=
    T.branch_vertex_degree_ge_index (4 : Fin 5) hv
  exact Nat.not_succ_le_self 3 (le_trans hdeg (hmax v))

theorem no_adjacent_degree_at_least_four_has_no_dominating_K5
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hno : NoAdjacentVerticesDegreeAtLeast G 4) :
    HasNoDominatingKModel G 5 := by
  rintro ⟨T⟩
  obtain ⟨p, q, hpq, hpdeg, hqdeg⟩ := dominating_K5_has_adjacent_degree_atLeast_four G T
  exact hno p q hpq ⟨hpdeg, hqdeg⟩

abbrev K55MinusPerfectMatchingVertex : Type :=
  Fin 5 ⊕ Fin 5

def K55MinusPerfectMatching : SimpleGraph K55MinusPerfectMatchingVertex where
  Adj
    | Sum.inl i, Sum.inr j => i ≠ j
    | Sum.inr j, Sum.inl i => i ≠ j
    | _, _ => False
  symm := by
    rintro (i | i) (j | j) h <;> simp_all [ne_comm]
  loopless := ⟨by
    rintro (i | i) h <;> simp_all⟩

private theorem K55_adj_left_right_iff (i j : Fin 5) :
    K55MinusPerfectMatching.Adj (Sum.inl i) (Sum.inr j) ↔ i ≠ j := by
  rfl

private theorem K55_adj_right_left_iff (i j : Fin 5) :
    K55MinusPerfectMatching.Adj (Sum.inr i) (Sum.inl j) ↔ i ≠ j := by
  simp [K55MinusPerfectMatching, ne_comm]

private theorem K55_not_adj_left_left (i j : Fin 5) :
    Not (K55MinusPerfectMatching.Adj (Sum.inl i) (Sum.inl j)) := by
  simp [K55MinusPerfectMatching]

private theorem K55_not_adj_right_right (i j : Fin 5) :
    Not (K55MinusPerfectMatching.Adj (Sum.inr i) (Sum.inr j)) := by
  simp [K55MinusPerfectMatching]

private theorem K55_neighbor_of_left {x : K55MinusPerfectMatchingVertex} {i : Fin 5}
    (h : K55MinusPerfectMatching.Adj x (Sum.inl i)) :
    Exists fun j : Fin 5 => x = Sum.inr j ∧ j ≠ i := by
  cases x with
  | inl j =>
      exact False.elim (K55_not_adj_left_left j i h)
  | inr j =>
      exact ⟨j, rfl, by simpa [K55MinusPerfectMatching, ne_comm] using h⟩

private theorem K55_neighbor_of_right {x : K55MinusPerfectMatchingVertex} {i : Fin 5}
    (h : K55MinusPerfectMatching.Adj x (Sum.inr i)) :
    Exists fun j : Fin 5 => x = Sum.inl j ∧ j ≠ i := by
  cases x with
  | inl j =>
      exact ⟨j, rfl, by simpa [K55MinusPerfectMatching] using h⟩
  | inr j =>
      exact False.elim (K55_not_adj_right_right j i h)

private def K55Mate : K55MinusPerfectMatchingVertex -> K55MinusPerfectMatchingVertex
  | Sum.inl i => Sum.inr i
  | Sum.inr i => Sum.inl i

private theorem K55_not_adj_mate (x : K55MinusPerfectMatchingVertex) :
    Not (K55MinusPerfectMatching.Adj x (K55Mate x)) := by
  cases x with
  | inl i =>
      simp [K55Mate, K55MinusPerfectMatching]
  | inr i =>
      simp [K55Mate, K55MinusPerfectMatching]

private theorem K55_triangle_free
    {x y z : K55MinusPerfectMatchingVertex}
    (hxy : K55MinusPerfectMatching.Adj x y)
    (hyz : K55MinusPerfectMatching.Adj y z)
    (hzx : K55MinusPerfectMatching.Adj z x) :
    False := by
  cases x <;> cases y <;> cases z <;> simp [K55MinusPerfectMatching] at *

private theorem K55_no_common_neighbor_of_adjacent
    {x y z : K55MinusPerfectMatchingVertex}
    (hxy : K55MinusPerfectMatching.Adj x y)
    (hzx : K55MinusPerfectMatching.Adj z x)
    (hzy : K55MinusPerfectMatching.Adj z y) :
    False :=
  K55_triangle_free hxy hzy.symm hzx

private def K55Swap : K55MinusPerfectMatchingVertex -> K55MinusPerfectMatchingVertex
  | Sum.inl i => Sum.inr i
  | Sum.inr i => Sum.inl i

private theorem K55Swap_injective : Function.Injective K55Swap := by
  intro x y h
  cases x <;> cases y <;> simp [K55Swap] at h ⊢
  · exact h
  · exact h

private def K55SwapEmbedding : K55MinusPerfectMatchingVertex ↪ K55MinusPerfectMatchingVertex :=
  ⟨K55Swap, K55Swap_injective⟩

private theorem K55Swap_adj {x y : K55MinusPerfectMatchingVertex}
    (h : K55MinusPerfectMatching.Adj x y) :
    K55MinusPerfectMatching.Adj (K55Swap x) (K55Swap y) := by
  cases x <;> cases y <;> simp [K55Swap, K55MinusPerfectMatching, ne_comm] at h ⊢
  all_goals exact h

private abbrev K55BranchSetsWitness
    (B : Fin 5 -> Finset K55MinusPerfectMatchingVertex) : Prop :=
  (forall i : Fin 5, (B i).Nonempty) ∧
  (forall i : Fin 5,
    forall x : K55MinusPerfectMatchingVertex,
      x ∈ B i ->
      (Exists fun y : K55MinusPerfectMatchingVertex => y ∈ B i ∧ y ≠ x) ->
      Exists fun y : K55MinusPerfectMatchingVertex =>
        y ∈ B i ∧ K55MinusPerfectMatching.Adj x y) ∧
  (forall i j : Fin 5,
    i ≠ j ->
    forall x : K55MinusPerfectMatchingVertex, x ∈ B i -> x ∈ B j -> False) ∧
  (forall i j : Fin 5,
    i < j ->
    forall v : K55MinusPerfectMatchingVertex,
      v ∈ B j ->
      Exists fun u : K55MinusPerfectMatchingVertex =>
        u ∈ B i ∧ K55MinusPerfectMatching.Adj u v) ∧
  (B (3 : Fin 5)).card = 1 ∧ (B (4 : Fin 5)).card = 1

private theorem K55BranchSetsWitness_swap
    {B : Fin 5 -> Finset K55MinusPerfectMatchingVertex}
    (h : K55BranchSetsWitness B) :
    K55BranchSetsWitness (fun i => (B i).image K55SwapEmbedding) := by
  classical
  rcases h with ⟨hne, hint, hdis, hdom, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨x, hx⟩ := hne i
    exact ⟨K55Swap x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  · intro i x hx hother
    rw [Finset.mem_image] at hx
    rcases hx with ⟨x₀, hx₀, rfl⟩
    obtain ⟨y, hy, hy_ne⟩ := hother
    rw [Finset.mem_image] at hy
    rcases hy with ⟨y₀, hy₀, rfl⟩
    have hy₀_ne : y₀ ≠ x₀ := by
      intro h
      exact hy_ne (by simp [h])
    obtain ⟨z₀, hz₀, hxz₀⟩ := hint i x₀ hx₀ ⟨y₀, hy₀, hy₀_ne⟩
    exact ⟨K55Swap z₀, Finset.mem_image.mpr ⟨z₀, hz₀, rfl⟩, K55Swap_adj hxz₀⟩
  · intro i j hij x hxi hxj
    rw [Finset.mem_image] at hxi hxj
    rcases hxi with ⟨xi, hxi, hxi_eq⟩
    rcases hxj with ⟨xj, hxj, hxj_eq⟩
    have hxij : xi = xj := K55Swap_injective (hxi_eq.trans hxj_eq.symm)
    exact hdis i j hij xi hxi (by simpa [hxij] using hxj)
  · intro i j hij v hv
    rw [Finset.mem_image] at hv
    rcases hv with ⟨v₀, hv₀, rfl⟩
    obtain ⟨u₀, hu₀, huv₀⟩ := hdom i j hij v₀ hv₀
    exact ⟨K55Swap u₀, Finset.mem_image.mpr ⟨u₀, hu₀, rfl⟩, K55Swap_adj huv₀⟩
  · rw [Finset.card_image_of_injective _ K55SwapEmbedding.injective, h3]
  · rw [Finset.card_image_of_injective _ K55SwapEmbedding.injective, h4]

private noncomputable def modelBranchFinset
    (T : DominatingK5Model K55MinusPerfectMatching) (i : Fin 5) :
    Finset K55MinusPerfectMatchingVertex := by
  classical
  exact Finset.univ.filter fun v => v ∈ (T.branch i).verts

private theorem modelBranchFinset_mem
    (T : DominatingK5Model K55MinusPerfectMatching) (i : Fin 5)
    (v : K55MinusPerfectMatchingVertex) :
    v ∈ modelBranchFinset T i ↔ v ∈ (T.branch i).verts := by
  classical
  simp [modelBranchFinset]

private theorem connected_branch_has_internal_neighbor
    (T : DominatingK5Model K55MinusPerfectMatching) (i : Fin 5)
    {x : K55MinusPerfectMatchingVertex}
    (hx : x ∈ (T.branch i).verts)
    (hother : Exists fun y : K55MinusPerfectMatchingVertex =>
      y ∈ (T.branch i).verts ∧ y ≠ x) :
    Exists fun y : K55MinusPerfectMatchingVertex =>
      y ∈ (T.branch i).verts ∧ K55MinusPerfectMatching.Adj x y := by
  classical
  obtain ⟨y, hy, hyx⟩ := hother
  let x' : (T.branch i).verts := ⟨x, hx⟩
  let y' : (T.branch i).verts := ⟨y, hy⟩
  have hxy' : x' ≠ y' := by
    intro h
    exact hyx (congrArg Subtype.val h).symm
  have hreach := T.connected i x' y'
  obtain ⟨z', hxz'⟩ := hreach.nonempty_neighborSet_left hxy'
  exact ⟨z', z'.2,
    SimpleGraph.Subgraph.coe_adj_sub (T.branch i) x' z' hxz'⟩

private theorem modelBranchFinsets_witness
    (T : DominatingK5Model K55MinusPerfectMatching)
    (h3 : BranchIsSingleton T (3 : Fin 5))
    (h4 : BranchIsSingleton T (4 : Fin 5)) :
    K55BranchSetsWitness (modelBranchFinset T) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨v, hv⟩ := (T.connected i).nonempty
    exact ⟨v, (modelBranchFinset_mem T i v).2 hv⟩
  · intro i x hx hother
    have hx' : x ∈ (T.branch i).verts := (modelBranchFinset_mem T i x).1 hx
    have hother' :
        Exists fun y : K55MinusPerfectMatchingVertex =>
          y ∈ (T.branch i).verts ∧ y ≠ x := by
      rcases hother with ⟨y, hy, hyx⟩
      exact ⟨y, (modelBranchFinset_mem T i y).1 hy, hyx⟩
    obtain ⟨y, hy, hxy⟩ := connected_branch_has_internal_neighbor T i hx' hother'
    exact ⟨y, (modelBranchFinset_mem T i y).2 hy, hxy⟩
  · intro i j hij x hxi hxj
    exact (Set.disjoint_left.mp (T.vertex_disjoint i j hij)
      ((modelBranchFinset_mem T i x).1 hxi)) ((modelBranchFinset_mem T j x).1 hxj)
  · intro i j hij v hv
    obtain ⟨u, hu, huv⟩ :=
      T.dominates i j hij v ((modelBranchFinset_mem T j v).1 hv)
    exact ⟨u, (modelBranchFinset_mem T i u).2 hu, huv⟩
  · rcases h3 with ⟨v, hv⟩
    have hfin : modelBranchFinset T (3 : Fin 5) = {v} := by
      ext x
      simp [modelBranchFinset_mem, hv]
    simp [hfin]
  · rcases h4 with ⟨v, hv⟩
    have hfin : modelBranchFinset T (4 : Fin 5) = {v} := by
      ext x
      simp [modelBranchFinset_mem, hv]
    simp [hfin]

private theorem singleton_tail_branches_adjacent
    (T : DominatingK5Model K55MinusPerfectMatching)
    (h3 : BranchIsSingleton T (3 : Fin 5))
    (h4 : BranchIsSingleton T (4 : Fin 5)) :
    Exists fun p : K55MinusPerfectMatchingVertex =>
      Exists fun q : K55MinusPerfectMatchingVertex =>
        (T.branch (3 : Fin 5)).verts = {p} ∧
        (T.branch (4 : Fin 5)).verts = {q} ∧
        K55MinusPerfectMatching.Adj p q := by
  rcases h3 with ⟨p, hp⟩
  rcases h4 with ⟨q, hq⟩
  have hq_mem : q ∈ (T.branch (4 : Fin 5)).verts := by
    simp [hq]
  obtain ⟨u, hu, huq⟩ := T.dominates (3 : Fin 5) (4 : Fin 5) (by decide) q hq_mem
  have hup : u = p := by
    simpa [hp] using hu
  rw [hup] at huq
  exact ⟨p, q, hp, hq, huq⟩

private theorem normalized_initial_branch_card_atLeast_two
    (T : DominatingK5Model K55MinusPerfectMatching)
    (h3 : BranchIsSingleton T (3 : Fin 5))
    (h4 : BranchIsSingleton T (4 : Fin 5))
    (i : Fin 5)
    (hi3 : i < (3 : Fin 5)) :
    2 <= (modelBranchFinset T i).card := by
  classical
  obtain ⟨p, q, hp, hq, hpq⟩ := singleton_tail_branches_adjacent T h3 h4
  have hp_mem : p ∈ (T.branch (3 : Fin 5)).verts := by
    simp [hp]
  have hq_mem : q ∈ (T.branch (4 : Fin 5)).verts := by
    simp [hq]
  obtain ⟨up, hup, hupp⟩ := T.dominates i (3 : Fin 5) hi3 p hp_mem
  have hi4 : i < (4 : Fin 5) := lt_trans hi3 (by decide)
  obtain ⟨uq, huq, huqq⟩ := T.dominates i (4 : Fin 5) hi4 q hq_mem
  have hne : up ≠ uq := by
    intro h
    exact K55_no_common_neighbor_of_adjacent hpq hupp (by simpa [h] using huqq)
  exact (Finset.one_lt_card_iff.mpr
    ⟨up, uq,
      (modelBranchFinset_mem T i up).2 hup,
      (modelBranchFinset_mem T i uq).2 huq, hne⟩)

private abbrev K55AssignedBranch
    (p q : K55MinusPerfectMatchingVertex)
    (a : K55MinusPerfectMatchingVertex -> Option (Fin 3)) :
    Fin 5 -> Finset K55MinusPerfectMatchingVertex
  | 0 => Finset.univ.filter fun v => a v = some (0 : Fin 3)
  | 1 => Finset.univ.filter fun v => a v = some (1 : Fin 3)
  | 2 => Finset.univ.filter fun v => a v = some (2 : Fin 3)
  | 3 => {p}
  | 4 => {q}

private abbrev K55AssignmentWitness
    (p q : K55MinusPerfectMatchingVertex)
    (a : K55MinusPerfectMatchingVertex -> Option (Fin 3)) : Prop :=
  K55BranchSetsWitness (K55AssignedBranch p q a)

private instance K55MinusPerfectMatching.instDecidableRel :
    DecidableRel K55MinusPerfectMatching.Adj := by
  intro x y
  cases x <;> cases y <;> simp [K55MinusPerfectMatching] <;> infer_instance

private def K55BranchSetsWitnessBool
    (B : Fin 5 -> Finset K55MinusPerfectMatchingVertex) : Bool :=
  decide (forall i : Fin 5, (B i).Nonempty) &&
  decide (forall i : Fin 5,
    forall x : K55MinusPerfectMatchingVertex,
      x ∈ B i ->
      (Exists fun y : K55MinusPerfectMatchingVertex => y ∈ B i ∧ y ≠ x) ->
      Exists fun y : K55MinusPerfectMatchingVertex =>
        y ∈ B i ∧ K55MinusPerfectMatching.Adj x y) &&
  decide (forall i j : Fin 5,
    i ≠ j ->
    forall x : K55MinusPerfectMatchingVertex, x ∈ B i -> x ∈ B j -> False) &&
  decide (forall i j : Fin 5,
    i < j ->
    forall v : K55MinusPerfectMatchingVertex,
      v ∈ B j ->
      Exists fun u : K55MinusPerfectMatchingVertex =>
        u ∈ B i ∧ K55MinusPerfectMatching.Adj u v) &&
  decide ((B (3 : Fin 5)).card = 1) &&
  decide ((B (4 : Fin 5)).card = 1)

private theorem K55BranchSetsWitnessBool_eq_true_of_witness
    {B : Fin 5 -> Finset K55MinusPerfectMatchingVertex}
    (h : K55BranchSetsWitness B) :
    K55BranchSetsWitnessBool B = true := by
  rcases h with ⟨hne, hint, hdis, hdom, h3, h4⟩
  have hne_dec := decide_eq_true hne
  have hint_dec := decide_eq_true hint
  have hdis_dec := decide_eq_true hdis
  have hdom_dec := decide_eq_true hdom
  have h3_dec := decide_eq_true h3
  have h4_dec := decide_eq_true h4
  unfold K55BranchSetsWitnessBool
  rw [hne_dec, hint_dec, hdis_dec, hdom_dec, h3_dec, h4_dec]
  rfl

private abbrev K55Remaining
    (p q : K55MinusPerfectMatchingVertex) : Type :=
  {v : K55MinusPerfectMatchingVertex // v ≠ p ∧ v ≠ q}

private abbrev K55AssignedBranchReduced
    (p q : K55MinusPerfectMatchingVertex)
    (a : K55Remaining p q -> Option (Fin 3)) :
    Fin 5 -> Finset K55MinusPerfectMatchingVertex
  | 0 => Finset.univ.filter fun v =>
      if h : v ≠ p ∧ v ≠ q then a ⟨v, h⟩ = some (0 : Fin 3) else False
  | 1 => Finset.univ.filter fun v =>
      if h : v ≠ p ∧ v ≠ q then a ⟨v, h⟩ = some (1 : Fin 3) else False
  | 2 => Finset.univ.filter fun v =>
      if h : v ≠ p ∧ v ≠ q then a ⟨v, h⟩ = some (2 : Fin 3) else False
  | 3 => {p}
  | 4 => {q}

private def fin5List : List (Fin 5) :=
  [0, 1, 2, 3, 4]

private def K55VertexList : List K55MinusPerfectMatchingVertex :=
  fin5List.map Sum.inl ++ fin5List.map Sum.inr

private theorem mem_fin5List (i : Fin 5) : i ∈ fin5List := by
  fin_cases i <;> simp [fin5List]

private theorem mem_K55VertexList (v : K55MinusPerfectMatchingVertex) :
    v ∈ K55VertexList := by
  cases v with
  | inl i =>
      simp [K55VertexList, mem_fin5List i]
  | inr i =>
      simp [K55VertexList, mem_fin5List i]

private def K55FastBranchWitnessBool
    (B : Fin 5 -> Finset K55MinusPerfectMatchingVertex) : Bool :=
  let vertices := K55VertexList
  let indices := fin5List
  indices.all (fun i =>
    vertices.any (fun x => decide (x ∈ B i))) &&
  indices.all (fun i =>
    vertices.all (fun x =>
      (!decide (x ∈ B i)) ||
        (!vertices.any (fun y => decide (y ∈ B i ∧ y ≠ x))) ||
          vertices.any (fun y => decide (y ∈ B i ∧ K55MinusPerfectMatching.Adj x y)))) &&
  indices.all (fun i =>
    indices.all (fun j =>
      decide (i = j) ||
        vertices.all (fun x =>
          (!decide (x ∈ B i)) || (!decide (x ∈ B j))))) &&
  indices.all (fun i =>
    indices.all (fun j =>
      (!decide (i < j)) ||
        vertices.all (fun v =>
          (!decide (v ∈ B j)) ||
            vertices.any (fun u =>
              decide (u ∈ B i ∧ K55MinusPerfectMatching.Adj u v))))) &&
  decide ((B (3 : Fin 5)).card = 1) &&
  decide ((B (4 : Fin 5)).card = 1)

private theorem K55FastBranchWitnessBool_eq_true_of_witness
    {B : Fin 5 -> Finset K55MinusPerfectMatchingVertex}
    (h : K55BranchSetsWitness B) :
    K55FastBranchWitnessBool B = true := by
  classical
  rcases h with ⟨hne, hint, hdis, hdom, h3, h4⟩
  unfold K55FastBranchWitnessBool
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro i _hi
    obtain ⟨x, hx⟩ := hne i
    rw [List.any_eq_true]
    exact ⟨x, mem_K55VertexList x, decide_eq_true hx⟩
  · rw [List.all_eq_true]
    intro i _hi
    rw [List.all_eq_true]
    intro x _hx
    by_cases hxi : x ∈ B i
    · by_cases hother : Exists fun y : K55MinusPerfectMatchingVertex => y ∈ B i ∧ y ≠ x
      · obtain ⟨y, hy, hxy⟩ := hint i x hxi hother
        have hany :
            (K55VertexList.any fun y => decide (y ∈ B i ∧ K55MinusPerfectMatching.Adj x y)) = true := by
          rw [List.any_eq_true]
          exact ⟨y, mem_K55VertexList y, decide_eq_true ⟨hy, hxy⟩⟩
        rw [hany]
        simp [decide_eq_true hxi]
      · have hno :
            (K55VertexList.any fun y => decide (y ∈ B i ∧ y ≠ x)) = false := by
          rw [Bool.eq_false_iff]
          intro hany
          rw [List.any_eq_true] at hany
          rcases hany with ⟨y, _hyList, hy⟩
          exact hother ⟨y, of_decide_eq_true hy⟩
        rw [hno]
        simp [decide_eq_true hxi]
    · simp [decide_eq_false_iff_not.mpr hxi]
  · rw [List.all_eq_true]
    intro i _hi
    rw [List.all_eq_true]
    intro j _hj
    by_cases hij : i = j
    · simp [decide_eq_true hij]
    · rw [decide_eq_false_iff_not.mpr hij]
      simp only [Bool.false_or]
      rw [List.all_eq_true]
      intro x _hx
      by_cases hxi : x ∈ B i
      · have hxj : x ∉ B j := by
          intro hxj
          exact hdis i j hij x hxi hxj
        simp [decide_eq_true hxi, decide_eq_false_iff_not.mpr hxj]
      · simp [decide_eq_false_iff_not.mpr hxi]
  · rw [List.all_eq_true]
    intro i _hi
    rw [List.all_eq_true]
    intro j _hj
    by_cases hij : i < j
    · rw [decide_eq_true hij]
      simp only [Bool.not_true, Bool.false_or]
      rw [List.all_eq_true]
      intro v _hv
      by_cases hvj : v ∈ B j
      · obtain ⟨u, hu, huv⟩ := hdom i j hij v hvj
        have hany :
            (K55VertexList.any fun u => decide (u ∈ B i ∧ K55MinusPerfectMatching.Adj u v)) = true := by
          rw [List.any_eq_true]
          exact ⟨u, mem_K55VertexList u, decide_eq_true ⟨hu, huv⟩⟩
        rw [hany]
        simp [decide_eq_true hvj]
      · simp [decide_eq_false_iff_not.mpr hvj]
    · simp [decide_eq_false_iff_not.mpr hij]
  · exact decide_eq_true h3
  · exact decide_eq_true h4

private def fin3AsFin5 (i : Fin 3) : Fin 5 :=
  ⟨i.1, Nat.lt_trans i.2 (by decide)⟩

private theorem fin3AsFin5_injective : Function.Injective fin3AsFin5 := by
  intro i j h
  apply Fin.ext
  simpa [fin3AsFin5] using congrArg Fin.val h

private theorem fin3AsFin5_lt_three (i : Fin 3) :
    fin3AsFin5 i < (3 : Fin 5) := by
  change i.1 < 3
  exact i.2

private theorem K55_reduced_no_solution :
    Not (Exists fun α : Fin 3 -> Fin 3 =>
      Exists fun β : Fin 3 -> Fin 3 =>
      Exists fun leftExtra : Option (Fin 3) =>
      Exists fun rightExtra : Option (Fin 3) =>
        Function.Injective α ∧ Function.Injective β ∧
        (forall i : Fin 3, α i = β i -> leftExtra = some i ∧ rightExtra = some i) ∧
        (forall i j : Fin 3, i < j -> β i = α j -> rightExtra = some i) ∧
        (forall i j : Fin 3, i < j -> α i = β j -> leftExtra = some i)) := by
  decide

private def K55RemainingIndex (a b c : Fin 5) : Fin 3 :=
  ⟨(c.1 - (if a.1 < c.1 then 1 else 0) -
      (if b.1 < c.1 then 1 else 0)) % 3, Nat.mod_lt _ (by decide)⟩

private theorem K55RemainingIndex_injective
    {a b c d : Fin 5}
    (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b)
    (h : K55RemainingIndex a b c = K55RemainingIndex a b d) :
    c = d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [K55RemainingIndex] at hab hca hcb hda hdb h ⊢

private theorem K55BranchSetsWitness_impossible_left_right
    {B : Fin 5 -> Finset K55MinusPerfectMatchingVertex}
    {a b : Fin 5}
    (hab : a ≠ b)
    (h3eq : B (3 : Fin 5) = {Sum.inl a})
    (h4eq : B (4 : Fin 5) = {Sum.inr b})
    (h : K55BranchSetsWitness B) :
    False := by
  classical
  rcases h with ⟨_hne, hint, hdis, hdom, _h3, _h4⟩
  let idx : Fin 3 -> Fin 5 := fin3AsFin5
  have hidx_inj : Function.Injective idx := fin3AsFin5_injective
  have hidx_lt_three : forall i : Fin 3, idx i < (3 : Fin 5) := fin3AsFin5_lt_three
  have hidx_lt_four : forall i : Fin 3, idx i < (4 : Fin 5) := by
    intro i
    exact lt_trans (hidx_lt_three i) (by decide)
  have hidx_ne_three : forall i : Fin 3, idx i ≠ (3 : Fin 5) := by
    intro i h
    exact (ne_of_lt (hidx_lt_three i)) h
  have hidx_ne_four : forall i : Fin 3, idx i ≠ (4 : Fin 5) := by
    intro i h
    exact (ne_of_lt (hidx_lt_four i)) h
  have hp_mem : Sum.inl a ∈ B (3 : Fin 5) := by
    simp [h3eq]
  have hq_mem : Sum.inr b ∈ B (4 : Fin 5) := by
    simp [h4eq]
  have hleft : forall i : Fin 3,
      Exists fun c : Fin 5 =>
        Sum.inl c ∈ B (idx i) ∧ c ≠ a ∧ c ≠ b := by
    intro i
    obtain ⟨u, hu, huq⟩ := hdom (idx i) (4 : Fin 5) (hidx_lt_four i) (Sum.inr b) hq_mem
    obtain ⟨c, rfl, hcb⟩ := K55_neighbor_of_right huq
    have hca : c ≠ a := by
      intro hca
      have hmem3 : Sum.inl c ∈ B (3 : Fin 5) := by
        simp [h3eq, hca]
      exact hdis (idx i) (3 : Fin 5) (hidx_ne_three i) (Sum.inl c) hu hmem3
    exact ⟨c, hu, hca, hcb⟩
  have hright : forall i : Fin 3,
      Exists fun c : Fin 5 =>
        Sum.inr c ∈ B (idx i) ∧ c ≠ a ∧ c ≠ b := by
    intro i
    obtain ⟨u, hu, hup⟩ := hdom (idx i) (3 : Fin 5) (hidx_lt_three i) (Sum.inl a) hp_mem
    obtain ⟨c, rfl, hca⟩ := K55_neighbor_of_left hup
    have hcb : c ≠ b := by
      intro hcb
      have hmem4 : Sum.inr c ∈ B (4 : Fin 5) := by
        simp [h4eq, hcb]
      exact hdis (idx i) (4 : Fin 5) (hidx_ne_four i) (Sum.inr c) hu hmem4
    exact ⟨c, hu, hca, hcb⟩
  choose α hα using hleft
  choose β hβ using hright
  have hαB : forall i : Fin 3, Sum.inl (α i) ∈ B (idx i) := fun i => (hα i).1
  have hα_ne_a : forall i : Fin 3, α i ≠ a := fun i => (hα i).2.1
  have hα_ne_b : forall i : Fin 3, α i ≠ b := fun i => (hα i).2.2
  have hβB : forall i : Fin 3, Sum.inr (β i) ∈ B (idx i) := fun i => (hβ i).1
  have hβ_ne_a : forall i : Fin 3, β i ≠ a := fun i => (hβ i).2.1
  have hβ_ne_b : forall i : Fin 3, β i ≠ b := fun i => (hβ i).2.2
  have hα_inj : Function.Injective α := by
    intro i j hij
    by_contra hne
    have hidx_ne : idx i ≠ idx j := fun hidx => hne (hidx_inj hidx)
    have hmemj : Sum.inl (α i) ∈ B (idx j) := by
      simpa [hij] using hαB j
    exact hdis (idx i) (idx j) hidx_ne (Sum.inl (α i)) (hαB i) hmemj
  have hβ_inj : Function.Injective β := by
    intro i j hij
    by_contra hne
    have hidx_ne : idx i ≠ idx j := fun hidx => hne (hidx_inj hidx)
    have hmemj : Sum.inr (β i) ∈ B (idx j) := by
      simpa [hij] using hβB j
    exact hdis (idx i) (idx j) hidx_ne (Sum.inr (β i)) (hβB i) hmemj
  let αr : Fin 3 -> Fin 3 := fun i => K55RemainingIndex a b (α i)
  let βr : Fin 3 -> Fin 3 := fun i => K55RemainingIndex a b (β i)
  have hαr_inj : Function.Injective αr := by
    intro i j hij
    apply hα_inj
    exact K55RemainingIndex_injective hab (hα_ne_a i) (hα_ne_b i)
      (hα_ne_a j) (hα_ne_b j) hij
  have hβr_inj : Function.Injective βr := by
    intro i j hij
    apply hβ_inj
    exact K55RemainingIndex_injective hab (hβ_ne_a i) (hβ_ne_b i)
      (hβ_ne_a j) (hβ_ne_b j) hij
  have hαr_surj : Function.Surjective αr :=
    hαr_inj.surjective_of_finite (Equiv.refl (Fin 3))
  have hβr_surj : Function.Surjective βr :=
    hβr_inj.surjective_of_finite (Equiv.refl (Fin 3))
  let leftExtra : Option (Fin 3) :=
    if h : Exists fun i : Fin 3 => Sum.inl b ∈ B (idx i) then some h.choose else none
  let rightExtra : Option (Fin 3) :=
    if h : Exists fun i : Fin 3 => Sum.inr a ∈ B (idx i) then some h.choose else none
  have hleftExtra_eq_some_of_mem :
      forall i : Fin 3, Sum.inl b ∈ B (idx i) -> leftExtra = some i := by
    intro i hmem
    have hex : Exists fun j : Fin 3 => Sum.inl b ∈ B (idx j) := ⟨i, hmem⟩
    have hchoose_eq : hex.choose = i := by
      by_contra hne
      have hidx_ne : idx hex.choose ≠ idx i := fun hidx => hne (hidx_inj hidx)
      exact hdis (idx hex.choose) (idx i) hidx_ne (Sum.inl b) hex.choose_spec hmem
    dsimp [leftExtra]
    rw [dif_pos hex]
    exact congrArg some hchoose_eq
  have hrightExtra_eq_some_of_mem :
      forall i : Fin 3, Sum.inr a ∈ B (idx i) -> rightExtra = some i := by
    intro i hmem
    have hex : Exists fun j : Fin 3 => Sum.inr a ∈ B (idx j) := ⟨i, hmem⟩
    have hchoose_eq : hex.choose = i := by
      by_contra hne
      have hidx_ne : idx hex.choose ≠ idx i := fun hidx => hne (hidx_inj hidx)
      exact hdis (idx hex.choose) (idx i) hidx_ne (Sum.inr a) hex.choose_spec hmem
    dsimp [rightExtra]
    rw [dif_pos hex]
    exact congrArg some hchoose_eq
  have hright_mem_eq_a_of_ne_forced :
      forall {i : Fin 3} {r : Fin 5},
        Sum.inr r ∈ B (idx i) -> r ≠ β i -> r = a := by
    intro i r hrmem hr_ne_forced
    by_contra hra
    have hrb : r ≠ b := by
      intro hrb
      have hmem4 : Sum.inr r ∈ B (4 : Fin 5) := by
        simp [h4eq, hrb]
      exact hdis (idx i) (4 : Fin 5) (hidx_ne_four i) (Sum.inr r) hrmem hmem4
    obtain ⟨j, hj⟩ := hβr_surj (K55RemainingIndex a b r)
    have hβjr : β j = r :=
      K55RemainingIndex_injective hab (hβ_ne_a j) (hβ_ne_b j) hra hrb hj
    by_cases hji : j = i
    · exact hr_ne_forced (by simpa [hji] using hβjr.symm)
    · have hidx_ne : idx i ≠ idx j := by
        intro hidx
        exact hji (hidx_inj hidx).symm
      have hmemj : Sum.inr r ∈ B (idx j) := by
        simpa [hβjr] using hβB j
      exact hdis (idx i) (idx j) hidx_ne (Sum.inr r) hrmem hmemj
  have hleft_mem_eq_b_of_ne_forced :
      forall {i : Fin 3} {r : Fin 5},
        Sum.inl r ∈ B (idx i) -> r ≠ α i -> r = b := by
    intro i r hrmem hr_ne_forced
    by_contra hrb
    have hra : r ≠ a := by
      intro hra
      have hmem3 : Sum.inl r ∈ B (3 : Fin 5) := by
        simp [h3eq, hra]
      exact hdis (idx i) (3 : Fin 5) (hidx_ne_three i) (Sum.inl r) hrmem hmem3
    obtain ⟨j, hj⟩ := hαr_surj (K55RemainingIndex a b r)
    have hαjr : α j = r :=
      K55RemainingIndex_injective hab (hα_ne_a j) (hα_ne_b j) hra hrb hj
    by_cases hji : j = i
    · exact hr_ne_forced (by simpa [hji] using hαjr.symm)
    · have hidx_ne : idx i ≠ idx j := by
        intro hidx
        exact hji (hidx_inj hidx).symm
      have hmemj : Sum.inl r ∈ B (idx j) := by
        simpa [hαjr] using hαB j
      exact hdis (idx i) (idx j) hidx_ne (Sum.inl r) hrmem hmemj
  have hconn :
      forall i : Fin 3, αr i = βr i -> leftExtra = some i ∧ rightExtra = some i := by
    intro i hir
    have hαβ : α i = β i :=
      K55RemainingIndex_injective hab (hα_ne_a i) (hα_ne_b i)
        (hβ_ne_a i) (hβ_ne_b i) hir
    have hother_left :
        Exists fun y : K55MinusPerfectMatchingVertex =>
          y ∈ B (idx i) ∧ y ≠ Sum.inl (α i) := by
      exact ⟨Sum.inr (β i), hβB i, by simp⟩
    obtain ⟨y, hyB, hyadj⟩ := hint (idx i) (Sum.inl (α i)) (hαB i) hother_left
    obtain ⟨r, hyr, hr_ne_α⟩ := K55_neighbor_of_left hyadj.symm
    subst y
    have hra : r = a :=
      hright_mem_eq_a_of_ne_forced hyB (by simpa [hαβ] using hr_ne_α)
    have hright_mem : Sum.inr a ∈ B (idx i) := by
      simpa [hra] using hyB
    have hother_right :
        Exists fun y : K55MinusPerfectMatchingVertex =>
          y ∈ B (idx i) ∧ y ≠ Sum.inr (β i) := by
      exact ⟨Sum.inl (α i), hαB i, by simp⟩
    obtain ⟨y, hyB, hyadj⟩ := hint (idx i) (Sum.inr (β i)) (hβB i) hother_right
    obtain ⟨r, hyr, hr_ne_β⟩ := K55_neighbor_of_right hyadj.symm
    subst y
    have hrb : r = b :=
      hleft_mem_eq_b_of_ne_forced hyB (by simpa [hαβ] using hr_ne_β)
    have hleft_mem : Sum.inl b ∈ B (idx i) := by
      simpa [hrb] using hyB
    exact ⟨hleftExtra_eq_some_of_mem i hleft_mem,
      hrightExtra_eq_some_of_mem i hright_mem⟩
  have hdom_right :
      forall i j : Fin 3, i < j -> βr i = αr j -> rightExtra = some i := by
    intro i j hij hir
    have hβα : β i = α j :=
      K55RemainingIndex_injective hab (hβ_ne_a i) (hβ_ne_b i)
        (hα_ne_a j) (hα_ne_b j) hir
    have hidx_lt : idx i < idx j := by
      change i.1 < j.1
      exact hij
    obtain ⟨u, huB, huadj⟩ := hdom (idx i) (idx j) hidx_lt (Sum.inl (α j)) (hαB j)
    obtain ⟨r, hur, hr_ne⟩ := K55_neighbor_of_left huadj
    subst u
    have hra : r = a :=
      hright_mem_eq_a_of_ne_forced huB (by simpa [hβα] using hr_ne)
    exact hrightExtra_eq_some_of_mem i (by simpa [hra] using huB)
  have hdom_left :
      forall i j : Fin 3, i < j -> αr i = βr j -> leftExtra = some i := by
    intro i j hij hir
    have hαβ : α i = β j :=
      K55RemainingIndex_injective hab (hα_ne_a i) (hα_ne_b i)
        (hβ_ne_a j) (hβ_ne_b j) hir
    have hidx_lt : idx i < idx j := by
      change i.1 < j.1
      exact hij
    obtain ⟨u, huB, huadj⟩ := hdom (idx i) (idx j) hidx_lt (Sum.inr (β j)) (hβB j)
    obtain ⟨r, hur, hr_ne⟩ := K55_neighbor_of_right huadj
    subst u
    have hrb : r = b :=
      hleft_mem_eq_b_of_ne_forced huB (by simpa [hαβ] using hr_ne)
    exact hleftExtra_eq_some_of_mem i (by simpa [hrb] using huB)
  exact K55_reduced_no_solution
    ⟨αr, βr, leftExtra, rightExtra, hαr_inj, hβr_inj, hconn, hdom_right, hdom_left⟩

private theorem K55MinusPerfectMatching_degree_eq_four
    (v : K55MinusPerfectMatchingVertex) :
    K55MinusPerfectMatching.degree v = 4 := by
  fin_cases v <;> decide

private def next5 : Fin 5 -> Fin 5
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 0

private theorem next5_injective : Function.Injective next5 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [next5] at h ⊢

private theorem next5_ne (i : Fin 5) : next5 i ≠ i := by
  fin_cases i <;> decide

private theorem next5_cross_or (i j : Fin 5) (hij : i ≠ j) :
    i ≠ next5 j ∨ j ≠ next5 i := by
  fin_cases i <;> fin_cases j <;> simp [next5] at hij ⊢

private theorem K55_branch_adj (i : Fin 5) :
    K55MinusPerfectMatching.Adj (Sum.inl i) (Sum.inr (next5 i)) := by
  have h : i ≠ next5 i := (next5_ne i).symm
  simpa [K55MinusPerfectMatching] using h

private def K55Branch (i : Fin 5) : K55MinusPerfectMatching.Subgraph :=
  K55MinusPerfectMatching.subgraphOfAdj (K55_branch_adj i)

theorem K55_minus_matching_has_K5_minor :
    ContainsMinor K5Graph K55MinusPerfectMatching := by
  refine ⟨{
    branch := K55Branch
    connected := ?_
    nonempty := ?_
    vertex_disjoint := ?_
    edge_realized := ?_
  }⟩
  · intro i
    exact (SimpleGraph.Subgraph.subgraphOfAdj_connected
      (K55_branch_adj i)).coe
  · intro i
    exact ⟨Sum.inl i, by simp [K55Branch]⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hx hy
    cases x with
    | inl k =>
        have hki : k = i := by
          simpa [K55Branch] using hx
        have hkj : k = j := by
          simpa [K55Branch] using hy
        exact hij (hki.symm.trans hkj)
    | inr k =>
        have hki : k = next5 i := by
          simpa [K55Branch] using hx
        have hkj : k = next5 j := by
          simpa [K55Branch] using hy
        exact hij (next5_injective (hki.symm.trans hkj))
  · intro i j hij
    rcases next5_cross_or i j hij.ne with hleft | hright
    · refine ⟨Sum.inl i, Sum.inr (next5 j), ?_, ?_, ?_⟩
      · simp [K55Branch]
      · simp [K55Branch]
      · simpa [K55MinusPerfectMatching] using hleft
    · refine ⟨Sum.inr (next5 i), Sum.inl j, ?_, ?_, ?_⟩
      · simp [K55Branch]
      · simp [K55Branch]
      · simpa [K55MinusPerfectMatching] using hright

theorem K55_minus_matching_has_no_dominating_K5 :
    HasNoDominatingKModel K55MinusPerfectMatching 5 := by
  rintro ⟨T⟩
  obtain ⟨T', h3, h4⟩ := dominating_K5_model_with_last_two_singletons T
  have hwit : K55BranchSetsWitness (modelBranchFinset T') :=
    modelBranchFinsets_witness T' h3 h4
  obtain ⟨p, q, hp, hq, hpq⟩ := singleton_tail_branches_adjacent T' h3 h4
  have hB3eq : modelBranchFinset T' (3 : Fin 5) = {p} := by
    ext x
    simp [modelBranchFinset_mem, hp]
  have hB4eq : modelBranchFinset T' (4 : Fin 5) = {q} := by
    ext x
    simp [modelBranchFinset_mem, hq]
  cases p with
  | inl a =>
      cases q with
      | inl b =>
          exact False.elim (K55_not_adj_left_left a b hpq)
      | inr b =>
          have hab : a ≠ b := (K55_adj_left_right_iff a b).1 hpq
          exact K55BranchSetsWitness_impossible_left_right hab hB3eq hB4eq hwit
  | inr a =>
      cases q with
      | inl b =>
          have hab : a ≠ b := (K55_adj_right_left_iff a b).1 hpq
          let Bswap : Fin 5 -> Finset K55MinusPerfectMatchingVertex :=
            fun i => (modelBranchFinset T' i).image K55SwapEmbedding
          have hswap : K55BranchSetsWitness Bswap := by
            simpa [Bswap] using K55BranchSetsWitness_swap hwit
          have hB3swap : Bswap (3 : Fin 5) = {Sum.inl a} := by
            ext x
            cases x <;> simp [Bswap, K55SwapEmbedding, K55Swap, hB3eq]
          have hB4swap : Bswap (4 : Fin 5) = {Sum.inr b} := by
            ext x
            cases x <;> simp [Bswap, K55SwapEmbedding, K55Swap, hB4eq]
          exact K55BranchSetsWitness_impossible_left_right hab hB3swap hB4swap hswap
      | inr b =>
          exact False.elim (K55_not_adj_right_right a b hpq)

end Schematic.Math.GraphTheory
