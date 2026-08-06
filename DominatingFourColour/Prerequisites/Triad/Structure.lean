import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Schematic.Math.GraphTheory.Minors.Society.ThreeBoundary
import DominatingFourColour.Basic

/-!
Cited graph-theoretic inputs used by the article but not proved in it.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

structure Triad (G : SimpleGraph V) (feet : Fin 3 -> V) where
  apex : V
  apex_not_foot : forall i : Fin 3, apex ≠ feet i
  leg : forall i : Fin 3, G.Walk apex (feet i)
  leg_isPath : forall i : Fin 3, (leg i).IsPath
  apex_only_common_vertex :
    forall i j : Fin 3, i ≠ j ->
      Disjoint (Walk.InternalVertices (leg i)) (Walk.InternalVertices (leg j))
  internal_vertices_avoid_feet :
    forall i j : Fin 3, feet i ∉ Walk.InternalVertices (leg j)

def Triad.vertexSet {feet : Fin 3 -> V} (T : Triad G feet) : Set V :=
  {v | Exists fun i : Fin 3 => v ∈ (T.leg i).support}

def Triad.carrier {feet : Fin 3 -> V} (T : Triad G feet) : G.Subgraph :=
  ⨆ i : Fin 3, (T.leg i).toSubgraph

theorem Triad.mem_carrier_edgeSet_iff
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {e : Sym2 V} :
    e ∈ T.carrier.edgeSet ↔
      Exists fun i : Fin 3 => e ∈ (T.leg i).toSubgraph.edgeSet := by
  rw [Triad.carrier, SimpleGraph.Subgraph.edgeSet_iSup]
  constructor
  · intro he
    simpa using (Set.mem_iUnion.mp he)
  · rintro ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

def Triad.Lean {feet : Fin 3 -> V} (T : Triad G feet) : Prop :=
  forall T' : Triad G feet, T'.vertexSet ⊆ T.vertexSet -> T.vertexSet ⊆ T'.vertexSet

theorem Triad.not_lean_of_contained_triad_omits_vertex
    {feet : Fin 3 -> V}
    (T T' : Triad G feet)
    (hsubset : T'.vertexSet ⊆ T.vertexSet)
    {z : V}
    (hzT : z ∈ T.vertexSet)
    (hzT' : z ∉ T'.vertexSet) :
    ¬ T.Lean := by
  intro hlean
  exact hzT' (hlean T' hsubset hzT)

theorem Triad.not_lean_of_contained_triad_omits_apex
    {feet : Fin 3 -> V}
    (T T' : Triad G feet)
    (hsubset : T'.vertexSet ⊆ T.vertexSet)
    (hapex : T.apex ∉ T'.vertexSet) :
    ¬ T.Lean :=
  T.not_lean_of_contained_triad_omits_vertex T' hsubset
    ⟨0, (T.leg 0).start_mem_support⟩ hapex

theorem fin3_eq_of_ne_ne
    {i j k l : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    (hli : l ≠ i)
    (hlj : l ≠ j) :
    l = k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp at *

theorem fin3_exists_ne_ne
    {i j : Fin 3}
    (hij : i ≠ j) :
    Exists fun k : Fin 3 => i ≠ k ∧ j ≠ k := by
  fin_cases i <;> fin_cases j <;> simp at *
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

namespace Fin3

theorem forall_of_three
    {P : Fin 3 -> Prop}
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    (hi : P i)
    (hj : P j)
    (hk : P k) :
    forall l : Fin 3, P l := by
  intro l
  by_cases hli : l = i
  · simpa [hli] using hi
  by_cases hlj : l = j
  · simpa [hlj] using hj
  have hlk : l = k := fin3_eq_of_ne_ne hij hik hjk hli hlj
  simpa [hlk] using hk

theorem pairwise_disjoint_of_three
    {α : Type*}
    {S : Fin 3 -> Set α}
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    (hdis_ij : Disjoint (S i) (S j))
    (hdis_ik : Disjoint (S i) (S k))
    (hdis_jk : Disjoint (S j) (S k)) :
    forall l m : Fin 3, l ≠ m -> Disjoint (S l) (S m) := by
  intro l m hlm
  by_cases hli : l = i
  · subst l
    by_cases hmj : m = j
    · simpa [hmj] using hdis_ij
    have hmi : m ≠ i := fun h => hlm h.symm
    have hmk : m = k := fin3_eq_of_ne_ne hij hik hjk hmi hmj
    simpa [hmk] using hdis_ik
  by_cases hlj : l = j
  · subst l
    by_cases hmi : m = i
    · simpa [hmi] using hdis_ij.symm
    have hmj : m ≠ j := fun h => hlm h.symm
    have hmk : m = k := fin3_eq_of_ne_ne hij hik hjk hmi hmj
    simpa [hmk] using hdis_jk
  have hlk : l = k := fin3_eq_of_ne_ne hij hik hjk hli hlj
  subst l
  by_cases hmi : m = i
  · simpa [hmi] using hdis_ik.symm
  by_cases hmj : m = j
  · simpa [hmj] using hdis_jk.symm
  have hmk : m = k := fin3_eq_of_ne_ne hij hik hjk hmi hmj
  exact False.elim (hlm hmk.symm)

theorem pairwise_disjoint_update
    {α ι : Type*}
    [DecidableEq ι]
    (S : ι -> Set α)
    (i : ι)
    (replacement : Set α)
    (hS : forall j k : ι, j ≠ k -> Disjoint (S j) (S k))
    (hreplacement : forall j : ι, j ≠ i -> Disjoint replacement (S j)) :
    forall j k : ι, j ≠ k ->
      Disjoint (if j = i then replacement else S j)
        (if k = i then replacement else S k) := by
  intro j k hjk
  by_cases hji : j = i
  · subst j
    have hki : k ≠ i := fun h => hjk h.symm
    simpa [hki] using hreplacement k hki
  by_cases hki : k = i
  · subst k
    simpa [hji] using (hreplacement j hji).symm
  simpa [hji, hki] using hS j k hjk

theorem sum_lt_of_update
    (f f' : Fin 3 -> Nat)
    (i : Fin 3)
    (hlt : f' i < f i)
    (heq : forall j : Fin 3, j ≠ i -> f' j = f j) :
    f' 0 + f' 1 + f' 2 < f 0 + f 1 + f 2 := by
  fin_cases i
  · rw [heq 1 (by decide), heq 2 (by decide)]
    exact Nat.add_lt_add_right
      (Nat.add_lt_add_right hlt (f 1)) (f 2)
  · rw [heq 0 (by decide), heq 2 (by decide)]
    exact Nat.add_lt_add_right
      (Nat.add_lt_add_left hlt (f 0)) (f 2)
  · rw [heq 0 (by decide), heq 1 (by decide), Nat.add_assoc, Nat.add_assoc]
    exact Nat.add_lt_add_left
      (Nat.add_lt_add_left hlt (f 1)) (f 0)

end Fin3

theorem fin3_range_eq_insert (f : Fin 3 -> V) :
    Set.range f = ({f 0, f 1, f 2} : Set V) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hx.symm⟩
    · exact ⟨2, hx.symm⟩

theorem ncard_le_three_of_subset_range_feet
    [Fintype V]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    {S : Set V}
    (hS : S ⊆ Set.range feet) :
    S.ncard <= 3 := by
  calc
    S.ncard <= (Set.range feet).ncard := Set.ncard_le_ncard hS
    _ = 3 := ncard_range_fin3_of_injective hfeet_injective

theorem exists_nonfoot_of_ncard_ge_four
    [Fintype V]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    {S : Set V}
    (hS_card : 4 <= S.ncard) :
    Exists fun x : V => x ∈ S ∧ x ∉ Set.range feet := by
  classical
  by_contra hnone
  have hS_subset : S ⊆ Set.range feet := by
    intro x hxS
    by_contra hxfeet
    exact hnone ⟨x, hxS, hxfeet⟩
  have hle : S.ncard <= 3 :=
    ncard_le_three_of_subset_range_feet hfeet_injective hS_subset
  omega

structure RSTLeanTriadData (G : SimpleGraph V) (feet : Fin 3 -> V) (root : V) where
  triad : Triad G feet
  lean : triad.Lean
  complement_connected : (G.induce triad.vertexSetᶜ).Connected
  root_outside : root ∉ triad.vertexSet
  inside_neighbors_at_most_three :
    forall v : V,
      v ∈ (triad.carrier.deleteVerts (Set.range feet)).verts ->
        (G.neighborSet v ∩ triad.vertexSet).ncard <= 3
  foot_has_neighbor_outside :
    forall i : Fin 3,
      Exists fun u : V =>
        u ∈ ((⊤ : G.Subgraph).deleteVerts triad.vertexSet).verts ∧
          G.Adj u (feet i)

theorem Triad.apex_mem_vertexSet {feet : Fin 3 -> V} (T : Triad G feet) :
    T.apex ∈ T.vertexSet := by
  exact ⟨0, (T.leg 0).start_mem_support⟩

theorem Triad.foot_mem_vertexSet {feet : Fin 3 -> V} (T : Triad G feet) (i : Fin 3) :
    feet i ∈ T.vertexSet := by
  exact ⟨i, (T.leg i).end_mem_support⟩

theorem Triad.insert_apex_range_subset_vertexSet
    {feet : Fin 3 -> V}
    (T : Triad G feet) :
    insert T.apex (Set.range feet) ⊆ T.vertexSet := by
  intro v hv
  rw [Set.mem_insert_iff] at hv
  rcases hv with rfl | ⟨i, rfl⟩
  · exact T.apex_mem_vertexSet
  · exact T.foot_mem_vertexSet i

theorem Triad.vertexSet_ncard_ge_four
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet) :
    4 <= T.vertexSet.ncard := by
  classical
  have hapex_not_range : T.apex ∉ Set.range feet := by
    rintro ⟨i, hi⟩
    exact T.apex_not_foot i hi.symm
  have hrange : (Set.range feet).ncard = 3 :=
    ncard_range_fin3_of_injective hfeet_injective
  have hinsert_card :
      (insert T.apex (Set.range feet)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem hapex_not_range]
    omega
  have hle :
      (insert T.apex (Set.range feet)).ncard <= T.vertexSet.ncard :=
    Set.ncard_le_ncard (T.insert_apex_range_subset_vertexSet)
  omega

theorem Triad.foot_mem_leg_support_iff
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    (i j : Fin 3) :
    feet i ∈ (T.leg j).support ↔ i = j := by
  constructor
  · intro hmem
    by_contra hij
    have hne_end : feet i ≠ feet j := by
      intro hfeet
      exact hij (hfeet_injective hfeet)
    have hinternal : feet i ∈ Walk.InternalVertices (T.leg j) :=
      ⟨hmem, (T.apex_not_foot i).symm, hne_end⟩
    exact T.internal_vertices_avoid_feet i j hinternal
  · intro hij
    subst j
    exact (T.leg i).end_mem_support

theorem Triad.diff_leg_support_inter_eq_apex
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j : Fin 3}
    (hij : i ≠ j)
    {v : V}
    (hvi : v ∈ (T.leg i).support)
    (hvj : v ∈ (T.leg j).support) :
    v = T.apex := by
  by_cases hvapex : v = T.apex
  · exact hvapex
  · exfalso
    have hvi_not_foot : v ≠ feet i := by
      intro hvfoot
      subst v
      have hidx : i = j :=
        (T.foot_mem_leg_support_iff hfeet_injective i j).mp hvj
      exact hij hidx
    have hvj_not_foot : v ≠ feet j := by
      intro hvfoot
      subst v
      have hidx : j = i :=
        (T.foot_mem_leg_support_iff hfeet_injective j i).mp hvi
      exact hij hidx.symm
    have hvi_internal : v ∈ Walk.InternalVertices (T.leg i) :=
      ⟨hvi, hvapex, hvi_not_foot⟩
    have hvj_internal : v ∈ Walk.InternalVertices (T.leg j) :=
      ⟨hvj, hvapex, hvj_not_foot⟩
    exact Set.disjoint_left.mp (T.apex_only_common_vertex i j hij)
      hvi_internal hvj_internal

theorem Triad.internal_ne_foot
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {i : Fin 3}
    {v : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i))
    (j : Fin 3) :
    v ≠ feet j := by
  intro hvfoot
  exact T.internal_vertices_avoid_feet j i (by simpa [hvfoot] using hv)

theorem Triad.internal_not_mem_other_leg_support
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (hfeet_injective : Function.Injective feet)
    {i j : Fin 3}
    (hij : i ≠ j)
    {v : V}
    (hv : v ∈ Walk.InternalVertices (T.leg i)) :
    v ∉ (T.leg j).support := by
  intro hvj
  exact hv.2.1
    (T.diff_leg_support_inter_eq_apex hfeet_injective hij hv.1 hvj)

theorem Triad.vertexSet_subset_of_leg_toSubgraph_le
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {H : G.Subgraph}
    (hleg_le : forall i : Fin 3, (T.leg i).toSubgraph ≤ H) :
    T.vertexSet ⊆ H.verts := by
  rintro v ⟨i, hv⟩
  exact Walk.support_subset_of_toSubgraph_le (hleg_le i) hv

end Schematic.Math.GraphTheory
