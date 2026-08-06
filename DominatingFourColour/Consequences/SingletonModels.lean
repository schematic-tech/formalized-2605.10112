import DominatingFourColour.Basic

/-!
Model-level consequences about singleton branch sets.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

structure ThirdBranchPathAndTailInducedCycleData
    {V : Type u} (G : SimpleGraph V) where
  model : DominatingK5Model G
  fourth_singleton : BranchIsSingleton model (3 : Fin 5)
  fifth_singleton : BranchIsSingleton model (4 : Fin 5)
  third_branch_path : IsPathSubgraph (model.branch (2 : Fin 5))
  tail_cycle : G.Subgraph
  tail_induced_cycle : IsCycleSubgraph tail_cycle
  tail_contains_third_branch_subgraph :
    model.branch (2 : Fin 5) ≤ tail_cycle
  tail_contains_third_branch :
    (model.branch (2 : Fin 5)).verts ⊆ tail_cycle.verts
  tail_contains_last_branches :
    (model.branch (3 : Fin 5)).verts ⊆ tail_cycle.verts ∧
      (model.branch (4 : Fin 5)).verts ⊆ tail_cycle.verts

def ThirdBranchPathAndTailInducedCycleConclusion
    {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (ThirdBranchPathAndTailInducedCycleData G)

theorem ThirdBranchPathAndTailInducedCycleData.fourth_mem
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G) :
    D.fourth_singleton.choose ∈ (D.model.branch (3 : Fin 5)).verts := by
  exact D.fourth_singleton.choose_mem

theorem ThirdBranchPathAndTailInducedCycleData.fifth_mem
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G) :
    D.fifth_singleton.choose ∈ (D.model.branch (4 : Fin 5)).verts := by
  exact D.fifth_singleton.choose_mem

theorem ThirdBranchPathAndTailInducedCycleData.tail_singletons_adjacent
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G) :
    G.Adj D.fourth_singleton.choose D.fifth_singleton.choose := by
  obtain ⟨u, hu, huv⟩ :=
    D.model.dominates (3 : Fin 5) (4 : Fin 5) (by decide)
      D.fifth_singleton.choose D.fifth_mem
  have hu_eq : u = D.fourth_singleton.choose :=
    D.fourth_singleton.eq_choose_of_mem hu
  simpa [hu_eq] using huv

theorem ThirdBranchPathAndTailInducedCycleData.tailK4_all_singleton_of_second_third
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hsecond : BranchIsSingleton D.model (1 : Fin 5))
    (hthird : BranchIsSingleton D.model (2 : Fin 5)) :
    forall i : Fin 4, BranchIsSingleton D.model.tailK4 i := by
  intro i
  fin_cases i
  · simpa [DominatingK5Model.tailK4] using hsecond
  · simpa [DominatingK5Model.tailK4] using hthird
  · simpa [DominatingK5Model.tailK4] using D.fourth_singleton
  · simpa [DominatingK5Model.tailK4] using D.fifth_singleton

theorem ThirdBranchPathAndTailInducedCycleData.tailK4_singleton_iff
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (i : Fin 4) :
    BranchIsSingleton D.model.tailK4 i ↔
      BranchIsSingleton D.model (Fin.succ i) := by
  simpa only [DominatingK5Model.tailK4] using
    D.model.branchIsSingleton_reindex (Fin.succOrderEmb 4) i

theorem ThirdBranchPathAndTailInducedCycleData.tailK4_all_singleton_iff
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G) :
    (forall i : Fin 4, BranchIsSingleton D.model.tailK4 i) ↔
      (forall i : Fin 4, BranchIsSingleton D.model (Fin.succ i)) := by
  constructor
  · intro h i
    exact (D.tailK4_singleton_iff i).mp (h i)
  · intro h i
    exact (D.tailK4_singleton_iff i).mpr (h i)

theorem ThirdBranchPathAndTailInducedCycleData.all_singleton_of_first_and_tailK4
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hfirst : BranchIsSingleton D.model (0 : Fin 5))
    (htail : forall i : Fin 4, BranchIsSingleton D.model.tailK4 i) :
    forall i : Fin 5, BranchIsSingleton D.model i := by
  intro i
  fin_cases i
  · exact hfirst
  · simpa [DominatingK5Model.tailK4] using htail (0 : Fin 4)
  · simpa [DominatingK5Model.tailK4] using htail (1 : Fin 4)
  · simpa [DominatingK5Model.tailK4] using htail (2 : Fin 4)
  · simpa [DominatingK5Model.tailK4] using htail (3 : Fin 4)

theorem ThirdBranchPathAndTailInducedCycleData.not_first_singleton_of_not_all_singleton_and_tailK4
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hnot_all : Not (forall i : Fin 5, BranchIsSingleton D.model i))
    (htail : forall i : Fin 4, BranchIsSingleton D.model.tailK4 i) :
    Not (BranchIsSingleton D.model (0 : Fin 5)) := by
  intro hfirst
  exact hnot_all (D.all_singleton_of_first_and_tailK4 hfirst htail)

theorem ThirdBranchPathAndTailInducedCycleData.first_branch_path_of_not_all_singleton_and_tailK4
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hnot_all : Not (forall i : Fin 5, BranchIsSingleton D.model i))
    (htail : forall i : Fin 4, BranchIsSingleton D.model.tailK4 i) :
    Exists fun x : V =>
      Exists fun y : V =>
        Exists fun p : G.Walk x y =>
          x ∈ (D.model.branch (0 : Fin 5)).verts ∧
            y ∈ (D.model.branch (0 : Fin 5)).verts ∧
              x ≠ y ∧ p.IsPath ∧
                p.toSubgraph ≤ D.model.branch (0 : Fin 5) := by
  exact D.model.exists_path_in_branch_of_not_singleton (0 : Fin 5)
    (D.not_first_singleton_of_not_all_singleton_and_tailK4 hnot_all htail)

theorem ThirdBranchPathAndTailInducedCycleData.tailK4_not_all_singleton_cases
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hnot_tail : Not (forall i : Fin 4, BranchIsSingleton D.model.tailK4 i)) :
    Not (BranchIsSingleton D.model (1 : Fin 5)) ∨
      Not (BranchIsSingleton D.model (2 : Fin 5)) := by
  classical
  by_cases hsecond : BranchIsSingleton D.model (1 : Fin 5)
  · by_cases hthird : BranchIsSingleton D.model (2 : Fin 5)
    · exact False.elim
        (hnot_tail (D.tailK4_all_singleton_of_second_third hsecond hthird))
    · exact Or.inr hthird
  · exact Or.inl hsecond

theorem ThirdBranchPathAndTailInducedCycleData.tailK4_not_all_singleton_pair_witnesses
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hnot_tail : Not (forall i : Fin 4, BranchIsSingleton D.model.tailK4 i)) :
    (Exists fun x : V =>
      Exists fun y : V =>
        x ∈ (D.model.branch (1 : Fin 5)).verts ∧
          y ∈ (D.model.branch (1 : Fin 5)).verts ∧ x ≠ y) ∨
      (Exists fun x : V =>
        Exists fun y : V =>
          x ∈ (D.model.branch (2 : Fin 5)).verts ∧
            y ∈ (D.model.branch (2 : Fin 5)).verts ∧ x ≠ y) := by
  rcases D.tailK4_not_all_singleton_cases hnot_tail with hsecond | hthird
  · exact Or.inl
      (D.model.exists_pair_mem_branch_of_not_singleton (1 : Fin 5) hsecond)
  · exact Or.inr
      (D.model.exists_pair_mem_branch_of_not_singleton (2 : Fin 5) hthird)

theorem ThirdBranchPathAndTailInducedCycleData.tailK4_not_all_singleton_path_witnesses
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G)
    (hnot_tail : Not (forall i : Fin 4, BranchIsSingleton D.model.tailK4 i)) :
    (Exists fun x : V =>
      Exists fun y : V =>
        Exists fun p : G.Walk x y =>
          x ∈ (D.model.branch (1 : Fin 5)).verts ∧
            y ∈ (D.model.branch (1 : Fin 5)).verts ∧
              x ≠ y ∧ p.IsPath ∧
                p.toSubgraph ≤ D.model.branch (1 : Fin 5)) ∨
      (Exists fun x : V =>
        Exists fun y : V =>
          Exists fun p : G.Walk x y =>
            x ∈ (D.model.branch (2 : Fin 5)).verts ∧
              y ∈ (D.model.branch (2 : Fin 5)).verts ∧
                x ≠ y ∧ p.IsPath ∧
                  p.toSubgraph ≤ D.model.branch (2 : Fin 5)) := by
  rcases D.tailK4_not_all_singleton_cases hnot_tail with hsecond | hthird
  · exact Or.inl
      (D.model.exists_path_in_branch_of_not_singleton (1 : Fin 5) hsecond)
  · exact Or.inr
      (D.model.exists_path_in_branch_of_not_singleton (2 : Fin 5) hthird)

private def replaceLastTwoBranches
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G) (w v : V) : Fin 5 -> G.Subgraph
  | 0 => T.branch 0
  | 1 => T.branch 1
  | 2 => T.branch 2
  | 3 => G.singletonSubgraph w
  | 4 => G.singletonSubgraph v

theorem dominating_K5_model_with_last_two_singletons
    {V : Type u} {G : SimpleGraph V}
    (T : DominatingK5Model G) :
    Exists fun T' : DominatingK5Model G =>
      BranchIsSingleton T' (3 : Fin 5) ∧ BranchIsSingleton T' (4 : Fin 5) := by
  classical
  obtain ⟨v, hv⟩ := (T.connected (4 : Fin 5)).nonempty
  obtain ⟨w, hw, hwv⟩ := T.dominates (3 : Fin 5) (4 : Fin 5) (by decide) v hv
  have hw_not_mem (k : Fin 5) (hk : (3 : Fin 5) ≠ k) :
      w ∉ (T.branch k).verts := by
    intro h
    exact (Set.disjoint_left.mp (T.vertex_disjoint (3 : Fin 5) k hk) hw) h
  have hv_not_mem (k : Fin 5) (hk : (4 : Fin 5) ≠ k) :
      v ∉ (T.branch k).verts := by
    intro h
    exact (Set.disjoint_left.mp (T.vertex_disjoint (4 : Fin 5) k hk) hv) h
  let T' : DominatingK5Model G := {
    branch := replaceLastTwoBranches T w v
    connected := by
      intro i
      fin_cases i <;> simp [replaceLastTwoBranches]
      · exact T.connected 0
      · exact T.connected 1
      · exact T.connected 2
      · exact SimpleGraph.Connected.of_subsingleton
      · exact SimpleGraph.Connected.of_subsingleton
    vertex_disjoint := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [replaceLastTwoBranches] at hij ⊢
      · simpa using T.vertex_disjoint (0 : Fin 5) (1 : Fin 5) (by decide)
      · simpa using T.vertex_disjoint (0 : Fin 5) (2 : Fin 5) (by decide)
      · exact hw_not_mem (0 : Fin 5) (by decide)
      · exact hv_not_mem (0 : Fin 5) (by decide)
      · simpa using T.vertex_disjoint (1 : Fin 5) (0 : Fin 5) (by decide)
      · simpa using T.vertex_disjoint (1 : Fin 5) (2 : Fin 5) (by decide)
      · exact hw_not_mem (1 : Fin 5) (by decide)
      · exact hv_not_mem (1 : Fin 5) (by decide)
      · simpa using T.vertex_disjoint (2 : Fin 5) (0 : Fin 5) (by decide)
      · simpa using T.vertex_disjoint (2 : Fin 5) (1 : Fin 5) (by decide)
      · exact hw_not_mem (2 : Fin 5) (by decide)
      · exact hv_not_mem (2 : Fin 5) (by decide)
      · exact hw_not_mem (0 : Fin 5) (by decide)
      · exact hw_not_mem (1 : Fin 5) (by decide)
      · exact hw_not_mem (2 : Fin 5) (by decide)
      · exact hwv.ne
      · exact hv_not_mem (0 : Fin 5) (by decide)
      · exact hv_not_mem (1 : Fin 5) (by decide)
      · exact hv_not_mem (2 : Fin 5) (by decide)
      · exact hwv.ne.symm
    dominates := by
      intro i j hij x hx
      fin_cases i <;> fin_cases j <;>
        simp [replaceLastTwoBranches] at hij hx ⊢
      · exact T.dominates (0 : Fin 5) (1 : Fin 5) (by decide) x hx
      · exact T.dominates (0 : Fin 5) (2 : Fin 5) (by decide) x hx
      · rw [hx]
        exact T.dominates (0 : Fin 5) (3 : Fin 5) (by decide) w hw
      · rw [hx]
        exact T.dominates (0 : Fin 5) (4 : Fin 5) (by decide) v hv
      · exact T.dominates (1 : Fin 5) (2 : Fin 5) (by decide) x hx
      · rw [hx]
        exact T.dominates (1 : Fin 5) (3 : Fin 5) (by decide) w hw
      · rw [hx]
        exact T.dominates (1 : Fin 5) (4 : Fin 5) (by decide) v hv
      · rw [hx]
        exact T.dominates (2 : Fin 5) (3 : Fin 5) (by decide) w hw
      · rw [hx]
        exact T.dominates (2 : Fin 5) (4 : Fin 5) (by decide) v hv
      · rw [hx]
        exact hwv
  }
  refine ⟨T', ?_, ?_⟩
  · exact ⟨w, by simp [T', replaceLastTwoBranches]⟩
  · exact ⟨v, by simp [T', replaceLastTwoBranches]⟩

theorem ThirdBranchPathAndTailInducedCycleData.distinct_incidentGraphEdges
    {V : Type u} {G : SimpleGraph V}
    (D : ThirdBranchPathAndTailInducedCycleData G) :
    Exists fun edge₁ : Sym2 V =>
      Exists fun edge₂ : Sym2 V =>
        edge₁ ≠ edge₂ ∧
          (Exists fun v : V => v ∈ edge₁ ∧ v ∈ edge₂) ∧
            edge₁ ∈ G.edgeSet ∧ edge₂ ∈ G.edgeSet := by
  classical
  obtain ⟨w, hw_single⟩ := D.fourth_singleton
  obtain ⟨v, hv_single⟩ := D.fifth_singleton
  have hw_mem : w ∈ (D.model.branch (3 : Fin 5)).verts := by
    simp [hw_single]
  have hv_mem : v ∈ (D.model.branch (4 : Fin 5)).verts := by
    simp [hv_single]
  obtain ⟨u, hu, huw⟩ :=
    D.model.dominates (2 : Fin 5) (3 : Fin 5) (by decide) w hw_mem
  obtain ⟨w', hw', hw'v⟩ :=
    D.model.dominates (3 : Fin 5) (4 : Fin 5) (by decide) v hv_mem
  have hw'_eq : w' = w := by
    simpa [hw_single] using hw'
  have hwv : G.Adj w v := by
    simpa [hw'_eq] using hw'v
  have huv_ne : u ≠ v := by
    intro huv
    exact (Set.disjoint_left.mp
      (D.model.vertex_disjoint (2 : Fin 5) (4 : Fin 5) (by decide)) hu)
      (by simpa [huv] using hv_mem)
  let edge₁ : Sym2 V := s(w, v)
  let edge₂ : Sym2 V := s(w, u)
  refine ⟨edge₁, edge₂, ?_, ?_, ?_⟩
  · intro heq
    have hv_edge₂ : v ∈ edge₂ := by
      rw [← heq]
      exact Sym2.mem_mk_right _ _
    rw [Sym2.mem_iff] at hv_edge₂
    rcases hv_edge₂ with hvw | hvu
    · exact hwv.ne hvw.symm
    · exact huv_ne hvu.symm
  · exact ⟨w, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
  · constructor
    · exact (SimpleGraph.mem_edgeSet (G := G)).2 hwv
    · exact (SimpleGraph.mem_edgeSet (G := G)).2 huw.symm

end Schematic.Math.GraphTheory
