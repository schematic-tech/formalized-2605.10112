import DominatingFourColour.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Complete-graph and degree base cases for the dominating-K4 lemma.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace DominatingK4

theorem exists_dominating_K4_model_of_complete
    [Fintype V]
    (h_card : 4 <= Fintype.card V)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v) :
    Nonempty (DominatingK4Model G) := by
  classical
  obtain ⟨e⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin 4) (β := V) (by simpa using h_card)
  exact ⟨DominatingModel.ofCompleteEmbedding h_complete e⟩

theorem exists_dominating_K4_model_of_complete_with_first
    [Fintype V]
    (h_card : 4 <= Fintype.card V)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v)
    (v0 : V) :
    Exists fun T : DominatingK4Model G => v0 ∈ (T.branch (0 : Fin 4)).verts := by
  classical
  have h_compl_card :
      3 <= Fintype.card {v : V // v ≠ v0} := by
    have hcard :
        Fintype.card {v : V // v ≠ v0} = Fintype.card V - 1 := by
      simp
    rw [hcard]
    omega
  obtain ⟨e3⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin 3) (β := {v : V // v ≠ v0}) h_compl_card
  let e3V : Fin 3 ↪ V := {
    toFun := fun i => e3 i
    inj' := fun _ _ hij => e3.injective (Subtype.ext hij)
  }
  have hv0_not_range : v0 ∉ Set.range e3V := by
    rintro ⟨i, hi⟩
    exact (e3 i).2 hi
  let e : Fin 4 ↪ V :=
    (Equiv.embeddingFinSucc 3 V).symm
      ⟨e3V, ⟨v0, hv0_not_range⟩⟩
  let T : DominatingK4Model G := DominatingModel.ofCompleteEmbedding h_complete e
  exact ⟨T, by
    simp [T, DominatingModel.ofCompleteEmbedding,
      DominatingModel.ofCliqueEmbedding, e]⟩

theorem degree_atLeast_three_of_three_neighbors
    [Fintype V] [DecidableRel G.Adj]
    {u a b c : V}
    (hua : G.Adj u a)
    (hub : G.Adj u b)
    (huc : G.Adj u c)
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    3 <= G.degree u := by
  classical
  let neighbors : Finset V := {a, b, c}
  have hneighbors_card : neighbors.card = 3 := by
    simp [neighbors, hab, hac, hbc]
  have hneighbors_subset : neighbors ⊆ G.neighborFinset u := by
    intro v hv
    simp only [neighbors, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · simpa only [SimpleGraph.mem_neighborFinset] using hua
    · simpa only [SimpleGraph.mem_neighborFinset] using hub
    · simpa only [SimpleGraph.mem_neighborFinset] using huc
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hneighbors_card]
  exact Finset.card_le_card hneighbors_subset

theorem degree_atLeast_three_of_complete
    [Fintype V] [DecidableRel G.Adj]
    (h_card : 4 <= Fintype.card V)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v)
    (v : V) :
    3 <= G.degree v := by
  classical
  have hneighbor : G.neighborSet v = ({v} : Set V)ᶜ := by
    ext w
    constructor
    · intro hw
      exact hw.ne'
    · intro hw
      have hw_ne : w ≠ v := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hw
      exact h_complete v w hw_ne.symm
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  have hcard_neighbor :
      Fintype.card (G.neighborSet v) =
        Fintype.card {w : V // w ∈ ({v} : Set V)ᶜ} :=
    Fintype.card_congr (Equiv.setCongr hneighbor)
  have hcard_compl :
      Fintype.card {w : V // w ∈ ({v} : Set V)ᶜ} = Fintype.card V - 1 := by
    simp
  rw [hcard_neighbor, hcard_compl]
  omega

theorem degree_le_two_of_nonadjacent_card_four
    [Fintype V] [DecidableRel G.Adj]
    (h_card : Fintype.card V = 4)
    {u v : V}
    (huv : u ≠ v)
    (hnot_adj : Not (G.Adj u v)) :
    G.degree u <= 2 := by
  classical
  have hsubset : G.neighborFinset u ⊆ (Finset.univ.erase u).erase v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.mem_univ w⟩
    · intro hwv
      subst w
      exact hnot_adj hw
    · exact hw.ne'
  have hv_mem : v ∈ Finset.univ.erase u := by
    rw [Finset.mem_erase]
    exact ⟨huv.symm, Finset.mem_univ v⟩
  have hcard_target : ((Finset.univ.erase u).erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hv_mem]
    rw [Finset.card_erase_of_mem (Finset.mem_univ u)]
    rw [Finset.card_univ, h_card]
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact le_trans (Finset.card_le_card hsubset) (by rw [hcard_target])

theorem complete_of_card_four_low_degree_clique
    [Fintype V] [DecidableRel G.Adj]
    (h_card : Fintype.card V = 4)
    (L : Finset V)
    (h_clique : G.IsClique (L : Set V))
    (h_low_degree_in_L : forall v : V, G.degree v <= 2 -> v ∈ L) :
    forall u v : V, u ≠ v -> G.Adj u v := by
  intro u v huv
  by_contra hnot_adj
  have hu_degree : G.degree u <= 2 :=
    degree_le_two_of_nonadjacent_card_four (G := G) h_card huv hnot_adj
  have hv_degree : G.degree v <= 2 :=
    degree_le_two_of_nonadjacent_card_four (G := G) h_card huv.symm
      (by
        intro h
        exact hnot_adj h.symm)
  exact hnot_adj (h_clique (h_low_degree_in_L u hu_degree)
    (h_low_degree_in_L v hv_degree) huv)

end DominatingK4

end Schematic.Math.GraphTheory
