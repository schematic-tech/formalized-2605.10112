import DominatingFourColour.Proof.Colouring.SeparatorClique

/-! Stitch colourings that agree on a separator. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

theorem colorable_of_separation_colorings_agree
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (right_coloring : (G.induce sep.right).Coloring (Fin c))
    (agree_on_separator :
      forall (v : V) (hv_left : v ∈ sep.left) (hv_right : v ∈ sep.right),
        left_coloring ⟨v, hv_left⟩ = right_coloring ⟨v, hv_right⟩) :
    G.Colorable c := by
  classical
  let color : V -> Fin c := fun v =>
    if hv : v ∈ sep.left then
      left_coloring ⟨v, hv⟩
    else
      right_coloring ⟨v, by
        have hv_cover : v ∈ sep.left ∪ sep.right := by
          rw [sep.covers]
          exact Set.mem_univ v
        rcases hv_cover with hv_left | hv_right
        · exact False.elim (hv hv_left)
        · exact hv_right⟩
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro v w hvw hsame
  have hv_cover : v ∈ sep.left ∪ sep.right := by
    rw [sep.covers]
    exact Set.mem_univ v
  have hw_cover : w ∈ sep.left ∪ sep.right := by
    rw [sep.covers]
    exact Set.mem_univ w
  by_cases hv_left : v ∈ sep.left
  · by_cases hw_left : w ∈ sep.left
    · have hvw_left :
          (G.induce sep.left).Adj ⟨v, hv_left⟩ ⟨w, hw_left⟩ := by
        simpa using hvw
      exact left_coloring.valid hvw_left (by simpa [color, hv_left, hw_left] using hsame)
    · have hw_right : w ∈ sep.right := by
        rcases hw_cover with hw_left' | hw_right
        · exact False.elim (hw_left hw_left')
        · exact hw_right
      by_cases hv_right : v ∈ sep.right
      · have hsame_right :
            right_coloring ⟨v, hv_right⟩ = right_coloring ⟨w, hw_right⟩ := by
          rw [← agree_on_separator v hv_left hv_right]
          simpa [color, hv_left, hw_left] using hsame
        have hvw_right :
            (G.induce sep.right).Adj ⟨v, hv_right⟩ ⟨w, hw_right⟩ := by
          simpa using hvw
        exact right_coloring.valid hvw_right hsame_right
      · exact False.elim (sep.no_cross hv_left hv_right hw_right hw_left hvw)
  · have hv_right : v ∈ sep.right := by
      rcases hv_cover with hv_left' | hv_right
      · exact False.elim (hv_left hv_left')
      · exact hv_right
    by_cases hw_left : w ∈ sep.left
    · by_cases hw_right : w ∈ sep.right
      · have hsame_right :
            right_coloring ⟨v, hv_right⟩ = right_coloring ⟨w, hw_right⟩ := by
          rw [← agree_on_separator w hw_left hw_right]
          simpa [color, hv_left, hw_left] using hsame
        have hvw_right :
            (G.induce sep.right).Adj ⟨v, hv_right⟩ ⟨w, hw_right⟩ := by
          simpa using hvw
        exact right_coloring.valid hvw_right hsame_right
      · exact False.elim (sep.no_cross hw_left hw_right hv_right hv_left hvw.symm)
    · have hw_right : w ∈ sep.right := by
        rcases hw_cover with hw_left' | hw_right
        · exact False.elim (hw_left hw_left')
        · exact hw_right
      have hvw_right :
          (G.induce sep.right).Adj ⟨v, hv_right⟩ ⟨w, hw_right⟩ := by
        simpa using hvw
      exact right_coloring.valid hvw_right (by simpa [color, hv_left, hw_left] using hsame)

/-- Two finite-valued maps with the same fibers differ by a permutation of their codomain. -/
theorem exists_recoloring_of_same_fibers
    {α : Type*} {c : Nat}
    (left right : α -> Fin c)
    (same_fibers : forall a b, right a = right b ↔ left a = left b) :
    Exists fun recolor : Fin c ≃ Fin c =>
      forall a, left a = recolor (right a) := by
  classical
  let classes := Set.range right
  letI : Fintype classes := Set.toFinite classes |>.fintype
  let rep : classes -> α := fun x => Classical.choose x.2
  have rep_spec (x : classes) : right (rep x) = x :=
    Classical.choose_spec x.2
  let rightClass : classes -> Fin c := fun x => x
  let leftClass : classes -> Fin c := fun x => left (rep x)
  have hleft_injective : Function.Injective leftClass := by
    intro x y hxy
    apply Subtype.ext
    exact (rep_spec x).symm.trans
      (((same_fibers (rep x) (rep y)).mpr hxy).trans (rep_spec y))
  obtain ⟨recolor, hrecolor⟩ := Equiv.Perm.exists_extending_pair
    rightClass leftClass Subtype.val_injective hleft_injective
  refine ⟨recolor, ?_⟩
  intro a
  let x : classes := ⟨right a, ⟨a, rfl⟩⟩
  have hleft : left (rep x) = left a :=
    (same_fibers _ _).mp (by simpa [x] using rep_spec x)
  exact hleft.symm.trans (hrecolor x).symm

theorem lemma_colouring
    {G : SimpleGraph V} {c : Nat}
    (D : PaperColouringStitchData G c) :
    G.Colorable c := by
  exact colorable_of_separation_colorings_agree D.sep D.left_coloring D.right_coloring
    D.agree_on_separator

end Schematic.Math.GraphTheory
