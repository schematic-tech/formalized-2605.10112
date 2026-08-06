import DominatingFourColour.Proof.Colouring.ColorClassContraction

/-! Final clique-, singleton-, and triple-separator colouring cases. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}


theorem colorable_of_separation_colorings_of_injective_separator
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (right_coloring : (G.induce sep.right).Coloring (Fin c))
    (hleft_injective : Function.Injective fun v : sep.separator =>
      left_coloring ⟨v, v.2.1⟩)
    (hright_injective : Function.Injective fun v : sep.separator =>
      right_coloring ⟨v, v.2.2⟩) :
    G.Colorable c := by
  classical
  let left : sep.separator -> Fin c := fun v => left_coloring ⟨v, v.2.1⟩
  let right : sep.separator -> Fin c := fun v => right_coloring ⟨v, v.2.2⟩
  obtain ⟨recolor, hagree⟩ := exists_recoloring_of_same_fibers left right (by
    intro a b
    constructor
    · exact fun h => congrArg left (hright_injective h)
    · exact fun h => congrArg right (hleft_injective h))
  let recolored_right : (G.induce sep.right).Coloring (Fin c) :=
    (SimpleGraph.Iso.completeGraph recolor).toHom.comp right_coloring
  exact colorable_of_separation_colorings_agree sep left_coloring recolored_right (by
    intro v hv_left hv_right
    exact hagree ⟨v, hv_left, hv_right⟩)

theorem colorable_of_separation_with_separator_clique_colorings
    {G : SimpleGraph V}
    (sep : Separation G)
    (hleft : sep.leftWithSeparatorClique.Colorable 4)
    (hright : sep.rightWithSeparatorClique.Colorable 4) :
    G.Colorable 4 := by
  classical
  obtain ⟨left_coloring₀⟩ := hleft
  obtain ⟨right_coloring₀⟩ := hright
  let left_coloring : (G.induce sep.left).Coloring (Fin 4) :=
    SimpleGraph.Coloring.mk (fun v : sep.left => left_coloring₀ v) (by
      intro a b hab hsame
      exact left_coloring₀.valid (Or.inl hab) hsame)
  let right_coloring : (G.induce sep.right).Coloring (Fin 4) :=
    SimpleGraph.Coloring.mk (fun v : sep.right => right_coloring₀ v) (by
      intro a b hab hsame
      exact right_coloring₀.valid (Or.inl hab) hsame)
  exact colorable_of_separation_colorings_of_injective_separator
    sep left_coloring right_coloring
    (by
      intro a b hcolor
      apply Subtype.ext
      by_contra hne
      exact left_coloring₀.valid
        (Or.inr ⟨a.2.2, b.2.2, fun h =>
          hne (congrArg (fun z : sep.left => (z : V)) h)⟩)
        (show left_coloring₀ ⟨(a : V), a.2.1⟩ =
            left_coloring₀ ⟨(b : V), b.2.1⟩ by
          simpa [left_coloring] using hcolor))
    (by
      intro a b hcolor
      apply Subtype.ext
      by_contra hne
      have hadj :
          sep.rightWithSeparatorClique.Adj
            ⟨(a : V), a.2.2⟩ ⟨(b : V), b.2.2⟩ := by
        exact Or.inr ⟨a.2.1, b.2.1, fun h =>
          hne (congrArg (fun z : sep.right => (z : V)) h)⟩
      exact right_coloring₀.valid hadj
        (show right_coloring₀ ⟨(a : V), a.2.2⟩ =
            right_coloring₀ ⟨(b : V), b.2.2⟩ by
          simpa [right_coloring] using hcolor))

theorem colorable_of_separation_singleton
    {G : SimpleGraph V}
    (sep : Separation G)
    (x : V)
    (hx_left : x ∈ sep.left)
    (hx_right : x ∈ sep.right)
    (hseparator_unique :
      forall v : V, v ∈ sep.left -> v ∈ sep.right -> v = x)
    (hleft : (G.induce sep.left).Colorable 4)
    (hright : (G.induce sep.right).Colorable 4) :
    G.Colorable 4 := by
  classical
  obtain ⟨left_coloring⟩ := hleft
  obtain ⟨right_coloring₀⟩ := hright
  let recolor : Fin 4 ≃ Fin 4 :=
    Equiv.swap (right_coloring₀ ⟨x, hx_right⟩) (left_coloring ⟨x, hx_left⟩)
  let right_coloring : (G.induce sep.right).Coloring (Fin 4) :=
    (SimpleGraph.Iso.completeGraph recolor).toHom.comp right_coloring₀
  have hagree :
      forall (v : V) (hv_left : v ∈ sep.left) (hv_right : v ∈ sep.right),
        left_coloring ⟨v, hv_left⟩ = right_coloring ⟨v, hv_right⟩ := by
    intro v hv_left hv_right
    have hvx : v = x := hseparator_unique v hv_left hv_right
    subst v
    have hleft_sub : (⟨x, hv_left⟩ : sep.left) = ⟨x, hx_left⟩ := Subtype.ext rfl
    have hright_sub : (⟨x, hv_right⟩ : sep.right) = ⟨x, hx_right⟩ := Subtype.ext rfl
    rw [hleft_sub, hright_sub]
    change left_coloring ⟨x, hx_left⟩ =
      recolor (right_coloring₀ ⟨x, hx_right⟩)
    simp [recolor, Equiv.swap_apply_left]
  exact colorable_of_separation_colorings_agree sep left_coloring right_coloring hagree

theorem colorable_of_separation_clique
    {G : SimpleGraph V}
    (sep : Separation G)
    (hseparator_clique : G.IsClique sep.separator)
    (hleft : (G.induce sep.left).Colorable 4)
    (hright : (G.induce sep.right).Colorable 4) :
    G.Colorable 4 := by
  obtain ⟨left_coloring⟩ := hleft
  obtain ⟨right_coloring⟩ := hright
  exact colorable_of_separation_colorings_of_injective_separator
    sep left_coloring right_coloring
    (sep.leftColoring_injective_on_separator_of_separator_clique
      left_coloring hseparator_clique)
    (by
      intro a b hcolor
      apply Subtype.ext
      by_contra hne
      exact right_coloring.valid
        (show (G.induce sep.right).Adj
          ⟨(a : V), a.2.2⟩ ⟨(b : V), b.2.2⟩ from
          hseparator_clique a.2 b.2 hne)
        hcolor)


/-!
MI integration extras: triple-separator color injectivity used by the
completed main-induction proof.
-/

theorem Separation.leftColoring_injective_on_triple_separator_of_pairwise_ne
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    {x y z : V}
    (hseparator : sep.separator = ({x, y, z} : Set V))
    (hxy_color :
      left_coloring ⟨x, (sep.triple_vertices_mem_left hseparator).1⟩ ≠
        left_coloring ⟨y, (sep.triple_vertices_mem_left hseparator).2.1⟩)
    (hxz_color :
      left_coloring ⟨x, (sep.triple_vertices_mem_left hseparator).1⟩ ≠
        left_coloring ⟨z, (sep.triple_vertices_mem_left hseparator).2.2⟩)
    (hyz_color :
      left_coloring ⟨y, (sep.triple_vertices_mem_left hseparator).2.1⟩ ≠
        left_coloring ⟨z, (sep.triple_vertices_mem_left hseparator).2.2⟩) :
    forall a b : sep.separator,
      left_coloring ⟨(a : V), a.2.1⟩ =
          left_coloring ⟨(b : V), b.2.1⟩ ->
        a = b := by
  classical
  intro a b hcolor
  have ha_tri : (a : V) = x ∨ (a : V) = y ∨ (a : V) = z := by
    have : (a : V) ∈ ({x, y, z} : Set V) := by
      simpa [hseparator] using a.2
    simpa [Set.mem_insert_iff] using this
  have hb_tri : (b : V) = x ∨ (b : V) = y ∨ (b : V) = z := by
    have : (b : V) ∈ ({x, y, z} : Set V) := by
      simpa [hseparator] using b.2
    simpa [Set.mem_insert_iff] using this
  rcases ha_tri with ha_x | ha_y | ha_z <;>
    rcases hb_tri with hb_x | hb_y | hb_z
  · exact Subtype.ext (ha_x.trans hb_x.symm)
  · exact False.elim (hxy_color (by simpa [ha_x, hb_y] using hcolor))
  · exact False.elim (hxz_color (by simpa [ha_x, hb_z] using hcolor))
  · exact False.elim (hxy_color (by simpa [ha_y, hb_x] using hcolor.symm))
  · exact Subtype.ext (ha_y.trans hb_y.symm)
  · exact False.elim (hyz_color (by simpa [ha_y, hb_z] using hcolor))
  · exact False.elim (hxz_color (by simpa [ha_z, hb_x] using hcolor.symm))
  · exact False.elim (hyz_color (by simpa [ha_z, hb_y] using hcolor.symm))
  · exact Subtype.ext (ha_z.trans hb_z.symm)


end Schematic.Math.GraphTheory
