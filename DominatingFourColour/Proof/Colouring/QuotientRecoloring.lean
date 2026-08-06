import DominatingFourColour.Proof.Colouring.Stitching

/-! Recolour quotient colourings to agree across a separator. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

theorem colorable_of_separation_right_quotient_coloring_agree
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (C : GraphContraction sep.rightWithSeparatorClique)
    (quot_coloring : C.graph.Coloring (Fin c))
    (hno_true_edge_collapsed :
      forall a b : sep.right,
        (G.induce sep.right).Adj a b -> C.map a ≠ C.map b)
    (agree_on_separator :
      forall (v : V) (hv_left : v ∈ sep.left) (hv_right : v ∈ sep.right),
        left_coloring ⟨v, hv_left⟩ = quot_coloring (C.map ⟨v, hv_right⟩)) :
    G.Colorable c := by
  classical
  let right_coloring : (G.induce sep.right).Coloring (Fin c) :=
    SimpleGraph.Coloring.mk (fun v : sep.right => quot_coloring (C.map v)) (by
      intro a b hab hsame
      have hside_adj : sep.rightWithSeparatorClique.Adj a b := Or.inl hab
      have hmap_ne : C.map a ≠ C.map b :=
        hno_true_edge_collapsed a b hab
      rcases C.map_adj hside_adj with hcollapsed | hquot_adj
      · exact hmap_ne hcollapsed
      · exact quot_coloring.valid hquot_adj hsame)
  exact colorable_of_separation_colorings_agree sep left_coloring right_coloring
    agree_on_separator

theorem colorable_of_separation_right_map_quotient_coloring_agree
    {G : SimpleGraph V} {W : Type u} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (f : sep.right -> W)
    (quot_coloring :
      (contractionTargetGraph sep.rightWithSeparatorClique f).Coloring (Fin c))
    (hno_true_edge_collapsed :
      forall a b : sep.right,
        (G.induce sep.right).Adj a b -> f a ≠ f b)
    (agree_on_separator :
      forall (v : V) (hv_left : v ∈ sep.left) (hv_right : v ∈ sep.right),
        left_coloring ⟨v, hv_left⟩ = quot_coloring (f ⟨v, hv_right⟩)) :
    G.Colorable c := by
  classical
  let right_coloring : (G.induce sep.right).Coloring (Fin c) :=
    SimpleGraph.Coloring.mk (fun v : sep.right => quot_coloring (f v)) (by
      intro a b hab hsame
      have hmap_ne : f a ≠ f b := hno_true_edge_collapsed a b hab
      have hside_adj : sep.rightWithSeparatorClique.Adj a b := Or.inl hab
      have hquot_adj :
          (contractionTargetGraph sep.rightWithSeparatorClique f).Adj (f a) (f b) :=
        ⟨hmap_ne, a, b, rfl, rfl, hside_adj⟩
      exact quot_coloring.valid hquot_adj hsame)
  exact colorable_of_separation_colorings_agree sep left_coloring right_coloring
    agree_on_separator

theorem colorable_of_separation_right_quotient_colorable_agree
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (C : GraphContraction sep.rightWithSeparatorClique)
    (hquot_colorable : C.graph.Colorable c)
    (hno_true_edge_collapsed :
      forall a b : sep.right,
        (G.induce sep.right).Adj a b -> C.map a ≠ C.map b)
    (agree_on_separator :
      forall (quot_coloring : C.graph.Coloring (Fin c)),
        Exists fun recolor : Fin c ≃ Fin c =>
          forall (v : V) (hv_left : v ∈ sep.left) (hv_right : v ∈ sep.right),
            left_coloring ⟨v, hv_left⟩ =
              recolor (quot_coloring (C.map ⟨v, hv_right⟩))) :
    G.Colorable c := by
  classical
  rcases hquot_colorable with ⟨quot_coloring₀⟩
  obtain ⟨recolor, hagree⟩ := agree_on_separator quot_coloring₀
  let quot_coloring : C.graph.Coloring (Fin c) :=
    (SimpleGraph.Iso.completeGraph recolor).toHom.comp quot_coloring₀
  exact colorable_of_separation_right_quotient_coloring_agree sep left_coloring C
    quot_coloring hno_true_edge_collapsed (by
      intro v hv_left hv_right
      exact hagree v hv_left hv_right)


theorem exists_recoloring_for_separator_color_class_quotient
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (C : GraphContraction sep.rightWithSeparatorClique)
    (quot_coloring : C.graph.Coloring (Fin c))
    (hseparator_classes :
      forall a b : sep.separator,
        C.map (⟨(a : V), a.2.2⟩ : sep.right) =
            C.map (⟨(b : V), b.2.2⟩ : sep.right) ↔
          left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩) :
    Exists fun recolor : Fin c ≃ Fin c =>
      forall (v : V) (hv_left : v ∈ sep.left) (hv_right : v ∈ sep.right),
        left_coloring ⟨v, hv_left⟩ =
          recolor (quot_coloring (C.map ⟨v, hv_right⟩)) := by
  let left : sep.separator -> Fin c := fun a =>
    left_coloring ⟨(a : V), a.2.1⟩
  let right : sep.separator -> Fin c := fun a =>
    quot_coloring (C.map ⟨(a : V), a.2.2⟩)
  obtain ⟨recolor, hagree⟩ := exists_recoloring_of_same_fibers left right (by
    intro a b
    constructor
    · intro hcolor
      by_contra hleft
      have hmap_ne := (hseparator_classes a b).not.mpr hleft
      have hadj := sep.rightWithSeparatorClique_separator_adj
        (a := ⟨(a : V), a.2.2⟩) (b := ⟨(b : V), b.2.2⟩)
        a.2.1 b.2.1 (fun h =>
          hleft (congrArg left (Subtype.ext
            (congrArg (fun x : sep.right => (x : V)) h))))
      rcases C.map_adj hadj with hmap | hquot
      · exact hmap_ne hmap
      · exact quot_coloring.valid hquot hcolor
    · exact fun hcolor => congrArg quot_coloring ((hseparator_classes a b).mpr hcolor))
  refine ⟨recolor, ?_⟩
  intro v hv_left hv_right
  exact hagree ⟨v, hv_left, hv_right⟩

theorem exists_recoloring_for_separator_color_class_map_quotient
    {G : SimpleGraph V} {W : Type u} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (f : sep.right -> W)
    (quot_coloring :
      (contractionTargetGraph sep.rightWithSeparatorClique f).Coloring (Fin c))
    (hseparator_classes :
      forall a b : sep.separator,
        f (⟨(a : V), a.2.2⟩ : sep.right) =
            f (⟨(b : V), b.2.2⟩ : sep.right) ↔
          left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩) :
    Exists fun recolor : Fin c ≃ Fin c =>
      forall (v : V) (hv_left : v ∈ sep.left) (hv_right : v ∈ sep.right),
        left_coloring ⟨v, hv_left⟩ =
          recolor (quot_coloring (f ⟨v, hv_right⟩)) := by
  let left : sep.separator -> Fin c := fun a =>
    left_coloring ⟨(a : V), a.2.1⟩
  let right : sep.separator -> Fin c := fun a =>
    quot_coloring (f ⟨(a : V), a.2.2⟩)
  obtain ⟨recolor, hagree⟩ := exists_recoloring_of_same_fibers left right (by
    intro a b
    constructor
    · intro hcolor
      by_contra hleft
      have hmap_ne := (hseparator_classes a b).not.mpr hleft
      have hside := sep.rightWithSeparatorClique_separator_adj
        (a := ⟨(a : V), a.2.2⟩) (b := ⟨(b : V), b.2.2⟩)
        a.2.1 b.2.1 (fun h =>
          hleft (congrArg left (Subtype.ext
            (congrArg (fun x : sep.right => (x : V)) h))))
      have hquot :
          (contractionTargetGraph sep.rightWithSeparatorClique f).Adj
            (f ⟨(a : V), a.2.2⟩) (f ⟨(b : V), b.2.2⟩) :=
        ⟨hmap_ne, _, _, rfl, rfl, hside⟩
      exact quot_coloring.valid hquot hcolor
    · exact fun hcolor => congrArg quot_coloring ((hseparator_classes a b).mpr hcolor))
  refine ⟨recolor, ?_⟩
  intro v hv_left hv_right
  exact hagree ⟨v, hv_left, hv_right⟩

theorem colorable_of_separation_right_map_quotient_colorable_agree
    {G : SimpleGraph V} {W : Type u} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (f : sep.right -> W)
    (hquot_colorable :
      (contractionTargetGraph sep.rightWithSeparatorClique f).Colorable c)
    (hno_true_edge_collapsed :
      forall a b : sep.right,
        (G.induce sep.right).Adj a b -> f a ≠ f b)
    (hseparator_classes :
      forall a b : sep.separator,
        f (⟨(a : V), a.2.2⟩ : sep.right) =
            f (⟨(b : V), b.2.2⟩ : sep.right) ↔
          left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩) :
    G.Colorable c := by
  classical
  rcases hquot_colorable with ⟨quot_coloring₀⟩
  obtain ⟨recolor, hagree⟩ :=
    exists_recoloring_for_separator_color_class_map_quotient
      sep left_coloring f quot_coloring₀ hseparator_classes
  let quot_coloring :
      (contractionTargetGraph sep.rightWithSeparatorClique f).Coloring (Fin c) :=
    (SimpleGraph.Iso.completeGraph recolor).toHom.comp quot_coloring₀
  exact colorable_of_separation_right_map_quotient_coloring_agree
    sep left_coloring f quot_coloring hno_true_edge_collapsed (by
      intro v hv_left hv_right
      exact hagree v hv_left hv_right)

end Schematic.Math.GraphTheory
