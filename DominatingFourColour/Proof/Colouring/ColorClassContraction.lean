import DominatingFourColour.Proof.Colouring.QuotientRecoloring

/-! The canonical contraction determined by separator colour classes. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

noncomputable def Separation.rightColorClassBaseMap
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c)) :
    sep.right -> Sum (Fin c) {x : sep.right // (x : V) ∉ sep.left} := by
  classical
  exact fun x =>
    if hx : (x : V) ∈ sep.left then
      Sum.inl (left_coloring ⟨(x : V), hx⟩)
    else
      Sum.inr ⟨x, hx⟩

theorem Separation.rightColorClassBaseMap_separator_classes
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c)) :
    forall a b : sep.separator,
      sep.rightColorClassBaseMap left_coloring (⟨(a : V), a.2.2⟩ : sep.right) =
          sep.rightColorClassBaseMap left_coloring (⟨(b : V), b.2.2⟩ : sep.right) ↔
        left_coloring ⟨(a : V), a.2.1⟩ =
          left_coloring ⟨(b : V), b.2.1⟩ := by
  classical
  intro a b
  constructor
  · intro h
    simpa [Separation.rightColorClassBaseMap, a.2.1, b.2.1] using h
  · intro h
    simp [Separation.rightColorClassBaseMap, a.2.1, b.2.1, h]

theorem Separation.rightColorClassBaseMap_no_true_edge_collapsed
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c)) :
    forall a b : sep.right,
      (G.induce sep.right).Adj a b ->
        sep.rightColorClassBaseMap left_coloring a ≠
          sep.rightColorClassBaseMap left_coloring b := by
  classical
  intro a b hab hmap
  by_cases ha_left : (a : V) ∈ sep.left
  · by_cases hb_left : (b : V) ∈ sep.left
    · have hcolors :
          left_coloring ⟨(a : V), ha_left⟩ =
            left_coloring ⟨(b : V), hb_left⟩ := by
        simpa [Separation.rightColorClassBaseMap, ha_left, hb_left] using hmap
      have hab_left :
          (G.induce sep.left).Adj ⟨(a : V), ha_left⟩ ⟨(b : V), hb_left⟩ := by
        exact hab
      exact left_coloring.valid hab_left hcolors
    · simp [Separation.rightColorClassBaseMap, ha_left, hb_left] at hmap
  · by_cases hb_left : (b : V) ∈ sep.left
    · simp [Separation.rightColorClassBaseMap, ha_left, hb_left] at hmap
    · have hsub : a = b := by
        simpa [Separation.rightColorClassBaseMap, ha_left, hb_left] using hmap
      exact hab.ne hsub

noncomputable def Separation.rightColorClassTarget
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c)) : Type u :=
  Set.range (sep.rightColorClassBaseMap left_coloring)

noncomputable def Separation.rightColorClassQuotientMap
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c)) :
    sep.right -> sep.rightColorClassTarget left_coloring := fun x =>
  ⟨sep.rightColorClassBaseMap left_coloring x, ⟨x, rfl⟩⟩

noncomputable instance Separation.rightColorClassTargetFintype
    {G : SimpleGraph V} [Fintype V] {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c)) :
    Fintype (sep.rightColorClassTarget left_coloring) := by
  classical
  letI : Fintype sep.right := sep.right.toFinite.fintype
  exact (Set.range (sep.rightColorClassBaseMap left_coloring)).toFinite.fintype

theorem Separation.rightColorClassQuotientMap_separator_classes
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c)) :
    forall a b : sep.separator,
      sep.rightColorClassQuotientMap left_coloring (⟨(a : V), a.2.2⟩ : sep.right) =
          sep.rightColorClassQuotientMap left_coloring (⟨(b : V), b.2.2⟩ : sep.right) ↔
        left_coloring ⟨(a : V), a.2.1⟩ =
          left_coloring ⟨(b : V), b.2.1⟩ := by
  classical
  intro a b
  constructor
  · intro h
    exact (sep.rightColorClassBaseMap_separator_classes left_coloring a b).mp
      (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (sep.rightColorClassBaseMap_separator_classes left_coloring a b).mpr h

theorem Separation.rightColorClassQuotientMap_no_true_edge_collapsed
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c)) :
    forall a b : sep.right,
      (G.induce sep.right).Adj a b ->
        sep.rightColorClassQuotientMap left_coloring a ≠
          sep.rightColorClassQuotientMap left_coloring b := by
  classical
  intro a b hab hmap
  exact sep.rightColorClassBaseMap_no_true_edge_collapsed left_coloring a b hab
    (congrArg Subtype.val hmap)

theorem Separation.leftColoring_injective_on_separator_of_separator_clique
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (hseparator_clique : G.IsClique sep.separator) :
    forall a b : sep.separator,
      left_coloring ⟨(a : V), a.2.1⟩ =
          left_coloring ⟨(b : V), b.2.1⟩ ->
        a = b := by
  intro a b hcolor
  by_cases hab : (a : V) = (b : V)
  · exact Subtype.ext hab
  · have hadj : G.Adj (a : V) (b : V) :=
      hseparator_clique a.2 b.2 hab
    have hadj_left :
        (G.induce sep.left).Adj
          ⟨(a : V), a.2.1⟩ ⟨(b : V), b.2.1⟩ := hadj
    exact False.elim (left_coloring.valid hadj_left hcolor)

theorem Separation.rightColorClassQuotientMap_fiber_singleton_of_separator_color_injective
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (hseparator_color_injective :
      forall a b : sep.separator,
        left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩ ->
          a = b) :
    forall v w : sep.right,
      sep.rightColorClassQuotientMap left_coloring v =
          sep.rightColorClassQuotientMap left_coloring w ->
        v = w := by
  classical
  intro v w hmap
  have hbase :
      sep.rightColorClassBaseMap left_coloring v =
        sep.rightColorClassBaseMap left_coloring w :=
    congrArg Subtype.val hmap
  by_cases hv_left : (v : V) ∈ sep.left
  · by_cases hw_left : (w : V) ∈ sep.left
    · have hcolor :
          left_coloring ⟨(v : V), hv_left⟩ =
            left_coloring ⟨(w : V), hw_left⟩ := by
        simpa [Separation.rightColorClassBaseMap, hv_left, hw_left] using hbase
      let a : sep.separator := ⟨(v : V), hv_left, v.2⟩
      let b : sep.separator := ⟨(w : V), hw_left, w.2⟩
      have hab : a = b := hseparator_color_injective a b hcolor
      have hval : (v : V) = (w : V) :=
        congrArg (fun x : sep.separator => (x : V)) hab
      exact Subtype.ext hval
    · simp [Separation.rightColorClassBaseMap, hv_left, hw_left] at hbase
  · by_cases hw_left : (w : V) ∈ sep.left
    · simp [Separation.rightColorClassBaseMap, hv_left, hw_left] at hbase
    · have hsub :
          (⟨v, hv_left⟩ :
            {x : sep.right // (x : V) ∉ sep.left}) =
          ⟨w, hw_left⟩ := by
        simpa [Separation.rightColorClassBaseMap, hv_left, hw_left] using hbase
      exact congrArg Subtype.val hsub

theorem Separation.rightColorClassQuotientMap_injective_of_separator_color_injective
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (hseparator_color_injective :
      forall a b : sep.separator,
        left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩ ->
          a = b) :
    Function.Injective (sep.rightColorClassQuotientMap left_coloring) := by
  intro v w hmap
  exact sep.rightColorClassQuotientMap_fiber_singleton_of_separator_color_injective
    left_coloring hseparator_color_injective v w hmap

theorem Separation.rightColorClassQuotientMap_injective_of_separator_clique
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (hseparator_clique : G.IsClique sep.separator) :
    Function.Injective (sep.rightColorClassQuotientMap left_coloring) := by
  exact sep.rightColorClassQuotientMap_injective_of_separator_color_injective
    left_coloring
    (sep.leftColoring_injective_on_separator_of_separator_clique
      left_coloring hseparator_clique)

theorem Separation.rightColorClassTarget_card_lt_of_proper
    {G : SimpleGraph V} [Fintype V] {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (hproper : sep.Proper) :
    Fintype.card (sep.rightColorClassTarget left_coloring) < Fintype.card V := by
  classical
  letI : Fintype sep.right := sep.right.toFinite.fintype
  have hle :
      Fintype.card (sep.rightColorClassTarget left_coloring) <= Fintype.card sep.right := by
    refine Fintype.card_le_of_surjective
      (sep.rightColorClassQuotientMap left_coloring) ?_
    intro y
    rcases y with ⟨_, hy⟩
    rcases hy with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hright_lt : Fintype.card sep.right < Fintype.card V := by
    have hnat := sep.natCard_right_lt_of_proper hproper
    simpa [Nat.card_eq_fintype_card] using hnat
  exact lt_of_le_of_lt hle hright_lt

noncomputable def Separation.rightColorClassContraction
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c)) :
    GraphContraction sep.rightWithSeparatorClique := by
  classical
  refine GraphContraction.ofMap sep.rightWithSeparatorClique
    (sep.rightColorClassQuotientMap left_coloring) ?_ ?_
  · intro y
    rcases y with ⟨_, hy⟩
    rcases hy with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  · intro y
    rcases y with ⟨tag, hy⟩
    rcases hy with ⟨r, hr⟩
    have hfr :
        sep.rightColorClassQuotientMap left_coloring r = ⟨tag, ⟨r, hr⟩⟩ := by
      exact Subtype.ext hr
    refine {
      preconnected := ?_
      nonempty := ?_
    }
    · intro a b
      have ha_base_tag :
          sep.rightColorClassBaseMap left_coloring (a : sep.right) = tag :=
        congrArg Subtype.val a.2
      have hb_base_tag :
          sep.rightColorClassBaseMap left_coloring (b : sep.right) = tag :=
        congrArg Subtype.val b.2
      have ha_base :
          sep.rightColorClassBaseMap left_coloring (a : sep.right) =
            sep.rightColorClassBaseMap left_coloring r :=
        ha_base_tag.trans hr.symm
      have hb_base :
          sep.rightColorClassBaseMap left_coloring (b : sep.right) =
            sep.rightColorClassBaseMap left_coloring r :=
        hb_base_tag.trans hr.symm
      by_cases hr_left : (r : V) ∈ sep.left
      · by_cases hab : a = b
        · exact hab ▸ SimpleGraph.Reachable.refl a
        · have ha_left : ((a : sep.right) : V) ∈ sep.left := by
            by_contra ha_not
            have hbad := ha_base
            simp [Separation.rightColorClassBaseMap, ha_not, hr_left] at hbad
          have hb_left : ((b : sep.right) : V) ∈ sep.left := by
            by_contra hb_not
            have hbad := hb_base
            simp [Separation.rightColorClassBaseMap, hb_not, hr_left] at hbad
          have hab_right : (a : sep.right) ≠ (b : sep.right) := by
            intro h
            exact hab (Subtype.ext h)
          have hside_adj :
              sep.rightWithSeparatorClique.Adj (a : sep.right) (b : sep.right) :=
            Or.inr ⟨ha_left, hb_left, hab_right⟩
          exact (show
            (sep.rightWithSeparatorClique.induce
              {x : sep.right | sep.rightColorClassQuotientMap left_coloring x =
                ⟨tag, ⟨r, hr⟩⟩}).Adj a b from hside_adj).reachable
      · have fiber_eq_rep :
            forall a :
              {x : sep.right | sep.rightColorClassQuotientMap left_coloring x =
                ⟨tag, ⟨r, hr⟩⟩},
              (a : sep.right) = r := by
          intro a
          have ha_base_tag :
              sep.rightColorClassBaseMap left_coloring (a : sep.right) = tag :=
            congrArg Subtype.val a.2
          have ha_base :
              sep.rightColorClassBaseMap left_coloring (a : sep.right) =
                sep.rightColorClassBaseMap left_coloring r :=
            ha_base_tag.trans hr.symm
          by_cases ha_left : ((a : sep.right) : V) ∈ sep.left
          · have hbad := ha_base
            simp [Separation.rightColorClassBaseMap, ha_left, hr_left] at hbad
          · have hsub :
                (⟨(a : sep.right), ha_left⟩ :
                  {x : sep.right // (x : V) ∉ sep.left}) = ⟨r, hr_left⟩ := by
              simpa [Separation.rightColorClassBaseMap, ha_left, hr_left] using ha_base
            exact congrArg Subtype.val hsub
        have hab : a = b := by
          apply Subtype.ext
          exact (fiber_eq_rep a).trans (fiber_eq_rep b).symm
        exact hab ▸ SimpleGraph.Reachable.refl a
    · exact ⟨⟨r, hfr⟩⟩

theorem Separation.rightColorClassContraction_graph_eq
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c)) :
    (sep.rightColorClassContraction left_coloring).graph =
      contractionTargetGraph sep.rightWithSeparatorClique
        (sep.rightColorClassQuotientMap left_coloring) := rfl

theorem Separation.rightColorClassContraction_fiber_singleton_of_separator_color_injective
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (hseparator_color_injective :
      forall a b : sep.separator,
        left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩ ->
          a = b) :
    forall y : (sep.rightColorClassContraction left_coloring).Target,
      forall v w : sep.right,
        (sep.rightColorClassContraction left_coloring).map v = y ->
          (sep.rightColorClassContraction left_coloring).map w = y ->
            v = w := by
  intro y v w hv hw
  exact sep.rightColorClassQuotientMap_fiber_singleton_of_separator_color_injective
    left_coloring hseparator_color_injective v w (hv.trans hw.symm)

theorem colorable_of_separation_right_color_class_baseMap_quotient
    {G : SimpleGraph V} [Fintype V] {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (hquot_colorable :
      (contractionTargetGraph sep.rightWithSeparatorClique
        (sep.rightColorClassBaseMap left_coloring)).Colorable c) :
    G.Colorable c :=
  colorable_of_separation_right_map_quotient_colorable_agree
    sep left_coloring (sep.rightColorClassBaseMap left_coloring)
    hquot_colorable
    (sep.rightColorClassBaseMap_no_true_edge_collapsed left_coloring)
    (sep.rightColorClassBaseMap_separator_classes left_coloring)

theorem colorable_of_separation_right_color_class_range_quotient
    {G : SimpleGraph V} [Fintype V] {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (hquot_colorable :
      (contractionTargetGraph sep.rightWithSeparatorClique
        (sep.rightColorClassQuotientMap left_coloring)).Colorable c) :
    G.Colorable c :=
  colorable_of_separation_right_map_quotient_colorable_agree
    sep left_coloring (sep.rightColorClassQuotientMap left_coloring)
    hquot_colorable
    (sep.rightColorClassQuotientMap_no_true_edge_collapsed left_coloring)
    (sep.rightColorClassQuotientMap_separator_classes left_coloring)

theorem colorable_of_separation_right_color_class_contraction
    {G : SimpleGraph V} [Fintype V] {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (hquot_colorable : (sep.rightColorClassContraction left_coloring).graph.Colorable c) :
    G.Colorable c := by
  exact colorable_of_separation_right_color_class_range_quotient sep left_coloring
    (by
      simpa [Separation.rightColorClassContraction_graph_eq] using hquot_colorable)

theorem colorable_of_separation_right_color_class_quotient
    {G : SimpleGraph V} {c : Nat}
    (sep : Separation G)
    (left_coloring : (G.induce sep.left).Coloring (Fin c))
    (C : GraphContraction sep.rightWithSeparatorClique)
    (hquot_colorable : C.graph.Colorable c)
    (hno_true_edge_collapsed :
      forall a b : sep.right,
        (G.induce sep.right).Adj a b -> C.map a ≠ C.map b)
    (hseparator_classes :
      forall a b : sep.separator,
        C.map (⟨(a : V), a.2.2⟩ : sep.right) =
            C.map (⟨(b : V), b.2.2⟩ : sep.right) ↔
          left_coloring ⟨(a : V), a.2.1⟩ =
            left_coloring ⟨(b : V), b.2.1⟩) :
    G.Colorable c := by
  classical
  exact colorable_of_separation_right_quotient_colorable_agree sep left_coloring C
    hquot_colorable hno_true_edge_collapsed (by
      intro quot_coloring
      exact exists_recoloring_for_separator_color_class_quotient
        sep left_coloring C quot_coloring hseparator_classes)

end Schematic.Math.GraphTheory
