import DominatingFourColour.Basic
import Schematic.Math.GraphTheory.Contractions
import Mathlib.Logic.Equiv.Fintype

/-! Complete each side of a separation along its separator. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

structure PaperColouringStitchData (G : SimpleGraph V) (c : Nat) where
  sep : Separation G
  proper : sep.Proper
  order_at_most : sep.OrderAtMost c
  left_coloring : (G.induce sep.left).Coloring (Fin c)
  right_coloring : (G.induce sep.right).Coloring (Fin c)
  agree_on_separator :
    forall (v : V) (hv_left : v ∈ sep.left) (hv_right : v ∈ sep.right),
      left_coloring ⟨v, hv_left⟩ = right_coloring ⟨v, hv_right⟩

def Separation.leftWithSeparatorClique
    {G : SimpleGraph V}
    (S : Separation G) : SimpleGraph S.left where
  Adj a b :=
    (G.induce S.left).Adj a b ∨
      ((a : V) ∈ S.right ∧ (b : V) ∈ S.right ∧ a ≠ b)
  symm := by
    rintro a b (hab | ⟨ha, hb, hne⟩)
    · exact Or.inl hab.symm
    · exact Or.inr ⟨hb, ha, hne.symm⟩
  loopless := ⟨by
    intro a h
    rcases h with h | h
    · exact h.ne rfl
    · exact h.2.2 rfl⟩

def Separation.rightWithSeparatorClique
    {G : SimpleGraph V}
    (S : Separation G) : SimpleGraph S.right :=
  S.symm.leftWithSeparatorClique

theorem Separation.leftWithSeparatorClique_adj_of_induce_adj
    {G : SimpleGraph V}
    (S : Separation G)
    {a b : S.left}
    (hab : (G.induce S.left).Adj a b) :
    S.leftWithSeparatorClique.Adj a b :=
  Or.inl hab

theorem Separation.rightWithSeparatorClique_adj_of_induce_adj
    {G : SimpleGraph V}
    (S : Separation G)
    {a b : S.right}
    (hab : (G.induce S.right).Adj a b) :
    S.rightWithSeparatorClique.Adj a b :=
  S.symm.leftWithSeparatorClique_adj_of_induce_adj hab

theorem Separation.leftWithSeparatorClique_separator_adj
    {G : SimpleGraph V}
    (S : Separation G)
    {a b : S.left}
    (ha : (a : V) ∈ S.right)
    (hb : (b : V) ∈ S.right)
    (hab : a ≠ b) :
    S.leftWithSeparatorClique.Adj a b :=
  Or.inr ⟨ha, hb, hab⟩

theorem Separation.rightWithSeparatorClique_separator_adj
    {G : SimpleGraph V}
    (S : Separation G)
    {a b : S.right}
    (ha : (a : V) ∈ S.left)
    (hb : (b : V) ∈ S.left)
    (hab : a ≠ b) :
    S.rightWithSeparatorClique.Adj a b :=
  S.symm.leftWithSeparatorClique_separator_adj ha hb hab

theorem Separation.leftWithSeparatorClique_separator_isClique
    {G : SimpleGraph V}
    (S : Separation G) :
    S.leftWithSeparatorClique.IsClique
      {v : S.left | (v : V) ∈ S.right} := by
  intro a ha b hb hne
  exact S.leftWithSeparatorClique_separator_adj ha hb hne

theorem Separation.rightWithSeparatorClique_separator_isClique
    {G : SimpleGraph V}
    (S : Separation G) :
    S.rightWithSeparatorClique.IsClique
      {v : S.right | (v : V) ∈ S.left} := by
  exact S.symm.leftWithSeparatorClique_separator_isClique

def Separation.leftInduceHomWithSeparatorClique
    {G : SimpleGraph V}
    (S : Separation G) :
    (G.induce S.left) →g S.leftWithSeparatorClique where
  toFun v := v
  map_rel' := by
    intro a b hab
    exact S.leftWithSeparatorClique_adj_of_induce_adj hab

def Separation.rightInduceHomWithSeparatorClique
    {G : SimpleGraph V}
    (S : Separation G) :
    (G.induce S.right) →g S.rightWithSeparatorClique :=
  S.symm.leftInduceHomWithSeparatorClique

def Separation.leftWithSeparatorCliqueHom
    {G : SimpleGraph V}
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator) :
    S.leftWithSeparatorClique →g G where
  toFun v := v
  map_rel' := by
    intro a b hab
    rcases hab with hab | ⟨ha_right, hb_right, hne⟩
    · exact hab
    · exact hseparator_clique
        ⟨a.2, ha_right⟩ ⟨b.2, hb_right⟩
        (by
          intro hab_eq
          exact hne (Subtype.ext hab_eq))

def Separation.rightWithSeparatorCliqueHom
    {G : SimpleGraph V}
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator) :
    S.rightWithSeparatorClique →g G :=
  S.symm.leftWithSeparatorCliqueHom (by
    simpa only [S.separator_symm] using hseparator_clique)

def Separation.leftOrderedClique
    {G : SimpleGraph V}
    (S : Separation G)
    (L : OrderedClique G)
    (hleft : L.vertexSet ⊆ S.left) :
    OrderedClique S.leftWithSeparatorClique := by
  cases L with
  | nil =>
      exact .nil
  | single v =>
      exact .single ⟨v, hleft (by simp [OrderedClique.vertexSet])⟩
  | pair v1 v2 edge =>
      let hv1 : v1 ∈ S.left := hleft (by simp [OrderedClique.vertexSet])
      let hv2 : v2 ∈ S.left := hleft (by simp [OrderedClique.vertexSet])
      exact .pair ⟨v1, hv1⟩ ⟨v2, hv2⟩ (Or.inl edge)

def Separation.rightOrderedClique
    {G : SimpleGraph V}
    (S : Separation G)
    (L : OrderedClique G)
    (hright : L.vertexSet ⊆ S.right) :
    OrderedClique S.rightWithSeparatorClique :=
  S.symm.leftOrderedClique L hright

noncomputable def Separation.rightRestrictedOrderedClique
    {G : SimpleGraph V}
    (S : Separation G)
    (L : OrderedClique G) :
    OrderedClique S.rightWithSeparatorClique := by
  classical
  cases L with
  | nil =>
      exact .nil
  | single v =>
      by_cases hv : v ∈ S.right
      · exact .single ⟨v, hv⟩
      · exact .nil
  | pair v1 v2 edge =>
      by_cases hv1 : v1 ∈ S.right
      · by_cases hv2 : v2 ∈ S.right
        · exact .pair ⟨v1, hv1⟩ ⟨v2, hv2⟩ (Or.inl edge)
        · exact .single ⟨v1, hv1⟩
      · by_cases hv2 : v2 ∈ S.right
        · exact .single ⟨v2, hv2⟩
        · exact .nil

theorem compatible_model_lift_leftWithSeparatorClique_of_separator_clique
    {G : SimpleGraph V}
    (S : Separation G)
    (L : OrderedClique G)
    (hleft : L.vertexSet ⊆ S.left)
    (hseparator_clique : G.IsClique S.separator) :
    CompatibleDominatingK5Model (S.leftOrderedClique L hleft) ->
      CompatibleDominatingK5Model L := by
  rintro ⟨T, hT⟩
  let f : S.leftWithSeparatorClique →g G := S.leftWithSeparatorCliqueHom hseparator_clique
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext h
  let Tmap : DominatingK5Model G := T.map f hf
  refine ⟨Tmap, ?_⟩
  cases L with
  | nil =>
      exact trivial
  | single v =>
      let hv : v ∈ S.left := hleft (by simp [OrderedClique.vertexSet])
      have hT' : T.branchIndex (⟨v, hv⟩ : S.left) <= 1 := by
        simpa [Separation.leftOrderedClique, LCompatible, hv] using hT
      have hidx :
          Tmap.branchIndex v = T.branchIndex (⟨v, hv⟩ : S.left) := by
        simpa [Tmap, f, Separation.leftWithSeparatorCliqueHom] using
          (T.branchIndex_map f hf (⟨v, hv⟩ : S.left))
      simpa [LCompatible, hidx] using hT'
  | pair v1 v2 edge =>
      let hv1 : v1 ∈ S.left := hleft (by simp [OrderedClique.vertexSet])
      let hv2 : v2 ∈ S.left := hleft (by simp [OrderedClique.vertexSet])
      have hT' :
          T.branchIndex (⟨v1, hv1⟩ : S.left) <= 1 ∧
            T.branchIndex (⟨v2, hv2⟩ : S.left) <= 2 ∧
              (T.branchIndex (⟨v2, hv2⟩ : S.left) = 2 ->
                T.branchIndex (⟨v1, hv1⟩ : S.left) = 1) := by
        simpa [Separation.leftOrderedClique, LCompatible, hv1, hv2] using hT
      have hidx1 :
          Tmap.branchIndex v1 = T.branchIndex (⟨v1, hv1⟩ : S.left) := by
        simpa [Tmap, f, Separation.leftWithSeparatorCliqueHom] using
          (T.branchIndex_map f hf (⟨v1, hv1⟩ : S.left))
      have hidx2 :
          Tmap.branchIndex v2 = T.branchIndex (⟨v2, hv2⟩ : S.left) := by
        simpa [Tmap, f, Separation.leftWithSeparatorCliqueHom] using
          (T.branchIndex_map f hf (⟨v2, hv2⟩ : S.left))
      simpa [LCompatible, hidx1, hidx2] using hT'

theorem compatible_model_lift_rightWithSeparatorClique_of_separator_clique
    {G : SimpleGraph V}
    (S : Separation G)
    (L : OrderedClique G)
    (hright : L.vertexSet ⊆ S.right)
    (hseparator_clique : G.IsClique S.separator) :
    CompatibleDominatingK5Model (S.rightOrderedClique L hright) ->
      CompatibleDominatingK5Model L :=
  compatible_model_lift_leftWithSeparatorClique_of_separator_clique
    S.symm L hright (by simpa only [S.separator_symm] using hseparator_clique)

theorem compatible_model_lift_rightWithSeparatorClique_restrict_of_separator_clique
    {G : SimpleGraph V}
    (S : Separation G)
    (L : OrderedClique G)
    (hseparator_clique : G.IsClique S.separator) :
    CompatibleDominatingK5Model (S.rightRestrictedOrderedClique L) ->
      CompatibleDominatingK5Model L := by
  classical
  rintro ⟨T, hT⟩
  let f : S.rightWithSeparatorClique →g G := S.rightWithSeparatorCliqueHom hseparator_clique
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext h
  let Tmap : DominatingK5Model G := T.map f hf
  have hidx_not_right :
      forall {v : V}, v ∉ S.right -> Tmap.branchIndex v = 0 := by
    intro v hv
    exact Tmap.branchIndex_eq_zero_of_forall_not_mem (by
      intro i hi
      simp only [Tmap, DominatingModel.map, SimpleGraph.Subgraph.map_verts,
        Set.mem_image] at hi
      rcases hi with ⟨x, _hx, hxv⟩
      exact hv (by
        rw [← hxv]
        exact x.2))
  refine ⟨Tmap, ?_⟩
  cases L with
  | nil =>
      exact trivial
  | single v =>
      by_cases hv : v ∈ S.right
      · have hT' : T.branchIndex (⟨v, hv⟩ : S.right) <= 1 := by
          simpa [Separation.rightRestrictedOrderedClique, hv, LCompatible] using hT
        have hidx :
            Tmap.branchIndex v = T.branchIndex (⟨v, hv⟩ : S.right) := by
          simpa [Tmap, f, Separation.rightWithSeparatorCliqueHom] using
            (T.branchIndex_map f hf (⟨v, hv⟩ : S.right))
        simpa [LCompatible, hidx] using hT'
      · have hidx : Tmap.branchIndex v = 0 := hidx_not_right hv
        simp [LCompatible, hidx]
  | pair v1 v2 edge =>
      by_cases hv1 : v1 ∈ S.right
      · by_cases hv2 : v2 ∈ S.right
        · have hT' :
              T.branchIndex (⟨v1, hv1⟩ : S.right) <= 1 ∧
                T.branchIndex (⟨v2, hv2⟩ : S.right) <= 2 ∧
                  (T.branchIndex (⟨v2, hv2⟩ : S.right) = 2 ->
                    T.branchIndex (⟨v1, hv1⟩ : S.right) = 1) := by
            simpa [Separation.rightRestrictedOrderedClique, hv1, hv2, LCompatible] using hT
          have hidx1 :
              Tmap.branchIndex v1 = T.branchIndex (⟨v1, hv1⟩ : S.right) := by
            simpa [Tmap, f, Separation.rightWithSeparatorCliqueHom] using
              (T.branchIndex_map f hf (⟨v1, hv1⟩ : S.right))
          have hidx2 :
              Tmap.branchIndex v2 = T.branchIndex (⟨v2, hv2⟩ : S.right) := by
            simpa [Tmap, f, Separation.rightWithSeparatorCliqueHom] using
              (T.branchIndex_map f hf (⟨v2, hv2⟩ : S.right))
          simpa [LCompatible, hidx1, hidx2] using hT'
        · have hT' : T.branchIndex (⟨v1, hv1⟩ : S.right) <= 1 := by
            simpa [Separation.rightRestrictedOrderedClique, hv1, hv2, LCompatible] using hT
          have hidx1 :
              Tmap.branchIndex v1 = T.branchIndex (⟨v1, hv1⟩ : S.right) := by
            simpa [Tmap, f, Separation.rightWithSeparatorCliqueHom] using
              (T.branchIndex_map f hf (⟨v1, hv1⟩ : S.right))
          have hidx2 : Tmap.branchIndex v2 = 0 := hidx_not_right hv2
          simp [LCompatible, hidx1, hidx2]
          exact hT'
      · by_cases hv2 : v2 ∈ S.right
        · have hT' : T.branchIndex (⟨v2, hv2⟩ : S.right) <= 1 := by
            simpa [Separation.rightRestrictedOrderedClique, hv1, hv2, LCompatible] using hT
          have hidx1 : Tmap.branchIndex v1 = 0 := hidx_not_right hv1
          have hidx2 :
              Tmap.branchIndex v2 = T.branchIndex (⟨v2, hv2⟩ : S.right) := by
            simpa [Tmap, f, Separation.rightWithSeparatorCliqueHom] using
              (T.branchIndex_map f hf (⟨v2, hv2⟩ : S.right))
          simp [LCompatible, hidx1, hidx2]
          omega
        · have hidx1 : Tmap.branchIndex v1 = 0 := hidx_not_right hv1
          have hidx2 : Tmap.branchIndex v2 = 0 := hidx_not_right hv2
          simp [LCompatible, hidx1, hidx2]

theorem no_model_leftWithSeparatorClique_of_global_no_model_of_separator_clique
    {G : SimpleGraph V}
    (S : Separation G)
    (L : OrderedClique G)
    (hleft : L.vertexSet ⊆ S.left)
    (hseparator_clique : G.IsClique S.separator)
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    Not (CompatibleDominatingK5Model (S.leftOrderedClique L hleft)) := by
  intro hside
  exact hno_model
    (compatible_model_lift_leftWithSeparatorClique_of_separator_clique
      S L hleft hseparator_clique hside)

theorem no_model_rightWithSeparatorClique_of_global_no_model_of_separator_clique
    {G : SimpleGraph V}
    (S : Separation G)
    (L : OrderedClique G)
    (hright : L.vertexSet ⊆ S.right)
    (hseparator_clique : G.IsClique S.separator)
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    Not (CompatibleDominatingK5Model (S.rightOrderedClique L hright)) :=
  no_model_leftWithSeparatorClique_of_global_no_model_of_separator_clique
    S.symm L hright (by simpa only [S.separator_symm] using hseparator_clique) hno_model

theorem no_model_rightWithSeparatorClique_restrict_of_global_no_model_of_separator_clique
    {G : SimpleGraph V}
    (S : Separation G)
    (L : OrderedClique G)
    (hseparator_clique : G.IsClique S.separator)
    (hno_model : Not (CompatibleDominatingK5Model L)) :
    Not (CompatibleDominatingK5Model (S.rightRestrictedOrderedClique L)) := by
  intro hside
  exact hno_model
    (compatible_model_lift_rightWithSeparatorClique_restrict_of_separator_clique
      S L hseparator_clique hside)

theorem compatible_nil_model_lift_leftWithSeparatorClique_of_separator_clique
    {G : SimpleGraph V}
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator) :
    CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique S.leftWithSeparatorClique) ->
      CompatibleDominatingK5Model (OrderedClique.nil : OrderedClique G) := by
  rintro ⟨T, _hT⟩
  exact ⟨T.map (S.leftWithSeparatorCliqueHom hseparator_clique)
    (by
      intro a b hab
      exact Subtype.ext hab),
    trivial⟩

theorem compatible_nil_model_lift_rightWithSeparatorClique_of_separator_clique
    {G : SimpleGraph V}
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator) :
    CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique) ->
      CompatibleDominatingK5Model (OrderedClique.nil : OrderedClique G) :=
  compatible_nil_model_lift_leftWithSeparatorClique_of_separator_clique
    S.symm (by simpa only [S.separator_symm] using hseparator_clique)

theorem no_nil_model_leftWithSeparatorClique_of_global_no_nil_model_of_separator_clique
    {G : SimpleGraph V}
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator)
    (hno_model :
      Not (CompatibleDominatingK5Model (OrderedClique.nil : OrderedClique G))) :
    Not (CompatibleDominatingK5Model
      (OrderedClique.nil : OrderedClique S.leftWithSeparatorClique)) := by
  intro hside
  exact hno_model
    (compatible_nil_model_lift_leftWithSeparatorClique_of_separator_clique
      S hseparator_clique hside)

theorem no_nil_model_rightWithSeparatorClique_of_global_no_nil_model_of_separator_clique
    {G : SimpleGraph V}
    (S : Separation G)
    (hseparator_clique : G.IsClique S.separator)
    (hno_model :
      Not (CompatibleDominatingK5Model (OrderedClique.nil : OrderedClique G))) :
    Not (CompatibleDominatingK5Model
      (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique)) :=
  no_nil_model_leftWithSeparatorClique_of_global_no_nil_model_of_separator_clique
    S.symm (by simpa only [S.separator_symm] using hseparator_clique) hno_model

theorem Separation.induce_left_colorable_of_leftWithSeparatorClique_colorable
    {G : SimpleGraph V}
    (S : Separation G)
    {c : Nat}
    (h : S.leftWithSeparatorClique.Colorable c) :
    (G.induce S.left).Colorable c :=
  SimpleGraph.Colorable.of_hom S.leftInduceHomWithSeparatorClique h

theorem Separation.induce_right_colorable_of_rightWithSeparatorClique_colorable
    {G : SimpleGraph V}
    (S : Separation G)
    {c : Nat}
    (h : S.rightWithSeparatorClique.Colorable c) :
    (G.induce S.right).Colorable c :=
  S.symm.induce_left_colorable_of_leftWithSeparatorClique_colorable h

end Schematic.Math.GraphTheory
