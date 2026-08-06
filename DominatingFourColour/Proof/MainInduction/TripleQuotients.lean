import DominatingFourColour.Proof.MainInduction.TripleContractions
import DominatingFourColour.Proof.MainInduction.SeparationColoring

/-! Color-class quotients and collapse cases for triple separators. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem Separation.triple_rightColorClassQuotientMap_same_fibers_pair_collapse
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hxy_same :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩)
    (hxz_diff :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩)
    (hyz_diff :
      left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ≠
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩) :
    let C := S.rightTripleXYContraction hxy hseparator
    forall a b : S.right,
      S.rightColorClassQuotientMap left_coloring a =
          S.rightColorClassQuotientMap left_coloring b ↔
        C.map a = C.map b := by
  classical
  intro C a b
  let rx := S.rightTripleX hseparator
  let ry := S.rightTripleY hseparator
  let hxy_right := S.rightTripleXYAdj hxy hseparator
  have hC_map_eq_iff :
      C.map a = C.map b ↔
        (a ∈ ({rx, ry} : Set S.right) ∧
          b ∈ ({rx, ry} : Set S.right)) ∨
        (a = b ∧ a ∉ ({rx, ry} : Set S.right) ∧
          b ∉ ({rx, ry} : Set S.right)) := by
    simpa [C, Separation.rightTripleXYContraction] using
      (GraphContraction.collapseEdge_map_eq_iff
        S.rightWithSeparatorClique hxy_right (v := a) (w := b))
  have hsep_cases :
      forall r : S.right, (r : V) ∈ S.left ->
        (r : V) = x ∨ (r : V) = y ∨ (r : V) = z := by
    intro r hr_left
    have hr_sep : (r : V) ∈ S.separator := ⟨hr_left, r.2⟩
    have : (r : V) ∈ ({x, y, z} : Set V) := by
      simpa [hseparator] using hr_sep
    simpa [Set.mem_insert_iff] using this
  have hin_pair_iff :
      forall r : S.right, r ∈ ({rx, ry} : Set S.right) ↔
        (r : V) = x ∨ (r : V) = y := by
    intro r
    constructor
    · intro hr
      rcases (by simpa using hr) with hrx | hry
      · exact Or.inl (congrArg (fun s : S.right => (s : V)) hrx)
      · exact Or.inr (congrArg (fun s : S.right => (s : V)) hry)
    · intro hr
      rcases hr with rfl | rfl
      · left
        rfl
      · right
        rfl
  constructor
  · intro hquot
    have hbase :
        S.rightColorClassBaseMap left_coloring a =
          S.rightColorClassBaseMap left_coloring b :=
      congrArg Subtype.val hquot
    by_cases ha_left : (a : V) ∈ S.left
    · by_cases hb_left : (b : V) ∈ S.left
      · have hcolor :
            left_coloring ⟨(a : V), ha_left⟩ =
              left_coloring ⟨(b : V), hb_left⟩ := by
          simpa [Separation.rightColorClassBaseMap, ha_left, hb_left] using hbase
        rcases hsep_cases a ha_left with ha_x | ha_y | ha_z <;>
          rcases hsep_cases b hb_left with hb_x | hb_y | hb_z
        · exact hC_map_eq_iff.mpr
            (Or.inl ⟨(hin_pair_iff a).mpr (Or.inl ha_x),
              (hin_pair_iff b).mpr (Or.inl hb_x)⟩)
        · exact hC_map_eq_iff.mpr
            (Or.inl ⟨(hin_pair_iff a).mpr (Or.inl ha_x),
              (hin_pair_iff b).mpr (Or.inr hb_y)⟩)
        · exact False.elim
            (hxz_diff (by simpa [ha_x, hb_z] using hcolor))
        · exact hC_map_eq_iff.mpr
            (Or.inl ⟨(hin_pair_iff a).mpr (Or.inr ha_y),
              (hin_pair_iff b).mpr (Or.inl hb_x)⟩)
        · exact hC_map_eq_iff.mpr
            (Or.inl ⟨(hin_pair_iff a).mpr (Or.inr ha_y),
              (hin_pair_iff b).mpr (Or.inr hb_y)⟩)
        · exact False.elim
            (hyz_diff (by simpa [ha_y, hb_z] using hcolor))
        · exact False.elim
            (hxz_diff (by simpa [ha_z, hb_x] using hcolor.symm))
        · exact False.elim
            (hyz_diff (by simpa [ha_z, hb_y] using hcolor.symm))
        · have hab : a = b := Subtype.ext (ha_z.trans hb_z.symm)
          exact by rw [hab]
      · simp [Separation.rightColorClassBaseMap, ha_left, hb_left] at hbase
    · by_cases hb_left : (b : V) ∈ S.left
      · simp [Separation.rightColorClassBaseMap, ha_left, hb_left] at hbase
      · have hab :
            (⟨a, ha_left⟩ : {r : S.right // (r : V) ∉ S.left}) =
              ⟨b, hb_left⟩ := by
          simpa [Separation.rightColorClassBaseMap, ha_left, hb_left] using hbase
        have hab' : a = b := congrArg Subtype.val hab
        rw [hab']
  · intro hC
    apply Subtype.ext
    change S.rightColorClassBaseMap left_coloring a =
      S.rightColorClassBaseMap left_coloring b
    have hcases := hC_map_eq_iff.mp hC
    rcases hcases with hboth | hout
    · rcases (hin_pair_iff a).mp hboth.1 with ha_x | ha_y <;>
        rcases (hin_pair_iff b).mp hboth.2 with hb_x | hb_y
      · simp [Separation.rightColorClassBaseMap,
          (S.triple_vertices_mem_left hseparator).1, ha_x, hb_x]
      · simpa [Separation.rightColorClassBaseMap,
          (S.triple_vertices_mem_left hseparator).1,
          (S.triple_vertices_mem_left hseparator).2.1, ha_x, hb_y] using hxy_same
      · simpa [Separation.rightColorClassBaseMap,
          (S.triple_vertices_mem_left hseparator).1,
          (S.triple_vertices_mem_left hseparator).2.1, ha_y, hb_x] using hxy_same.symm
      · simp [Separation.rightColorClassBaseMap,
          (S.triple_vertices_mem_left hseparator).2.1, ha_y, hb_y]
    · rcases hout with ⟨hab, _ha, _hb⟩
      rw [hab]

theorem Separation.triple_pair_right_color_class_quotient_colorable_of_pair_collapse_colorable
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hxy_same :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩)
    (hxz_diff :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩)
    (hyz_diff :
      left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ≠
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩) :
    let C := S.rightTripleXYContraction hxy hseparator
    C.graph.Colorable 4 ->
      (contractionTargetGraph S.rightWithSeparatorClique
        (S.rightColorClassQuotientMap left_coloring)).Colorable 4 := by
  classical
  intro C hC_colorable
  let g : S.right -> C.Target := fun r => C.map r
  have hg_colorable :
      (contractionTargetGraph S.rightWithSeparatorClique g).Colorable 4 := by
    simpa [g, C, Separation.rightTripleXYContraction,
      GraphContraction.collapseEdge,
      GraphContraction.collapseSubgraph, GraphContraction.ofMap] using hC_colorable
  have hsame_fibers :
      forall a b : S.right,
        S.rightColorClassQuotientMap left_coloring a =
            S.rightColorClassQuotientMap left_coloring b ↔
          g a = g b := by
    simpa [g, C] using
      S.triple_rightColorClassQuotientMap_same_fibers_pair_collapse
        hxy hxz hyz hseparator left_coloring hxy_same hxz_diff hyz_diff
  exact
    GraphContraction.contractionTargetGraph_colorable_of_same_fibers
      (G := S.rightWithSeparatorClique)
      (S.rightColorClassQuotientMap left_coloring) g hsame_fibers hg_colorable

theorem Separation.triple_pair_xz_right_color_class_quotient_colorable_of_pair_collapse_colorable
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hxz_same :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩)
    (hxy_diff :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩)
    (hyz_diff :
      left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ≠
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩) :
    let C := S.rightTripleXZContraction hxz hseparator
    C.graph.Colorable 4 ->
      (contractionTargetGraph S.rightWithSeparatorClique
        (S.rightColorClassQuotientMap left_coloring)).Colorable 4 := by
  classical
  have hseparator_xzy : S.separator = ({x, z, y} : Set V) := by
    rw [hseparator]
    ext v
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hxz_same' :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator_xzy).1⟩ =
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator_xzy).2.1⟩ := by
    simpa using hxz_same
  have hxy_diff' :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator_xzy).1⟩ ≠
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator_xzy).2.2⟩ := by
    simpa using hxy_diff
  have hzy_diff' :
      left_coloring ⟨z, (S.triple_vertices_mem_left hseparator_xzy).2.1⟩ ≠
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator_xzy).2.2⟩ := by
    intro hzy_same
    exact hyz_diff (by simpa using hzy_same.symm)
  simpa [hseparator_xzy] using
    (S.triple_pair_right_color_class_quotient_colorable_of_pair_collapse_colorable
      (x := x) (y := z) (z := y)
      hxz hxy hyz.symm hseparator_xzy left_coloring
      hxz_same' hxy_diff' hzy_diff')

theorem Separation.triple_pair_yz_right_color_class_quotient_colorable_of_pair_collapse_colorable
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hyz_same :
      left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ =
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩)
    (hxy_diff :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩)
    (hxz_diff :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩) :
    let C := S.rightTripleYZContraction hyz hseparator
    C.graph.Colorable 4 ->
      (contractionTargetGraph S.rightWithSeparatorClique
        (S.rightColorClassQuotientMap left_coloring)).Colorable 4 := by
  classical
  have hseparator_yzx : S.separator = ({y, z, x} : Set V) := by
    rw [hseparator]
    ext v
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hyz_same' :
      left_coloring ⟨y, (S.triple_vertices_mem_left hseparator_yzx).1⟩ =
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator_yzx).2.1⟩ := by
    simpa using hyz_same
  have hyx_diff' :
      left_coloring ⟨y, (S.triple_vertices_mem_left hseparator_yzx).1⟩ ≠
        left_coloring ⟨x, (S.triple_vertices_mem_left hseparator_yzx).2.2⟩ := by
    intro hyx_same
    exact hxy_diff (by simpa using hyx_same.symm)
  have hzx_diff' :
      left_coloring ⟨z, (S.triple_vertices_mem_left hseparator_yzx).2.1⟩ ≠
        left_coloring ⟨x, (S.triple_vertices_mem_left hseparator_yzx).2.2⟩ := by
    intro hzx_same
    exact hxz_diff (by simpa using hzx_same.symm)
  simpa [hseparator_yzx] using
    (S.triple_pair_right_color_class_quotient_colorable_of_pair_collapse_colorable
      (x := y) (y := z) (z := x)
      hyz hxy.symm hxz.symm hseparator_yzx left_coloring
      hyz_same' hyx_diff' hzx_diff')

theorem Separation.triple_rightColorClassQuotientMap_same_fibers_triple_collapse
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hxy_same :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩)
    (hxz_same :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩) :
    let C := S.rightTripleXYZContraction hxy hxz hseparator
    forall a b : S.right,
      S.rightColorClassQuotientMap left_coloring a =
          S.rightColorClassQuotientMap left_coloring b ↔
        C.map a = C.map b := by
  classical
  intro C a b
  let rx := S.rightTripleX hseparator
  let ry := S.rightTripleY hseparator
  let rz := S.rightTripleZ hseparator
  let hxy_right := S.rightTripleXYAdj hxy hseparator
  let hxz_right := S.rightTripleXZAdj hxz hseparator
  have hx_left : x ∈ S.left := (S.triple_vertices_mem_left hseparator).1
  have hy_left : y ∈ S.left := (S.triple_vertices_mem_left hseparator).2.1
  have hz_left : z ∈ S.left := (S.triple_vertices_mem_left hseparator).2.2
  have hin_triple_iff :
      forall r : S.right, r ∈ ({rx, ry, rz} : Set S.right) ↔
        (r : V) = x ∨ (r : V) = y ∨ (r : V) = z := by
    intro r
    constructor
    · intro hr
      rcases Set.mem_insert_iff.mp hr with hrx | htail
      · exact Or.inl (congrArg (fun s : S.right => (s : V)) hrx)
      · rcases Set.mem_insert_iff.mp htail with hry | hrz
        · exact Or.inr (Or.inl (congrArg (fun s : S.right => (s : V)) hry))
        · exact Or.inr (Or.inr (congrArg (fun s : S.right => (s : V))
            (Set.mem_singleton_iff.mp hrz)))
    · intro hr
      rcases hr with hrx | hry | hrz
      · exact Or.inl (Subtype.ext hrx)
      · exact Or.inr (Or.inl (Subtype.ext hry))
      · exact Or.inr (Or.inr (Set.mem_singleton_iff.mpr (Subtype.ext hrz)))
  have hC_map_eq_iff :
      C.map a = C.map b ↔
        (a ∈ ({rx, ry, rz} : Set S.right) ∧
          b ∈ ({rx, ry, rz} : Set S.right)) ∨
        (a = b ∧ a ∉ ({rx, ry, rz} : Set S.right) ∧
          b ∉ ({rx, ry, rz} : Set S.right)) := by
    simpa [C, Separation.rightTripleXYZContraction] using
      (GraphContraction.collapseTriple_map_eq_iff
        S.rightWithSeparatorClique hxy_right hxz_right (v := a) (w := b))
  have hsep_cases :
      forall r : S.right, (r : V) ∈ S.left ->
        (r : V) = x ∨ (r : V) = y ∨ (r : V) = z := by
    intro r hr_left
    have hr_sep : (r : V) ∈ S.separator := ⟨hr_left, r.2⟩
    have : (r : V) ∈ ({x, y, z} : Set V) := by
      simpa [hseparator] using hr_sep
    simpa [Set.mem_insert_iff] using this
  have hcolor_eq_x :
      forall r : S.right, forall hr_left : (r : V) ∈ S.left,
        (r : V) = x ∨ (r : V) = y ∨ (r : V) = z ->
          left_coloring ⟨(r : V), hr_left⟩ =
            left_coloring ⟨x, hx_left⟩ := by
    intro r hr_left hcases
    rcases hcases with hrx | hry | hrz
    · exact congrArg left_coloring (Subtype.ext hrx)
    · exact (congrArg left_coloring (Subtype.ext hry)).trans hxy_same.symm
    · exact (congrArg left_coloring (Subtype.ext hrz)).trans hxz_same.symm
  constructor
  · intro hquot
    have hbase :
        S.rightColorClassBaseMap left_coloring a =
          S.rightColorClassBaseMap left_coloring b :=
      congrArg Subtype.val hquot
    by_cases ha_left : (a : V) ∈ S.left
    · by_cases hb_left : (b : V) ∈ S.left
      · exact hC_map_eq_iff.mpr
          (Or.inl ⟨(hin_triple_iff a).mpr (hsep_cases a ha_left),
            (hin_triple_iff b).mpr (hsep_cases b hb_left)⟩)
      · simp [Separation.rightColorClassBaseMap, ha_left, hb_left] at hbase
    · by_cases hb_left : (b : V) ∈ S.left
      · simp [Separation.rightColorClassBaseMap, ha_left, hb_left] at hbase
      · have hab :
            (⟨a, ha_left⟩ : {r : S.right // (r : V) ∉ S.left}) =
              ⟨b, hb_left⟩ := by
          simpa [Separation.rightColorClassBaseMap, ha_left, hb_left] using hbase
        have hab' : a = b := congrArg Subtype.val hab
        rw [hab']
  · intro hC
    apply Subtype.ext
    change S.rightColorClassBaseMap left_coloring a =
      S.rightColorClassBaseMap left_coloring b
    rcases hC_map_eq_iff.mp hC with hboth | hout
    · have ha_cases := (hin_triple_iff a).mp hboth.1
      have hb_cases := (hin_triple_iff b).mp hboth.2
      have ha_left : (a : V) ∈ S.left := by
        rcases ha_cases with hax | hay | haz
        · simpa [hax] using hx_left
        · simpa [hay] using hy_left
        · simpa [haz] using hz_left
      have hb_left : (b : V) ∈ S.left := by
        rcases hb_cases with hbx | hby | hbz
        · simpa [hbx] using hx_left
        · simpa [hby] using hy_left
        · simpa [hbz] using hz_left
      simp only [Separation.rightColorClassBaseMap]
      rw [dif_pos ha_left, dif_pos hb_left]
      apply congrArg Sum.inl
      exact (hcolor_eq_x a ha_left ha_cases).trans
        (hcolor_eq_x b hb_left hb_cases).symm
    · rcases hout with ⟨hab, _ha, _hb⟩
      rw [hab]

theorem Separation.triple_all_same_right_color_class_quotient_colorable_of_triple_collapse_colorable
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hxy_same :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩)
    (hxz_same :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩) :
    let C := S.rightTripleXYZContraction hxy hxz hseparator
    C.graph.Colorable 4 ->
      (contractionTargetGraph S.rightWithSeparatorClique
        (S.rightColorClassQuotientMap left_coloring)).Colorable 4 := by
  classical
  intro C hC_colorable
  let g : S.right -> C.Target := fun r => C.map r
  have hg_colorable :
      (contractionTargetGraph S.rightWithSeparatorClique g).Colorable 4 := by
    simpa [g, C, Separation.rightTripleXYZContraction,
      GraphContraction.collapseTriple,
      GraphContraction.collapseSubgraph, GraphContraction.ofMap] using hC_colorable
  have hsame_fibers :
      forall a b : S.right,
        S.rightColorClassQuotientMap left_coloring a =
            S.rightColorClassQuotientMap left_coloring b ↔
          g a = g b := by
    simpa [g, C] using
      S.triple_rightColorClassQuotientMap_same_fibers_triple_collapse
        hxy hxz hseparator left_coloring hxy_same hxz_same
  exact
    GraphContraction.contractionTargetGraph_colorable_of_same_fibers
      (G := S.rightWithSeparatorClique)
      (S.rightColorClassQuotientMap left_coloring) g hsame_fibers hg_colorable

theorem colorable_of_triple_separation_right_quotient_colorable_by_color_cases
    [Fintype V]
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V))
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hdistinct :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
          left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ->
        left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩ ->
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ≠
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩ ->
        (contractionTargetGraph S.rightWithSeparatorClique
          (S.rightColorClassQuotientMap left_coloring)).Colorable 4)
    (hxy :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
          left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ->
        left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩ ->
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ≠
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩ ->
        (contractionTargetGraph S.rightWithSeparatorClique
          (S.rightColorClassQuotientMap left_coloring)).Colorable 4)
    (hxz :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
          left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ->
        left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩ ->
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ≠
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩ ->
        (contractionTargetGraph S.rightWithSeparatorClique
          (S.rightColorClassQuotientMap left_coloring)).Colorable 4)
    (hyz :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
          left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ->
        left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ ≠
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩ ->
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ =
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩ ->
        (contractionTargetGraph S.rightWithSeparatorClique
          (S.rightColorClassQuotientMap left_coloring)).Colorable 4)
    (hall :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
          left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ->
        left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩ ->
        (contractionTargetGraph S.rightWithSeparatorClique
          (S.rightColorClassQuotientMap left_coloring)).Colorable 4) :
    G.Colorable 4 := by
  classical
  refine colorable_of_separation_right_color_class_range_quotient S left_coloring ?_
  by_cases hxy_same :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩
  · by_cases hxz_same :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩
    · exact hall hxy_same hxz_same
    · have hyz_diff :
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ≠
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩ := by
        intro hyz_same
        exact hxz_same (hxy_same.trans hyz_same)
      exact hxy hxy_same hxz_same hyz_diff
  · by_cases hxz_same :
      left_coloring ⟨x, (S.triple_vertices_mem_left hseparator).1⟩ =
        left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩
    · have hyz_diff :
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ ≠
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩ := by
        intro hyz_same
        exact hxy_same (hxz_same.trans hyz_same.symm)
      exact hxz hxy_same hxz_same hyz_diff
    · by_cases hyz_same :
        left_coloring ⟨y, (S.triple_vertices_mem_left hseparator).2.1⟩ =
          left_coloring ⟨z, (S.triple_vertices_mem_left hseparator).2.2⟩
      · exact hyz hxy_same hxz_same hyz_same
      · exact hdistinct hxy_same hxz_same hyz_same

theorem colorable_of_triple_separation_collapse_colorable_by_color_cases
    [Fintype V]
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (left_coloring : (G.induce S.left).Coloring (Fin 4))
    (hright : S.rightWithSeparatorClique.Colorable 4)
    (hxy_collapse :
      (S.rightTripleXYContraction hxy hseparator).graph.Colorable 4)
    (hxz_collapse :
      (S.rightTripleXZContraction hxz hseparator).graph.Colorable 4)
    (hyz_collapse :
      (S.rightTripleYZContraction hyz hseparator).graph.Colorable 4)
    (hxyz_collapse :
      (S.rightTripleXYZContraction hxy hxz hseparator).graph.Colorable 4) :
    G.Colorable 4 := by
  classical
  refine
    colorable_of_triple_separation_right_quotient_colorable_by_color_cases
      (G := G) S hseparator left_coloring ?_ ?_ ?_ ?_ ?_
  · intro hxy_color hxz_color hyz_color
    exact
      right_color_class_quotient_colorable_of_rightWithSeparatorClique_colorable_of_triple_colors_distinct
        (G := G) S hseparator left_coloring hxy_color hxz_color hyz_color hright
  · intro hxy_same hxz_diff hyz_diff
    exact
      S.triple_pair_right_color_class_quotient_colorable_of_pair_collapse_colorable
        hxy hxz hyz hseparator left_coloring hxy_same hxz_diff hyz_diff
        hxy_collapse
  · intro hxy_diff hxz_same hyz_diff
    exact
      S.triple_pair_xz_right_color_class_quotient_colorable_of_pair_collapse_colorable
        hxy hxz hyz hseparator left_coloring hxz_same hxy_diff hyz_diff
        hxz_collapse
  · intro hxy_diff hxz_diff hyz_same
    exact
      S.triple_pair_yz_right_color_class_quotient_colorable_of_pair_collapse_colorable
        hxy hxz hyz hseparator left_coloring hyz_same hxy_diff hxz_diff
        hyz_collapse
  · intro hxy_same hxz_same
    exact
      S.triple_all_same_right_color_class_quotient_colorable_of_triple_collapse_colorable
        hxy hxz hseparator left_coloring hxy_same hxz_same hxyz_collapse

private theorem contraction_colorable_of_smaller_induction
    [Fintype V]
    {W : Type u} [Fintype W]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (H : SimpleGraph W)
    (hW_card : Fintype.card W < Fintype.card V)
    (C : GraphContraction H)
    [Fintype C.Target]
    (hC_card_W : Fintype.card C.Target < Fintype.card W)
    (hno_model : Not (CompatibleDominatingK5Model
      (OrderedClique.nil : OrderedClique C.graph))) :
    C.graph.Colorable 4 := by
  rcases hIH C.graph (lt_trans hC_card_W hW_card)
      (OrderedClique.nil : OrderedClique C.graph) with hcolor | hmodel
  · exact hcolor
  · exact False.elim (hno_model hmodel)

private theorem edge_collapse_colorable_of_smaller_induction
    [Fintype V]
    {W : Type u} [Fintype W]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (H : SimpleGraph W)
    (hW_card : Fintype.card W < Fintype.card V)
    {a b : W} (edge : H.Adj a b)
    (hno_model : Not (CompatibleDominatingK5Model
      (OrderedClique.nil : OrderedClique
        (GraphContraction.collapseEdge H edge).graph))) :
    (GraphContraction.collapseEdge H edge).graph.Colorable 4 := by
  let C := GraphContraction.collapseEdge H edge
  letI : Fintype C.Target := by
    dsimp [C, GraphContraction.collapseEdge]
    infer_instance
  exact contraction_colorable_of_smaller_induction hIH H hW_card C
    (by simpa [C] using
      (GraphContraction.collapseEdge_target_card_lt (V := W) H edge))
    (by simpa [C] using hno_model)

private theorem triple_collapse_colorable_of_smaller_induction
    [Fintype V]
    {W : Type u} [Fintype W]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (H : SimpleGraph W)
    (hW_card : Fintype.card W < Fintype.card V)
    {a b c : W} (edge_ab : H.Adj a b) (edge_ac : H.Adj a c)
    (hno_model : Not (CompatibleDominatingK5Model
      (OrderedClique.nil : OrderedClique
        (GraphContraction.collapseTriple H edge_ab edge_ac).graph))) :
    (GraphContraction.collapseTriple H edge_ab edge_ac).graph.Colorable 4 := by
  let C := GraphContraction.collapseTriple H edge_ab edge_ac
  letI : Fintype C.Target := by
    dsimp [C, GraphContraction.collapseTriple]
    infer_instance
  exact contraction_colorable_of_smaller_induction hIH H hW_card C
    (by simpa [C] using
      (GraphContraction.collapseTriple_target_card_lt (V := W)
        H edge_ab edge_ac))
    (by simpa [C] using hno_model)

theorem colorable_of_triple_separation_collapses_no_model
    [Fintype V]
    (hIH : ColorOrCompatibleModelBelow.{u} (Fintype.card V))
    (S : Separation G)
    (hproper : S.Proper)
    (hleft_colorable : (G.induce S.left).Colorable 4)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hno_right :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique)))
    (hno_xy :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (S.rightTripleXYContraction hxy hseparator).graph)))
    (hno_xz :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (S.rightTripleXZContraction hxz hseparator).graph)))
    (hno_yz :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (S.rightTripleYZContraction hyz hseparator).graph)))
    (hno_xyz :
      Not (CompatibleDominatingK5Model
        (OrderedClique.nil : OrderedClique
          (S.rightTripleXYZContraction hxy hxz hseparator).graph))) :
    G.Colorable 4 := by
  classical
  letI : Fintype S.right := S.right.toFinite.fintype
  have hright_card_lt : Fintype.card S.right < Fintype.card V := by
    have hnat := S.natCard_right_lt_of_proper hproper
    simpa [Nat.card_eq_fintype_card] using hnat
  have hright : S.rightWithSeparatorClique.Colorable 4 := by
    rcases hIH S.rightWithSeparatorClique hright_card_lt
        (OrderedClique.nil : OrderedClique S.rightWithSeparatorClique) with
      hcolor | hmodel
    · exact hcolor
    · exact False.elim (hno_right hmodel)
  have hxy_collapse :
      (S.rightTripleXYContraction hxy hseparator).graph.Colorable 4 := by
    simpa [Separation.rightTripleXYContraction] using
      edge_collapse_colorable_of_smaller_induction hIH
        S.rightWithSeparatorClique hright_card_lt
        (S.rightTripleXYAdj hxy hseparator) (by
          simpa [Separation.rightTripleXYContraction] using hno_xy)
  have hxz_collapse :
      (S.rightTripleXZContraction hxz hseparator).graph.Colorable 4 := by
    simpa [Separation.rightTripleXZContraction] using
      edge_collapse_colorable_of_smaller_induction hIH
        S.rightWithSeparatorClique hright_card_lt
        (S.rightTripleXZAdj hxz hseparator) (by
          simpa [Separation.rightTripleXZContraction] using hno_xz)
  have hyz_collapse :
      (S.rightTripleYZContraction hyz hseparator).graph.Colorable 4 := by
    simpa [Separation.rightTripleYZContraction] using
      edge_collapse_colorable_of_smaller_induction hIH
        S.rightWithSeparatorClique hright_card_lt
        (S.rightTripleYZAdj hyz hseparator) (by
          simpa [Separation.rightTripleYZContraction] using hno_yz)
  have hxyz_collapse :
      (S.rightTripleXYZContraction hxy hxz hseparator).graph.Colorable 4 := by
    simpa [Separation.rightTripleXYZContraction] using
      triple_collapse_colorable_of_smaller_induction hIH
        S.rightWithSeparatorClique hright_card_lt
        (S.rightTripleXYAdj hxy hseparator)
        (S.rightTripleXZAdj hxz hseparator) (by
          simpa [Separation.rightTripleXYZContraction] using hno_xyz)
  rcases hleft_colorable with ⟨left_coloring⟩
  exact
    colorable_of_triple_separation_collapse_colorable_by_color_cases
      (G := G) S hxy hxz hyz hseparator left_coloring hright
      hxy_collapse hxz_collapse hyz_collapse hxyz_collapse

end Schematic.Math.GraphTheory
