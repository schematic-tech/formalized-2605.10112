import DominatingFourColour.Prerequisites.TripodMinimal.ReroutingReduction

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

def Tripod.attachComponentOf
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {x : V}
    (hx : x ∉ Set.range H.attach) :
    Set V :=
  induceComponentSupport (G := G)
    ((G.induce (Set.range H.attach)ᶜ).connectedComponentMk ⟨x, hx⟩)

theorem Tripod.mem_attachComponentOf_self
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {x : V}
    (hx : x ∉ Set.range H.attach) :
    x ∈ H.attachComponentOf hx := by
  exact ⟨hx, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

theorem Tripod.attachComponentOf_subset_attach_compl
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {x : V}
    (hx : x ∉ Set.range H.attach) :
    H.attachComponentOf hx ⊆ (Set.range H.attach)ᶜ :=
  induceComponentSupport_subset (G := G)
    ((G.induce (Set.range H.attach)ᶜ).connectedComponentMk ⟨x, hx⟩)

theorem Tripod.attachComponentOf_connected
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {x : V}
    (hx : x ∉ Set.range H.attach) :
    (G.induce (H.attachComponentOf hx)).Connected :=
  induceComponentSupport_connected (G := G)
    ((G.induce (Set.range H.attach)ᶜ).connectedComponentMk ⟨x, hx⟩)

theorem Tripod.mem_attachComponentOf_of_adj
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {x y : V}
    (hx : x ∉ Set.range H.attach)
    (hy : y ∉ Set.range H.attach)
    (hxy : G.Adj x y) :
    y ∈ H.attachComponentOf hx := by
  exact induceComponentSupport_mem_of_adj
    (G := G)
    ((G.induce (Set.range H.attach)ᶜ).connectedComponentMk ⟨x, hx⟩)
    (H.mem_attachComponentOf_self hx) hy hxy

theorem Tripod.old_foot_mem_attachComponentOf_penultimate_of_length_gt_one
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hlen : 1 < (H.leg i).length) :
    feet i ∈
      H.attachComponentOf
        (H.leg_penultimate_not_mem_attach_range_of_length_gt_one hlen) := by
  exact H.mem_attachComponentOf_of_adj
    (H.leg_penultimate_not_mem_attach_range_of_length_gt_one hlen)
    (H.foot_not_mem_attach_range_of_positive_leg (by omega))
    (H.positive_leg_penultimate_adj_foot (by omega))

theorem Tripod.attachComponentOf_closed
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {x : V}
    (hx : x ∉ Set.range H.attach) :
    forall {a b : V},
      a ∈ H.attachComponentOf hx ->
        b ∉ H.attachComponentOf hx ->
          b ∉ Set.range H.attach ->
            Not (G.Adj a b) := by
  intro a b ha hb hb_attach hab
  exact hb (induceComponentSupport_mem_of_adj
    (G := G)
    ((G.induce (Set.range H.attach)ᶜ).connectedComponentMk ⟨x, hx⟩)
    ha hb_attach hab)

def AvoidingSetPath
    (G : SimpleGraph V)
    (X Z F : Set V) : Prop :=
  Exists fun x : V => x ∈ X ∧
    Exists fun z : V => z ∈ Z ∧
      Exists fun p : G.Walk x z =>
        forall v : V, v ∈ p.support -> v ∉ F

def reachableFromSetOutside
    (G : SimpleGraph V)
    (X F : Set V) : Set V :=
  {v : V |
    Exists fun hvF : v ∉ F =>
      Exists fun x : V =>
        x ∈ X ∧
          Exists fun hxF : x ∉ F =>
            (G.induce Fᶜ).Reachable ⟨x, hxF⟩ ⟨v, hvF⟩}

theorem mem_reachableFromSetOutside_self
    {X F : Set V}
    {x : V}
    (hxX : x ∈ X)
    (hxF : x ∉ F) :
    x ∈ reachableFromSetOutside G X F := by
  exact ⟨hxF, x, hxX, hxF, SimpleGraph.Reachable.rfl⟩

theorem reachableFromSetOutside_subset_compl
    {X F : Set V} :
    reachableFromSetOutside G X F ⊆ Fᶜ := by
  intro v hv
  rcases hv with ⟨hvF, _x, _hxX, _hxF, _hreach⟩
  exact hvF

theorem reachableFromSetOutside_closed
    {X F : Set V} :
    forall {a b : V},
      a ∈ reachableFromSetOutside G X F ->
        b ∉ reachableFromSetOutside G X F ->
          b ∉ F ->
            Not (G.Adj a b) := by
  intro a b ha hb hbF hab
  rcases ha with ⟨haF, x, hxX, hxF, hreach⟩
  have hab_ind :
      (G.induce Fᶜ).Adj ⟨a, haF⟩ ⟨b, hbF⟩ := by
    simpa using hab
  exact hb ⟨hbF, x, hxX, hxF, hreach.trans hab_ind.reachable⟩

theorem reachableFromSetOutside_disjoint_of_no_avoidingSetPath
    {X Z F : Set V}
    (hno_path : Not (AvoidingSetPath G X Z F)) :
    Disjoint (reachableFromSetOutside G X F) Z := by
  rw [Set.disjoint_left]
  intro z hzK hzZ
  rcases hzK with ⟨hzF, x, hxX, hxF, hreach⟩
  obtain ⟨p⟩ := hreach
  let q : G.Walk x z := p.map (SimpleGraph.Embedding.induce Fᶜ).toHom
  have hq : forall v : V, v ∈ q.support -> v ∉ F := by
    intro v hv
    change v ∈ (p.map (SimpleGraph.Embedding.induce Fᶜ).toHom).support at hv
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hv
    rcases hv with ⟨w, _hw, rfl⟩
    exact w.2
  exact hno_path ⟨x, hxX, z, hzZ, q, hq⟩

theorem avoidingSetPath_or_closed_component
    {X Z F : Set V}
    (hX : Exists fun x : V => x ∈ X ∧ x ∉ F) :
    AvoidingSetPath G X Z F ∨
      Exists fun K : Set V =>
        K.Nonempty ∧ K ⊆ Fᶜ ∧
          (Exists fun x : V => x ∈ X ∧ x ∈ K) ∧
            Disjoint K Z ∧
              (forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ F ->
                Not (G.Adj a b)) := by
  rcases hX with ⟨x, hxX, hxF⟩
  let C : (G.induce Fᶜ).ConnectedComponent :=
    (G.induce Fᶜ).connectedComponentMk ⟨x, hxF⟩
  let K : Set V := induceComponentSupport (G := G) C
  have hxK : x ∈ K := by
    exact ⟨hxF, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  by_cases hhit : Exists fun z : V => z ∈ Z ∧ z ∈ K
  · rcases hhit with ⟨z, hzZ, hzK⟩
    have hK_connected : (G.induce K).Connected :=
      induceComponentSupport_connected (G := G) C
    obtain ⟨p, hpK⟩ :=
      connected_induce_exists_walk_support_subset
        (G := G) hK_connected hxK hzK
    exact Or.inl ⟨x, hxX, z, hzZ, p, by
      intro v hv
      exact (induceComponentSupport_subset (G := G) C (hpK v hv))⟩
  · right
    refine ⟨K, ⟨x, hxK⟩, induceComponentSupport_subset (G := G) C,
      ⟨x, hxX, hxK⟩, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro v hvK hvZ
      exact hhit ⟨v, hvZ, hvK⟩
    · intro a b ha hb hbF hab
      exact hb (induceComponentSupport_mem_of_adj (G := G) C ha hbF hab)

theorem Tripod.exists_legLengthMinimal
    {feet : Fin 3 -> V}
    (htripod : Nonempty (Tripod G feet)) :
    Exists fun H : Tripod G feet => H.LegLengthMinimal := by
  classical
  let P : Nat -> Prop := fun n =>
    Exists fun H : Tripod G feet => H.legLengthSum = n
  have hP : Exists P := by
    rcases htripod with ⟨H⟩
    exact ⟨H.legLengthSum, H, rfl⟩
  obtain ⟨H, hH⟩ := Nat.find_spec hP
  refine ⟨H, ?_⟩
  intro H'
  rw [hH]
  exact Nat.find_min' hP ⟨H', rfl⟩

theorem Tripod.not_legLengthMinimal_of_legLengthSum_lt
    {feet : Fin 3 -> V}
    (H H' : Tripod G feet)
    (hlt : H'.legLengthSum < H.legLengthSum) :
    Not H.LegLengthMinimal := by
  intro hmin
  exact Nat.not_lt_of_ge (hmin H') hlt

theorem Tripod.legLengthSum_eq_zero_of_minimal_and_positive_leg_rerouting
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hmin : H.LegLengthMinimal)
    (hreroute :
      forall i : Fin 3,
        0 < (H.leg i).length ->
          Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum) :
    H.legLengthSum = 0 := by
  by_contra hnot_zero
  have hnot_legless : Not H.Legless := by
    intro hlegless
    exact hnot_zero (H.legLengthSum_eq_zero_of_legless hlegless)
  obtain ⟨i, hpos⟩ := H.exists_positive_leg_of_not_legless hnot_legless
  obtain ⟨H', hlt⟩ := hreroute i hpos
  exact H.not_legLengthMinimal_of_legLengthSum_lt H' hlt hmin

def Tripod.leftLegOfLegless
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (i : Fin 3) :
    G.Walk H.left (feet i) :=
  ((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).copy rfl (hH i)

def Tripod.rightLegOfLegless
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (i : Fin 3) :
    G.Walk H.right (feet i) :=
  ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1).reverse.copy rfl (hH i)

theorem Tripod.mem_leftLegOfLegless_support_iff
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (i : Fin 3)
    {v : V} :
    v ∈ (H.leftLegOfLegless hH i).support ↔
      v ∈ ((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).support := by
  simp [Tripod.leftLegOfLegless]

theorem Tripod.mem_rightLegOfLegless_support_iff
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (i : Fin 3)
    {v : V} :
    v ∈ (H.rightLegOfLegless hH i).support ↔
      v ∈ ((H.rim i).dropUntil (H.attach i) (H.attach_mem_rim i).1).support := by
  simp [Tripod.rightLegOfLegless, SimpleGraph.Walk.support_reverse,
    List.mem_reverse]

theorem Tripod.leftLegOfLegless_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (i : Fin 3) :
    (H.leftLegOfLegless hH i).IsPath := by
  simpa [Tripod.leftLegOfLegless] using
    (H.rim_isPath i).takeUntil (H.attach_mem_rim i).1

theorem Tripod.rightLegOfLegless_isPath
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (i : Fin 3) :
    (H.rightLegOfLegless hH i).IsPath := by
  simpa [Tripod.rightLegOfLegless] using
    ((H.rim_isPath i).dropUntil (H.attach_mem_rim i).1).reverse

theorem Tripod.leftLegOfLegless_internalVertices_subset_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (i : Fin 3) :
    Walk.InternalVertices (H.leftLegOfLegless hH i) ⊆
      Walk.InternalVertices (H.rim i) := by
  rw [Tripod.leftLegOfLegless, Walk.internalVertices_copy]
  exact
    Walk.IsPath.internalVertices_takeUntil_subset_internalVertices
      (H.rim_isPath i) (H.attach_mem_rim i).1 (H.attach_mem_rim i).2.2

theorem Tripod.rightLegOfLegless_internalVertices_subset_rim
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (i : Fin 3) :
    Walk.InternalVertices (H.rightLegOfLegless hH i) ⊆
      Walk.InternalVertices (H.rim i) := by
  rw [Tripod.rightLegOfLegless, Walk.internalVertices_copy, Walk.internalVertices_reverse]
  exact
    (Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
      (H.rim_isPath i) (H.attach_mem_rim i).1 (H.attach_mem_rim i).2.1)

theorem Tripod.leftLegOfLegless_internalVertices_disjoint
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    {i j : Fin 3}
    (hij : i ≠ j) :
    Disjoint (Walk.InternalVertices (H.leftLegOfLegless hH i))
      (Walk.InternalVertices (H.leftLegOfLegless hH j)) := by
  rw [Set.disjoint_left]
  intro v hvi hvj
  exact Set.disjoint_left.mp (H.rim_internals_disjoint i j hij)
    (H.leftLegOfLegless_internalVertices_subset_rim hH i hvi)
    (H.leftLegOfLegless_internalVertices_subset_rim hH j hvj)

theorem Tripod.rightLegOfLegless_internalVertices_disjoint
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    {i j : Fin 3}
    (hij : i ≠ j) :
    Disjoint (Walk.InternalVertices (H.rightLegOfLegless hH i))
      (Walk.InternalVertices (H.rightLegOfLegless hH j)) := by
  rw [Set.disjoint_left]
  intro v hvi hvj
  exact Set.disjoint_left.mp (H.rim_internals_disjoint i j hij)
    (H.rightLegOfLegless_internalVertices_subset_rim hH i hvi)
    (H.rightLegOfLegless_internalVertices_subset_rim hH j hvj)

theorem Tripod.leftLegOfLegless_internal_vertices_avoid_feet
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (i j : Fin 3) :
    feet i ∉ Walk.InternalVertices (H.leftLegOfLegless hH j) := by
  by_cases hij : i = j
  · subst j
    intro h
    exact h.2.2 rfl
  · intro h
    have hi_rim : feet i ∈ Walk.InternalVertices (H.rim i) := by
      simpa [hH i] using H.attach_mem_rim i
    have hj_rim : feet i ∈ Walk.InternalVertices (H.rim j) :=
      H.leftLegOfLegless_internalVertices_subset_rim hH j h
    exact Set.disjoint_left.mp (H.rim_internals_disjoint i j hij) hi_rim hj_rim

theorem Tripod.rightLegOfLegless_internal_vertices_avoid_feet
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (i j : Fin 3) :
    feet i ∉ Walk.InternalVertices (H.rightLegOfLegless hH j) := by
  by_cases hij : i = j
  · subst j
    intro h
    exact h.2.2 rfl
  · intro h
    have hi_rim : feet i ∈ Walk.InternalVertices (H.rim i) := by
      simpa [hH i] using H.attach_mem_rim i
    have hj_rim : feet i ∈ Walk.InternalVertices (H.rim j) :=
      H.rightLegOfLegless_internalVertices_subset_rim hH j h
    exact Set.disjoint_left.mp (H.rim_internals_disjoint i j hij) hi_rim hj_rim

def Tripod.leftTriadOfLegless
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless) :
    Triad G feet where
  apex := H.left
  apex_not_foot := H.left_not_foot
  leg := H.leftLegOfLegless hH
  leg_isPath := H.leftLegOfLegless_isPath hH
  apex_only_common_vertex := by
    intro i j hij
    exact H.leftLegOfLegless_internalVertices_disjoint hH hij
  internal_vertices_avoid_feet :=
    H.leftLegOfLegless_internal_vertices_avoid_feet hH

def Tripod.rightTriadOfLegless
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless) :
    Triad G feet where
  apex := H.right
  apex_not_foot := H.right_not_foot
  leg := H.rightLegOfLegless hH
  leg_isPath := H.rightLegOfLegless_isPath hH
  apex_only_common_vertex := by
    intro i j hij
    exact H.rightLegOfLegless_internalVertices_disjoint hH hij
  internal_vertices_avoid_feet :=
    H.rightLegOfLegless_internal_vertices_avoid_feet hH

theorem Tripod.left_right_triadOfLegless_inter_subset_feet
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless) :
    (H.leftTriadOfLegless hH).vertexSet ∩
      (H.rightTriadOfLegless hH).vertexSet ⊆ Set.range feet := by
  rintro v ⟨hleft, hright⟩
  rcases hleft with ⟨i, hvi_leg⟩
  rcases hright with ⟨j, hvj_leg⟩
  have hvi_take :
      v ∈ ((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).support :=
    (H.mem_leftLegOfLegless_support_iff hH i).mp hvi_leg
  have hvj_drop :
      v ∈ ((H.rim j).dropUntil (H.attach j) (H.attach_mem_rim j).1).support :=
    (H.mem_rightLegOfLegless_support_iff hH j).mp hvj_leg
  by_cases hij : i = j
  · subst j
    have hv_attach : v = H.attach i :=
      Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        (H.rim_isPath i) (H.attach_mem_rim i).1 hvi_take hvj_drop
    exact ⟨i, (hv_attach.trans (hH i)).symm⟩
  · exfalso
    have hvi_rim : v ∈ (H.rim i).support :=
      SimpleGraph.Walk.support_takeUntil_subset (H.rim i)
        (H.attach_mem_rim i).1 hvi_take
    have hvj_rim : v ∈ (H.rim j).support :=
      SimpleGraph.Walk.support_dropUntil_subset (H.rim j)
        (H.attach_mem_rim j).1 hvj_drop
    by_cases hv_left : v = H.left
    · have hleft_not_drop :
          H.left ∉
            ((H.rim j).dropUntil (H.attach j) (H.attach_mem_rim j).1).support :=
        Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          (H.rim_isPath j) (H.attach_mem_rim j).1 (H.attach_mem_rim j).2.1
      exact hleft_not_drop (hv_left ▸ hvj_drop)
    by_cases hv_right : v = H.right
    · have hright_not_take :
          H.right ∉
            ((H.rim i).takeUntil (H.attach i) (H.attach_mem_rim i).1).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (H.rim_isPath i) (H.attach_mem_rim i).1 (H.attach_mem_rim i).2.2.symm
      exact hright_not_take (hv_right ▸ hvi_take)
    have hvi_internal : v ∈ Walk.InternalVertices (H.rim i) :=
      ⟨hvi_rim, hv_left, hv_right⟩
    have hvj_internal : v ∈ Walk.InternalVertices (H.rim j) :=
      ⟨hvj_rim, hv_left, hv_right⟩
    exact Set.disjoint_left.mp (H.rim_internals_disjoint i j hij)
      hvi_internal hvj_internal

theorem Tripod.left_right_triadOfLegless_edge_disjoint
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (hfeet_injective : Function.Injective feet) :
    Disjoint (H.leftTriadOfLegless hH).carrier.edgeSet
      (H.rightTriadOfLegless hH).carrier.edgeSet := by
  rw [Set.disjoint_left]
  intro e he_left he_right
  let TL : Triad G feet := H.leftTriadOfLegless hH
  let TR : Triad G feet := H.rightTriadOfLegless hH
  change e ∈ TL.carrier.edgeSet at he_left
  change e ∈ TR.carrier.edgeSet at he_right
  obtain ⟨i, hi_sub⟩ :=
    (Triad.mem_carrier_edgeSet_iff (T := TL)).mp he_left
  obtain ⟨j, hj_sub⟩ :=
    (Triad.mem_carrier_edgeSet_iff (T := TR)).mp he_right
  have hi_edges : e ∈ (TL.leg i).edges :=
    (SimpleGraph.Walk.mem_edges_toSubgraph (TL.leg i)).mp hi_sub
  have hj_edges : e ∈ (TR.leg j).edges :=
    (SimpleGraph.Walk.mem_edges_toSubgraph (TR.leg j)).mp hj_sub
  have hleft_support := Walk.out_mem_support_of_mem_edges (p := TL.leg i) hi_edges
  have hright_support := Walk.out_mem_support_of_mem_edges (p := TR.leg j) hj_edges
  have hinter :
      TL.vertexSet ∩ TR.vertexSet ⊆ Set.range feet := by
    simpa [TL, TR] using H.left_right_triadOfLegless_inter_subset_feet hH
  have hfst_range : e.out.1 ∈ Set.range feet :=
    hinter ⟨⟨i, hleft_support.1⟩, ⟨j, hright_support.1⟩⟩
  have hsnd_range : e.out.2 ∈ Set.range feet :=
    hinter ⟨⟨i, hleft_support.2⟩, ⟨j, hright_support.2⟩⟩
  rcases hfst_range with ⟨a, ha⟩
  rcases hsnd_range with ⟨b, hb⟩
  have hfst_foot_support : feet a ∈ (TL.leg i).support := by
    simpa [ha] using hleft_support.1
  have hsnd_foot_support : feet b ∈ (TL.leg i).support := by
    simpa [hb] using hleft_support.2
  have hai : a = i :=
    (TL.foot_mem_leg_support_iff hfeet_injective a i).mp hfst_foot_support
  have hbi : b = i :=
    (TL.foot_mem_leg_support_iff hfeet_injective b i).mp hsnd_foot_support
  have hout_eq : e.out.1 = e.out.2 := by
    calc
      e.out.1 = feet a := ha.symm
      _ = feet i := by rw [hai]
      _ = feet b := by rw [hbi]
      _ = e.out.2 := hb
  have hdiag : e.IsDiag := by
    have heq : e = s(e.out.1, e.out.2) := by
      rw [Sym2.mk, e.out_eq]
    rw [heq]
    exact hout_eq
  exact (G.not_isDiag_of_mem_edgeSet (TL.carrier.edgeSet_subset he_left)) hdiag

def Tripod.toLeglessTripod
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (hH : H.Legless)
    (hfeet_injective : Function.Injective feet) :
    LeglessTripod G feet where
  first := H.leftTriadOfLegless hH
  second := H.rightTriadOfLegless hH
  edge_disjoint :=
    H.left_right_triadOfLegless_edge_disjoint hH hfeet_injective
  meet_only_at_feet :=
    H.left_right_triadOfLegless_inter_subset_feet hH

def LeglessTripod.of_two_common_neighbors
    {feet : Fin 3 -> V}
    {apex₁ apex₂ : V}
    (hapex₁_not_foot : forall i : Fin 3, apex₁ ≠ feet i)
    (hadj₁ : forall i : Fin 3, G.Adj apex₁ (feet i))
    (hapex₂_not_foot : forall i : Fin 3, apex₂ ≠ feet i)
    (hadj₂ : forall i : Fin 3, G.Adj apex₂ (feet i))
    (hapex_ne : apex₁ ≠ apex₂) :
    LeglessTripod G feet where
  first := Triad.of_common_neighbor (G := G) hapex₁_not_foot hadj₁
  second := Triad.of_common_neighbor (G := G) hapex₂_not_foot hadj₂
  edge_disjoint := by
    rw [Set.disjoint_left]
    intro e he₁ he₂
    have hapex₁_mem : apex₁ ∈ e :=
      Triad.common_neighbor_apex_mem_of_mem_carrier_edge
        (G := G) hapex₁_not_foot hadj₁ he₁
    exact
      (Triad.common_neighbor_not_mem_of_mem_carrier_edge
        (G := G) hapex₂_not_foot hadj₂ hapex_ne hapex₁_not_foot he₂)
        hapex₁_mem
  meet_only_at_feet := by
    intro v hv
    have hv₁ :
        v = apex₁ ∨ v ∈ Set.range feet :=
      (Triad.common_neighbor_mem_vertexSet_iff
        (G := G) hapex₁_not_foot hadj₁).mp hv.1
    have hv₂ :
        v = apex₂ ∨ v ∈ Set.range feet :=
      (Triad.common_neighbor_mem_vertexSet_iff
        (G := G) hapex₂_not_foot hadj₂).mp hv.2
    rcases hv₁ with rfl | hfeet
    · rcases hv₂ with hapex_eq | hfeet
      · exact False.elim (hapex_ne hapex_eq)
      · exact hfeet
    · exact hfeet

theorem rst_planar_or_legless_tripod_of_two_common_neighbors
    {feet : Fin 3 -> V}
    {apex₁ apex₂ : V}
    (hapex₁_not_foot : forall i : Fin 3, apex₁ ≠ feet i)
    (hadj₁ : forall i : Fin 3, G.Adj apex₁ (feet i))
    (hapex₂_not_foot : forall i : Fin 3, apex₂ ≠ feet i)
    (hadj₂ : forall i : Fin 3, G.Adj apex₂ (feet i))
    (hapex_ne : apex₁ ≠ apex₂) :
    IsPlanar G ∨ Nonempty (LeglessTripod G feet) := by
  exact Or.inr ⟨LeglessTripod.of_two_common_neighbors
    (G := G) hapex₁_not_foot hadj₁ hapex₂_not_foot hadj₂ hapex_ne⟩

theorem rst_planar_or_legless_tripod_of_complete
    [Fintype V]
    (h_card : 5 <= Fintype.card V)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v)
    (feet : Fin 3 -> V)
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2)) :
    IsPlanar G ∨ Nonempty (LeglessTripod G feet) := by
  classical
  let feetEmbedding : Fin 3 ↪ V := ⟨feet, IsTriangle.injective_fin3 h_triangle⟩
  letI : Fintype (Set.range feet) := Set.fintypeRange feet
  letI : Fintype ((Set.range feet)ᶜ : Set V) := ((Set.range feet)ᶜ).toFinite.fintype
  have hrange_card : Fintype.card (Set.range feet) = 3 := by
    simpa [feetEmbedding, Fintype.card_fin] using
      (Fintype.card_range feetEmbedding)
  have hcompl_card : 2 <= Fintype.card ((Set.range feet)ᶜ : Set V) := by
    rw [Fintype.card_compl_set (Set.range feet), hrange_card]
    omega
  obtain ⟨apexEmbedding⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin 2) (β := ((Set.range feet)ᶜ : Set V)) (by
        simpa [Fintype.card_fin] using hcompl_card)
  let apex₁ : V := apexEmbedding 0
  let apex₂ : V := apexEmbedding 1
  have hapex₁_not_foot : forall i : Fin 3, apex₁ ≠ feet i := by
    intro i h
    exact (apexEmbedding 0).2 ⟨i, h.symm⟩
  have hapex₂_not_foot : forall i : Fin 3, apex₂ ≠ feet i := by
    intro i h
    exact (apexEmbedding 1).2 ⟨i, h.symm⟩
  have hapex_ne : apex₁ ≠ apex₂ := by
    intro h
    have hfin : (0 : Fin 2) = 1 := apexEmbedding.injective (Subtype.ext h)
    exact Fin.zero_ne_one hfin
  exact rst_planar_or_legless_tripod_of_two_common_neighbors
    (G := G) hapex₁_not_foot
    (fun i => h_complete apex₁ (feet i) (hapex₁_not_foot i))
    hapex₂_not_foot
    (fun i => h_complete apex₂ (feet i) (hapex₂_not_foot i))
    hapex_ne

theorem LeglessTripod.range_feet_subset_inter_vertexSet
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet) :
    Set.range feet ⊆ T.first.vertexSet ∩ T.second.vertexSet := by
  rintro v ⟨i, rfl⟩
  exact ⟨T.first.foot_mem_vertexSet i, T.second.foot_mem_vertexSet i⟩

theorem LeglessTripod.inter_vertexSet_eq_range_feet
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet) :
    T.first.vertexSet ∩ T.second.vertexSet = Set.range feet := by
  exact Set.Subset.antisymm T.meet_only_at_feet T.range_feet_subset_inter_vertexSet

theorem LeglessTripod.first_vertexSet_inter_second_compl_eq_punctured
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet) :
    T.first.vertexSet ∩ T.second.vertexSetᶜ =
      T.first.vertexSet \ Set.range feet := by
  ext v
  constructor
  · intro hv
    exact ⟨hv.1, by
      intro hvfeet
      exact hv.2 ((T.range_feet_subset_inter_vertexSet hvfeet).2)⟩
  · intro hv
    exact ⟨hv.1, by
      intro hvsecond
      exact hv.2 (T.meet_only_at_feet ⟨hv.1, hvsecond⟩)⟩

theorem LeglessTripod.second_vertexSet_inter_first_compl_eq_punctured
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet) :
    T.second.vertexSet ∩ T.first.vertexSetᶜ =
      T.second.vertexSet \ Set.range feet := by
  ext v
  constructor
  · intro hv
    exact ⟨hv.1, by
      intro hvfeet
      exact hv.2 ((T.range_feet_subset_inter_vertexSet hvfeet).1)⟩
  · intro hv
    exact ⟨hv.1, by
      intro hvfirst
      exact hv.2 (T.meet_only_at_feet ⟨hvfirst, hv.1⟩)⟩

theorem LeglessTripod.first_punctured_subset_second_complement
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet) :
    (T.first.carrier.deleteVerts (Set.range feet)).verts ⊆ T.second.vertexSetᶜ := by
  intro x hx hx_second
  rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hx
  exact hx.2 (T.meet_only_at_feet ⟨T.first.mem_carrier_verts_iff.mp hx.1, hx_second⟩)

theorem LeglessTripod.second_punctured_subset_first_complement
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet) :
    (T.second.carrier.deleteVerts (Set.range feet)).verts ⊆ T.first.vertexSetᶜ := by
  intro x hx hx_first
  rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hx
  exact hx.2 (T.meet_only_at_feet ⟨hx_first, T.second.mem_carrier_verts_iff.mp hx.1⟩)

theorem LeglessTripod.vertex_avoids_first_or_second
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    {v : V}
    (hv_not_foot : v ∉ Set.range feet) :
    v ∉ T.first.vertexSet ∨ v ∉ T.second.vertexSet := by
  by_cases hv_first : v ∈ T.first.vertexSet
  · right
    intro hv_second
    exact hv_not_foot (T.meet_only_at_feet ⟨hv_first, hv_second⟩)
  · exact Or.inl hv_first

def LeglessTripod.rimWalk
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (i : Fin 3) :
    G.Walk T.first.apex T.second.apex :=
  (T.first.leg i).append (T.second.leg i).reverse

theorem LeglessTripod.foot_mem_rimWalk_support
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (i : Fin 3) :
    feet i ∈ (T.rimWalk i).support := by
  rw [LeglessTripod.rimWalk, SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl (T.first.leg i).end_mem_support

theorem LeglessTripod.foot_mem_rimWalk_internalVertices
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (i : Fin 3) :
    feet i ∈ Walk.InternalVertices (T.rimWalk i) := by
  refine ⟨T.foot_mem_rimWalk_support i, ?_, ?_⟩
  · exact (T.first.apex_not_foot i).symm
  · exact (T.second.apex_not_foot i).symm

theorem LeglessTripod.first_leg_support_subset_rimWalk
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (i : Fin 3) :
    {v : V | v ∈ (T.first.leg i).support} ⊆
      {v : V | v ∈ (T.rimWalk i).support} := by
  intro v hv
  change v ∈ (T.rimWalk i).support
  rw [LeglessTripod.rimWalk, SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl hv

theorem LeglessTripod.second_leg_support_subset_rimWalk
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (i : Fin 3) :
    {v : V | v ∈ (T.second.leg i).support} ⊆
      {v : V | v ∈ (T.rimWalk i).support} := by
  intro v hv
  change v ∈ (T.rimWalk i).support
  rw [LeglessTripod.rimWalk, SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inr (by
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
    exact hv)

theorem LeglessTripod.rimWalk_support_subset_vertexSets
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (i : Fin 3) :
    {v : V | v ∈ (T.rimWalk i).support} ⊆
      T.first.vertexSet ∪ T.second.vertexSet := by
  intro v hv
  change v ∈ (T.rimWalk i).support at hv
  rw [LeglessTripod.rimWalk,
    SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hv | hv
  · exact Or.inl ⟨i, hv⟩
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
    exact Or.inr ⟨i, hv⟩

theorem LeglessTripod.same_leg_support_inter_eq_foot
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3)
    {v : V}
    (hfirst : v ∈ (T.first.leg i).support)
    (hsecond : v ∈ (T.second.leg i).support) :
    v = feet i := by
  have hvfeet : v ∈ Set.range feet :=
    T.meet_only_at_feet ⟨⟨i, hfirst⟩, ⟨i, hsecond⟩⟩
  rcases hvfeet with ⟨j, rfl⟩
  have hji : j = i :=
    (T.first.foot_mem_leg_support_iff hfeet_injective j i).mp hfirst
  simp [hji]

theorem LeglessTripod.cross_leg_support_inter_eq_foot
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    {i j : Fin 3}
    {v : V}
    (hfirst : v ∈ (T.first.leg i).support)
    (hsecond : v ∈ (T.second.leg j).support) :
    i = j ∧ v = feet i := by
  have hvfeet : v ∈ Set.range feet :=
    T.meet_only_at_feet ⟨⟨i, hfirst⟩, ⟨j, hsecond⟩⟩
  rcases hvfeet with ⟨k, rfl⟩
  have hki : k = i :=
    (T.first.foot_mem_leg_support_iff hfeet_injective k i).mp hfirst
  have hkj : k = j :=
    (T.second.foot_mem_leg_support_iff hfeet_injective k j).mp hsecond
  exact ⟨hki.symm.trans hkj, by simp [hki]⟩

theorem LeglessTripod.rimWalk_isPath
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3) :
    (T.rimWalk i).IsPath := by
  rw [LeglessTripod.rimWalk]
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    (T.first.leg_isPath i) (T.second.leg_isPath i).reverse ?_
  intro v hvfirst hvsecond
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hvsecond
  exact T.same_leg_support_inter_eq_foot hfeet_injective i hvfirst hvsecond

theorem LeglessTripod.rimWalk_internalVertices_disjoint
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    {i j : Fin 3}
    (hij : i ≠ j) :
    Disjoint (Walk.InternalVertices (T.rimWalk i))
      (Walk.InternalVertices (T.rimWalk j)) := by
  rw [Set.disjoint_left]
  intro v hvi hvj
  have hvi_support : v ∈ (T.rimWalk i).support := hvi.1
  have hvj_support : v ∈ (T.rimWalk j).support := hvj.1
  rw [LeglessTripod.rimWalk,
    SimpleGraph.Walk.mem_support_append_iff] at hvi_support
  rw [LeglessTripod.rimWalk,
    SimpleGraph.Walk.mem_support_append_iff] at hvj_support
  rcases hvi_support with hfirst_i | hsecond_i
  · rcases hvj_support with hfirst_j | hsecond_j
    · have hvapex : v = T.first.apex :=
        T.first.diff_leg_support_inter_eq_apex hfeet_injective hij hfirst_i hfirst_j
      exact hvi.2.1 hvapex
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hsecond_j
      have hidx :
          i = j :=
        (T.cross_leg_support_inter_eq_foot hfeet_injective hfirst_i hsecond_j).1
      exact hij hidx
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hsecond_i
    rcases hvj_support with hfirst_j | hsecond_j
    · have hidx :
          j = i :=
        (T.cross_leg_support_inter_eq_foot hfeet_injective hfirst_j hsecond_i).1
      exact hij hidx.symm
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hsecond_j
      have hvapex : v = T.second.apex :=
        T.second.diff_leg_support_inter_eq_apex hfeet_injective hij hsecond_i hsecond_j
      exact hvi.2.2 hvapex

def LeglessTripod.toTripod
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet) :
    Tripod G feet where
  left := T.first.apex
  right := T.second.apex
  left_ne_right := by
    intro hapex
    have hsecond : T.first.apex ∈ T.second.vertexSet := by
      simpa [← hapex] using T.second.apex_mem_vertexSet
    have hfoot : T.first.apex ∈ Set.range feet :=
      T.meet_only_at_feet ⟨T.first.apex_mem_vertexSet, hsecond⟩
    rcases hfoot with ⟨i, hi⟩
    exact T.first.apex_not_foot i hi.symm
  left_not_foot := T.first.apex_not_foot
  right_not_foot := T.second.apex_not_foot
  rim := T.rimWalk
  rim_isPath := T.rimWalk_isPath hfeet_injective
  attach := feet
  attach_mem_rim := T.foot_mem_rimWalk_internalVertices
  rim_internals_disjoint := by
    intro i j hij
    exact T.rimWalk_internalVertices_disjoint hfeet_injective hij
  leg := fun i => (SimpleGraph.Walk.nil : G.Walk (feet i) (feet i))
  leg_isPath := fun _ => SimpleGraph.Walk.IsPath.nil
  legs_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro v hvi hvj
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hvi hvj
    exact hij (hfeet_injective (hvi.symm.trans hvj))
  leg_meets_rims_only_at_attach := by
    intro _i _j _v hvleg _hvrim
    simpa using hvleg

theorem LeglessTripod.toTripod_legless
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet) :
    (T.toTripod hfeet_injective).Legless := by
  intro _i
  rfl

theorem LeglessTripod.exists_tripod_legless_of_nonempty
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hT : Nonempty (LeglessTripod G feet)) :
    Exists fun H : Tripod G feet => H.Legless := by
  rcases hT with ⟨T⟩
  exact ⟨T.toTripod hfeet_injective, T.toTripod_legless hfeet_injective⟩

theorem Tripod.exists_legless_iff_nonempty_leglessTripod
    [DecidableEq V]
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet) :
    (Exists fun H : Tripod G feet => H.Legless) ↔
      Nonempty (LeglessTripod G feet) := by
  constructor
  · rintro ⟨H, hH⟩
    exact ⟨H.toLeglessTripod hH hfeet_injective⟩
  · exact LeglessTripod.exists_tripod_legless_of_nonempty hfeet_injective

theorem LeglessTripod.first_apex_not_second_vertexSet
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet) :
    T.first.apex ∉ T.second.vertexSet := by
  intro hsecond
  have hfoot : T.first.apex ∈ Set.range feet :=
    T.meet_only_at_feet ⟨T.first.apex_mem_vertexSet, hsecond⟩
  rcases hfoot with ⟨i, hi⟩
  exact T.first.apex_not_foot i hi.symm

theorem LeglessTripod.second_apex_not_first_vertexSet
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet) :
    T.second.apex ∉ T.first.vertexSet := by
  intro hfirst
  have hfoot : T.second.apex ∈ Set.range feet :=
    T.meet_only_at_feet ⟨hfirst, T.second.apex_mem_vertexSet⟩
  rcases hfoot with ⟨i, hi⟩
  exact T.second.apex_not_foot i hi.symm

theorem LeglessTripod.apex_ne
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet) :
    T.first.apex ≠ T.second.apex := by
  intro h
  exact T.first_apex_not_second_vertexSet (by
    simpa [h] using T.second.apex_mem_vertexSet)

theorem LeglessTripod.foot_has_neighbor_outside_second
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3) :
    Exists fun u : V =>
      u ∈ ((⊤ : G.Subgraph).deleteVerts T.second.vertexSet).verts ∧ G.Adj u (feet i) := by
  obtain ⟨u, hu, hui⟩ :=
    T.first.foot_has_neighbor_in_punctured_carrier hfeet_injective i
  refine ⟨u, ?_, hui⟩
  rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
  exact ⟨by simp, T.first_punctured_subset_second_complement hu⟩

theorem LeglessTripod.foot_has_neighbor_outside_first
    {feet : Fin 3 -> V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3) :
    Exists fun u : V =>
      u ∈ ((⊤ : G.Subgraph).deleteVerts T.first.vertexSet).verts ∧ G.Adj u (feet i) := by
  obtain ⟨u, hu, hui⟩ :=
    T.second.foot_has_neighbor_in_punctured_carrier hfeet_injective i
  refine ⟨u, ?_, hui⟩
  rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
  exact ⟨by simp, T.second_punctured_subset_first_complement hu⟩

def RSTLeanTriadData.of_legless_tripod_first
    {feet : Fin 3 -> V}
    {root : V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (hlean : T.first.Lean)
    (hcomplement_connected : (G.induce T.first.vertexSetᶜ).Connected)
    (hroot_outside : root ∉ T.first.vertexSet)
    (hinside_neighbors :
      forall v : V,
        v ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts ->
          (G.neighborSet v ∩ T.first.vertexSet).ncard <= 3) :
    RSTLeanTriadData G feet root where
  triad := T.first
  lean := hlean
  complement_connected := hcomplement_connected
  root_outside := hroot_outside
  inside_neighbors_at_most_three := hinside_neighbors
  foot_has_neighbor_outside := T.foot_has_neighbor_outside_first hfeet_injective

def RSTLeanTriadData.of_legless_tripod_second
    {feet : Fin 3 -> V}
    {root : V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (hlean : T.second.Lean)
    (hcomplement_connected : (G.induce T.second.vertexSetᶜ).Connected)
    (hroot_outside : root ∉ T.second.vertexSet)
    (hinside_neighbors :
      forall v : V,
        v ∈ (T.second.carrier.deleteVerts (Set.range feet)).verts ->
          (G.neighborSet v ∩ T.second.vertexSet).ncard <= 3) :
    RSTLeanTriadData G feet root where
  triad := T.second
  lean := hlean
  complement_connected := hcomplement_connected
  root_outside := hroot_outside
  inside_neighbors_at_most_three := hinside_neighbors
  foot_has_neighbor_outside := T.foot_has_neighbor_outside_second hfeet_injective

theorem LeglessTripod.exists_rstLeanTriadData_of_one_side
    {feet : Fin 3 -> V}
    {root : V}
    (T : LeglessTripod G feet)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet)
    (hfirst_lean : T.first.Lean)
    (hsecond_lean : T.second.Lean)
    (hfirst_complement_connected : (G.induce T.first.vertexSetᶜ).Connected)
    (hsecond_complement_connected : (G.induce T.second.vertexSetᶜ).Connected)
    (hfirst_inside_neighbors :
      forall v : V,
        v ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts ->
          (G.neighborSet v ∩ T.first.vertexSet).ncard <= 3)
    (hsecond_inside_neighbors :
      forall v : V,
        v ∈ (T.second.carrier.deleteVerts (Set.range feet)).verts ->
          (G.neighborSet v ∩ T.second.vertexSet).ncard <= 3) :
    Nonempty (RSTLeanTriadData G feet root) := by
  rcases T.vertex_avoids_first_or_second hroot_not_feet with hroot_first | hroot_second
  · exact ⟨RSTLeanTriadData.of_legless_tripod_first T hfeet_injective hfirst_lean
      hfirst_complement_connected hroot_first hfirst_inside_neighbors⟩
  · exact ⟨RSTLeanTriadData.of_legless_tripod_second T hfeet_injective hsecond_lean
      hsecond_complement_connected hroot_second hsecond_inside_neighbors⟩

def LeglessTripodRSTCertificate
    (G : SimpleGraph V) (feet : Fin 3 -> V) : Prop :=
  Exists fun T : LeglessTripod G feet =>
    T.first.Lean ∧
      T.second.Lean ∧
        (G.induce T.first.vertexSetᶜ).Connected ∧
          (G.induce T.second.vertexSetᶜ).Connected ∧
            (forall v : V,
              v ∈ (T.first.carrier.deleteVerts (Set.range feet)).verts ->
                (G.neighborSet v ∩ T.first.vertexSet).ncard <= 3) ∧
              (forall v : V,
                v ∈ (T.second.carrier.deleteVerts (Set.range feet)).verts ->
                  (G.neighborSet v ∩ T.second.vertexSet).ncard <= 3)

theorem LeglessTripodRSTCertificate.of_two_common_neighbors
    [Fintype V]
    {feet : Fin 3 -> V}
    {apex₁ apex₂ : V}
    (hapex₁_not_foot : forall i : Fin 3, apex₁ ≠ feet i)
    (hadj₁ : forall i : Fin 3, G.Adj apex₁ (feet i))
    (hapex₂_not_foot : forall i : Fin 3, apex₂ ≠ feet i)
    (hadj₂ : forall i : Fin 3, G.Adj apex₂ (feet i))
    (hapex_ne : apex₁ ≠ apex₂)
    (hfeet_injective : Function.Injective feet)
    (hfirst_complement_connected :
      (G.induce (Triad.of_common_neighbor
        (G := G) hapex₁_not_foot hadj₁).vertexSetᶜ).Connected)
    (hsecond_complement_connected :
      (G.induce (Triad.of_common_neighbor
        (G := G) hapex₂_not_foot hadj₂).vertexSetᶜ).Connected) :
    LeglessTripodRSTCertificate G feet := by
  classical
  let T : LeglessTripod G feet :=
    LeglessTripod.of_two_common_neighbors
      (G := G) hapex₁_not_foot hadj₁ hapex₂_not_foot hadj₂ hapex_ne
  refine ⟨T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [T, LeglessTripod.of_two_common_neighbors] using
      Triad.common_neighbor_lean (G := G) hapex₁_not_foot hadj₁
  · simpa [T, LeglessTripod.of_two_common_neighbors] using
      Triad.common_neighbor_lean (G := G) hapex₂_not_foot hadj₂
  · simpa [T, LeglessTripod.of_two_common_neighbors] using
      hfirst_complement_connected
  · simpa [T, LeglessTripod.of_two_common_neighbors] using
      hsecond_complement_connected
  · simpa [T, LeglessTripod.of_two_common_neighbors] using
      Triad.common_neighbor_inside_neighbors_at_most_three
        (G := G) hapex₁_not_foot hadj₁ hfeet_injective
  · simpa [T, LeglessTripod.of_two_common_neighbors] using
      Triad.common_neighbor_inside_neighbors_at_most_three
        (G := G) hapex₂_not_foot hadj₂ hfeet_injective

theorem LeglessTripodRSTCertificate.to_rstLeanTriadData
    {feet : Fin 3 -> V}
    {root : V}
    (hcert : LeglessTripodRSTCertificate G feet)
    (hfeet_injective : Function.Injective feet)
    (hroot_not_feet : root ∉ Set.range feet) :
    Nonempty (RSTLeanTriadData G feet root) := by
  rcases hcert with
    ⟨T, hfirst_lean, hsecond_lean, hfirst_complement_connected,
      hsecond_complement_connected, hfirst_inside_neighbors,
      hsecond_inside_neighbors⟩
  exact T.exists_rstLeanTriadData_of_one_side hfeet_injective hroot_not_feet
    hfirst_lean hsecond_lean hfirst_complement_connected
    hsecond_complement_connected hfirst_inside_neighbors hsecond_inside_neighbors

end Schematic.Math.GraphTheory
