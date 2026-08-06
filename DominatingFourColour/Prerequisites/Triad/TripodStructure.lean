import DominatingFourColour.Prerequisites.Triad.NeighborBounds

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

structure LeglessTripod (G : SimpleGraph V) (feet : Fin 3 -> V) where
  first : Triad G feet
  second : Triad G feet
  edge_disjoint :
    Disjoint first.carrier.edgeSet second.carrier.edgeSet
  meet_only_at_feet :
    first.vertexSet ∩ second.vertexSet ⊆ Set.range feet

structure Tripod (G : SimpleGraph V) (feet : Fin 3 -> V) where
  left : V
  right : V
  left_ne_right : left ≠ right
  left_not_foot : forall i : Fin 3, left ≠ feet i
  right_not_foot : forall i : Fin 3, right ≠ feet i
  rim : Fin 3 -> G.Walk left right
  rim_isPath : forall i : Fin 3, (rim i).IsPath
  attach : Fin 3 -> V
  attach_mem_rim : forall i : Fin 3, attach i ∈ Walk.InternalVertices (rim i)
  rim_internals_disjoint :
    forall i j : Fin 3, i ≠ j ->
      Disjoint (Walk.InternalVertices (rim i)) (Walk.InternalVertices (rim j))
  leg : forall i : Fin 3, G.Walk (attach i) (feet i)
  leg_isPath : forall i : Fin 3, (leg i).IsPath
  legs_disjoint :
    forall i j : Fin 3, i ≠ j ->
      Disjoint {v : V | v ∈ (leg i).support} {v : V | v ∈ (leg j).support}
  leg_meets_rims_only_at_attach :
    forall i j : Fin 3, forall v : V,
      v ∈ (leg i).support ->
        v ∈ (rim j).support ->
          v = attach i

/-- Reverse the common rim endpoints of a tripod, leaving its feet and legs fixed. -/
def Tripod.flip {feet : Fin 3 -> V} (H : Tripod G feet) : Tripod G feet where
  left := H.right
  right := H.left
  left_ne_right := H.left_ne_right.symm
  left_not_foot := H.right_not_foot
  right_not_foot := H.left_not_foot
  rim i := (H.rim i).reverse
  rim_isPath i := (H.rim_isPath i).reverse
  attach := H.attach
  attach_mem_rim i := by
    simpa [Walk.internalVertices_reverse] using H.attach_mem_rim i
  rim_internals_disjoint i j hij := by
    simpa [Walk.internalVertices_reverse] using H.rim_internals_disjoint i j hij
  leg := H.leg
  leg_isPath := H.leg_isPath
  legs_disjoint := H.legs_disjoint
  leg_meets_rims_only_at_attach i j v hvLeg hvRim := by
    apply H.leg_meets_rims_only_at_attach i j v hvLeg
    simpa [SimpleGraph.Walk.support_reverse] using hvRim

@[simp] theorem Tripod.flip_left {feet : Fin 3 -> V} (H : Tripod G feet) :
    H.flip.left = H.right := rfl

@[simp] theorem Tripod.flip_right {feet : Fin 3 -> V} (H : Tripod G feet) :
    H.flip.right = H.left := rfl

@[simp] theorem Tripod.flip_rim {feet : Fin 3 -> V} (H : Tripod G feet) (i : Fin 3) :
    H.flip.rim i = (H.rim i).reverse := rfl

@[simp] theorem Tripod.flip_attach {feet : Fin 3 -> V} (H : Tripod G feet) (i : Fin 3) :
    H.flip.attach i = H.attach i := rfl

@[simp] theorem Tripod.flip_leg {feet : Fin 3 -> V} (H : Tripod G feet) (i : Fin 3) :
    H.flip.leg i = H.leg i := rfl

def Tripod.rimVertexSet {feet : Fin 3 -> V} (H : Tripod G feet) : Set V :=
  {v | Exists fun i : Fin 3 => v ∈ (H.rim i).support}

def Tripod.legVertexSet {feet : Fin 3 -> V} (H : Tripod G feet) : Set V :=
  {v | Exists fun i : Fin 3 => v ∈ (H.leg i).support}

def Tripod.vertexSet {feet : Fin 3 -> V} (H : Tripod G feet) : Set V :=
  H.rimVertexSet ∪ H.legVertexSet

@[simp] theorem Tripod.flip_rimVertexSet
    {feet : Fin 3 -> V} (H : Tripod G feet) :
    H.flip.rimVertexSet = H.rimVertexSet := by
  ext v
  simp [Tripod.rimVertexSet, SimpleGraph.Walk.support_reverse]

@[simp] theorem Tripod.flip_legVertexSet
    {feet : Fin 3 -> V} (H : Tripod G feet) :
    H.flip.legVertexSet = H.legVertexSet := rfl

@[simp] theorem Tripod.flip_vertexSet
    {feet : Fin 3 -> V} (H : Tripod G feet) :
    H.flip.vertexSet = H.vertexSet := by
  simp [Tripod.vertexSet]

def Tripod.NoOtherVertexIn
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (Z : Set V) : Prop :=
  H.vertexSet ∩ Z ⊆ Set.range feet

theorem Tripod.mem_rimVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {v : V}
    (hv : v ∈ (H.rim i).support) :
    v ∈ H.rimVertexSet :=
  ⟨i, hv⟩

theorem Tripod.mem_legVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {v : V}
    (hv : v ∈ (H.leg i).support) :
    v ∈ H.legVertexSet :=
  ⟨i, hv⟩

theorem Tripod.left_mem_rimVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.left ∈ H.rimVertexSet :=
  H.mem_rimVertexSet (i := 0) (H.rim 0).start_mem_support

theorem Tripod.right_mem_rimVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.right ∈ H.rimVertexSet := by
  simpa using H.flip.left_mem_rimVertexSet

theorem Tripod.attach_mem_rimVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    H.attach i ∈ H.rimVertexSet :=
  H.mem_rimVertexSet (i := i) (H.attach_mem_rim i).1

theorem Tripod.attach_mem_legVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    H.attach i ∈ H.legVertexSet :=
  H.mem_legVertexSet (i := i) (H.leg i).start_mem_support

theorem Tripod.attach_range_subset_legVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    Set.range H.attach ⊆ H.legVertexSet := by
  rintro v ⟨i, rfl⟩
  exact H.attach_mem_legVertexSet i

theorem Tripod.not_mem_attach_range_of_not_mem_legVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {v : V}
    (hv : v ∉ H.legVertexSet) :
    v ∉ Set.range H.attach := by
  intro hattach
  exact hv (H.attach_range_subset_legVertexSet hattach)

theorem Tripod.foot_mem_legVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    feet i ∈ H.legVertexSet :=
  H.mem_legVertexSet (i := i) (H.leg i).end_mem_support

theorem Tripod.rimVertexSet_subset_vertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.rimVertexSet ⊆ H.vertexSet :=
  fun _ hv => Or.inl hv

theorem Tripod.legVertexSet_subset_vertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.legVertexSet ⊆ H.vertexSet :=
  fun _ hv => Or.inr hv

theorem Tripod.left_mem_vertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.left ∈ H.vertexSet :=
  H.rimVertexSet_subset_vertexSet H.left_mem_rimVertexSet

theorem Tripod.right_mem_vertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.right ∈ H.vertexSet := by
  simpa using H.flip.left_mem_vertexSet

theorem Tripod.attach_mem_vertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    H.attach i ∈ H.vertexSet :=
  H.rimVertexSet_subset_vertexSet (H.attach_mem_rimVertexSet i)

theorem Tripod.foot_mem_vertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    feet i ∈ H.vertexSet :=
  H.legVertexSet_subset_vertexSet (H.foot_mem_legVertexSet i)

theorem Tripod.mem_attach_range_of_mem_rimVertexSet_of_mem_legVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {v : V}
    (hvrim : v ∈ H.rimVertexSet)
    (hvleg : v ∈ H.legVertexSet) :
    v ∈ Set.range H.attach := by
  rcases hvrim with ⟨j, hvj⟩
  rcases hvleg with ⟨i, hvi⟩
  exact ⟨i, (H.leg_meets_rims_only_at_attach i j v hvi hvj).symm⟩

theorem Tripod.rimVertexSet_inter_legVertexSet_subset_attach_range
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.rimVertexSet ∩ H.legVertexSet ⊆ Set.range H.attach := by
  rintro v ⟨hvrim, hvleg⟩
  exact H.mem_attach_range_of_mem_rimVertexSet_of_mem_legVertexSet hvrim hvleg

theorem Tripod.not_mem_legVertexSet_of_mem_rimVertexSet_of_not_attach
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {v : V}
    (hvrim : v ∈ H.rimVertexSet)
    (hvattach : v ∉ Set.range H.attach) :
    v ∉ H.legVertexSet := by
  intro hvleg
  exact hvattach
    (H.mem_attach_range_of_mem_rimVertexSet_of_mem_legVertexSet hvrim hvleg)

theorem Tripod.left_not_mem_legVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.left ∉ H.legVertexSet := by
  intro hleg
  rcases H.mem_attach_range_of_mem_rimVertexSet_of_mem_legVertexSet
      H.left_mem_rimVertexSet hleg with ⟨i, hi⟩
  exact (H.attach_mem_rim i).2.1 hi

theorem Tripod.right_not_mem_legVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.right ∉ H.legVertexSet := by
  simpa using H.flip.left_not_mem_legVertexSet

theorem Tripod.feet_subset_of_noOtherVertexIn
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {Z : Set V}
    (hZ : forall i : Fin 3, feet i ∈ Z) :
    Set.range feet ⊆ H.vertexSet ∩ Z := by
  rintro v ⟨i, rfl⟩
  exact ⟨H.foot_mem_vertexSet i, hZ i⟩

def Tripod.Legless {feet : Fin 3 -> V} (H : Tripod G feet) : Prop :=
  forall i : Fin 3, H.attach i = feet i

@[simp] theorem Tripod.flip_legless
    {feet : Fin 3 -> V} (H : Tripod G feet) :
    H.flip.Legless ↔ H.Legless := Iff.rfl

theorem Tripod.attach_ne_left
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    H.attach i ≠ H.left :=
  (H.attach_mem_rim i).2.1

theorem Tripod.attach_ne_right
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3) :
    H.attach i ≠ H.right := by
  simpa using H.flip.attach_ne_left i

theorem Tripod.leg_support_ne_left
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {v : V}
    (hv : v ∈ (H.leg i).support) :
    v ≠ H.left := by
  intro hv_left
  have hleft_rim : v ∈ (H.rim i).support := by
    simp [hv_left]
  have hv_attach : v = H.attach i :=
    H.leg_meets_rims_only_at_attach i i v hv hleft_rim
  exact H.attach_ne_left i (hv_attach.symm.trans hv_left)

theorem Tripod.leg_support_ne_right
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    {v : V}
    (hv : v ∈ (H.leg i).support) :
    v ≠ H.right := by
  simpa using H.flip.leg_support_ne_left hv

theorem Tripod.attach_injective
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    Function.Injective H.attach := by
  intro i j hij_attach
  by_contra hij
  exact Set.disjoint_left.mp (H.rim_internals_disjoint i j hij)
    (by simpa [hij_attach] using H.attach_mem_rim i)
    (H.attach_mem_rim j)

theorem Tripod.attach_range_ncard_eq_three
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    (Set.range H.attach).ncard = 3 := by
  rw [Set.ncard_range_of_injective H.attach_injective]
  simp

theorem Tripod.left_not_mem_attach_range
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.left ∉ Set.range H.attach := by
  rintro ⟨i, hi⟩
  exact H.attach_ne_left i hi

theorem Tripod.right_not_mem_attach_range
    {feet : Fin 3 -> V}
    (H : Tripod G feet) :
    H.right ∉ Set.range H.attach := by
  simpa using H.flip.left_not_mem_attach_range

theorem Tripod.eq_endpoint_or_exists_rim_internal_of_mem_rimVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {x : V}
    (hx : x ∈ H.rimVertexSet) :
    x = H.left ∨ x = H.right ∨
      Exists fun i : Fin 3 => x ∈ Walk.InternalVertices (H.rim i) := by
  rcases hx with ⟨i, hxi⟩
  by_cases hleft : x = H.left
  · exact Or.inl hleft
  · by_cases hright : x = H.right
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr ⟨i, hxi, hleft, hright⟩)

theorem Tripod.eq_endpoint_or_exists_rim_internal_of_mem_rimVertexSet_diff_legVertexSet
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {x : V}
    (hx : x ∈ H.rimVertexSet \ H.legVertexSet) :
    x = H.left ∨ x = H.right ∨
      Exists fun i : Fin 3 => x ∈ Walk.InternalVertices (H.rim i) :=
  H.eq_endpoint_or_exists_rim_internal_of_mem_rimVertexSet hx.1

theorem Tripod.attach_range_orderAtMost_three
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (S : Separation G)
    (hS : S.separator = Set.range H.attach) :
    S.OrderAtMost 3 := by
  classical
  let F : Finset V := Finset.univ.image H.attach
  have hF : (F : Set V) = Set.range H.attach := by
    ext v
    simp [F]
  refine ⟨F, ?_, ?_⟩
  · rw [hF, hS]
  · calc
      F.card <= (Finset.univ : Finset (Fin 3)).card :=
        Finset.card_image_le
      _ = 3 := by simp

theorem Tripod.attach_range_orderEq_three
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (S : Separation G)
    (hS : S.separator = Set.range H.attach) :
    S.OrderEq 3 := by
  classical
  let F : Finset V := Finset.univ.image H.attach
  have hF : (F : Set V) = Set.range H.attach := by
    ext v
    simp [F]
  refine ⟨F, ?_, ?_⟩
  · rw [hF, hS]
  · change (Finset.univ.image H.attach).card = 3
    rw [Finset.card_image_of_injective _ H.attach_injective]
    simp

def Tripod.legLengthSum {feet : Fin 3 -> V} (H : Tripod G feet) : Nat :=
  (H.leg 0).length + (H.leg 1).length + (H.leg 2).length

@[simp] theorem Tripod.flip_legLengthSum
    {feet : Fin 3 -> V} (H : Tripod G feet) :
    H.flip.legLengthSum = H.legLengthSum := rfl

end Schematic.Math.GraphTheory
