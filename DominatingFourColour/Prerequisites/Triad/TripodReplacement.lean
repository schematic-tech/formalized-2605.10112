import DominatingFourColour.Prerequisites.Triad.TripodStructure

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

def Tripod.replaceLeg
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (p : G.Walk (H.attach i) (feet i))
    (hp : p.IsPath)
    (hlegs_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint {v : V | v ∈ p.support} {v : V | v ∈ (H.leg j).support})
    (hmeets_rims :
      forall j : Fin 3, forall v : V,
        v ∈ p.support ->
          v ∈ (H.rim j).support ->
            v = H.attach i) :
    Tripod G feet where
  left := H.left
  right := H.right
  left_ne_right := H.left_ne_right
  left_not_foot := H.left_not_foot
  right_not_foot := H.right_not_foot
  rim := H.rim
  rim_isPath := H.rim_isPath
  attach := H.attach
  attach_mem_rim := H.attach_mem_rim
  rim_internals_disjoint := H.rim_internals_disjoint
  leg j :=
    if hji : j = i then
      p.copy (by simp [hji]) (by simp [hji])
    else
      H.leg j
  leg_isPath j := by
    by_cases hji : j = i
    · simp [hji, hp]
    · simp [hji, H.leg_isPath j]
  legs_disjoint := by
    intro j k hjk
    have hdis := Fin3.pairwise_disjoint_update
        (fun j => {v : V | v ∈ (H.leg j).support}) i
        {v : V | v ∈ p.support} H.legs_disjoint hlegs_disjoint j k hjk
    by_cases hji : j = i <;> by_cases hki : k = i <;>
      simp [hji, hki] at hdis ⊢ <;> assumption
  leg_meets_rims_only_at_attach := by
    intro j k v hvleg hvrim
    by_cases hji : j = i
    · subst j
      have hvleg' : v ∈ p.support := by
        simpa using hvleg
      exact hmeets_rims k v hvleg' hvrim
    · have hvleg_old : v ∈ (H.leg j).support := by
        simpa [hji] using hvleg
      exact H.leg_meets_rims_only_at_attach j k v hvleg_old hvrim

@[simp]
theorem Tripod.replaceLeg_leg_self
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (p : G.Walk (H.attach i) (feet i))
    (hp : p.IsPath)
    (hlegs_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint {v : V | v ∈ p.support} {v : V | v ∈ (H.leg j).support})
    (hmeets_rims :
      forall j : Fin 3, forall v : V,
        v ∈ p.support ->
          v ∈ (H.rim j).support ->
            v = H.attach i) :
    (H.replaceLeg i p hp hlegs_disjoint hmeets_rims).leg i = p := by
  simp [Tripod.replaceLeg]

@[simp]
theorem Tripod.replaceLeg_leg_ne
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i j : Fin 3}
    (hji : j ≠ i)
    (p : G.Walk (H.attach i) (feet i))
    (hp : p.IsPath)
    (hlegs_disjoint :
      forall k : Fin 3, k ≠ i ->
        Disjoint {v : V | v ∈ p.support} {v : V | v ∈ (H.leg k).support})
    (hmeets_rims :
      forall k : Fin 3, forall v : V,
        v ∈ p.support ->
          v ∈ (H.rim k).support ->
            v = H.attach i) :
    (H.replaceLeg i p hp hlegs_disjoint hmeets_rims).leg j = H.leg j := by
  simp [Tripod.replaceLeg, hji]

theorem Tripod.replaceLeg_legLengthSum_lt
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (p : G.Walk (H.attach i) (feet i))
    (hp : p.IsPath)
    (hlegs_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint {v : V | v ∈ p.support} {v : V | v ∈ (H.leg j).support})
    (hmeets_rims :
      forall j : Fin 3, forall v : V,
        v ∈ p.support ->
          v ∈ (H.rim j).support ->
            v = H.attach i)
    (hlt : p.length < (H.leg i).length) :
    (H.replaceLeg i p hp hlegs_disjoint hmeets_rims).legLengthSum <
      H.legLengthSum := by
  simpa [Tripod.legLengthSum] using
    (Fin3.sum_lt_of_update
      (fun j => (H.leg j).length)
      (fun j =>
        ((H.replaceLeg i p hp hlegs_disjoint hmeets_rims).leg j).length)
      i (by simpa using hlt) (by
        intro j hji
        simpa using congrArg (fun w => w.length)
          (H.replaceLeg_leg_ne hji p hp hlegs_disjoint hmeets_rims)))

theorem Tripod.exists_legLengthSum_lt_of_shorter_same_attach_path
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (p : G.Walk (H.attach i) (feet i))
    (hp : p.IsPath)
    (hlegs_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint {v : V | v ∈ p.support} {v : V | v ∈ (H.leg j).support})
    (hmeets_rims :
      forall j : Fin 3, forall v : V,
        v ∈ p.support ->
          v ∈ (H.rim j).support ->
            v = H.attach i)
    (hlt : p.length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum :=
  ⟨H.replaceLeg i p hp hlegs_disjoint hmeets_rims,
    H.replaceLeg_legLengthSum_lt i p hp hlegs_disjoint hmeets_rims hlt⟩

theorem Tripod.exists_legLengthSum_lt_of_shorter_same_attach_subpath
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (p : G.Walk (H.attach i) (feet i))
    (hp : p.IsPath)
    (hsubset : forall v : V, v ∈ p.support -> v ∈ (H.leg i).support)
    (hlt : p.length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  refine H.exists_legLengthSum_lt_of_shorter_same_attach_path i p hp ?_ ?_ hlt
  · intro j hij
    rw [Set.disjoint_left]
    intro v hvp hvj
    exact Set.disjoint_left.mp (H.legs_disjoint i j (fun h => hij h.symm))
      (hsubset v hvp) hvj
  · intro j v hvp hvrim
    exact H.leg_meets_rims_only_at_attach i j v (hsubset v hvp) hvrim

def Tripod.replaceRimAndLeg
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (newRim : G.Walk H.left H.right)
    (newAttach : V)
    (hnewAttach_mem_rim : newAttach ∈ Walk.InternalVertices newRim)
    (newLeg : G.Walk newAttach (feet i))
    (hnewRim_path : newRim.IsPath)
    (hnewLeg_path : newLeg.IsPath)
    (hrim_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint (Walk.InternalVertices newRim) (Walk.InternalVertices (H.rim j)))
    (hleg_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint {v : V | v ∈ newLeg.support} {v : V | v ∈ (H.leg j).support})
    (hnewLeg_meets_newRim :
      forall v : V, v ∈ newLeg.support -> v ∈ newRim.support -> v = newAttach)
    (hnewLeg_meets_oldRim :
      forall j : Fin 3, j ≠ i ->
        forall v : V, v ∈ newLeg.support -> v ∈ (H.rim j).support ->
          v = newAttach)
    (holdLeg_meets_newRim :
      forall j : Fin 3, j ≠ i ->
        forall v : V, v ∈ (H.leg j).support -> v ∈ newRim.support ->
          v = H.attach j) :
    Tripod G feet where
  left := H.left
  right := H.right
  left_ne_right := H.left_ne_right
  left_not_foot := H.left_not_foot
  right_not_foot := H.right_not_foot
  rim j :=
    if hji : j = i then
      newRim
    else
      H.rim j
  rim_isPath j := by
    by_cases hji : j = i
    · simp [hji, hnewRim_path]
    · simp [hji, H.rim_isPath j]
  attach j :=
    if hji : j = i then
      newAttach
    else
      H.attach j
  attach_mem_rim := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hnewAttach_mem_rim
    · simpa [hji] using H.attach_mem_rim j
  rim_internals_disjoint := by
    intro j k hjk
    have hdis := Fin3.pairwise_disjoint_update
        (fun j => Walk.InternalVertices (H.rim j)) i
        (Walk.InternalVertices newRim) H.rim_internals_disjoint hrim_disjoint j k hjk
    by_cases hji : j = i <;> by_cases hki : k = i <;>
      simp [hji, hki] at hdis ⊢ <;> assumption
  leg j :=
    if hji : j = i then
      newLeg.copy (by simp [hji]) (by simp [hji])
    else
      (H.leg j).copy (by simp [hji]) rfl
  leg_isPath j := by
    by_cases hji : j = i
    · simp [hji, hnewLeg_path]
    · simp [hji, H.leg_isPath j]
  legs_disjoint := by
    intro j k hjk
    have hdis := Fin3.pairwise_disjoint_update
        (fun j => {v : V | v ∈ (H.leg j).support}) i
        {v : V | v ∈ newLeg.support} H.legs_disjoint hleg_disjoint j k hjk
    by_cases hji : j = i <;> by_cases hki : k = i <;>
      simp [hji, hki] at hdis ⊢ <;> assumption
  leg_meets_rims_only_at_attach := by
    intro j k v hvleg hvrim
    by_cases hji : j = i
    · subst j
      have hvleg_new : v ∈ newLeg.support := by
        simpa using hvleg
      by_cases hki : k = i
      · subst k
        have hvrim_new : v ∈ newRim.support := by
          simpa using hvrim
        simpa using hnewLeg_meets_newRim v hvleg_new hvrim_new
      · have hvrim_old : v ∈ (H.rim k).support := by
          simpa [hki] using hvrim
        simpa using hnewLeg_meets_oldRim k hki v hvleg_new hvrim_old
    · have hvleg_old : v ∈ (H.leg j).support := by
        simpa [hji] using hvleg
      by_cases hki : k = i
      · subst k
        have hvrim_new : v ∈ newRim.support := by
          simpa using hvrim
        simpa [hji] using holdLeg_meets_newRim j hji v hvleg_old hvrim_new
      · have hvrim_old : v ∈ (H.rim k).support := by
          simpa [hki] using hvrim
        simpa [hji, hki] using
          H.leg_meets_rims_only_at_attach j k v hvleg_old hvrim_old

theorem Tripod.replaceRimAndLeg_legLengthSum_lt
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (newRim : G.Walk H.left H.right)
    (newAttach : V)
    (hnewAttach_mem_rim : newAttach ∈ Walk.InternalVertices newRim)
    (newLeg : G.Walk newAttach (feet i))
    (hnewRim_path : newRim.IsPath)
    (hnewLeg_path : newLeg.IsPath)
    (hrim_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint (Walk.InternalVertices newRim) (Walk.InternalVertices (H.rim j)))
    (hleg_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint {v : V | v ∈ newLeg.support} {v : V | v ∈ (H.leg j).support})
    (hnewLeg_meets_newRim :
      forall v : V, v ∈ newLeg.support -> v ∈ newRim.support -> v = newAttach)
    (hnewLeg_meets_oldRim :
      forall j : Fin 3, j ≠ i ->
        forall v : V, v ∈ newLeg.support -> v ∈ (H.rim j).support ->
          v = newAttach)
    (holdLeg_meets_newRim :
      forall j : Fin 3, j ≠ i ->
        forall v : V, v ∈ (H.leg j).support -> v ∈ newRim.support ->
          v = H.attach j)
    (hlt : newLeg.length < (H.leg i).length) :
    (H.replaceRimAndLeg i newRim newAttach hnewAttach_mem_rim newLeg
      hnewRim_path hnewLeg_path hrim_disjoint hleg_disjoint
      hnewLeg_meets_newRim hnewLeg_meets_oldRim holdLeg_meets_newRim).legLengthSum <
        H.legLengthSum := by
  simpa [Tripod.legLengthSum] using
    (Fin3.sum_lt_of_update
      (fun j => (H.leg j).length)
      (fun j =>
        ((H.replaceRimAndLeg i newRim newAttach hnewAttach_mem_rim newLeg
          hnewRim_path hnewLeg_path hrim_disjoint hleg_disjoint
          hnewLeg_meets_newRim hnewLeg_meets_oldRim holdLeg_meets_newRim).leg j).length)
      i (by simpa [Tripod.replaceRimAndLeg] using hlt) (by
        intro j hji
        simp [Tripod.replaceRimAndLeg, hji]))

theorem Tripod.exists_legLengthSum_lt_of_replaceRimAndLeg
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    (newRim : G.Walk H.left H.right)
    (newAttach : V)
    (hnewAttach_mem_rim : newAttach ∈ Walk.InternalVertices newRim)
    (newLeg : G.Walk newAttach (feet i))
    (hnewRim_path : newRim.IsPath)
    (hnewLeg_path : newLeg.IsPath)
    (hrim_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint (Walk.InternalVertices newRim) (Walk.InternalVertices (H.rim j)))
    (hleg_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint {v : V | v ∈ newLeg.support} {v : V | v ∈ (H.leg j).support})
    (hnewLeg_meets_newRim :
      forall v : V, v ∈ newLeg.support -> v ∈ newRim.support -> v = newAttach)
    (hnewLeg_meets_oldRim :
      forall j : Fin 3, j ≠ i ->
        forall v : V, v ∈ newLeg.support -> v ∈ (H.rim j).support ->
          v = newAttach)
    (holdLeg_meets_newRim :
      forall j : Fin 3, j ≠ i ->
        forall v : V, v ∈ (H.leg j).support -> v ∈ newRim.support ->
          v = H.attach j)
    (hlt : newLeg.length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum :=
  ⟨H.replaceRimAndLeg i newRim newAttach hnewAttach_mem_rim newLeg
      hnewRim_path hnewLeg_path hrim_disjoint hleg_disjoint
      hnewLeg_meets_newRim hnewLeg_meets_oldRim holdLeg_meets_newRim,
    H.replaceRimAndLeg_legLengthSum_lt i newRim newAttach hnewAttach_mem_rim
      newLeg hnewRim_path hnewLeg_path hrim_disjoint hleg_disjoint
      hnewLeg_meets_newRim hnewLeg_meets_oldRim holdLeg_meets_newRim hlt⟩

theorem Tripod.exists_legLengthSum_lt_of_shorter_same_rim_path
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    (i : Fin 3)
    {x : V}
    (hx : x ∈ Walk.InternalVertices (H.rim i))
    (p : G.Walk x (feet i))
    (hp : p.IsPath)
    (hleg_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint {v : V | v ∈ p.support} {v : V | v ∈ (H.leg j).support})
    (hp_meets_rims :
      forall j : Fin 3, forall v : V,
        v ∈ p.support -> v ∈ (H.rim j).support -> v = x)
    (hlt : p.length < (H.leg i).length) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum :=
  H.exists_legLengthSum_lt_of_replaceRimAndLeg i (H.rim i) x hx p
    (H.rim_isPath i) hp
    (by
      intro j hji
      exact H.rim_internals_disjoint i j (fun hij => hji hij.symm))
    hleg_disjoint
    (hp_meets_rims i)
    (by
      intro j _hji v hvp hvrim
      exact hp_meets_rims j v hvp hvrim)
    (by
      intro j hji v hvleg hvrim
      exact H.leg_meets_rims_only_at_attach j i v hvleg hvrim)
    hlt

theorem Tripod.exists_legLengthSum_lt_of_replaceRim_attach_foot
    {feet : Fin 3 -> V}
    (H : Tripod G feet)
    {i : Fin 3}
    (hpos : 0 < (H.leg i).length)
    (newRim : G.Walk H.left H.right)
    (hfoot_mem_newRim : feet i ∈ Walk.InternalVertices newRim)
    (hnewRim_path : newRim.IsPath)
    (hrim_disjoint :
      forall j : Fin 3, j ≠ i ->
        Disjoint (Walk.InternalVertices newRim) (Walk.InternalVertices (H.rim j)))
    (holdLeg_meets_newRim :
      forall j : Fin 3, j ≠ i ->
        forall v : V, v ∈ (H.leg j).support -> v ∈ newRim.support ->
          v = H.attach j) :
    Exists fun H' : Tripod G feet => H'.legLengthSum < H.legLengthSum := by
  refine H.exists_legLengthSum_lt_of_replaceRimAndLeg
    i newRim (feet i) hfoot_mem_newRim
    (SimpleGraph.Walk.nil : G.Walk (feet i) (feet i))
    hnewRim_path SimpleGraph.Walk.IsPath.nil hrim_disjoint ?_ ?_ ?_
    holdLeg_meets_newRim ?_
  · intro j hji
    rw [Set.disjoint_left]
    intro v hvnil hvj
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hvnil
    subst v
    exact Set.disjoint_left.mp (H.legs_disjoint i j (fun hij => hji hij.symm))
      (H.leg i).end_mem_support hvj
  · intro v hvnil _hvrim
    simpa using hvnil
  · intro j _hji v hvnil _hvrim
    simpa using hvnil
  · simpa using hpos

end Schematic.Math.GraphTheory
