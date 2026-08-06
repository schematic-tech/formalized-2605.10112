import DominatingFourColour.Prerequisites.TripodMinimal.RSTStatements

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

theorem exists_lean_subtriad
    [Fintype V]
    (feet : Fin 3 -> V)
    (h_exists : Nonempty (Triad G feet)) :
    Exists fun T : Triad G feet => T.Lean := by
  classical
  let P : Nat -> Prop := fun n => Exists fun T : Triad G feet => T.vertexSet.ncard = n
  have hP : Exists P := by
    rcases h_exists with ⟨T⟩
    exact ⟨T.vertexSet.ncard, T, rfl⟩
  obtain ⟨T, hT_card⟩ := Nat.find_spec hP
  refine ⟨T, ?_⟩
  intro T' hT'_subset
  have hcard : T.vertexSet.ncard <= T'.vertexSet.ncard := by
    rw [hT_card]
    exact Nat.find_min' hP ⟨T', rfl⟩
  have heq : T'.vertexSet = T.vertexSet :=
    Set.eq_of_subset_of_ncard_le hT'_subset hcard
  exact heq.symm.subset

theorem Triad.exists_lean_subtriad_subset
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet) :
    Exists fun T' : Triad G feet =>
      T'.Lean ∧ T'.vertexSet ⊆ T.vertexSet := by
  classical
  let P : Nat -> Prop := fun n =>
    Exists fun T' : Triad G feet =>
      T'.vertexSet ⊆ T.vertexSet ∧ T'.vertexSet.ncard = n
  have hP : Exists P := by
    exact ⟨T.vertexSet.ncard, T, subset_rfl, rfl⟩
  obtain ⟨T₀, hT₀_subset, hT₀_card⟩ := Nat.find_spec hP
  refine ⟨T₀, ?_, hT₀_subset⟩
  intro T' hT'_subset
  have hT'_T : T'.vertexSet ⊆ T.vertexSet :=
    Set.Subset.trans hT'_subset hT₀_subset
  have hcard : T₀.vertexSet.ncard <= T'.vertexSet.ncard := by
    rw [hT₀_card]
    exact Nat.find_min' hP ⟨T', hT'_T, rfl⟩
  have heq : T'.vertexSet = T₀.vertexSet :=
    Set.eq_of_subset_of_ncard_le hT'_subset hcard
  exact heq.symm.subset

theorem Triad.not_lean_iff_exists_strict_subtriad
    {feet : Fin 3 -> V}
    (T : Triad G feet) :
    Not T.Lean ↔ Exists fun T' : Triad G feet => T'.vertexSet ⊂ T.vertexSet := by
  constructor
  · intro hnot
    rw [Triad.Lean] at hnot
    push Not at hnot
    rcases hnot with ⟨T', hsubset, hnot_superset⟩
    exact ⟨T', hsubset, hnot_superset⟩
  · rintro ⟨T', hstrict⟩ hlean
    exact hstrict.2 (hlean T' hstrict.1)

theorem Triad.lean_iff_no_strict_subtriad
    {feet : Fin 3 -> V}
    (T : Triad G feet) :
    T.Lean ↔ Not (Exists fun T' : Triad G feet => T'.vertexSet ⊂ T.vertexSet) := by
  rw [← T.not_lean_iff_exists_strict_subtriad, not_not]

def Triad.AvoidsSet {feet : Fin 3 -> V} (T : Triad G feet) (W : Set V) : Prop :=
  Disjoint T.vertexSet W

abbrev Triad.Flap {feet : Fin 3 -> V} (T : Triad G feet) :=
  (G.induce T.vertexSetᶜ).ConnectedComponent

def Triad.flapVertexSet
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap) :
    Set V :=
  induceComponentSupport (G := G) B

theorem Triad.flapVertexSet_subset_complement
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap) :
    T.flapVertexSet B ⊆ T.vertexSetᶜ :=
  induceComponentSupport_subset (G := G) B

theorem Triad.flapVertexSet_nonempty
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap) :
    (T.flapVertexSet B).Nonempty :=
  induceComponentSupport_nonempty (G := G) B

theorem Triad.exists_flap_containing_vertex_outside
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {x : V}
    (hx : x ∉ T.vertexSet) :
    Exists fun B : T.Flap => x ∈ T.flapVertexSet B := by
  let xC : (T.vertexSetᶜ : Set V) := ⟨x, hx⟩
  let B : T.Flap := (G.induce T.vertexSetᶜ).connectedComponentMk xC
  refine ⟨B, ?_⟩
  exact ⟨hx, by
    change xC ∈ B.supp
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

noncomputable def Triad.flapSizeProfileWith
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap) :
    List Nat := by
  classical
  letI : Fintype (T.vertexSetᶜ : Set V) := (T.vertexSetᶜ).toFinite.fintype
  exact
    (T.flapVertexSet B).ncard ::
      Multiset.sort
        (((Finset.univ.erase B : Finset T.Flap).val.map
          fun C => (T.flapVertexSet C).ncard))
        (fun a b : Nat => b <= a)

noncomputable def Triad.flapSizeTailWith
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap) :
    List Nat := by
  classical
  letI : Fintype (T.vertexSetᶜ : Set V) := (T.vertexSetᶜ).toFinite.fintype
  exact
    Multiset.sort
      (((Finset.univ.erase B : Finset T.Flap).val.map
        fun C => (T.flapVertexSet C).ncard))
      (fun a b : Nat => b <= a)

theorem Triad.flapSizeProfileWith_eq_cons_tailWith
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap) :
    T.flapSizeProfileWith B =
      (T.flapVertexSet B).ncard :: T.flapSizeTailWith B := by
  simp [Triad.flapSizeProfileWith, Triad.flapSizeTailWith]

theorem Triad.mem_flapSizeTailWith_iff
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap)
    {n : Nat} :
    n ∈ T.flapSizeTailWith B ↔
      Exists fun C : T.Flap => C ≠ B ∧ n = (T.flapVertexSet C).ncard := by
  classical
  rw [Triad.flapSizeTailWith, Multiset.mem_sort]
  simp only [Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨C, hC_erase, hCn⟩
    exact ⟨C, (Finset.mem_erase.mp hC_erase).1, hCn.symm⟩
  · rintro ⟨C, hCB, rfl⟩
    refine ⟨C, ?_, rfl⟩
    simpa [Finset.mem_erase] using hCB

theorem Triad.mem_flapSizeTailWith_of_ne
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {B C : T.Flap}
    (hCB : C ≠ B) :
    (T.flapVertexSet C).ncard ∈ T.flapSizeTailWith B := by
  exact (T.mem_flapSizeTailWith_iff B).mpr ⟨C, hCB, rfl⟩

theorem Triad.mem_erase_flapSizeTailWith_of_ncard_ne
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {B D E : T.Flap}
    (hEB : E ≠ B)
    (hsize_ne :
      (T.flapVertexSet E).ncard ≠ (T.flapVertexSet D).ncard) :
    (T.flapVertexSet E).ncard ∈
      ((T.flapSizeTailWith B : Multiset Nat).erase
        (T.flapVertexSet D).ncard) := by
  exact (Multiset.mem_erase_of_ne hsize_ne).2
    (by
      simpa using T.mem_flapSizeTailWith_of_ne hEB)

theorem multiset_mem_erase_map_of_mem_of_ne
    {α β : Type*}
    [DecidableEq α]
    [DecidableEq β]
    {s : Multiset α}
    {d e : α}
    (hd : d ∈ s)
    (he : e ∈ s)
    (hed : e ≠ d)
    (f : α -> β) :
    f e ∈ (s.map f).erase (f d) := by
  have he_erase : e ∈ s.erase d := by
    exact (Multiset.mem_erase_of_ne hed).2 he
  have hmap_mem : f e ∈ (s.erase d).map f := by
    exact Multiset.mem_map.mpr ⟨e, he_erase, rfl⟩
  have hmap_erase :
      (s.erase d).map f = (s.map f).erase (f d) :=
    Multiset.map_erase_of_mem f s hd
  simpa [hmap_erase] using hmap_mem

theorem Triad.mem_erase_flapSizeTailWith_of_ne
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {B D E : T.Flap}
    (hDB : D ≠ B)
    (hEB : E ≠ B)
    (hED : E ≠ D) :
    (T.flapVertexSet E).ncard ∈
      ((T.flapSizeTailWith B : Multiset Nat).erase
        (T.flapVertexSet D).ncard) := by
  classical
  letI : Fintype (T.vertexSetᶜ : Set V) := (T.vertexSetᶜ).toFinite.fintype
  let tailFlaps : Multiset T.Flap :=
    (Finset.univ.erase B : Finset T.Flap).val
  have hD_mem : D ∈ tailFlaps := by
    exact (Multiset.mem_erase_of_ne hDB).2 (by simp)
  have hE_mem : E ∈ tailFlaps := by
    exact (Multiset.mem_erase_of_ne hEB).2 (by simp)
  have hmem :
      (fun C : T.Flap => (T.flapVertexSet C).ncard) E ∈
        ((tailFlaps.map fun C : T.Flap => (T.flapVertexSet C).ncard).erase
          ((fun C : T.Flap => (T.flapVertexSet C).ncard) D)) :=
    multiset_mem_erase_map_of_mem_of_ne hD_mem hE_mem hED
      (fun C : T.Flap => (T.flapVertexSet C).ncard)
  simpa [Triad.flapSizeTailWith, tailFlaps] using hmem

theorem Triad.flapSizeTailWith_pairwise_desc
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    (B : T.Flap) :
    (T.flapSizeTailWith B).Pairwise (fun a b : Nat => b <= a) := by
  classical
  simp [Triad.flapSizeTailWith]

theorem Triad.flapSizeTailWith_min_of_other_flap_ncard_minimal
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {B D : T.Flap}
    (hD_min :
      forall E : T.Flap, E ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet E).ncard)
    {n : Nat}
    (hn : n ∈ T.flapSizeTailWith B) :
    (T.flapVertexSet D).ncard <= n := by
  obtain ⟨C, hCB, rfl⟩ :=
    (T.mem_flapSizeTailWith_iff B).mp hn
  exact hD_min C hCB

theorem Triad.flapSizeProfileWith_lt_of_tailWith_lt
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B : T.Flap}
    {B' : T'.Flap}
    (hhead :
      (T.flapVertexSet B).ncard = (T'.flapVertexSet B').ncard)
    (htail : T.flapSizeTailWith B < T'.flapSizeTailWith B') :
    T.flapSizeProfileWith B < T'.flapSizeProfileWith B' := by
  change List.Lex (fun a b : Nat => a < b)
    (T.flapSizeProfileWith B) (T'.flapSizeProfileWith B')
  rw [T.flapSizeProfileWith_eq_cons_tailWith B,
    T'.flapSizeProfileWith_eq_cons_tailWith B']
  rw [hhead]
  exact List.Lex.cons htail

theorem Triad.flapSizeProfileWith_lt_of_tailWith_lt_of_distinguished_eq
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B : T.Flap}
    {B' : T'.Flap}
    (hB_eq : T.flapVertexSet B = T'.flapVertexSet B')
    (htail : T.flapSizeTailWith B < T'.flapSizeTailWith B') :
    T.flapSizeProfileWith B < T'.flapSizeProfileWith B' := by
  exact Triad.flapSizeProfileWith_lt_of_tailWith_lt
    (G := G) (T := T) (T' := T') (B := B) (B' := B')
    (by rw [hB_eq]) htail

theorem list_lt_of_exists_mem_gt_all_of_pairwise_desc
    {xs ys : List Nat}
    (hys_pairwise : ys.Pairwise (fun a b : Nat => b <= a))
    (hgt : Exists fun y : Nat => y ∈ ys ∧ forall x : Nat, x ∈ xs -> x < y) :
    xs < ys := by
  rcases hgt with ⟨y, hy_mem, hy_gt⟩
  change List.Lex (fun a b : Nat => a < b) xs ys
  cases ys with
  | nil => cases hy_mem
  | cons y₀ ys =>
      have hy_le_y₀ : y <= y₀ := by
        cases hy_mem with
        | head => rfl
        | tail =>
            exact List.rel_of_pairwise_cons hys_pairwise (by assumption)
      cases xs with
      | nil => exact List.Lex.nil
      | cons x xs =>
          exact List.Lex.rel (lt_of_lt_of_le (hy_gt x (by simp)) hy_le_y₀)

theorem list_mem_le_head_of_pairwise_desc
    {a n : Nat}
    {xs : List Nat}
    (hxs_pairwise : (a :: xs).Pairwise (fun x y : Nat => y <= x))
    (hn : n ∈ a :: xs) :
    n <= a := by
  cases hn with
  | head => rfl
  | tail =>
      exact List.rel_of_pairwise_cons hxs_pairwise (by assumption)

theorem list_le_of_sublist_of_pairwise_desc
    {xs ys : List Nat}
    (hsub : List.Sublist xs ys)
    (hys_pairwise : ys.Pairwise (fun x y : Nat => y <= x)) :
    xs <= ys := by
  induction ys generalizing xs with
  | nil =>
      have hxs_nil : xs = [] := List.eq_nil_of_sublist_nil hsub
      subst xs
      rfl
  | cons a ys ih =>
      cases xs with
      | nil =>
          exact le_of_lt List.Lex.nil
      | cons x xs =>
          have hys_tail_pairwise : ys.Pairwise (fun x y : Nat => y <= x) :=
            (List.pairwise_cons.mp hys_pairwise).2
          rcases List.cons_sublist_cons'.mp hsub with hskip | ⟨hxa, hxs_sub⟩
          · have hx_mem_ys : x ∈ ys :=
              List.mem_of_cons_sublist hskip
            have hx_le_a : x <= a :=
              (List.pairwise_cons.mp hys_pairwise).1 x hx_mem_ys
            rcases lt_or_eq_of_le hx_le_a with hxa_lt | hxa_eq
            · exact le_of_lt (List.Lex.rel hxa_lt)
            · have hskip_a : List.Sublist (a :: xs) ys := by
                simpa [hxa_eq] using hskip
              have hxs_sub_ys : List.Sublist xs ys :=
                (List.sublist_cons_of_sublist a (List.Sublist.refl xs)).trans hskip_a
              have hle : a :: xs <= a :: ys :=
                List.cons_le_cons a (ih hxs_sub_ys hys_tail_pairwise)
              simpa [hxa_eq] using hle
          · have hle : a :: xs <= a :: ys :=
              List.cons_le_cons a (ih hxs_sub hys_tail_pairwise)
            simpa [hxa] using hle

theorem list_le_of_subperm_of_pairwise_desc
    {xs ys : List Nat}
    (hsubperm : List.Subperm xs ys)
    (hxs_pairwise : xs.Pairwise (fun x y : Nat => y <= x))
    (hys_pairwise : ys.Pairwise (fun x y : Nat => y <= x)) :
    xs <= ys := by
  exact list_le_of_sublist_of_pairwise_desc
    (List.sublist_of_subperm_of_sortedGE hsubperm
      hxs_pairwise.sortedGE hys_pairwise.sortedGE)
    hys_pairwise

theorem multiset_sort_le_list_of_le_pairwise_desc
    {s : Multiset Nat}
    {ys : List Nat}
    (hle : s <= (ys : Multiset Nat))
    (hys_pairwise : ys.Pairwise (fun x y : Nat => y <= x)) :
    Multiset.sort s (fun x y : Nat => y <= x) <= ys := by
  have hsubperm :
      List.Subperm (Multiset.sort s (fun x y : Nat => y <= x)) ys := by
    apply (Multiset.coe_le).mp
    simpa using hle
  exact list_le_of_subperm_of_pairwise_desc hsubperm
    (Multiset.pairwise_sort (s := s) (r := fun x y : Nat => y <= x))
    hys_pairwise

theorem list_le_of_forall₂_le
    {xs ys : List Nat}
    (h : List.Forall₂ (fun x y : Nat => x <= y) xs ys) :
    xs <= ys := by
  induction h with
  | nil => rfl
  | cons hxy _ ih =>
      rcases lt_or_eq_of_le hxy with hlt | heq
      · exact le_of_lt (List.Lex.rel hlt)
      · subst_vars
        exact List.cons_le_cons _ ih

theorem list_le_of_sublistForall₂_le_of_pairwise_desc
    {xs ys : List Nat}
    (h : List.SublistForall₂ (fun x y : Nat => x <= y) xs ys)
    (hys_pairwise : ys.Pairwise (fun x y : Nat => y <= x)) :
    xs <= ys := by
  obtain ⟨zs, hfor, hsub⟩ := (List.sublistForall₂_iff).mp h
  exact le_trans (list_le_of_forall₂_le hfor)
    (list_le_of_sublist_of_pairwise_desc hsub hys_pairwise)

theorem multiset_sort_map_le_of_coarsening_aux
    {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β]
    (wx : α -> Nat) (wy : β -> Nat) (f : α -> β) :
    forall n : Nat, forall sx : Multiset α, sx.card = n -> forall ty : Multiset β,
      sx.Nodup ->
      (forall a : α, a ∈ sx -> 0 < wx a) ->
      (forall a : α, a ∈ sx -> f a ∈ ty) ->
      (forall a : α, a ∈ sx -> wx a <= wy (f a)) ->
      (forall a a' : α, a ∈ sx -> a' ∈ sx -> a' ≠ a ->
        f a' = f a -> wy (f a) = wx a -> False) ->
      Multiset.sort (sx.map wx) (fun x y : Nat => y <= x) <=
        Multiset.sort (ty.map wy) (fun x y : Nat => y <= x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro sx hsx_card ty hnodup hpos hmem hle hunique
      by_cases hsx_zero : sx = 0
      · subst sx
        simp only [Multiset.map_zero, Multiset.sort_zero]
        cases Multiset.sort (ty.map wy) (fun x y : Nat => y <= x) with
        | nil => rfl
        | cons y ys => exact le_of_lt List.Lex.nil
      · obtain ⟨a, ha_sx, ha_max⟩ := Multiset.exists_max_image wx hsx_zero
        let b : β := f a
        have hb_ty : b ∈ ty := hmem a ha_sx
        by_cases htarget_strict : Exists fun c : β => c ∈ ty ∧ wx a < wy c
        · obtain ⟨c, hc_ty, hc_gt⟩ := htarget_strict
          apply le_of_lt
          refine list_lt_of_exists_mem_gt_all_of_pairwise_desc
            (Multiset.pairwise_sort (s := ty.map wy) (r := fun x y : Nat => y <= x)) ?_
          refine ⟨wy c, ?_, ?_⟩
          · exact (Multiset.mem_sort _).mpr (Multiset.mem_map.mpr ⟨c, hc_ty, rfl⟩)
          · intro x hx
            rw [Multiset.mem_sort] at hx
            rcases Multiset.mem_map.mp hx with ⟨a', ha'_sx, rfl⟩
            exact lt_of_le_of_lt (ha_max a' ha'_sx) hc_gt
        · have htarget_le : forall c : β, c ∈ ty -> wy c <= wx a := by
            intro c hc
            exact le_of_not_gt (by
              intro hgt
              exact htarget_strict ⟨c, hc, hgt⟩)
          have hb_eq : wy b = wx a := by
            exact le_antisymm (htarget_le b hb_ty) (hle a ha_sx)
          have hsx_erase_card_lt : (sx.erase a).card < n := by
            have hcard := Multiset.card_erase_add_one ha_sx
            omega
          have hrec :
              Multiset.sort ((sx.erase a).map wx) (fun x y : Nat => y <= x) <=
                Multiset.sort ((ty.erase b).map wy) (fun x y : Nat => y <= x) := by
            refine ih (sx.erase a).card hsx_erase_card_lt (sx.erase a) rfl (ty.erase b)
              (hnodup.erase a) ?_ ?_ ?_ ?_
            · intro c hc
              exact hpos c (Multiset.mem_of_mem_erase hc)
            · intro c hc
              have hc_sx : c ∈ sx := Multiset.mem_of_mem_erase hc
              have hfc_ty : f c ∈ ty := hmem c hc_sx
              have hc_ne_a : c ≠ a := by
                intro hca
                subst c
                exact hnodup.notMem_erase hc
              have hfc_ne_b : f c ≠ b := by
                intro hfc_eq
                exact hunique a c ha_sx hc_sx hc_ne_a hfc_eq hb_eq
              exact (Multiset.mem_erase_of_ne hfc_ne_b).2 hfc_ty
            · intro c hc
              exact hle c (Multiset.mem_of_mem_erase hc)
            · intro c d hc hd hdc hfd hEq
              exact hunique c d (Multiset.mem_of_mem_erase hc)
                (Multiset.mem_of_mem_erase hd) hdc hfd hEq
          have hsx_map_cons :
              wx a ::ₘ ((sx.erase a).map wx) = sx.map wx := by
            simpa using congrArg (Multiset.map wx) (Multiset.cons_erase ha_sx)
          have hty_map_cons :
              wy b ::ₘ ((ty.erase b).map wy) = ty.map wy := by
            simpa using congrArg (Multiset.map wy) (Multiset.cons_erase hb_ty)
          have hsx_sort :
              Multiset.sort (sx.map wx) (fun x y : Nat => y <= x) =
                wx a :: Multiset.sort ((sx.erase a).map wx) (fun x y : Nat => y <= x) := by
            rw [← hsx_map_cons]
            refine Multiset.sort_cons
              (a := wx a) (s := (sx.erase a).map wx)
              (r := fun x y : Nat => y <= x) ?_
            intro z hz
            rcases Multiset.mem_map.mp hz with ⟨c, hc_erase, rfl⟩
            exact ha_max c (Multiset.mem_of_mem_erase hc_erase)
          have hty_sort :
              Multiset.sort (ty.map wy) (fun x y : Nat => y <= x) =
                wy b :: Multiset.sort ((ty.erase b).map wy) (fun x y : Nat => y <= x) := by
            rw [← hty_map_cons]
            refine Multiset.sort_cons
              (a := wy b) (s := (ty.erase b).map wy)
              (r := fun x y : Nat => y <= x) ?_
            intro z hz
            rcases Multiset.mem_map.mp hz with ⟨c, hc_erase, rfl⟩
            simpa [hb_eq] using htarget_le c (Multiset.mem_of_mem_erase hc_erase)
          rw [hsx_sort, hty_sort, hb_eq]
          exact List.cons_le_cons (wx a) hrec

theorem multiset_sort_map_le_of_coarsening
    {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β]
    (wx : α -> Nat) (wy : β -> Nat) (f : α -> β)
    (sx : Multiset α) (ty : Multiset β)
    (hnodup : sx.Nodup)
    (hpos : forall a : α, a ∈ sx -> 0 < wx a)
    (hmem : forall a : α, a ∈ sx -> f a ∈ ty)
    (hle : forall a : α, a ∈ sx -> wx a <= wy (f a))
    (hunique : forall a a' : α, a ∈ sx -> a' ∈ sx -> a' ≠ a ->
      f a' = f a -> wy (f a) = wx a -> False) :
    Multiset.sort (sx.map wx) (fun x y : Nat => y <= x) <=
      Multiset.sort (ty.map wy) (fun x y : Nat => y <= x) := by
  exact multiset_sort_map_le_of_coarsening_aux wx wy f sx.card sx rfl ty
    hnodup hpos hmem hle hunique

theorem multiset_sort_map_lt_of_coarsening_aux
    {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β]
    (wx : α -> Nat) (wy : β -> Nat) (f : α -> β) :
    forall n : Nat, forall sx : Multiset α, sx.card = n -> forall ty : Multiset β,
      sx.Nodup ->
      (forall a : α, a ∈ sx -> 0 < wx a) ->
      (forall a : α, a ∈ sx -> f a ∈ ty) ->
      (forall a : α, a ∈ sx -> wx a <= wy (f a)) ->
      (forall a a' : α, a ∈ sx -> a' ∈ sx -> a' ≠ a ->
        f a' = f a -> wy (f a) = wx a -> False) ->
      (Exists fun a : α => a ∈ sx ∧ wx a < wy (f a)) ->
      Multiset.sort (sx.map wx) (fun x y : Nat => y <= x) <
        Multiset.sort (ty.map wy) (fun x y : Nat => y <= x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro sx hsx_card ty hnodup hpos hmem hle hunique hstrict
      by_cases hsx_zero : sx = 0
      · subst sx
        rcases hstrict with ⟨a, ha, _⟩
        cases ha
      · obtain ⟨a, ha_sx, ha_max⟩ := Multiset.exists_max_image wx hsx_zero
        let b : β := f a
        have hb_ty : b ∈ ty := hmem a ha_sx
        by_cases htarget_strict : Exists fun c : β => c ∈ ty ∧ wx a < wy c
        · obtain ⟨c, hc_ty, hc_gt⟩ := htarget_strict
          refine list_lt_of_exists_mem_gt_all_of_pairwise_desc
            (Multiset.pairwise_sort (s := ty.map wy) (r := fun x y : Nat => y <= x)) ?_
          refine ⟨wy c, ?_, ?_⟩
          · exact (Multiset.mem_sort _).mpr (Multiset.mem_map.mpr ⟨c, hc_ty, rfl⟩)
          · intro x hx
            rw [Multiset.mem_sort] at hx
            rcases Multiset.mem_map.mp hx with ⟨a', ha'_sx, rfl⟩
            exact lt_of_le_of_lt (ha_max a' ha'_sx) hc_gt
        · have htarget_le : forall c : β, c ∈ ty -> wy c <= wx a := by
            intro c hc
            exact le_of_not_gt (by
              intro hgt
              exact htarget_strict ⟨c, hc, hgt⟩)
          have hb_eq : wy b = wx a := by
            exact le_antisymm (htarget_le b hb_ty) (hle a ha_sx)
          obtain ⟨a0, ha0_sx, ha0_strict⟩ := hstrict
          have ha0_ne_a : a0 ≠ a := by
            intro h
            subst a0
            exact (not_lt_of_ge (htarget_le b hb_ty))
              (by simpa [b] using ha0_strict)
          have ha0_erase : a0 ∈ sx.erase a :=
            (Multiset.mem_erase_of_ne ha0_ne_a).2 ha0_sx
          have hsx_erase_card_lt : (sx.erase a).card < n := by
            have hcard := Multiset.card_erase_add_one ha_sx
            omega
          have hrec :
              Multiset.sort ((sx.erase a).map wx) (fun x y : Nat => y <= x) <
                Multiset.sort ((ty.erase b).map wy) (fun x y : Nat => y <= x) := by
            refine ih (sx.erase a).card hsx_erase_card_lt (sx.erase a) rfl (ty.erase b)
              (hnodup.erase a) ?_ ?_ ?_ ?_ ?_
            · intro c hc
              exact hpos c (Multiset.mem_of_mem_erase hc)
            · intro c hc
              have hc_sx : c ∈ sx := Multiset.mem_of_mem_erase hc
              have hfc_ty : f c ∈ ty := hmem c hc_sx
              have hc_ne_a : c ≠ a := by
                intro hca
                subst c
                exact hnodup.notMem_erase hc
              have hfc_ne_b : f c ≠ b := by
                intro hfc_eq
                exact hunique a c ha_sx hc_sx hc_ne_a hfc_eq hb_eq
              exact (Multiset.mem_erase_of_ne hfc_ne_b).2 hfc_ty
            · intro c hc
              exact hle c (Multiset.mem_of_mem_erase hc)
            · intro c d hc hd hdc hfd hEq
              exact hunique c d (Multiset.mem_of_mem_erase hc)
                (Multiset.mem_of_mem_erase hd) hdc hfd hEq
            · exact ⟨a0, ha0_erase, ha0_strict⟩
          have hsx_map_cons :
              wx a ::ₘ ((sx.erase a).map wx) = sx.map wx := by
            simpa using congrArg (Multiset.map wx) (Multiset.cons_erase ha_sx)
          have hty_map_cons :
              wy b ::ₘ ((ty.erase b).map wy) = ty.map wy := by
            simpa using congrArg (Multiset.map wy) (Multiset.cons_erase hb_ty)
          have hsx_sort :
              Multiset.sort (sx.map wx) (fun x y : Nat => y <= x) =
                wx a :: Multiset.sort ((sx.erase a).map wx) (fun x y : Nat => y <= x) := by
            rw [← hsx_map_cons]
            refine Multiset.sort_cons
              (a := wx a) (s := (sx.erase a).map wx)
              (r := fun x y : Nat => y <= x) ?_
            intro z hz
            rcases Multiset.mem_map.mp hz with ⟨c, hc_erase, rfl⟩
            exact ha_max c (Multiset.mem_of_mem_erase hc_erase)
          have hty_sort :
              Multiset.sort (ty.map wy) (fun x y : Nat => y <= x) =
                wy b :: Multiset.sort ((ty.erase b).map wy) (fun x y : Nat => y <= x) := by
            rw [← hty_map_cons]
            refine Multiset.sort_cons
              (a := wy b) (s := (ty.erase b).map wy)
              (r := fun x y : Nat => y <= x) ?_
            intro z hz
            rcases Multiset.mem_map.mp hz with ⟨c, hc_erase, rfl⟩
            simpa [hb_eq] using htarget_le c (Multiset.mem_of_mem_erase hc_erase)
          rw [hsx_sort, hty_sort, hb_eq]
          exact List.Lex.cons hrec

theorem multiset_sort_map_lt_of_coarsening
    {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β]
    (wx : α -> Nat) (wy : β -> Nat) (f : α -> β)
    (sx : Multiset α) (ty : Multiset β)
    (hnodup : sx.Nodup)
    (hpos : forall a : α, a ∈ sx -> 0 < wx a)
    (hmem : forall a : α, a ∈ sx -> f a ∈ ty)
    (hle : forall a : α, a ∈ sx -> wx a <= wy (f a))
    (hunique : forall a a' : α, a ∈ sx -> a' ∈ sx -> a' ≠ a ->
      f a' = f a -> wy (f a) = wx a -> False)
    (hstrict : Exists fun a : α => a ∈ sx ∧ wx a < wy (f a)) :
    Multiset.sort (sx.map wx) (fun x y : Nat => y <= x) <
      Multiset.sort (ty.map wy) (fun x y : Nat => y <= x) := by
  exact multiset_sort_map_lt_of_coarsening_aux wx wy f sx.card sx rfl ty
    hnodup hpos hmem hle hunique hstrict

theorem Triad.flapSizeTailWith_lt_of_exists_new_tail_entry_gt_all
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B : T.Flap}
    {B' : T'.Flap}
    (hgt :
      Exists fun n : Nat =>
        n ∈ T'.flapSizeTailWith B' ∧
          forall m : Nat, m ∈ T.flapSizeTailWith B -> m < n) :
    T.flapSizeTailWith B < T'.flapSizeTailWith B' := by
  exact list_lt_of_exists_mem_gt_all_of_pairwise_desc
    (T'.flapSizeTailWith_pairwise_desc B') hgt

theorem list_lt_sort_cons_erase_min_of_pairwise_desc
    {xs : List Nat}
    {d e e' : Nat}
    (hxs_pairwise : xs.Pairwise (fun x y : Nat => y <= x))
    (hd_mem : d ∈ xs)
    (hd_min : forall n : Nat, n ∈ xs -> d <= n)
    (he_mem : e ∈ xs)
    (he_lt : e < e') :
    xs <
      Multiset.sort (e' ::ₘ ((xs : Multiset Nat).erase d))
        (fun x y : Nat => y <= x) := by
  induction xs generalizing d e e' with
  | nil => cases hd_mem
  | cons a as ih =>
      by_cases he'_gt_a : a < e'
      · refine list_lt_of_exists_mem_gt_all_of_pairwise_desc
          (Multiset.pairwise_sort
            (s := e' ::ₘ (((a :: as : List Nat) : Multiset Nat).erase d))
            (r := fun x y : Nat => y <= x)) ?_
        refine ⟨e', ?_, ?_⟩
        · simp
        · intro x hx
          exact lt_of_le_of_lt
            (list_mem_le_head_of_pairwise_desc hxs_pairwise hx) he'_gt_a
      · have he'_le_a : e' <= a := le_of_not_gt he'_gt_a
        have hd_ne_a : d ≠ a := by
          intro hda
          have ha_le_e : a <= e := by
            simpa [hda] using hd_min e he_mem
          omega
        have ha_ne_d : a ≠ d := hd_ne_a.symm
        have he_ne_a : e ≠ a := by
          intro hea
          omega
        have hd_mem_as : d ∈ as := by
          cases hd_mem with
          | head => exact False.elim (hd_ne_a rfl)
          | tail => assumption
        have he_mem_as : e ∈ as := by
          cases he_mem with
          | head => exact False.elim (he_ne_a rfl)
          | tail => assumption
        have has_pairwise : as.Pairwise (fun x y : Nat => y <= x) :=
          (List.pairwise_cons.mp hxs_pairwise).2
        have hd_min_as : forall n : Nat, n ∈ as -> d <= n := by
          intro n hn
          exact hd_min n (List.mem_cons_of_mem a hn)
        have hih :
            as <
              Multiset.sort (e' ::ₘ ((as : Multiset Nat).erase d))
                (fun x y : Nat => y <= x) :=
          ih has_pairwise hd_mem_as hd_min_as he_mem_as he_lt
        have herase :
            (((a :: as : List Nat) : Multiset Nat).erase d) =
              a ::ₘ ((as : Multiset Nat).erase d) := by
          simpa using
            (Multiset.erase_cons_tail (s := (as : Multiset Nat)) ha_ne_d)
        have hforall :
            forall b : Nat,
              b ∈ e' ::ₘ ((as : Multiset Nat).erase d) -> b <= a := by
          intro b hb
          rcases Multiset.mem_cons.mp hb with rfl | hb_erase
          · exact he'_le_a
          · have hb_as_multiset : b ∈ (as : Multiset Nat) :=
              Multiset.mem_of_mem_erase hb_erase
            have hb_as : b ∈ as := by
              simpa using hb_as_multiset
            exact list_mem_le_head_of_pairwise_desc hxs_pairwise
              (List.mem_cons_of_mem a hb_as)
        have hsort :
            Multiset.sort
                (e' ::ₘ (((a :: as : List Nat) : Multiset Nat).erase d))
                (fun x y : Nat => y <= x) =
              a ::
                Multiset.sort (e' ::ₘ ((as : Multiset Nat).erase d))
                  (fun x y : Nat => y <= x) := by
          rw [herase, Multiset.cons_swap e' a]
          exact Multiset.sort_cons
            (a := a) (s := e' ::ₘ ((as : Multiset Nat).erase d))
            (r := fun x y : Nat => y <= x) hforall
        rw [hsort]
        exact List.Lex.cons hih

theorem list_lt_sort_cons_erase_min_erase_of_pairwise_desc
    {xs : List Nat}
    {d e e' : Nat}
    (hxs_pairwise : xs.Pairwise (fun x y : Nat => y <= x))
    (hd_mem : d ∈ xs)
    (hd_min : forall n : Nat, n ∈ xs -> d <= n)
    (he_mem_erase : e ∈ ((xs : Multiset Nat).erase d))
    (he_lt : e < e') :
    xs <
      Multiset.sort (e' ::ₘ (((xs : Multiset Nat).erase d).erase e))
        (fun x y : Nat => y <= x) := by
  induction xs generalizing d e e' with
  | nil => cases hd_mem
  | cons a as ih =>
      by_cases he'_gt_a : a < e'
      · refine list_lt_of_exists_mem_gt_all_of_pairwise_desc
          (Multiset.pairwise_sort
            (s := e' ::ₘ ((((a :: as : List Nat) : Multiset Nat).erase d).erase e))
            (r := fun x y : Nat => y <= x)) ?_
        refine ⟨e', ?_, ?_⟩
        · simp
        · intro x hx
          exact lt_of_le_of_lt
            (list_mem_le_head_of_pairwise_desc hxs_pairwise hx) he'_gt_a
      · have he'_le_a : e' <= a := le_of_not_gt he'_gt_a
        have he_mem : e ∈ a :: as :=
          Multiset.mem_of_mem_erase he_mem_erase
        have hd_ne_a : d ≠ a := by
          intro hda
          have ha_le_e : a <= e := by
            simpa [hda] using hd_min e he_mem
          omega
        have ha_ne_d : a ≠ d := hd_ne_a.symm
        have he_ne_a : e ≠ a := by
          intro hea
          omega
        have ha_ne_e : a ≠ e := he_ne_a.symm
        have hd_mem_as : d ∈ as := by
          cases hd_mem with
          | head => exact False.elim (hd_ne_a rfl)
          | tail => assumption
        have has_pairwise : as.Pairwise (fun x y : Nat => y <= x) :=
          (List.pairwise_cons.mp hxs_pairwise).2
        have hd_min_as : forall n : Nat, n ∈ as -> d <= n := by
          intro n hn
          exact hd_min n (List.mem_cons_of_mem a hn)
        have herase_d :
            (((a :: as : List Nat) : Multiset Nat).erase d) =
              a ::ₘ ((as : Multiset Nat).erase d) := by
          simpa using
            (Multiset.erase_cons_tail (s := (as : Multiset Nat)) ha_ne_d)
        have he_mem_erase_as : e ∈ ((as : Multiset Nat).erase d) := by
          rw [herase_d] at he_mem_erase
          rcases Multiset.mem_cons.mp he_mem_erase with he_eq_a | he_tail
          · exact False.elim (he_ne_a he_eq_a)
          · exact he_tail
        have hih :
            as <
              Multiset.sort (e' ::ₘ (((as : Multiset Nat).erase d).erase e))
                (fun x y : Nat => y <= x) :=
          ih has_pairwise hd_mem_as hd_min_as he_mem_erase_as he_lt
        have herase :
            ((((a :: as : List Nat) : Multiset Nat).erase d).erase e) =
              a ::ₘ (((as : Multiset Nat).erase d).erase e) := by
          rw [herase_d]
          simpa using
            (Multiset.erase_cons_tail
              (s := ((as : Multiset Nat).erase d)) ha_ne_e)
        have hforall :
            forall b : Nat,
              b ∈ e' ::ₘ (((as : Multiset Nat).erase d).erase e) -> b <= a := by
          intro b hb
          rcases Multiset.mem_cons.mp hb with rfl | hb_erase
          · exact he'_le_a
          · have hb_as_multiset : b ∈ (as : Multiset Nat) :=
              Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hb_erase)
            have hb_as : b ∈ as := by
              simpa using hb_as_multiset
            exact list_mem_le_head_of_pairwise_desc hxs_pairwise
              (List.mem_cons_of_mem a hb_as)
        have hsort :
            Multiset.sort
                (e' ::ₘ ((((a :: as : List Nat) : Multiset Nat).erase d).erase e))
                (fun x y : Nat => y <= x) =
              a ::
                Multiset.sort
                  (e' ::ₘ (((as : Multiset Nat).erase d).erase e))
                  (fun x y : Nat => y <= x) := by
          rw [herase, Multiset.cons_swap e' a]
          exact Multiset.sort_cons
            (a := a) (s := e' ::ₘ (((as : Multiset Nat).erase d).erase e))
            (r := fun x y : Nat => y <= x) hforall
        rw [hsort]
        exact List.Lex.cons hih

theorem Triad.flapSizeTailWith_lt_sort_cons_erase_min
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {B D E : T.Flap}
    (hDB : D ≠ B)
    (hEB : E ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    {e' : Nat}
    (hE_lt : (T.flapVertexSet E).ncard < e') :
    T.flapSizeTailWith B <
      Multiset.sort
        (e' ::ₘ ((T.flapSizeTailWith B : Multiset Nat).erase
          (T.flapVertexSet D).ncard))
        (fun x y : Nat => y <= x) := by
  exact list_lt_sort_cons_erase_min_of_pairwise_desc
    (T.flapSizeTailWith_pairwise_desc B)
    (T.mem_flapSizeTailWith_of_ne hDB)
    (by
      intro n hn
      exact T.flapSizeTailWith_min_of_other_flap_ncard_minimal hD_min hn)
    (T.mem_flapSizeTailWith_of_ne hEB)
    hE_lt

theorem Triad.flapSizeTailWith_lt_sort_cons_erase_min_erase
    [Fintype V]
    {feet : Fin 3 -> V}
    (T : Triad G feet)
    {B D E : T.Flap}
    (hDB : D ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    (hE_mem_after_erase :
      (T.flapVertexSet E).ncard ∈
        ((T.flapSizeTailWith B : Multiset Nat).erase
          (T.flapVertexSet D).ncard))
    {e' : Nat}
    (hE_lt : (T.flapVertexSet E).ncard < e') :
    T.flapSizeTailWith B <
      Multiset.sort
        (e' ::ₘ (((T.flapSizeTailWith B : Multiset Nat).erase
          (T.flapVertexSet D).ncard).erase (T.flapVertexSet E).ncard))
        (fun x y : Nat => y <= x) := by
  exact list_lt_sort_cons_erase_min_erase_of_pairwise_desc
    (T.flapSizeTailWith_pairwise_desc B)
    (T.mem_flapSizeTailWith_of_ne hDB)
    (by
      intro n hn
      exact T.flapSizeTailWith_min_of_other_flap_ncard_minimal hD_min hn)
    hE_mem_after_erase
    hE_lt

theorem Triad.flapSizeTailWith_lt_of_sort_cons_erase_min_le
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B D E : T.Flap}
    {B' : T'.Flap}
    (hDB : D ≠ B)
    (hEB : E ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    {e' : Nat}
    (hE_lt : (T.flapVertexSet E).ncard < e')
    (hreplacement_le :
      Multiset.sort
          (e' ::ₘ ((T.flapSizeTailWith B : Multiset Nat).erase
            (T.flapVertexSet D).ncard))
          (fun x y : Nat => y <= x) <=
        T'.flapSizeTailWith B') :
    T.flapSizeTailWith B < T'.flapSizeTailWith B' := by
  exact lt_of_lt_of_le
    (T.flapSizeTailWith_lt_sort_cons_erase_min hDB hEB hD_min hE_lt)
    hreplacement_le

theorem Triad.flapSizeTailWith_lt_of_sort_cons_erase_min_multiset_le
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B D E : T.Flap}
    {B' : T'.Flap}
    (hDB : D ≠ B)
    (hEB : E ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    {e' : Nat}
    (hE_lt : (T.flapVertexSet E).ncard < e')
    (hreplacement_le :
      e' ::ₘ ((T.flapSizeTailWith B : Multiset Nat).erase
        (T.flapVertexSet D).ncard) <=
        (T'.flapSizeTailWith B' : Multiset Nat)) :
    T.flapSizeTailWith B < T'.flapSizeTailWith B' := by
  exact T.flapSizeTailWith_lt_of_sort_cons_erase_min_le
    (T' := T') (B' := B') hDB hEB hD_min hE_lt
    (multiset_sort_le_list_of_le_pairwise_desc hreplacement_le
      (T'.flapSizeTailWith_pairwise_desc B'))

theorem Triad.flapSizeTailWith_lt_of_sort_cons_erase_min_sublistForall₂
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B D E : T.Flap}
    {B' : T'.Flap}
    (hDB : D ≠ B)
    (hEB : E ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    {e' : Nat}
    (hE_lt : (T.flapVertexSet E).ncard < e')
    (hreplacement_le :
      List.SublistForall₂ (fun x y : Nat => x <= y)
        (Multiset.sort
          (e' ::ₘ ((T.flapSizeTailWith B : Multiset Nat).erase
            (T.flapVertexSet D).ncard))
          (fun x y : Nat => y <= x))
        (T'.flapSizeTailWith B')) :
    T.flapSizeTailWith B < T'.flapSizeTailWith B' := by
  exact lt_of_lt_of_le
    (T.flapSizeTailWith_lt_sort_cons_erase_min hDB hEB hD_min hE_lt)
    (list_le_of_sublistForall₂_le_of_pairwise_desc hreplacement_le
      (T'.flapSizeTailWith_pairwise_desc B'))

theorem Triad.flapSizeTailWith_lt_of_sort_cons_erase_min_erase_sublistForall₂
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B D E : T.Flap}
    {B' : T'.Flap}
    (hDB : D ≠ B)
    (hD_min :
      forall F : T.Flap, F ≠ B ->
        (T.flapVertexSet D).ncard <= (T.flapVertexSet F).ncard)
    (hE_mem_after_erase :
      (T.flapVertexSet E).ncard ∈
        ((T.flapSizeTailWith B : Multiset Nat).erase
          (T.flapVertexSet D).ncard))
    {e' : Nat}
    (hE_lt : (T.flapVertexSet E).ncard < e')
    (hreplacement_le :
      List.SublistForall₂ (fun x y : Nat => x <= y)
        (Multiset.sort
          (e' ::ₘ (((T.flapSizeTailWith B : Multiset Nat).erase
            (T.flapVertexSet D).ncard).erase (T.flapVertexSet E).ncard))
          (fun x y : Nat => y <= x))
        (T'.flapSizeTailWith B')) :
    T.flapSizeTailWith B < T'.flapSizeTailWith B' := by
  exact lt_of_lt_of_le
    (T.flapSizeTailWith_lt_sort_cons_erase_min_erase hDB hD_min
      hE_mem_after_erase hE_lt)
    (list_le_of_sublistForall₂_le_of_pairwise_desc hreplacement_le
      (T'.flapSizeTailWith_pairwise_desc B'))

theorem Triad.flapSizeProfileWith_lt_of_distinguished_ncard_lt
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B : T.Flap}
    {B' : T'.Flap}
    (h :
      (T.flapVertexSet B).ncard < (T'.flapVertexSet B').ncard) :
    T.flapSizeProfileWith B < T'.flapSizeProfileWith B' := by
  change List.Lex (fun a b : Nat => a < b)
    (T.flapSizeProfileWith B) (T'.flapSizeProfileWith B')
  simp only [Triad.flapSizeProfileWith]
  exact List.Lex.rel h

theorem Triad.flapSizeProfileWith_lt_of_distinguished_flap_ssubset
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B : T.Flap}
    {B' : T'.Flap}
    (hsubset : T.flapVertexSet B ⊂ T'.flapVertexSet B') :
    T.flapSizeProfileWith B < T'.flapSizeProfileWith B' := by
  exact Triad.flapSizeProfileWith_lt_of_distinguished_ncard_lt
    (G := G) (Set.ncard_lt_ncard hsubset)

theorem Triad.distinguished_ncard_le_of_flapSizeProfileWith_le
    [Fintype V]
    {feet : Fin 3 -> V}
    {T T' : Triad G feet}
    {B : T.Flap}
    {B' : T'.Flap}
    (hprofile :
      T'.flapSizeProfileWith B' <= T.flapSizeProfileWith B) :
    (T'.flapVertexSet B').ncard <= (T.flapVertexSet B).ncard := by
  rw [le_iff_lt_or_eq] at hprofile
  rcases hprofile with hlt | heq
  · have hhead :=
      List.head_le_of_lt (a' := (T'.flapVertexSet B').ncard)
        (a := (T.flapVertexSet B).ncard) hlt
    simpa [Triad.flapSizeProfileWith] using hhead
  · have hhead := congrArg (fun l : List Nat => l.head!) heq
    simpa [Triad.flapSizeProfileWith] using hhead.le

def RST31LexLarger (xs ys : List Nat) : Prop :=
  ys < xs


end Schematic.Math.GraphTheory
