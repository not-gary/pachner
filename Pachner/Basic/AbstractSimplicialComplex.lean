/-
Copyright (c) 2025 Garett Cunningham, Daniel Zach, Stefan Friedl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Garett Cunningham, Daniel Zach, Stefan Friedl
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

section AbstractSimplicialComplex
variable (E : Type _)

@[ext]
structure AbstractSimplicialComplex where
  faces : Set (Finset E)
  empty_notMem : ∅ ∉ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ≠ ∅ → t ∈ faces

variable
  {E : Type _}
  {X Y : AbstractSimplicialComplex E} {s t : Finset E} {x : E}

namespace AbstractSimplicialComplex

instance : Membership (Finset E) (AbstractSimplicialComplex E) :=
  ⟨fun K s => s ∈ K.faces⟩

@[simp]
def ofErase
    (faces : Set (Finset E))
    (down_closed : ∀ s ∈ faces, ∀ t ⊆ s, t ∈ faces)
  : AbstractSimplicialComplex E where
    faces := faces \ {∅}
    empty_notMem h := h.2 (Set.mem_singleton _)
    down_closed hs hts ht := ⟨down_closed _ hs.1 _ hts, ht⟩

@[simp]
def ofSubcomplex
    (K : AbstractSimplicialComplex E)
    (faces : Set (Finset E))
    (subset : faces ⊆ K.faces)
    (down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces)
  : AbstractSimplicialComplex E :=
    { faces
      empty_notMem := fun h => K.empty_notMem (subset h)
      down_closed := fun hs hts _ => down_closed hs hts }

@[simp]
def ofGeometric {𝕜 E} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (K : Geometry.SimplicialComplex 𝕜 E)
  : AbstractSimplicialComplex E := ⟨K.faces, K.empty_notMem, K.down_closed⟩

def vertices (K : AbstractSimplicialComplex E) : Set E :=
  { x | {x} ∈ K.faces }

theorem mem_vertices : x ∈ X.vertices ↔ {x} ∈ X.faces := Iff.rfl

theorem vertices_eq : X.vertices = ⋃ k ∈ X.faces, (k : Set E) := by
  ext x
  refine ⟨fun h => Set.mem_biUnion h <| Finset.mem_coe.2 <| Finset.mem_singleton_self x, fun h => ?_⟩
  obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.1 h
  exact X.down_closed hs (Finset.singleton_subset_iff.2 <| Finset.mem_coe.1 hx) (Finset.singleton_ne_empty _)

def facets (K : AbstractSimplicialComplex E) : Set (Finset E) :=
  { s ∈ K.faces | ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t }

theorem mem_facets : s ∈ X.facets ↔ s ∈ X.faces ∧ ∀ t ∈ X.faces, s ⊆ t → s = t :=
  Set.mem_sep_iff

theorem facets_subset : X.facets ⊆ X.faces := fun _ hs => hs.1

theorem not_facet_iff_subface (s_in_X : s ∈ X.faces) : s ∉ X.facets ↔ ∃ t, t ∈ X.faces ∧ s ⊂ t := by
  refine ⟨fun hs' : ¬(_ ∧ _) => ?_, ?_⟩
  · push_neg at hs'
    obtain ⟨t, ht⟩ := hs' s_in_X
    exact ⟨t, ht.1, ⟨ht.2.1, fun hts => ht.2.2 (Finset.Subset.antisymm ht.2.1 hts)⟩⟩
  · rintro ⟨t, ht⟩ ⟨hs, hs'⟩
    have := hs' ht.1 ht.2.1
    rw [this] at ht
    exact ht.2.2 (Finset.Subset.refl t)

instance : Min (AbstractSimplicialComplex E) :=
  ⟨fun K L =>
    { faces := K.faces ∩ L.faces
      empty_notMem := fun h => K.empty_notMem (Set.inter_subset_left h)
      down_closed := fun hs hst ht => ⟨K.down_closed hs.1 hst ht, L.down_closed hs.2 hst ht⟩ }⟩

instance : SemilatticeInf (AbstractSimplicialComplex E) :=
  { PartialOrder.lift faces (fun _ _ => AbstractSimplicialComplex.ext) with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ hs => hs.1
    inf_le_right := fun _ _ _ hs => hs.2
    le_inf := fun _ _ _ hKL hKM _ hs => ⟨hKL hs, hKM hs⟩ }

instance hasBot : Bot (AbstractSimplicialComplex E) :=
  ⟨{  faces := ∅
      empty_notMem := Set.notMem_empty ∅
      down_closed := fun hs => (Set.notMem_empty _ hs).elim }⟩

instance : OrderBot (AbstractSimplicialComplex E) :=
  { AbstractSimplicialComplex.hasBot with bot_le := fun _ => Set.empty_subset _ }

instance : Inhabited (AbstractSimplicialComplex E) :=
  ⟨⊥⟩

theorem faces_bot : (⊥ : AbstractSimplicialComplex E).faces = ∅ := rfl

theorem facets_bot : (⊥ : AbstractSimplicialComplex E).facets = ∅ :=
by
  apply Set.eq_empty_of_subset_empty
  apply facets_subset

end AbstractSimplicialComplex

@[simp]
def Geometry.SimplicialComplex.ofAbstract {𝕜 E}
    [Ring 𝕜] [PartialOrder 𝕜]
    [AddCommGroup E] [Module 𝕜 E]
    (K : AbstractSimplicialComplex E)
    (indep : ∀ {s}, s ∈ K.faces → AffineIndependent 𝕜 ((↑) : s → E))
    (inter_subset_convexHull : ∀ {s t}, s ∈ K.faces → t ∈ K.faces →
        convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E))
  : Geometry.SimplicialComplex 𝕜 E :=
    ⟨K.faces, K.empty_notMem, indep, K.down_closed, inter_subset_convexHull⟩

theorem ofAbstract_ofGeometric_id {𝕜 E}
    [Ring 𝕜] [PartialOrder 𝕜]
    [AddCommGroup E] [Module 𝕜 E]
    (K : AbstractSimplicialComplex E)
    (indep : ∀ {s}, s ∈ K.faces → AffineIndependent 𝕜 ((↑) : s → E))
    (inter_subset_convexHull : ∀ {s t}, s ∈ K.faces → t ∈ K.faces →
        convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E))
  : AbstractSimplicialComplex.ofGeometric (Geometry.SimplicialComplex.ofAbstract K indep inter_subset_convexHull) = K :=
by
  simp only [AbstractSimplicialComplex.ofGeometric, Geometry.SimplicialComplex.ofAbstract]

theorem ofGeometric_ofAbstract_id {𝕜 E}
    [Ring 𝕜] [PartialOrder 𝕜]
    [AddCommGroup E] [Module 𝕜 E]
    (K : Geometry.SimplicialComplex 𝕜 E)
  : Geometry.SimplicialComplex.ofAbstract (AbstractSimplicialComplex.ofGeometric K) K.indep K.inter_subset_convexHull = K :=
by
  simp only [Geometry.SimplicialComplex.ofAbstract, AbstractSimplicialComplex.ofGeometric]

theorem face_nonempty : s ∈ X.faces → s ≠ ∅ := by
  contrapose
  rw [ne_eq, not_not]
  intro s_empty
  rw [s_empty]
  apply X.empty_notMem

theorem vertices_setOf : X.vertices = {x : E | ∃ s ∈ X.faces, x ∈ s} := by
  simp only [Set.ext_iff, Set.mem_setOf]
  intros v
  constructor
  { intros v_in_X
    use {v}
    constructor
    assumption
    rw [Finset.mem_singleton] }
  { intros v_in_s
    choose s s_in_X v_in_s using v_in_s
    have v_set_in_s : {v} ∈ X.faces :=
    by
      apply X.down_closed s_in_X
      rw [Finset.singleton_subset_iff]
      assumption
      simp only [ne_eq, Finset.singleton_ne_empty, not_false_eq_true]
    assumption }

instance vertices.Finite [DecidableEq E]
    (X : AbstractSimplicialComplex E) [Finite X.faces]
  : Finite X.vertices :=
by
  rw [AbstractSimplicialComplex.vertices_eq]
  rw [Set.biUnion_eq_iUnion]
  apply Set.finite_iUnion
  intros s_in_X
  simp only [Finset.finite_toSet]

theorem face_subset_vertices : s ∈ X.faces → ↑s ⊆ X.vertices := by
  intro s_in_X
  rw [vertices_setOf, Set.subset_def]
  intro x x_in_s
  rw [Set.mem_setOf]
  use s; constructor <;> assumption

instance vertices.FintypeConverse [DecidableEq E]
    (X : AbstractSimplicialComplex E) [X_dec : DecidablePred fun s => s ∈ X.faces]
  : Fintype X.vertices → Fintype X.faces :=
by
  intro fin_vert_X
  apply Set.fintypeSubset ↑(Finset.powerset (@Set.toFinset _ (X.vertices) fin_vert_X))
  rw [Set.subset_def]
  intro s s_in_X
  rw [Finset.mem_coe, Finset.mem_powerset, Set.subset_toFinset]
  apply face_subset_vertices
  assumption

instance vertices.Fintype [DecidableEq E]
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
  : Fintype X.vertices :=
by
  rw [AbstractSimplicialComplex.vertices_eq, Set.biUnion_eq_iUnion]
  apply Set.fintypeiUnion

theorem vertex_if_mem_face
    (s_in_X : s ∈ X.faces)
    (x_in_s : x ∈ s)
  : x ∈ X.vertices :=
by
  rw [vertices_setOf, Set.mem_setOf]
  use s

theorem vertex_iff_in_face : x ∈ X.vertices ↔ ∃ s ∈ X.faces, x ∈ s := by rw [vertices_setOf, Set.mem_setOf]

theorem vertices_bot : (⊥ : AbstractSimplicialComplex E).vertices = ∅ :=
by
  rw [vertices_setOf, Set.eq_empty_iff_forall_notMem]
  intro x
  simp only [Set.mem_setOf, not_exists, Set.mem_singleton_iff]
  intro s
  rw [not_and]
  intro s_empty
  rw [AbstractSimplicialComplex.faces_bot] at s_empty
  contradiction

theorem vertices_congr : X = Y → X.vertices = Y.vertices := by
  intro X_eq_Y
  simp only [vertices_setOf, X_eq_Y]

@[simp]
def Simplex
    (V : Finset E)
  : AbstractSimplicialComplex E :=
AbstractSimplicialComplex.mk
  (V.powerset.toSet \ {∅})
  (by
    rw [Set.mem_diff, not_and]
    intros empty_in_power
    tauto)
  (by
    intros s t s_face t_sset_s t_nonempty
    rw [Set.mem_diff] at ⊢ s_face
    choose s_in_power s_nin_empty using s_face
    constructor

    rw [Finset.mem_coe, Finset.mem_powerset] at ⊢ s_in_power
    transitivity s <;> assumption

    rw [Set.mem_singleton_iff]
    assumption)

instance Simplex.Finite (s : Finset E) : Finite (Simplex s).faces :=
by
  simp only [Simplex, Finite.Set.finite_diff]

instance Simplex.Fintype [DecidableEq E] (s : Finset E) : Fintype (Simplex s).faces :=
by
  simp only [Simplex]
  apply Set.fintypeDiff

theorem simplex_vertices
    (s : Finset E)
  : (Simplex s).vertices = s :=
by
  rw [vertices_setOf]
  simp only [Set.ext_iff, Set.mem_setOf, Simplex, Set.mem_singleton_iff]
  intro y
  constructor
  intro y_in_union
  choose t t_in_simplex y_in_t using y_in_union
  simp only [Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_iff] at t_in_simplex
  choose t_in_simplex t_nonempty using t_in_simplex
  specialize t_in_simplex y_in_t
  rw [Finset.mem_coe]
  assumption
  intro y_in_s
  use s; constructor
  rw [Set.mem_diff, Finset.mem_coe]
  constructor
  apply Finset.mem_powerset_self
  simp only [Set.mem_singleton_iff]
  simp only[Finset.eq_empty_iff_forall_notMem, not_forall, not_not]
  rw [Finset.mem_coe] at y_in_s
  use y
  assumption

section Subcomplex

def IsSubcomplex
    (X Y : AbstractSimplicialComplex E)
  : Prop :=
    X.faces ⊆ Y.faces

@[reducible]
instance AbstractSimplicialComplex.instHasSubset : HasSubset (AbstractSimplicialComplex E) :=
  ⟨IsSubcomplex⟩

theorem isSubcomplex_vertices
    (Y_subcomp_X : Y ⊆ X)
  : ∀ x : E, x ∈ Y.vertices → x ∈ X.vertices :=
by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def] at Y_subcomp_X
  intro y y_in_vert_Y
  simp only [AbstractSimplicialComplex.vertices_eq, Set.mem_iUnion] at y_in_vert_Y ⊢
  choose s Hs y_in_s using y_in_vert_Y
  specialize Y_subcomp_X s Hs
  use s

theorem isSubcomplex_vertices_subset
    (Y_subcomp_X : Y ⊆ X)
  : Y.vertices ⊆ X.vertices := by
  simp only [Set.subset_def]
  apply isSubcomplex_vertices Y_subcomp_X

def IsFace
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
  : Prop :=
    Simplex s ⊆ X

theorem face_iff_simplex_subcomplex [Nonempty s] : s ∈ X.faces ↔ Simplex s ⊆ X := by
  constructor
  intro s_in_X_simpl
  simp only [IsSubcomplex, Simplex, AbstractSimplicialComplex.instHasSubset]
  rw [Set.subset_def]
  intro x x_in_s_power
  rw [Set.mem_diff, Finset.mem_coe, Finset.mem_powerset] at x_in_s_power
  choose x_sset_s x_nonempty using x_in_s_power
  apply X.down_closed s_in_X_simpl
  assumption
  rw [Set.mem_singleton_iff] at x_nonempty
  assumption
  intro s_simpl_X
  simp only [IsSubcomplex, Simplex, AbstractSimplicialComplex.instHasSubset] at s_simpl_X
  rw [Set.subset_def] at s_simpl_X
  specialize s_simpl_X s
  rw [Set.mem_diff, Finset.mem_coe] at s_simpl_X
  specialize s_simpl_X
    (by
      constructor
      apply Finset.mem_powerset_self s
      simp only [Set.mem_singleton_iff, ← Finset.nonempty_iff_ne_empty, ← Finset.nonempty_coe_sort]
      assumption)
  assumption

theorem isSubcomplex_face_imp_face : s ∈ X.faces → X ⊆ Y → s ∈ Y.faces := by
  intro s_in_X X_sub_Y
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def] at X_sub_Y
  specialize X_sub_Y s s_in_X
  assumption

end Subcomplex
