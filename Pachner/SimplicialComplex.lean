import Mathlib.Tactic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

open scoped BigOperators

section AbstractSimplicialComplex

variable (E : Type*)

@[ext]
structure AbstractSimplicialComplex where
  faces : Set (Finset E)
  empty_notMem : ∅ ∉ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ≠ ∅ → t ∈ faces

namespace AbstractSimplicialComplex
variable {K : AbstractSimplicialComplex E} {s t : Finset E} {x : E}

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

def vertices (K : AbstractSimplicialComplex E) : Set E :=
  { x | {x} ∈ K.faces }

theorem mem_vertices : x ∈ K.vertices ↔ {x} ∈ K.faces := Iff.rfl

theorem vertices_eq : K.vertices = ⋃ k ∈ K.faces, (k : Set E) := by
  ext x
  refine ⟨fun h => Set.mem_biUnion h <| Finset.mem_coe.2 <| Finset.mem_singleton_self x, fun h => ?_⟩
  obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.1 h
  exact K.down_closed hs (Finset.singleton_subset_iff.2 <| Finset.mem_coe.1 hx) (Finset.singleton_ne_empty _)

def facets (K : AbstractSimplicialComplex E) : Set (Finset E) :=
  { s ∈ K.faces | ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t }

theorem mem_facets : s ∈ K.facets ↔ s ∈ K.faces ∧ ∀ t ∈ K.faces, s ⊆ t → s = t :=
  Set.mem_sep_iff

theorem facets_subset : K.facets ⊆ K.faces := fun _ hs => hs.1

theorem not_facet_iff_subface (hs : s ∈ K.faces) : s ∉ K.facets ↔ ∃ t, t ∈ K.faces ∧ s ⊂ t := by
  refine ⟨fun hs' : ¬(_ ∧ _) => ?_, ?_⟩
  · push_neg at hs'
    obtain ⟨t, ht⟩ := hs' hs
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
  { AbstractSimplicialComplex.hasBot E with bot_le := fun _ => Set.empty_subset _ }

instance : Inhabited (AbstractSimplicialComplex E) :=
  ⟨⊥⟩

theorem faces_bot : (⊥ : AbstractSimplicialComplex E).faces = ∅ := rfl

theorem facets_bot : (⊥ : AbstractSimplicialComplex E).facets = ∅ :=
by
  apply Set.eq_empty_of_subset_empty
  apply facets_subset

end AbstractSimplicialComplex

variable {E : Type*}

theorem face_nonempty
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
  : s ∈ X.faces → s ≠ ∅ :=
by
  contrapose
  rw [ne_eq, not_not]
  intro s_empty
  rw [s_empty]
  apply X.empty_notMem

theorem vertices_setOf (X : AbstractSimplicialComplex E) :
    X.vertices = {x : E | ∃ s ∈ X.faces, x ∈ s} :=
by
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

theorem simplex_subset_vertices
    (X : AbstractSimplicialComplex E) (s : Finset E) :
      s ∈ X.faces → ↑s ⊆ X.vertices :=
by
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
  apply simplex_subset_vertices
  assumption

instance vertices.Fintype [DecidableEq E]
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
  : Fintype X.vertices :=
by
  rw [AbstractSimplicialComplex.vertices_eq, Set.biUnion_eq_iUnion]
  apply Set.fintypeiUnion

theorem simplex_mem_is_vertex
    (X : AbstractSimplicialComplex E)
    (s : Finset E) (x : E)
    (s_in_X : s ∈ X.faces)
    (x_in_s : x ∈ s)
  : x ∈ X.vertices :=
by
  rw [vertices_setOf, Set.mem_setOf]
  use s

theorem vertex_iff_in_simplex
    (X : AbstractSimplicialComplex E) (x : E)
  : x ∈ X.vertices ↔ ∃ s ∈ X.faces, x ∈ s := by rw [vertices_setOf, Set.mem_setOf]

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

theorem vertices_congr
    (X Y : AbstractSimplicialComplex E)
  : X.faces = Y.faces → X.vertices = Y.vertices :=
by
  intro X_eq_Y
  simp only [vertices_setOf, X_eq_Y]

-- The simplex generated by a finset
@[simp]
def simplex
    (V : Finset E)
  : AbstractSimplicialComplex E :=
AbstractSimplicialComplex.mk
  (V.powerset.toSet \ {∅})
  (by
    rw [Set.mem_diff, not_and]
    intros empty_in_power
    tauto)
  (by
    intros s t s_simplex t_sset_s t_nonempty
    rw [Set.mem_diff] at ⊢ s_simplex
    choose s_in_power s_nin_empty using s_simplex
    constructor

    rw [Finset.mem_coe, Finset.mem_powerset] at ⊢ s_in_power
    transitivity s <;> assumption

    rw [Set.mem_singleton_iff]
    assumption)

instance simplex.Finite (s : Finset E) : Finite (@simplex E s).faces :=
by
  simp only [simplex, Finite.Set.finite_diff]

theorem simplex_vertices
    (s : Finset E)
  : (@simplex E s).vertices = s :=
by
  rw [vertices_setOf]
  simp only [Set.ext_iff, Set.mem_setOf, simplex, Set.mem_singleton_iff]
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

-- #print stdSimplex
-- The standard n-simplex is generated by {0,...,n}
-- @[simp]
-- def stdSimplex (n : ℕ) : SimplicialComplex ℕ :=
--   simplex (Finset.range (n + 1))

/-
# Dimension of simplices and simplicial complexes
-/
-- The dimension of a simplex is just its cardinality - 1.
@[simp]
def face_dim (s : Finset E) : ℤ :=
  Finset.card s - 1

@[simp]
def IsKSimplex (s : Finset E) (k : ℕ) :=
  face_dim s = k

-- -1
-- A simplicial complex has dimension n
-- if n is the maximal dimension of all simplices.
@[simp]
def HasDimensionLeq
    (X : AbstractSimplicialComplex E) (n : ℕ) :=
  ∀ s ∈ X.faces, face_dim s ≤ n

@[simp]
def HasDimensionGeq
    (X : AbstractSimplicialComplex E) (n : ℕ) :=
  ∃ s ∈ X.faces, face_dim s ≥ n

@[simp]
def HasDimension
    (X : AbstractSimplicialComplex E) (n : ℕ) :=
  HasDimensionLeq X n ∧ HasDimensionGeq X n

theorem dim_geq_zero_iff_nonempty
    (s : Finset E)
  : 0 ≤ face_dim s ↔ s ≠ ∅ :=
by
  unfold face_dim
  rw [Ne, ← Finset.card_eq_zero]
  constructor
  contrapose
  simp only [Classical.not_not]
  intro s_card_zero
  rw [s_card_zero]
  omega
  intro s_card_ne_zero
  have s_card_pos : s.card > 0 := by omega
  linarith

theorem dim_neg_one_iff_empty
    (s : Finset E)
  : face_dim s = -1 ↔ s = ∅ :=
by
  unfold face_dim
  rw [← Finset.card_eq_zero]
  constructor
  intro s_card_neg_one
  simp only [sub_eq_neg_self, Nat.cast_eq_zero] at s_card_neg_one
  assumption
  intro s_card_zero
  rw [s_card_zero]
  simp

theorem dim_zero_iff_vertex
    (s : Finset E)
  : face_dim s = 0 ↔ ∃ x : E, s = {x} :=
by
  unfold face_dim
  constructor
  intro s_card_minus_one
  have s_card_one : s.card = 1 := by linarith
  rw [← Finset.card_eq_one]
  assumption
  intro exists_x
  rw [← Finset.card_eq_one] at exists_x
  rw [exists_x]
  simp

theorem simplex_decomp [DecidableEq E]
    (s : Finset E)
  : 0 < face_dim s → ∃ x ∈ s, ∃ t : Finset E, t = s \ {x} :=
by
  unfold face_dim
  intro s_card_pos
  have s_card_gt_one : 1 < s.card := by linarith
  rw [Finset.one_lt_card] at s_card_gt_one
  choose a a_in_s b b_in_s a_ne_b using s_card_gt_one
  use a; constructor; assumption
  use s \ {a}

theorem simplex_decomp_dim [DecidableEq E]
    (s : Finset E)
    (x : E)
    (x_in_s : x ∈ s)
  : 0 < face_dim s → 0 ≤ face_dim (s \ {x}) :=
by
  unfold face_dim
  intro s_card_pos
  have s_card_gt_one : 1 < s.card := by linarith
  rw [Finset.card_sdiff, Finset.card_singleton]
  apply Int.sub_nonneg_of_le
  rw [Int.ofNat_sub, Int.ofNat_one, Int.le_sub_one_iff]
  rw [Nat.one_lt_cast]
  assumption
  apply le_of_lt
  assumption
  rw [Finset.singleton_subset_iff]
  assumption

theorem simplex_decomp_dim_eq [DecidableEq E]
    (s : Finset E)
    (x : E)
    (x_in_s : x ∈ s)
  : 0 < face_dim s → face_dim (s \ {x}) = face_dim s - 1 :=
by
  unfold face_dim
  intro s_card_pos
  rw [Finset.card_sdiff, Finset.card_singleton]
  rw [sub_left_inj, Int.ofNat_sub, Int.ofNat_one]
  linarith
  rw [Finset.singleton_subset_iff]
  assumption

-- The dimension of a finite complex is the maximum
-- dimension of its simplices.
instance DimSet.Finite
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
  : Finite (Finset.image face_dim X.faces.toFinset) :=
by
  apply Set.finite_mem_finset

-- theorem dim_set_nonempty
--     (X : AbstractSimplicialComplex 𝕜 E)
--     [Fintype X.faces] [Nonempty X.faces]
--   : (Finset.image dim (X.faces.toFinset).Nonempty :=
-- by
--   apply Finset.Nonempty.image
--   unfold Finset.Nonempty
--   use ∅
--   rw [← Finset.mem_coe, Set.coe_toFinset]
--   apply simplicialComplex_empty_simplex

@[simp]
def AbstractSimplicialComplex.dim
    (X : AbstractSimplicialComplex E)
    [Fintype X.faces] : ℤ :=
  Finset.max' ((Finset.image face_dim X.faces.toFinset) ∪ {-1})
  (by
    unfold Finset.Nonempty
    use -1
    rw [Finset.mem_union]
    right
    rw [Finset.mem_singleton])

/-
# Disjointness of simplicial complexes.
-/
section Disjoint

variable [DecidableEq α]

-- Define when two simplicial complexes are disjoint via disjointness of vertices.
def DisjointComplexes
    (X Y : AbstractSimplicialComplex E) : Prop :=
  Disjoint (X.vertices) (Y.vertices)

-- Indeed, this implies simplices are disjoint, too.
theorem disjoint_simplices_iff_disj_vertices [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
    (s t : Finset E)
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces)
  : DisjointComplexes X Y → Disjoint s t :=
by
  simp only [DisjointComplexes, AbstractSimplicialComplex.vertices_eq]
  intro XY_disj
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.subset_empty_iff] at XY_disj
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.subset_empty, ← Finset.coe_subset,
    Finset.coe_empty, Finset.coe_inter]
  apply
    @Set.Subset.trans _ _
      ((⋃ (s : Finset E) (H : s ∈ X.faces), ↑s) ∩ ⋃ (s : Finset E) (H : s ∈ Y.faces), ↑s)
  apply Set.inter_subset_inter <;> apply Set.subset_biUnion_of_mem <;> assumption
  simp only [Set.subset_empty_iff] at ⊢ XY_disj
  assumption

-- Disjoint singletons are also disjoint.
theorem disjoint_singleton
    (X : AbstractSimplicialComplex E)
    (x : E)
  : x ∉ X.vertices → DisjointComplexes X (simplex {x}) :=
by
  simp only [DisjointComplexes, simplex_vertices {x}]
  intro x_nin_X
  rw [Set.disjoint_iff_inter_eq_empty, Finset.coe_singleton, Set.inter_singleton_eq_empty]
  assumption

end Disjoint

/-
# Operators on simplicial complexes.
-/
section Operators

variable [DecidableEq E]

@[simp]
def simplicialUnion
    (X Y : AbstractSimplicialComplex E)
  : AbstractSimplicialComplex E :=
    AbstractSimplicialComplex.mk
    (X.faces ∪ Y.faces)
    (by
      rw [Set.mem_union, not_or]
      constructor
      apply X.empty_notMem
      apply Y.empty_notMem)
    (by
      intro s t s_in_XY t t_sset_s
      rw [Set.mem_union] at *
      cases' s_in_XY with s_in_X s_in_Y
      left
      apply X.down_closed <;> assumption
      right
      apply Y.down_closed <;> assumption)

@[reducible]
instance AbstractSimplicialComplex.instHasUnion : Union (AbstractSimplicialComplex E) :=
  ⟨simplicialUnion⟩

instance simplicialUnion.Fintype [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
    [Fintype X.faces] [Fintype Y.faces]
  : Fintype (X ∪ Y).faces :=
by
  simp only [AbstractSimplicialComplex.instHasUnion, simplicialUnion, AbstractSimplicialComplex.mk.injEq]
  apply Set.fintypeUnion

instance simplicialUnion.Finite
    (X Y : AbstractSimplicialComplex E)
    [Finite X.faces] [Finite Y.faces]
  : Finite (X ∪ Y).faces :=
by
  simp only [AbstractSimplicialComplex.instHasUnion, simplicialUnion, AbstractSimplicialComplex.mk.injEq]
  rw [Set.finite_coe_iff, Set.finite_union, ← Set.finite_coe_iff]
  constructor <;> assumption

theorem simplicial_union_assoc
    (X Y Z : AbstractSimplicialComplex E)
  : X ∪ Y ∪ Z = X ∪ (Y ∪ Z) :=
by
  simp only [AbstractSimplicialComplex.instHasUnion, simplicialUnion, AbstractSimplicialComplex.mk.injEq]
  rw [Set.union_assoc]

theorem simplicial_union_comm
    (X Y : AbstractSimplicialComplex E)
  : X ∪ Y = Y ∪ X :=
by
  simp only [AbstractSimplicialComplex.instHasUnion, simplicialUnion, AbstractSimplicialComplex.mk.injEq]
  rw [Set.union_comm]

theorem simplicial_union_simplices
    (X Y : AbstractSimplicialComplex E)
  : (X ∪ Y).faces = X.faces ∪ Y.faces :=
by
  simp only [AbstractSimplicialComplex.instHasUnion, simplicialUnion]

theorem simplicial_union_dim
    (X Y : AbstractSimplicialComplex E)
    [Fintype X.faces] [Fintype Y.faces]
  : (X ∪ Y).dim = max (X.dim) (Y.dim) :=
by
  unfold AbstractSimplicialComplex.dim
  apply le_antisymm
  · apply Finset.max'_le
    intro y y_in_img
    simp only [Finset.mem_image, simplicialUnion, Set.mem_union, Finset.mem_union, Set.mem_toFinset] at y_in_img
    cases' y_in_img with y_in_img y_empty
    choose s s_in_union dim_s_y using y_in_img
    rw [le_max_iff]
    cases' s_in_union with s_in_X s_in_Y
    left
    apply Finset.le_max'
    rw [Finset.mem_union]
    left
    rw [Finset.mem_image]
    use s; constructor
    rw [Set.mem_toFinset]
    assumption
    assumption
    right
    apply Finset.le_max'
    rw [Finset.mem_union]
    left
    rw [Finset.mem_image]
    use s; constructor
    rw [Set.mem_toFinset]
    assumption
    assumption
    rw [le_max_iff]
    left
    apply Finset.le_max'
    rw [Finset.mem_union]
    right; assumption
  · rw [max_le_iff]
    constructor
    rw [Finset.max'_le_iff]
    intro y y_in_img
    simp only [Finset.mem_union, Finset.mem_image, Set.mem_toFinset] at y_in_img
    cases' y_in_img with y_in_img y_empty
    choose s s_in_X dim_s_y using y_in_img
    apply Finset.le_max'
    rw [Finset.mem_union]
    left
    simp only [Finset.mem_image, simplicialUnion, Set.mem_union, Set.mem_toFinset]
    use s; constructor
    left; assumption
    assumption
    apply Finset.le_max'
    rw [Finset.mem_union]
    right
    assumption
    rw [Finset.max'_le_iff]
    intro y y_in_img
    simp only [Finset.mem_union, Finset.mem_image, Set.mem_toFinset] at y_in_img
    cases' y_in_img with y_in_img y_empty
    choose s s_in_Y dim_s_y using y_in_img
    apply Finset.le_max'
    simp only [Finset.mem_union, Finset.mem_image, simplicialUnion, Set.mem_union, Set.mem_toFinset]
    left
    use s; constructor
    right; assumption
    assumption
    apply Finset.le_max'
    rw [Finset.mem_union]
    right; assumption

@[simp]
def simplicialInter
    (X Y : AbstractSimplicialComplex E)
  : AbstractSimplicialComplex E :=
    AbstractSimplicialComplex.mk
    (X.faces ∩ Y.faces)
    (by
      rw [Set.mem_inter_iff, not_and]
      intro contra
      apply Y.empty_notMem)
    (by
      intro s t s_in_XY t_sset_s t_ne
      rw [Set.mem_inter_iff] at ⊢ s_in_XY
      cases' s_in_XY with s_in_X s_in_Y
      constructor
      apply X.down_closed <;> assumption
      apply Y.down_closed <;> assumption)

@[reducible]
instance AbstractSimplicialComplex.instHasInter : Inter (AbstractSimplicialComplex E) :=
  ⟨simplicialInter⟩

theorem simplicial_inter_assoc
    (X Y Z : AbstractSimplicialComplex E)
  : X ∩ Y ∩ Z = X ∩ (Y ∩ Z) :=
by
  simp only [AbstractSimplicialComplex.instHasInter, simplicialInter, AbstractSimplicialComplex.mk.injEq]
  rw [Set.inter_assoc]

theorem simplicial_inter_comm
    (X Y : AbstractSimplicialComplex E)
  : X ∩ Y = Y ∩ X :=
by
  simp only [AbstractSimplicialComplex.instHasInter, simplicialInter, AbstractSimplicialComplex.mk.injEq]
  rw [Set.inter_comm]

end Operators

/-
# Subcomplexes
-/
-- Define a subcomplex in the usual way:
-- i.e., simplices are contained in the other.
def IsSubcomplex
    (X Y : AbstractSimplicialComplex E)
  : Prop :=
    X.faces ⊆ Y.faces

@[reducible]
instance AbstractSimplicialComplex.instHasSubset : HasSubset (AbstractSimplicialComplex E) :=
  ⟨IsSubcomplex⟩

theorem is_subcomplex_vertex
    (X Y : AbstractSimplicialComplex E)
    (Y_subcomp_X : Y ⊆ X)
  : ∀ x : E, x ∈ Y.vertices → x ∈ X.vertices :=
by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def] at Y_subcomp_X
  intro y y_in_vert_Y
  simp only [AbstractSimplicialComplex.vertices_eq, Set.mem_iUnion] at y_in_vert_Y ⊢
  choose s Hs y_in_s using y_in_vert_Y
  specialize Y_subcomp_X s Hs
  use s

theorem is_subcomplex_vertices
    (X Y : AbstractSimplicialComplex E)
    (Y_subcomp_X : Y ⊆ X)
  : Y.vertices ⊆ X.vertices := by
  simp only [Set.subset_def]
  apply is_subcomplex_vertex X Y Y_subcomp_X

-- Equivalent, useful definition of a simplex as a subcomplex of the original.
def IsSimplex
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
  : Prop :=
    simplex s ⊆ X

theorem simplex_iff_subcomplex_mem
    (X : AbstractSimplicialComplex E)
    (s : Finset E) [Nonempty s]
  : s ∈ X.faces ↔ simplex s ⊆ X :=
by
  constructor
  intro s_in_X_simpl
  simp only [IsSubcomplex, simplex, AbstractSimplicialComplex.instHasSubset]
  rw [Set.subset_def]
  intro x x_in_s_power
  rw [Set.mem_diff, Finset.mem_coe, Finset.mem_powerset] at x_in_s_power
  choose x_sset_s x_nonempty using x_in_s_power
  apply X.down_closed s_in_X_simpl
  assumption
  rw [Set.mem_singleton_iff] at x_nonempty
  assumption
  intro s_simpl_X
  simp only [IsSubcomplex, simplex, AbstractSimplicialComplex.instHasSubset] at s_simpl_X
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

theorem simplicial_union_eq_left_iff_subcomplex [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
  : (X ∪ Y).faces = X.faces ↔ Y ⊆ X :=
  by
  simp only [AbstractSimplicialComplex.instHasUnion, simplicialUnion, AbstractSimplicialComplex.instHasSubset, IsSubcomplex]
  apply Set.union_eq_left

theorem simplicial_union_eq_right_iff_subcomplex [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
  : (X ∪ Y).faces = Y.faces ↔ X ⊆ Y :=
by
  simp only [AbstractSimplicialComplex.instHasUnion, simplicialUnion, AbstractSimplicialComplex.instHasSubset, IsSubcomplex]
  apply Set.union_eq_right

theorem subcomplex_simplicial_union_left_simplices [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
  : ∀ s : Finset E, s ∈ X.faces → s ∈ (X ∪ Y).faces :=
by
  apply Set.subset_union_left

theorem subcomplex_simplicial_union_left [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
  : X ⊆ X ∪ Y :=
by
  simp only [AbstractSimplicialComplex.instHasUnion, AbstractSimplicialComplex.instHasSubset, IsSubcomplex, simplicialUnion]
  apply Set.subset_union_left

theorem subcomplex_simplicial_union_right_simplices [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
  : ∀ s : Finset E, s ∈ Y.faces → s ∈ (X ∪ Y).faces :=
by
  apply Set.subset_union_right

theorem subcomplex_simplicial_union_right [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
  : Y ⊆ X ∪ Y :=
by
  simp only [AbstractSimplicialComplex.instHasUnion, AbstractSimplicialComplex.instHasSubset, IsSubcomplex, simplicialUnion]
  apply Set.subset_union_right

theorem simplex_if_in_subcomplex
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E)
  : s ∈ X.faces → X ⊆ Y → s ∈ Y.faces :=
by
  intro s_in_X X_sub_Y
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def] at X_sub_Y
  specialize X_sub_Y s s_in_X
  assumption

theorem subcomplex_simplicial_inter_left_simplices [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
  : ∀ s : Finset E, s ∈ (X ∩ Y).faces → s ∈ X.faces :=
by
  apply Set.inter_subset_left

theorem subcomplex_simplicial_inter_left [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
  : X ∩ Y ⊆ X :=
by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, simplicialInter]
  apply Set.inter_subset_left

theorem subcomplex_simplicial_inter_right_simplices [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
  : ∀ s : Finset E, s ∈ (X ∩ Y).faces → s ∈ Y.faces :=
by
  apply Set.inter_subset_right

theorem subcomplex_simplicial_inter_right [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
  : X ∩ Y ⊆ Y :=
by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, simplicialInter]
  apply Set.inter_subset_right

theorem singleton_inter_eq_empty_iff_not_mem [DecidableEq E]
    {s : Finset E} {a : E}
  : {a} ∩ s = ∅ ↔ a ∉ s :=
by
  simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, not_and]
  constructor
  intro as_disj
  specialize as_disj a (by apply Finset.mem_singleton_self)
  assumption
  intro a_nin_s x x_in_a
  rw [Finset.mem_singleton] at x_in_a
  rw [x_in_a]
  assumption
