import Pachner.Basic.AbstractSimplicialComplex
import Pachner.Basic.Dimension

variable {E 𝕜 : Type*}
variable [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

section SimplicialUnion

def simplicialUnion_faces
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : Set (Finset E) := X.faces ∪ Y.faces

theorem simplicialUnion_empty_notMem
    {X Y : Geometry.SimplicialComplex 𝕜 E}
  : ∅ ∉ simplicialUnion_faces X Y :=
by
  unfold simplicialUnion_faces
  rw [Set.mem_union, not_or]
  constructor
  apply X.empty_notMem
  apply Y.empty_notMem

theorem simplicialUnion_indep
    {X Y : Geometry.SimplicialComplex 𝕜 E}
  : ∀ {s}, s ∈ simplicialUnion_faces X Y → AffineIndependent 𝕜 ((↑) : s → E) :=
by
  sorry

theorem simplicialUnion_down_closed
    {X Y : Geometry.SimplicialComplex 𝕜 E}
  : ∀ {s t}, s ∈ simplicialUnion_faces X Y → t ⊆ s → t.Nonempty → t ∈ simplicialUnion_faces X Y :=
by
  unfold simplicialUnion_faces
  intro s t s_in_XY t t_sset_s
  rw [Set.mem_union] at *
  cases' s_in_XY with s_in_X s_in_Y
  left
  apply X.down_closed <;> assumption
  right
  apply Y.down_closed <;> assumption

theorem simplicialUnion_inter_subset_convexHull
    {X Y : Geometry.SimplicialComplex 𝕜 E}
  : ∀ {s t}, s ∈ simplicialUnion_faces X Y → t ∈ simplicialUnion_faces X Y →
      convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E) :=
by
  sorry

@[simp]
def simplicialUnion
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : Geometry.SimplicialComplex 𝕜 E :=
      ⟨X.faces ∪ Y.faces, simplicialUnion_empty_notMem, simplicialUnion_indep, simplicialUnion_down_closed, simplicialUnion_inter_subset_convexHull⟩

@[reducible]
instance Geometry.SimplicialComplex.instHasUnion : Union (Geometry.SimplicialComplex 𝕜 E) :=
  ⟨simplicialUnion⟩

instance simplicialUnion.Fintype [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
    [Fintype X.faces] [Fintype Y.faces]
  : Fintype (X ∪ Y).faces :=
by
  simp only [Geometry.SimplicialComplex.instHasUnion, simplicialUnion]
  apply Set.fintypeUnion

instance simplicialUnion.Finite
    (X Y : Geometry.SimplicialComplex 𝕜 E)
    [Finite X.faces] [Finite Y.faces]
  : Finite (X ∪ Y).faces :=
by
  simp only [Geometry.SimplicialComplex.instHasUnion, simplicialUnion]
  rw [Set.finite_coe_iff, Set.finite_union, ← Set.finite_coe_iff]
  constructor <;> assumption

theorem simplicial_union_assoc
    (X Y Z : Geometry.SimplicialComplex 𝕜 E)
  : X ∪ Y ∪ Z = X ∪ (Y ∪ Z) :=
by
  simp only [Geometry.SimplicialComplex.instHasUnion, simplicialUnion, Geometry.SimplicialComplex.mk.injEq]
  rw [Set.union_assoc]

theorem simplicial_union_comm
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : X ∪ Y = Y ∪ X :=
by
  simp only [Geometry.SimplicialComplex.instHasUnion, simplicialUnion, Geometry.SimplicialComplex.mk.injEq]
  rw [Set.union_comm]

theorem simplicial_union_simplices
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : (X ∪ Y) = X ∪ Y :=
by
  simp only [Geometry.SimplicialComplex.instHasUnion, simplicialUnion]

theorem simplicial_union_eq_left_iff_subcomplex [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : (X ∪ Y).faces = X.faces ↔ Y ⊆ X :=
by
  simp only [Geometry.SimplicialComplex.instHasUnion, simplicialUnion, Geometry.SimplicialComplex.instHasSubset, IsSubcomplex]
  apply Set.union_eq_left

theorem simplicial_union_eq_right_iff_subcomplex [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : (X ∪ Y).faces = Y.faces ↔ X ⊆ Y :=
by
  simp only [Geometry.SimplicialComplex.instHasUnion, simplicialUnion, Geometry.SimplicialComplex.instHasSubset, IsSubcomplex]
  apply Set.union_eq_right

theorem subcomplex_simplicial_union_left_simplices [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : ∀ s : Finset E, s ∈ X.faces → s ∈ (X ∪ Y).faces :=
by
  apply Set.subset_union_left

theorem subcomplex_simplicial_union_left [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : X ⊆ X ∪ Y :=
by
  simp only [Geometry.SimplicialComplex.instHasUnion, Geometry.SimplicialComplex.instHasSubset, IsSubcomplex, simplicialUnion]
  apply Set.subset_union_left

theorem subcomplex_simplicial_union_right_simplices [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : ∀ s : Finset E, s ∈ Y.faces → s ∈ (X ∪ Y).faces :=
by
  apply Set.subset_union_right

theorem subcomplex_simplicial_union_right [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : Y ⊆ X ∪ Y :=
by
  simp only [Geometry.SimplicialComplex.instHasUnion, Geometry.SimplicialComplex.instHasSubset, IsSubcomplex, simplicialUnion]
  apply Set.subset_union_right


end SimplicialUnion


section SimplicialUnion.Dimension
variable [DecidableEq E]


theorem simplicial_union_dim
    (X Y : Geometry.SimplicialComplex 𝕜 E)
    [Fintype X.faces] [Fintype Y.faces]
  : (X ∪ Y).dim = max (X.dim) (Y.dim) :=
by
  unfold Geometry.SimplicialComplex.dim
  apply le_antisymm
  · apply Finset.max'_le
    intro y y_in_img
    simp only [Finset.mem_image, Finset.mem_union, Set.mem_toFinset] at y_in_img
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
    simp only [Finset.mem_image, Set.mem_toFinset]
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
    simp only [Finset.mem_union, Finset.mem_image, Set.mem_toFinset]
    left
    use s; constructor
    right; assumption
    assumption
    apply Finset.le_max'
    rw [Finset.mem_union]
    right; assumption


end SimplicialUnion.Dimension
