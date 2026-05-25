/-
Copyright (c) 2025 Garett Cunningham, Daniel Zach, Stefan Friedl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Garett Cunningham, Daniel Zach, Stefan Friedl
-/

import Pachner.Basic.AbstractSimplicialComplex
import Pachner.Basic.Dimension

variable
  {E : Type _}
  {X Y Z : AbstractSimplicialComplex E}

section SimplicialUnion

@[simp]
def SimplicialUnion
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
  ⟨SimplicialUnion⟩

instance SimplicialUnion.Fintype [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
    [Fintype X.faces] [Fintype Y.faces]
  : Fintype (X ∪ Y).faces :=
by
  simp only [AbstractSimplicialComplex.instHasUnion, SimplicialUnion]
  apply Set.fintypeUnion

instance SimplicialUnion.Finite
    (X Y : AbstractSimplicialComplex E)
    [Finite X.faces] [Finite Y.faces]
  : Finite (X ∪ Y).faces :=
by
  simp only [AbstractSimplicialComplex.instHasUnion, SimplicialUnion]
  rw [Set.finite_coe_iff, Set.finite_union, ← Set.finite_coe_iff]
  constructor <;> assumption

theorem simplicialUnion_assoc : X ∪ Y ∪ Z = X ∪ (Y ∪ Z) := by
  simp only [AbstractSimplicialComplex.instHasUnion, SimplicialUnion, Set.union_assoc]

theorem simplicialUnion_comm : X ∪ Y = Y ∪ X := by
  simp only [AbstractSimplicialComplex.instHasUnion, SimplicialUnion, Set.union_comm]

theorem simplicialUnion_eq_left_iff_subcomplex : (X ∪ Y) = X ↔ Y ⊆ X := by
  simp only [AbstractSimplicialComplex.instHasUnion, SimplicialUnion, AbstractSimplicialComplex.ext_iff,
    AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.union_eq_left]

theorem simplicialUnion_eq_right_iff_subcomplex : (X ∪ Y) = Y ↔ X ⊆ Y := by
  simp only [AbstractSimplicialComplex.instHasUnion, SimplicialUnion, AbstractSimplicialComplex.ext_iff,
    AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.union_eq_right]

theorem simplicialUnion_subcomplex_left : X ⊆ X ∪ Y := by
  simp only [AbstractSimplicialComplex.instHasUnion, AbstractSimplicialComplex.instHasSubset,
    IsSubcomplex, SimplicialUnion, Set.subset_union_left]

theorem simplicialUnion_subcomplex_right : Y ⊆ X ∪ Y := by
  simp only [AbstractSimplicialComplex.instHasUnion, AbstractSimplicialComplex.instHasSubset,
    IsSubcomplex, SimplicialUnion, Set.subset_union_right]

end SimplicialUnion

section SimplicialUnion.Dimension

theorem simplicial_union_dim
    [DecidableEq E]
    [Fintype X.faces] [Fintype Y.faces]
  : (X ∪ Y).dim = max (X.dim) (Y.dim) :=
by
  unfold AbstractSimplicialComplex.dim
  apply le_antisymm
  · apply Finset.max'_le
    intro y y_in_img
    simp only [Finset.mem_image, SimplicialUnion, Set.mem_union, Finset.mem_union, Set.mem_toFinset] at y_in_img
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
    simp only [Finset.mem_image, SimplicialUnion, Set.mem_union, Set.mem_toFinset]
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
    simp only [Finset.mem_union, Finset.mem_image, SimplicialUnion, Set.mem_union, Set.mem_toFinset]
    left
    use s; constructor
    right; assumption
    assumption
    apply Finset.le_max'
    rw [Finset.mem_union]
    right; assumption


end SimplicialUnion.Dimension
