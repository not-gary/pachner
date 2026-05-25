/-
Copyright (c) 2025 Garett Cunningham, Daniel Zach, Stefan Friedl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Garett Cunningham, Daniel Zach, Stefan Friedl
-/

import Pachner.Basic.AbstractSimplicialComplex

variable
  {E : Type _}
  {X Y Z : AbstractSimplicialComplex E} {s : Finset E} {x : E}

@[simp]
def SimplicialInter
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
  ⟨SimplicialInter⟩

theorem simplicialInter_assoc : X ∩ Y ∩ Z = X ∩ (Y ∩ Z) := by
  simp only [AbstractSimplicialComplex.instHasInter, SimplicialInter, AbstractSimplicialComplex.ext_iff,
    Set.inter_assoc]

theorem simplicialInter_comm : X ∩ Y = Y ∩ X := by
  simp only [AbstractSimplicialComplex.instHasInter, SimplicialInter, AbstractSimplicialComplex.ext_iff,
    Set.inter_comm]

theorem simplicialInter_subcomplex_left : X ∩ Y ⊆ X := by
  simp only [AbstractSimplicialComplex.instHasInter, SimplicialInter, AbstractSimplicialComplex.ext_iff,
    AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.inter_subset_left]

theorem implicialInter_subcomplex_right : X ∩ Y ⊆ Y := by
  simp only [AbstractSimplicialComplex.instHasInter, SimplicialInter, AbstractSimplicialComplex.ext_iff,
    AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.inter_subset_right]

theorem singleton_inter_eq_empty_iff_not_mem [DecidableEq E] : {x} ∩ s = ∅ ↔ x ∉ s := by
  simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, not_and]
  constructor
  intro as_disj
  specialize as_disj x (by apply Finset.mem_singleton_self)
  assumption
  intro a_nin_s x x_in_a
  rw [Finset.mem_singleton] at x_in_a
  rw [x_in_a]
  assumption
