import Pachner.Basic.AbstractSimplicialComplex

variable {E : Type _}

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
