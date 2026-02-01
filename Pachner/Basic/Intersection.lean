import Pachner.Basic.AbstractSimplicialComplex

variable {E 𝕜 : Type*}
variable [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

def simplicialInter_faces
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : Set (Finset E) := X.faces ∩ Y.faces

theorem simplicialInter_empty_notMem
    {X Y : Geometry.SimplicialComplex 𝕜 E}
  : ∅ ∉ simplicialInter_faces X Y :=
by
  unfold simplicialInter_faces
  rw [Set.mem_inter_iff, not_and]
  intro contra
  apply Y.empty_notMem

theorem simplicialInter_indep
    {X Y : Geometry.SimplicialComplex 𝕜 E}
  : ∀ {s}, s ∈ simplicialInter_faces X Y → AffineIndependent 𝕜 ((↑) : s → E) :=
by
  sorry

theorem simplicialInter_down_closed
    {X Y : Geometry.SimplicialComplex 𝕜 E}
  : ∀ {s t}, s ∈ simplicialInter_faces X Y → t ⊆ s → t.Nonempty → t ∈ simplicialInter_faces X Y :=
by
  unfold simplicialInter_faces
  intro s t s_in_XY t_sset_s t_ne
  rw [Set.mem_inter_iff] at ⊢ s_in_XY
  cases' s_in_XY with s_in_X s_in_Y
  constructor
  apply X.down_closed <;> assumption
  apply Y.down_closed <;> assumption

theorem simplicialInter_inter_subset_convexHull
    {X Y : Geometry.SimplicialComplex 𝕜 E}
  : ∀ {s t}, s ∈ simplicialInter_faces X Y → t ∈ simplicialInter_faces X Y →
      convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E) :=
by
  sorry

@[simp]
def simplicialInter
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : Geometry.SimplicialComplex 𝕜 E :=
      ⟨X.faces ∩ Y.faces, simplicialInter_empty_notMem, simplicialInter_indep, simplicialInter_down_closed, simplicialInter_inter_subset_convexHull⟩

@[reducible]
instance Geometry.SimplicialComplex.instHasInter : Inter (Geometry.SimplicialComplex 𝕜 E) :=
  ⟨simplicialInter⟩

theorem simplicial_inter_assoc
    (X Y Z : Geometry.SimplicialComplex 𝕜 E)
  : X ∩ Y ∩ Z = X ∩ (Y ∩ Z) :=
by
  simp only [Geometry.SimplicialComplex.instHasInter, simplicialInter, Geometry.SimplicialComplex.mk.injEq]
  rw [Set.inter_assoc]

theorem simplicial_inter_comm
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : X ∩ Y = Y ∩ X :=
by
  simp only [Geometry.SimplicialComplex.instHasInter, simplicialInter, Geometry.SimplicialComplex.mk.injEq]
  rw [Set.inter_comm]

theorem subcomplex_simplicial_inter_left_simplices [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : ∀ s : Finset E, s ∈ (X ∩ Y).faces → s ∈ X.faces :=
by
  apply Set.inter_subset_left

theorem subcomplex_simplicial_inter_left [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : X ∩ Y ⊆ X :=
by
  simp only [Geometry.SimplicialComplex.instHasSubset, IsSubcomplex]
  apply Set.inter_subset_left

theorem subcomplex_simplicial_inter_right_simplices [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : ∀ s : Finset E, s ∈ (X ∩ Y).faces → s ∈ Y.faces :=
by
  apply Set.inter_subset_right

theorem subcomplex_simplicial_inter_right [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : X ∩ Y ⊆ Y :=
by
  simp only [Geometry.SimplicialComplex.instHasSubset, IsSubcomplex]
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
