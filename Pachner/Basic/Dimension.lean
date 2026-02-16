import Pachner.Basic.AbstractSimplicialComplex

variable {E : Type _}

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

variable {s : Finset E} {x : E}

theorem dim_geq_zero_iff_nonempty : 0 ≤ face_dim s ↔ s ≠ ∅ := by
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

theorem dim_neg_one_iff_empty : face_dim s = -1 ↔ s = ∅ := by
  unfold face_dim
  rw [← Finset.card_eq_zero]
  constructor
  intro s_card_neg_one
  simp only [sub_eq_neg_self, Nat.cast_eq_zero] at s_card_neg_one
  assumption
  intro s_card_zero
  rw [s_card_zero]
  simp

theorem dim_zero_iff_vertex : face_dim s = 0 ↔ ∃ x : E, s = {x} := by
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

theorem simplex_decomp [DecidableEq E] : 0 < face_dim s → ∃ x ∈ s, ∃ t : Finset E, t = s \ {x} := by
  unfold face_dim
  intro s_card_pos
  have s_card_gt_one : 1 < s.card := by linarith
  rw [Finset.one_lt_card] at s_card_gt_one
  choose a a_in_s b b_in_s a_ne_b using s_card_gt_one
  use a; constructor; assumption
  use s \ {a}

theorem simplex_decomp_dim
    [DecidableEq E]
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

theorem simplex_decomp_dim_eq
    [DecidableEq E]
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
    [Fintype X.faces]
  : ℤ :=
  Finset.max' ((Finset.image face_dim X.faces.toFinset) ∪ {-1})
  (by
    unfold Finset.Nonempty
    use -1
    rw [Finset.mem_union]
    right
    rw [Finset.mem_singleton])
