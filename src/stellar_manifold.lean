import tactic          -- standard proof tactics
import data.set        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset     -- type-level finite sets
import .simplicial_complex
import .simplicial_subcomplex
import .stellar

variables {α : Type*} [decidable_eq α]

def stellar_n_sphere
    (n : ℕ)
  : simplicial_complex ℕ
:= simplicial_complex.mk
    (finset.powerset (finset.range (n + 2)) \ {finset.range (n + 2)})
    (begin
      simp, safe,

      have : s ⊆ finset.range(n + 2) -> finset.range(n + 2) ⊆ s -> s = finset.range(n + 2), from
      begin
        exact subset_antisymm,
      end,
      finish,

      have : t ⊆ s -> s ⊆ finset.range(n + 2) -> t ⊆ finset.range(n + 2), from
      begin
        exact subset_trans,
      end,
      finish
    end)

notation `S` n := stellar_n_sphere n

def stellar_n_disk
    (n : ℕ)
  : simplicial_complex ℕ
:= simplicial_complex.mk
    (finset.powerset (finset.range (n + 1)))
    (by {simp, tauto})

notation `D` n := stellar_n_disk n

def is_stellar_sphere
    (X : simplicial_complex α)
  : Prop
:= ∃ n : ℕ, is_stellar_equivalent X (S (n + 1))

def is_stellar_n_sphere
    (X : simplicial_complex α)
    (n : ℕ)
  : Prop
:= is_stellar_equivalent X (S (n + 1))

def is_stellar_ball
    (X : simplicial_complex α)
  : Prop
:= ∃ n : ℕ, is_stellar_equivalent X (D (n + 1))

def is_stellar_n_ball
    (X : simplicial_complex α)
    (n : ℕ)
  : Prop
:= is_stellar_equivalent X (D (n + 1))

@[simp]
def is_stellar_manifold
    (X : simplicial_complex α)
  : Prop
:= ∀ x : α,
    ({x} ∈ X.simplices) →
      is_stellar_sphere (Lk(X, {x})) ∨
      is_stellar_ball (Lk(X, {x}))

structure stellar_manifold (α : Type*) [decidable_eq α]
:= mk :: (complex : simplicial_complex α)
         (stellar_manifold : is_stellar_manifold complex)

/-
# Boundary of a Stellar Manifold
-/

-- Boundary of a complex is the simplices whose
-- link is not a sphere.
-- noncomputable
def simplicial_complex_boundary
    (X : simplicial_complex α)
  : simplicial_complex α
:= simplicial_complex.mk
    ({s ∈ X.simplices | s ∈ X.simplices → ¬is_stellar_sphere (Lk(X, s) (by { assumption, }))})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [set.mem_sep_iff],
      split,
      apply simplicial_complex_empty_simplex,

      sorry,
    end)
    (sorry)

-- Computability requires proof that is_stellar_sphere is decidable.
-- So, we assume the noncomputable finite instance on X.
noncomputable
instance simplicial_complex_boundary.fintype
    (X : simplicial_complex α) [finite X.simplices]
  : fintype (simplicial_complex_boundary X).simplices
:= begin
  simp only[simplicial_complex_boundary, simplicial_complex.simplices],
  apply set.finite.fintype,
  apply set.finite.sep,
  rw [←set.finite_coe_iff],
  assumption,
end

lemma boundary_simplex_in_complex
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_bd_X : s ∈ (simplicial_complex_boundary X).simplices)
  : s ∈ X.simplices
:= sorry

-- Lemma 3.6, p.16
lemma boundary_link_comm
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_bd_X : s ∈ (simplicial_complex_boundary X).simplices)
  : simplicial_complex_boundary (Lk(X, s) (boundary_simplex_in_complex X s s_in_bd_X)) ≅ₛₜ Lk(simplicial_complex_boundary X, s) s_in_bd_X
:= sorry

/-
# Closed Stellar Manifolds
-/

def is_closed_stellar_manifold
    (M : stellar_manifold α)
  : Prop
:= ∀ m : α,
    ({m} ∈ M.complex.simplices) →
      is_stellar_sphere (Lk(M.complex, {m}) (by assumption))

structure closed_stellar_manifold (α : Type*) [decidable_eq α]
:= mk :: (manifold : stellar_manifold α)
         (closed : is_closed_stellar_manifold manifold)

/-
# Properties of Stellar Balls/Spheres
-/

-- Lemma 3.2 (1), p.10
lemma stellar_n_ball_is_stellar_mfd
  : ∀ (n : ℕ), is_stellar_manifold (D n)
:= sorry

-- Lemma 3.2 (2), p.10
lemma stellar_n_sphere_is_stellar_mfd
  : ∀ (n : ℕ), is_stellar_manifold (S n)
:= begin
  sorry
end

-- Lemma 3.3 (1), p.12
lemma join_stellar_balls
    (X Y : simplicial_complex α)
  : is_stellar_ball X → is_stellar_ball Y → is_stellar_ball (X ⋆ Y)
:= sorry

-- Lemma 3.3 (2), p.12
lemma join_stellar_spheres
    (X Y : simplicial_complex α)
  : is_stellar_sphere X → is_stellar_sphere Y → is_stellar_sphere (X ⋆ Y)
:= sorry

-- Lemma 3.3 (3), p.12
lemma join_stellar_ball_and_sphere
    (X Y : simplicial_complex α)
  : is_stellar_ball X → is_stellar_sphere Y → is_stellar_ball (X ⋆ Y)
:= sorry

-- Proposition 3.4 (1), p.13
lemma stellar_link_is_stellar_ball_or_sphere
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : is_stellar_ball (Lk(X, s) s_in_X) ∨ is_stellar_sphere (Lk(X, s) s_in_X)
:= sorry

-- Proposition 3.4 (2), p.13
lemma stellar_eq_preserves_stellar_mfd
    (X Y : simplicial_complex α)
  : is_stellar_manifold X → X ≅ₛₜ Y → is_stellar_manifold Y
:= sorry

-- Lemma 3.8, p.17
lemma stellar_ball_boundary_ident
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (φ : simplicial_coe (α × ℕ) α)
    (s_in_X : s ∈ X.simplices)
    (s_nin_bd : s ∉ (simplicial_complex_boundary X).simplices)
    (x_nin_X : x ∉ vertices X)
  : simplicial_complex_boundary (@stellar_subdivision _ _ X s s_ne x s_in_X x_nin_X φ)
      ≅ simplicial_complex_boundary X
:= sorry

-- Corollary 3.9, p.17
lemma boundary_of_ball_is_sphere
    (X : simplicial_complex α)
    (n : ℕ)
  : is_stellar_n_ball X n → is_stellar_n_sphere (simplicial_complex_boundary X) n
:= sorry

-- Corollary 3.10, p.17
lemma closed_mfd_empty_boundary
    (X : closed_stellar_manifold α)
  : simplicial_complex_boundary X.manifold.complex = empty_sc
:= sorry

-- Proposition 3.11 (1), p.18
lemma stellar_ball_boundary_dist_join_union
    (X Y : simplicial_complex α)
    (X_stellar_ball : is_stellar_ball X)
    (Y_stellar_ball : is_stellar_ball Y)
  : simplicial_complex_boundary (X ⋆ Y) ≅ (X ⋆ (simplicial_complex_boundary Y)) ∪ ((simplicial_complex_boundary X) ⋆ Y)
:= sorry

-- Proposition 3.12 (2), p.18
lemma stellar_sphere_ball_boundary_distr_join_left
    (X Y : simplicial_complex α)
    (X_stellar_sphere : is_stellar_sphere X)
    (Y_stellar_ball : is_stellar_ball Y)
  : simplicial_complex_boundary (X ⋆ Y) ≅ X ⋆ (simplicial_complex_boundary Y)
:= sorry

-- Corollary 3.12, p.20
lemma stellar_ball_boundary_comm_cone_union
    (X : simplicial_complex α)
    (x : α)
    (φ : simplicial_coe (α × ℕ) α)
    (X_stellar_ball : is_stellar_ball X)
    (x_nin_X : x ∉ vertices X)
  : simplicial_complex_boundary (cone X x x_nin_X) ≅ φ[(cone (simplicial_complex_boundary X) x sorry)] ∪ X
:= sorry

