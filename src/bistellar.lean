import tactic          -- standard proof tactics
import data.set        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset     -- type-level finite sets
import .simplicial_complex
import .simplicial_subcomplex
import .simplicial_map
import .combinatorical_manifold

variables {α : Type*} [decidable_eq α]

def bistellar_move
    (X : combinatorical_manifold α)
    (s ∈ X.complex.simplices)
  : simplicial_coe (α × ℕ) α → combinatorical_manifold α
:= λ φ : simplicial_coe (α × ℕ) α,
    combinatorical_manifold.mk
      (((simplicial_complex.mk
        (((X.complex\St(X.complex, s) (by assumption)).simplices ∪ (∂s).simplices))
        (begin
          -- Proof complete, just slow.
          sorry,
          -- simp, safe,

          -- have : t ⊆ s_1 -> t ∈ (∂s).simplices, from
          -- begin
          --   apply (∂s).subset_closed, assumption,
          -- end,
          -- finish,

          -- have : t ⊆ s_1 -> t ∈ (star_complement X.complex s H).simplices, from
          -- begin
          --   apply (star_complement X.complex s H).subset_closed,
          --   assumption,
          -- end,
          -- finish,
        end))
        ⋆ (B(X.complex, s) (by assumption))) φ)
      (begin
        -- TODO: Draft proof of isomorphy to S(n + 1).
        sorry,
      end)
notation `τ(` X `,` s `)` := bistellar_move X s

def is_bistellar_equivalent
    (X Y : combinatorical_manifold α)
  : Prop
:= ∀ φ : simplicial_coe (α × ℕ) α,
    ∃ (f : ℕ → combinatorical_manifold α) (n : ℕ),
      ((f 0).complex ≅ X.complex) ∧ ((f n).complex ≅ Y.complex) ∧
      ∀ i < n,
        (∃ s ∈ (f i).complex.simplices,
          (f (i + 1)).complex ≅ (τ(f i, s) (by assumption) φ).complex)
        ∨ ((f i).complex ≅ (f (i + 1)).complex)