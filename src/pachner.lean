import tactic          -- standard proof tactics
import data.set        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset     -- type-level finite sets
import .simplicial_complex
import .simplicial_subcomplex
import .combinatorical_manifold
import .stellar
import .bistellar

variables {α β : Type*}
variables [decidable_eq α] [decidable_eq β]

theorem pachner
    (X : closed_combinatorical_manifold α)
    (Y : closed_combinatorical_manifold β)
  : is_bistellar_equivalent X.manifold Y.manifold ↔
      is_stellar_equivalent X.manifold.complex Y.manifold.complex
:=
begin
  unfold is_bistellar_equivalent,
  unfold is_stellar_equivalent,
  split, intros,

  -- bistellar => stellar
  sorry,
  -- stellar => bistellar
  sorry,
end