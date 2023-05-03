import tactic          -- standard proof tactics
import data.set        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset     -- type-level finite sets
import .simplicial_complex
import .simplicial_subcomplex
import .simplicial_map

variables {α : Type*} [decidable_eq α]

def stellar_subdivision
    (X : simplicial_complex α)
    (s : finset α) [nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : simplicial_coe (α × ℕ) α → simplicial_complex α
:= λ φ : simplicial_coe (α × ℕ) α,
    (X\St(X, s) s_in_X) ∪ φ[((φ[((simplex {x}) ⋆ ∂s)]) ⋆ Lk(X, s) s_in_X)]
notation `σ(` X `, ` s `; ` x `, ` φ `; ` s_ne `, ` s_in_X `, ` x_nin_X `)` := @stellar_subdivision _ _ X s s_ne x s_in_X x_nin_X φ

@[simp]
def stellar_move
  : simplicial_complex α → simplicial_complex α → Prop
:= λ X Y : simplicial_complex α,
    ∀ φ : simplicial_coe (α × ℕ) α,
      (∃ (t : finset α) (Ht : t ∈ Y.simplices) [Ht_ne : nonempty t]
        (y : α) (Hy : y ∉ vertices Y),
        X ≅ @stellar_subdivision _ _ Y t Ht_ne y Ht Hy φ)
      ∨
      (∃ (s : finset α) (Hs : s ∈ X.simplices) [Hs_ne : nonempty s]
         (x : α) (Hx : x ∉ vertices X),
        Y ≅ @stellar_subdivision _ _ X s Hs_ne x Hs Hx φ)
      ∨ (X ≅ Y)

def stellar_equiv
    (X : simplicial_complex α)
  : simplicial_complex α → Prop
:= relation.refl_trans_gen stellar_move X
infixl ` ≅ₛₜ `:50 := stellar_equiv

@[refl]
lemma stellar_equiv_refl
    (X : simplicial_complex α)
  : X ≅ₛₜ X
:= begin
  unfold stellar_equiv,
end

@[symm]
lemma stellar_equiv_symm
    (X Y : simplicial_complex α)
  : X ≅ₛₜ Y ↔ Y ≅ₛₜ X
:= begin
  unfold stellar_equiv,
  split;
  { apply relation.refl_trans_gen.symmetric,
    rw [←swap_eq_iff],
    simp only[stellar_move, function.swap],
    apply funext, intro K,
    apply funext, intro L,
    apply propext,
    split,
    
    intros L_move_K φ,
    specialize L_move_K φ,
    cases L_move_K,
    
    right, left,
    choose s Hs Hs_ne x Hx L_subdiv_K using L_move_K,
    use s, use Hs, use Hs_ne, use x, use Hx,
    assumption,
    
    cases L_move_K,
    left,
    choose t Ht Ht_ne y Hy K_subdiv_L using L_move_K,
    use t, use Ht, use Ht_ne, use y, use Hy,
    assumption,
    
    right, right,
    rw [simplicial_iso_symm],
    assumption,
    
    intros K_move_L φ,
    specialize K_move_L φ,
    cases K_move_L,
    
    right, left,
    choose s Hs Hs_ne x Hx K_subdiv_L using K_move_L,
    use s, use Hs, use Hs_ne, use x, use Hx,
    assumption,
    
    cases K_move_L,
    left,
    choose t Ht Ht_ne y Hy L_subdiv_K using K_move_L,
    use t, use Ht, use Ht_ne, use y, use Hy,
    assumption,
    
    right, right,
    rw [simplicial_iso_symm],
    assumption, }
end

@[trans]
lemma stellar_equiv_trans
    (X Y Z : simplicial_complex α)
  : X ≅ₛₜ Y → Y ≅ₛₜ Z → X ≅ₛₜ Z
:= begin
  unfold stellar_equiv,
  apply relation.transitive_refl_trans_gen,
end

lemma iso_stellar_equiv
    (X Y : simplicial_complex α)
  : X ≅ Y → X ≅ₛₜ Y
:= begin
  intro X_iso_Y,
  simp only[stellar_equiv],
  apply relation.refl_trans_gen.single,
  simp only[stellar_move],
  intro φ,
  right, right,
  assumption,
end

/-
# Properties of Stellar Subdivision
-/

lemma stellar_subdiv_distr_join_left
    (X Y : simplicial_complex α)
    (s : finset α) [nonempty s]
    (x : α)
    (φ : simplicial_coe (α × ℕ) α)
    (ψ : simplicial_coe ((α × ℕ) × ℕ) (α × ℕ))
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : σ(X, s; x, φ; sorry, sorry, sorry) ⋆ Y ≅ σ((X ⋆ Y), (s ⊔ₛ ∅); (x, 0), ψ; sorry, sorry, sorry)
:= begin
  unfold stellar_subdivision,

  rw simplicial_iso_symm
    (star_complement X s ∪
      φ[(φ[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s))] ⋆ Y)
    (star_complement (X ⋆ Y) (s ⊔ₛ ∅) ∪
      ψ[(ψ[(simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅))] ⋆ Lk((X ⋆ Y), (s ⊔ₛ ∅)))]),
  
  have H1 :
    ((star_complement (X ⋆ Y) (s ⊔ₛ ∅) ∪
      ψ[(ψ[(simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅))] ⋆ Lk((X ⋆ Y), (s ⊔ₛ ∅)))])
    ≅
    ((star_complement X s) ⋆ Y ∪
      ψ[(ψ[(simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅))] ⋆ Lk((X ⋆ Y), (s ⊔ₛ ∅)))])), from
  begin
    apply simplicial_iso_union_left,
    rw [simplicial_iso_symm],
    apply simplicial_iso_trans
      (star_complement X s ⋆ Y)
      (Y ⋆ star_complement X s),
    apply simplicial_join_comm,
    apply join_distl_star_complement,
    apply s_in_X,
  end,

  have H2 :
    (((star_complement X s) ⋆ Y ∪
      ψ[(ψ[(simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅))] ⋆ Lk((X ⋆ Y), (s ⊔ₛ ∅)))])
    ≅
    ((star_complement X s) ⋆ Y ∪
      ψ[(ψ[(simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅))] ⋆ (Lk(X, s) ⋆ Y))])), from
  begin
    apply simplicial_iso_union_right,
    apply coe_preserves_iso,
    apply simplicial_join_iso₂,

    apply simplicial_iso_refl,

    rw [simplicial_iso_symm],
    apply simplicial_iso_trans
      (Lk(X, s) ⋆ Y)
      (Y ⋆ (Lk(X, s))),
    apply simplicial_join_comm,
    apply join_distl_link,
    assumption,
  end,

  have H3 :
    (((star_complement X s) ⋆ Y ∪
      ψ[(ψ[(simplex {(x, 0)} ⋆ ∂(s ⊔ₛ ∅))] ⋆ (Lk(X, s) ⋆ Y))])
    ≅
    ((star_complement X s ∪
      (φ[(φ[(simplex {x} ⋆ ∂s)] ⋆ (Lk(X, s)))])) ⋆ Y)), from
  begin
    rw [simplicial_iso_symm],
    apply simplicial_iso_trans
      ((star_complement X s ∪
        (φ[(φ[(simplex {x} ⋆ ∂s)] ⋆ (Lk(X, s)))])) ⋆ Y)
      (((star_complement X s) ⋆ Y) ∪
        (φ[(φ[(simplex {x} ⋆ ∂s)] ⋆ (Lk(X, s)))] ⋆ Y)),
    apply simplicial_join_distr_union_right,

    apply simplicial_iso_union_right,
    sorry
  end,

  sorry
end

lemma stellar_subdiv_distr_join_right
    (X Y : simplicial_complex α)
    (t : finset α) [nonempty t]
    (y : α)
    (φ : simplicial_coe (α × ℕ) α)
    (ψ : simplicial_coe ((α × ℕ) × ℕ) (α × ℕ))
    (s_in_X : t ∈ Y.simplices)
    (x_nin_X : y ∉ vertices Y)
  : X ⋆ σ(Y, t; y, φ; sorry, sorry, sorry) ≅ σ((X ⋆ Y), (∅ ⊔ₛ t); (y, 1), ψ; sorry, sorry, sorry)
:= sorry

-- Lemma 3.1, p.10
lemma join_comm_stellar_equiv
    (X Y Z W : simplicial_complex α)
    (φ : simplicial_coe (α × ℕ) α)
  : X ≅ₛₜ Y → Z ≅ₛₜ W → (X ⋆ Z) ≅ₛₜ (Y ⋆ W)
:= begin
  intros X_eq_Y Z_eq_W,
  transitivity (Y ⋆ Z),

  unfold stellar_equiv at *,
  induction X_eq_Y with K L X_eq_K K_move_L H_ind,
  refl,

  apply @relation.refl_trans_gen.tail _ _ _ (K ⋆ Z) (L ⋆ Z),
  apply H_ind,

  simp only[stellar_move] at K_move_L ⊢,
  intro ψ,
  specialize K_move_L φ,
  cases K_move_L,

  left,
  choose t Ht Ht_ne y Hy K_subdiv_L using K_move_L,
  
  use (t ⊔ₛ ∅),
  have Ht_empty : (t ⊔ₛ ∅) ∈ (L ⋆ Z).simplices, from
  begin
    rw [simplicial_join_sep],
    split,
    assumption,
    apply simplicial_complex_empty_simplex,
  end,
  use Ht_empty,

  let Ht_empty_ne := @simplex_disjoint.nonempty.left _ _ t Ht_ne,
  use Ht_empty_ne,

  use (y, 0),
  have Hy_0 : (y, 0) ∉ vertices (L ⋆ Z), from
  begin
    rw [simplicial_join_vertices_mem_left],
    assumption,
  end,
  use Hy_0,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans
    (@stellar_subdivision _ _ (L ⋆ Z) (t ⊔ₛ ∅) Ht_empty_ne (y, 0) Ht_empty Hy_0 ψ)
    ((@stellar_subdivision _ _ L t Ht_ne y Ht Hy φ) ⋆ Z),
  rw [simplicial_iso_symm],
  apply @stellar_subdiv_distr_join_left _ _ _ _ _ Ht_ne;
  assumption,

  apply simplicial_join_iso_left,
  rw [simplicial_iso_symm],
  assumption,

  cases K_move_L,
  right, left,
  choose s Hs Hs_ne x Hx L_subdiv_K using K_move_L,

  use (s ⊔ₛ ∅),
  have Hs_empty : (s ⊔ₛ ∅) ∈ (K ⋆ Z).simplices, from
  begin
    rw [simplicial_join_sep],
    split,
    assumption,
    apply simplicial_complex_empty_simplex,
  end,
  use Hs_empty,

  let Hs_empty_ne := @simplex_disjoint.nonempty.left _ _ s Hs_ne,
  use Hs_empty_ne,

  use (x, 0),
  have Hx_0 : (x, 0) ∉ vertices (K ⋆ Z), from
  begin
    rw [simplicial_join_vertices_mem_left],
    assumption,
  end,
  use Hx_0,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans
    (@stellar_subdivision _ _ (K ⋆ Z) (s ⊔ₛ ∅) Hs_empty_ne (x, 0) Hs_empty Hx_0 ψ)
    ((@stellar_subdivision _ _ K s Hs_ne x Hs Hx φ) ⋆ Z),
  rw [simplicial_iso_symm],
  apply @stellar_subdiv_distr_join_left _ _ _ _ _ Hs_ne;
  assumption,

  apply simplicial_join_iso_left,
  rw [simplicial_iso_symm],
  assumption,

  right, right,
  apply simplicial_join_iso_left,
  assumption,

  unfold stellar_equiv at *,
  induction Z_eq_W with K L Z_eq_K K_move_L H_ind,
  refl,

  apply @relation.refl_trans_gen.tail _ _ _ (Y ⋆ K) (Y ⋆ L),
  apply H_ind,

  simp only[stellar_move] at K_move_L ⊢,
  intro ψ,
  specialize K_move_L φ,
  cases K_move_L,

  left,
  choose t Ht Ht_ne y Hy K_subdiv_L using K_move_L,

  use (∅ ⊔ₛ t),
  have Ht_empty : (∅ ⊔ₛ t) ∈ (Y ⋆ L).simplices, from
  begin
    rw [simplicial_join_sep],
    split,
    apply simplicial_complex_empty_simplex,
    assumption,
  end,
  use Ht_empty,

  let Ht_empty_ne := @simplex_disjoint.nonempty.right _ _ t Ht_ne,
  use Ht_empty_ne,

  use (y, 1),
  have Hy_1 : (y, 1) ∉ vertices (Y ⋆ L), from
  begin
    rw [simplicial_join_vertices_mem_right],
    assumption,
  end,
  use Hy_1,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans
    (@stellar_subdivision _ _ (Y ⋆ L) (∅ ⊔ₛ t) Ht_empty_ne (y, 1) Ht_empty Hy_1 ψ)
    (Y ⋆ @stellar_subdivision _ _ L t Ht_ne y Ht Hy φ),
  rw [simplicial_iso_symm],
  apply @stellar_subdiv_distr_join_right _ _ _ _ _ Ht_ne;
  assumption,

  apply simplicial_join_iso_right,
  rw [simplicial_iso_symm],
  assumption,

  cases K_move_L,
  right, left,
  choose s Hs Hs_ne x Hx L_subdiv_K using K_move_L,

  use (∅ ⊔ₛ s),
  have Hs_empty : (∅ ⊔ₛ s) ∈ (Y ⋆ K).simplices, from
  begin
    rw [simplicial_join_sep],
    split,
    apply simplicial_complex_empty_simplex,
    assumption,
  end,
  use Hs_empty,

  let Hs_empty_ne := @simplex_disjoint.nonempty.right _ _ s Hs_ne,
  use Hs_empty_ne,

  use (x, 1),
  have Hx_1 : (x, 1) ∉ vertices (Y ⋆ K), from
  begin
    rw [simplicial_join_vertices_mem_right],
    assumption,
  end,
  use Hx_1,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans
    (@stellar_subdivision _ _ (Y ⋆ K) (∅ ⊔ₛ s) Hs_empty_ne (x, 1) Hs_empty Hx_1 ψ)
    (Y ⋆ @stellar_subdivision _ _ K s Hs_ne x Hs Hx φ),
  rw [simplicial_iso_symm],
  apply @stellar_subdiv_distr_join_right _ _ _ _ _ Hs_ne;
  assumption,

  apply simplicial_join_iso_right,
  rw [simplicial_iso_symm],
  assumption,

  right, right,
  apply simplicial_join_iso_right,
  assumption,
end