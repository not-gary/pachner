import tactic          -- standard proof tactics
import data.set.basic        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset.basic     -- type-level finite sets
import .simplicial_complex
import .simplicial_subcomplex
import .simplicial_map

variables {α β : Type*}
variables [decidable_eq α] [decidable_eq β]

def stellar_subdivision
    (X : simplicial_complex α)
    (s : finset α) [nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : simplicial_complex α
:= (X\St(X, s) s_in_X) ∪ (π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]
notation `σ(` X `, ` s `, ` x `; ` s_ne `, ` s_in_X `, ` x_nin_X `)` := @stellar_subdivision _ _ X s s_ne x s_in_X x_nin_X

instance stellar_subdivision.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : fintype (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices
:= sorry

instance stellar_subdivision.fintype_converse
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    [fintype (σ(X, s, x; s_ne, s_in_X, x_nin_X)).simplices]
  : fintype X.simplices
:= sorry

lemma stellar_subdiv_preserves_dim
    (X : simplicial_complex α) [X_fin : fintype X.simplices]
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : @dim_of_complex α X = @dim_of_complex α (σ(X, s, x; s_ne, s_in_X, x_nin_X))
      (@stellar_subdivision.fintype α _ X X_fin s s_ne x s_in_X x_nin_X)
:= sorry

@[simp]
def stellar_move
  : simplicial_complex α → simplicial_complex α → Prop
:= λ X Y : simplicial_complex α,
      (∃ (t : finset α) (Ht : t ∈ Y.simplices) [Ht_ne : nonempty t]
        (y : α) (Hy : y ∉ vertices Y),
        X ≅ @stellar_subdivision _ _ Y t Ht_ne y Ht Hy)
      ∨
      (∃ (s : finset α) (Hs : s ∈ X.simplices) [Hs_ne : nonempty s]
         (x : α) (Hx : x ∉ vertices X),
        Y ≅ @stellar_subdivision _ _ X s Hs_ne x Hs Hx)
      ∨ (X ≅ Y)

instance stellar_move.fintype
    (X Y : simplicial_complex α) [fintype X.simplices]
    (X_move_Y : stellar_move X Y)
  : fintype Y.simplices
:= sorry

lemma stellar_move_preserves_dim
    (X Y : simplicial_complex α) [X_fin : fintype X.simplices]
    (X_move_Y : stellar_move X Y)
  : @dim_of_complex α X = @dim_of_complex α Y (@stellar_move.fintype α _ X Y X_fin X_move_Y)
:= sorry

def stellar_equiv
    (X : simplicial_complex α)
  : simplicial_complex α → Prop
:= relation.refl_trans_gen stellar_move X
infixl ` ≅ₛₜ `:50 := stellar_equiv

instance stellar_equiv.fintype
    (X Y : simplicial_complex α) [fintype X.simplices]
    (X_eq_Y : X ≅ₛₜ Y)
  : fintype Y.simplices
:= sorry

lemma stellar_equiv_preserves_dim
    (X Y : simplicial_complex α) [X_fin : fintype X.simplices]
    (X_eq_Y : X ≅ₛₜ Y)
  : @dim_of_complex α X = @dim_of_complex α Y (@stellar_equiv.fintype α _ X Y X_fin X_eq_Y)
:= sorry

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
    
    intro L_move_K,
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
    
    intro K_move_L,
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

lemma stellar_equiv_neg_trans
    (X Y Z : simplicial_complex α)
  : X ≅ₛₜ Y → ¬Y ≅ₛₜ Z → ¬X ≅ₛₜ Z
:= begin
  intros X_eq_Y Y_neq_Z,
  revert Y_neq_Z,
  contrapose,
  simp only [not_not],
  intro X_eq_Z,
  rw [stellar_equiv_symm] at X_eq_Y,
  revert X_eq_Y X_eq_Z,
  apply stellar_equiv_trans,
end

lemma stellar_equiv_iso
    (X Y : simplicial_complex α)
    (Z W : simplicial_complex β)
  : X ≅ Z → Y ≅ W → X ≅ₛₜ Y → Z ≅ₛₜ W
:= sorry

lemma stellar_equiv_preserves_iso
    (X Y : simplicial_complex α)
  : X ≅ Y → X ≅ₛₜ Y
:= begin
  intro X_iso_Y,
  simp only[stellar_equiv],
  apply relation.refl_trans_gen.single,
  simp only[stellar_move],
  right, right,
  assumption,
end

lemma simplicial_join_stellar_equiv
    (X Y Z W : simplicial_complex α)
  : X ≅ₛₜ Z → Y ≅ₛₜ W → X ⋆ Y ≅ₛₜ Z ⋆ W
:= sorry

lemma simplicial_join_stellar_equiv_left
    (X Y Z : simplicial_complex α)
  : X ≅ₛₜ Y → X ⋆ Z ≅ₛₜ Y ⋆ Z
:= sorry

lemma simplicial_join_stellar_equiv_right
    (X Y Z : simplicial_complex α)
  : X ≅ₛₜ Y → Z ⋆ X ≅ₛₜ Z ⋆ Y
:= sorry

/-
# Properties of Stellar Subdivision
-/

-- TODO: borked
lemma stellar_subdiv_distr_join_left
    (X Y : simplicial_complex α)
    (s : finset α) [nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : σ(X, s, x; sorry, sorry, sorry) ⋆ Y ≅ σ((X ⋆ Y), (s ⊔ₛ ∅), (x, 0); sorry, sorry, sorry)
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
    apply simplicial_join_distr_union_right_iso,

    apply simplicial_iso_union_right,
    sorry
  end,

  sorry
end

lemma stellar_subdiv_distr_join_right
    (X Y : simplicial_complex α)
    (t : finset α) [nonempty t]
    (y : α)
    (s_in_X : t ∈ Y.simplices)
    (x_nin_X : y ∉ vertices Y)
  : X ⋆ σ(Y, t, y; sorry, sorry, sorry) ≅ σ((X ⋆ Y), (∅ ⊔ₛ t), (y, 1); sorry, sorry, sorry)
:= sorry

-- Lemma 3.1, p.10
lemma join_comm_stellar_equiv
    (X Y Z W : simplicial_complex α)
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
    (@stellar_subdivision _ _ (L ⋆ Z) (t ⊔ₛ ∅) Ht_empty_ne (y, 0) Ht_empty Hy_0)
    ((@stellar_subdivision _ _ L t Ht_ne y Ht Hy) ⋆ Z),
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
    (@stellar_subdivision _ _ (K ⋆ Z) (s ⊔ₛ ∅) Hs_empty_ne (x, 0) Hs_empty Hx_0)
    ((@stellar_subdivision _ _ K s Hs_ne x Hs Hx) ⋆ Z),
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
    (@stellar_subdivision _ _ (Y ⋆ L) (∅ ⊔ₛ t) Ht_empty_ne (y, 1) Ht_empty Hy_1)
    (Y ⋆ @stellar_subdivision _ _ L t Ht_ne y Ht Hy),
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
    (@stellar_subdivision _ _ (Y ⋆ K) (∅ ⊔ₛ s) Hs_empty_ne (x, 1) Hs_empty Hx_1)
    (Y ⋆ @stellar_subdivision _ _ K s Hs_ne x Hs Hx),
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

lemma stellar_subdiv_link_of_star_complement
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : t ∈ (X\St(X, s) s_in_X).simplices →
      t ∉ ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices →
        (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry).simplices = (Lk(X, t) sorry).simplices
:= sorry

lemma stellar_subdiv_link_of_star
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : (∃ (t₁ t₂ t₃ : finset α),
        nonempty t₁ ∧ t₁ ∈ (Lk(X, s) s_in_X).simplices ∧
        nonempty t₂ ∧ t₂ ∈ (∂s).simplices ∧
        nonempty t₃ ∧ t₃ ∈ (@simplex α {x}).simplices ∧
        t = t₁ ∪ t₂ ∪ t₃) →
      (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry).simplices = {∅}
:= sorry

lemma stellar_subdiv_link_of_link_barycenter
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : (∃ (t₁ t₂ : finset α),
        nonempty t₁ ∧ t₁ ∈ (Lk(X, s) s_in_X).simplices ∧
        nonempty t₂ ∧ t₂ ∈ (@simplex α {x}).simplices ∧
        t = t₁ ∪ t₂) →
      (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry).simplices = (∂s).simplices
:= sorry

lemma stellar_subdiv_link_of_boundary_barycenter
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : (∃ (t₁ t₂ : finset α),
        nonempty t₁ ∧ t₁ ∈ (@simplex α {x}).simplices ∧
        nonempty t₂ ∧ t₂ ∈ (∂s).simplices ∧
        t = t₁ ∪ t₂) →
      (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry).simplices = (Lk(X, s) s_in_X).simplices
:= sorry

lemma stellar_subdiv_link_of_barycenter
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), {x}) sorry).simplices = ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices
:= sorry

lemma star_boundary_is_join
    (X : simplicial_complex α)
    (s : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : ((X\St(X, s) s_in_X) ∩ (π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices
      = ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices
:= sorry

lemma stellar_subdiv_anticomm_link_left_ac
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ (star_complement X s s_in_X).simplices) →
        (t ∪ u ∈ (star_complement X s s_in_X).simplices) →
          (t ∩ u = ∅) →
            u ∈ (σ((Lk(X, t) t_in_X), s\t, x; sorry, sorry, sorry)).simplices
:= begin
  intros u u_in_star_comp tu_in_star_comp tu_disj,
  simp only[link, stellar_subdivision, star_complement, simplicial_union] at u_in_star_comp tu_in_star_comp ⊢,
  simp only[set.mem_union, set.mem_sep_iff] at u_in_star_comp tu_in_star_comp ⊢,

  choose u_in_X s_nss_u using u_in_star_comp,
  choose tu_in_X s_nss_tu using tu_in_star_comp,

  have st_nss_u : ¬(s\t ⊆ u), from
  begin
    revert s_nss_tu,
    contrapose,
    simp only[not_not],
    intro st_ss_u,

    apply @finset.union_subset_left _ _ s t,
    rw [←finset.union_sdiff_self_eq_union, finset.union_sdiff_symm],
    apply finset.union_subset_union_right,
    assumption,
  end,
  
  left, split, split,
  assumption,
  split; assumption,
  assumption,
end

lemma stellar_subdiv_anticomm_link_left_ad
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ (star_complement X s s_in_X).simplices) →
        (t ∪ u ∈ ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices) →
          (t ∩ u = ∅) →
            u ∈ (σ((Lk(X, t) t_in_X), s\t, x; sorry, sorry, sorry)).simplices
:= begin
  intros u u_in_star_comp tu_in_join tu_disj,
  simp only[link, stellar_subdivision, star_complement, simplicial_union] at u_in_star_comp tu_in_join ⊢,
  simp only[set.mem_union, set.mem_sep_iff] at u_in_star_comp ⊢,
  choose u_in_X s_nss_u using u_in_star_comp,

  rw [join_proj_disj_union_mem] at tu_in_join,
  choose t'₂ t'₂_in_join u'₂ u'₂_in_join t₁ t₁_in_link u₁ u₁_in_link tu_decomp using tu_in_join,
  choose t_decomp u_decomp tu_in_join tu_in_link using tu_decomp,

  simp only[set.mem_sep_iff] at t₁_in_link u₁_in_link tu_in_link,
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link,
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link,
  choose tu₁_in_X stu₁_in_X stu₁_disj using tu_in_link,

  rw [join_proj_mem] at t'₂_in_join u'₂_in_join,
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'₂_in_join,
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'₂_in_join,
  subst u'_decomp,
  subst t'_decomp,

  rw [simplex_boundary_mem_iff_subset] at u₂_in_bd t₂_in_bd,

  have u₃_empty : u₃ = ∅, by sorry,
  have t₃_empty : t₃ = ∅, by sorry,
  subst u₃,
  subst t₃,
  simp only[finset.empty_union] at u_decomp t_decomp tu_in_join,
  rw [finset.union_comm] at u_decomp t_decomp,

  left, split, split,
  exact u_in_X,
  split,
  
  rw [u_decomp, t_decomp],
  apply X.subset_closed (t₁ ∪ u₁ ∪ s),
  rw [finset.union_comm],
  exact stu₁_in_X,
  
  have tu_ss_s : t₂ ∪ u₂ ⊆ s, from
  begin
    apply finset.union_subset;
    rw [finset.ssubset_iff_subset_ne] at t₂_in_bd u₂_in_bd;
    sorry,
  end,
  rw [finset.union_assoc, finset.union_comm u₁ u₂, ←finset.union_assoc t₂, finset.union_comm (t₂ ∪ u₂), ←finset.union_assoc],
  apply finset.union_subset_union_right,
  exact tu_ss_s,
  
  exact tu_disj,
  
  rw [t_decomp, finset.sdiff_union_distrib],
  have st₁_sdiff_ident : s \ t₁ = s, from
  begin
    apply finset.sdiff_eq_self_of_disjoint,
    rw [finset.disjoint_iff_inter_eq_empty],
    exact st₁_disj,
  end,
  
  rw [st₁_sdiff_ident, finset.inter_sdiff, finset.inter_self],
  rw [join_proj_disj_union_mem] at tu_in_join,
  choose t₃ t₃_in_barycenter u₃ u₃_in_barycenter t₂ t₂_in_bd u₂ u₂_in_bd tu₂_decomp using tu_in_join,
  choose t₂_decomp u₂_decomp tu₃_in_barycenter tu₂_in_bd using tu₂_decomp,
  
  have u₃_empty : u₃ = ∅, by sorry,
  have t₃_empty : t₃ = ∅, by sorry,
  subst u₃,
  subst t₃,
  rw [finset.empty_union] at t₂_decomp u₂_decomp tu₃_in_barycenter,
  rw [←u₂_decomp, ←t₂_decomp, simplex_boundary_mem_iff_subset] at tu₂_in_bd,

  subst u₂_decomp,
  subst t₂_decomp,
  
  have u₂_ss_st₂_sdiff : u₂ ⊂ s \ t₂, from
  begin
    rw [finset.ssubset_iff_subset_ne] at tu₂_in_bd ⊢,
    choose tu₂_ss_s tu₂_ne_s using tu₂_in_bd,
    split,

    rw [finset.subset_sdiff],
    split,
    apply @finset.subset.trans _ _ (t₂ ∪ u₂),
    apply finset.subset_union_right,
    exact tu₂_ss_s,
    rw [finset.disjoint_iff_inter_eq_empty, ←finset.subset_empty],
    rw [←tu_disj, t_decomp, u_decomp],
    rw [finset.inter_comm],
    apply finset.inter_subset_inter;
    apply finset.subset_union_right,

    rw [finset.union_comm] at tu₂_ne_s,
    have H1 : s = s ∪ t₂, from
    begin
      symmetry,
      rw [finset.union_eq_left_iff_subset],
      rw [finset.ssubset_def] at t₂_in_bd,
      tauto,
    end,
    rw [H1] at tu₂_ne_s,
    revert tu₂_ne_s,
    contrapose,
    simp only[not_ne_iff],
    rw [←@finset.sdiff_union_self_eq_union _ _ s],
    exact congr_arg (λ (a : finset α), a ∪ t₂),
  end,

  rw [←finset.lt_iff_ssubset, finset.partial_order.lt_iff_le_not_le, finset.le_iff_subset, finset.le_iff_subset] at u₂_ss_st₂_sdiff,
  choose u₂_ss_st₂ st₂_nss_u₂ using u₂_ss_st₂_sdiff,
  
  rw [finset.not_subset] at st₂_nss_u₂ ⊢,
  choose y y_in_st₂ y_nin_u₂ using st₂_nss_u₂,
  use y, use y_in_st₂,
  rw [u_decomp, finset.not_mem_union],
  split,
  
  rw [finset.eq_empty_iff_forall_not_mem] at su₁_disj,
  specialize su₁_disj y,
  simp only[finset.mem_inter, not_and_distrib] at su₁_disj,
  cases su₁_disj with contra y_nin_u₁,
  
  have H : y ∈ s, from
  begin
    apply @finset.mem_of_subset _ (s \ t₂),
    apply finset.sdiff_subset,
    exact y_in_st₂,
  end,
  contradiction,
  
  exact y_nin_u₁,
  exact y_nin_u₂,
end

lemma stellar_subdiv_anticomm_link_left_bc
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices) →
        (t ∪ u ∈ (star_complement X s s_in_X).simplices) →
          (t ∩ u = ∅) →
            u ∈ (σ((Lk(X, t) t_in_X), s\t, x; sorry, sorry, sorry)).simplices
:= begin
  intros u u_in_join tu_in_star_comp tu_disj,
  simp only[link, stellar_subdivision, star_complement, simplicial_union] at u_in_join tu_in_star_comp ⊢,
  simp only[set.mem_union, set.mem_sep_iff] at tu_in_star_comp ⊢,
  choose tu_in_X s_nss_tu using tu_in_star_comp,

  rw [join_proj_mem] at u_in_join,
  choose u'₂ u'₂_in_join u₁ u₁_in_link u_decomp using u_in_join,

  simp only[set.mem_sep_iff] at u₁_in_link,
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link,

  rw [join_proj_mem] at u'₂_in_join,
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp using u'₂_in_join,
  subst u'_decomp,

  left, split, split,
  apply X.subset_closed (t ∪ u),
  assumption,
  apply finset.subset_union_right,
  
  split; assumption,
  
  revert s_nss_tu,
  contrapose,
  simp only[not_not],
  intro st_ss_u,

  apply @finset.union_subset_left _ _ s t,
  rw [←finset.union_sdiff_self_eq_union, finset.union_sdiff_symm],
  apply finset.union_subset_union_right,
  assumption,
end

lemma stellar_subdiv_anticomm_link_left_bd
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices) →
        (t ∪ u ∈ ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices) →
          (t ∩ u = ∅) →
            u ∈ (σ((Lk(X, t) t_in_X), s\t, x; sorry, sorry, sorry)).simplices
:= begin
  intros u u_in_join tu_in_join tu_disj,
  simp only[link, stellar_subdivision, star_complement, simplicial_union] at u_in_join tu_in_join ⊢,

  rw [join_proj_disj_union_mem] at tu_in_join,
  choose t'₂ t'₂_in_join u'₂ u'₂_in_join t₁ t₁_in_link u₁ u₁_in_link tu_decomp using tu_in_join,
  choose t_decomp u_decomp tu_in_join tu_in_link using tu_decomp,

  simp only[set.mem_sep_iff] at t₁_in_link u₁_in_link tu_in_link,
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link,
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link,
  choose tu₁_in_X stu₁_in_X stu₁_disj using tu_in_link,

  rw [join_proj_disj_union_mem] at tu_in_join,
  choose t₃ t₃_in_barycenter u₃ u₃_in_barycenter t₂ t₂_in_bd u₂ u₂_in_bd tu₂_decomp using tu_in_join,
  choose t₂_decomp u₂_decomp tu₃_in_barycenter tu₂_in_bd using tu₂_decomp,
  
  have t₃_empty : t₃ = ∅, by sorry,
  subst t₃,
  simp only[finset.empty_union] at t₂_decomp u₂_decomp tu₃_in_barycenter,
  rw [simplex_boundary_mem_iff_subset] at tu₂_in_bd u₂_in_bd t₂_in_bd,
  rw [t₂_decomp] at *,
  rw [u₂_decomp] at *,

  right,
  
  rw [join_proj_mem],
  have tu₂_disj : t₂ ∩ u₂ = ∅, from
  begin
    rw [←finset.subset_empty],
    apply @finset.subset.trans _ _ (t ∩ u),
    apply finset.inter_subset_inter,

    rw [t_decomp],
    apply @finset.subset_union_left _ _ t₂ t₁,

    rw [u_decomp, finset.union_assoc, finset.union_comm, finset.union_assoc],
    apply @finset.subset_union_left _ _ u₂ (u₁ ∪ u₃),

    rw [finset.subset_empty],
    assumption,
  end,

  have st₁_sdiff_ident : s \ t₁ = s, from
  begin
    apply finset.sdiff_eq_self_of_disjoint,
    rw [finset.disjoint_iff_inter_eq_empty],
    assumption,
  end,

  have u₂_ss_st₂_sdiff : u₂ ⊂ s \ t₂, from
  begin
    rw [finset.ssubset_iff_subset_ne] at tu₂_in_bd ⊢,
    choose tu₂_ss_s tu₂_ne_s using tu₂_in_bd,
    split,

    rw [finset.subset_sdiff],
    split,
    apply @finset.subset.trans _ _ (t₂ ∪ u₂),
    apply finset.subset_union_right,
    assumption,
    rw [finset.disjoint_iff_inter_eq_empty, ←finset.subset_empty],
    rw [←tu_disj, t_decomp, u_decomp],
    rw [finset.inter_comm],
    apply finset.inter_subset_inter,
    apply @finset.subset_union_left _ _ t₂ t₁,
    rw [finset.union_assoc, finset.union_comm, finset.union_assoc],
    apply @finset.subset_union_left _ _ u₂ (u₁ ∪ u₃),

    rw [finset.union_comm] at tu₂_ne_s,
    have H1 : s = s ∪ t₂, from
    begin
      symmetry,
      rw [finset.union_eq_left_iff_subset],
      rw [finset.ssubset_def] at t₂_in_bd,
      sorry,
    end,
    rw [H1] at tu₂_ne_s,
    revert tu₂_ne_s,
    contrapose,
    simp only[not_ne_iff],
    rw [←@finset.sdiff_union_self_eq_union _ _ s],
    exact congr_arg (λ (a : finset α), a ∪ t₂),
  end,

  have u₂_ss_st : u₂ ⊂ s \ t, from
  begin
    rw [t_decomp, finset.sdiff_union_distrib, st₁_sdiff_ident, finset.inter_comm, finset.inter_sdiff, finset.inter_self],
    assumption,
  end,

  use (u₃ ∪ u₂), split,

  rw [join_proj_disj_union_mem],
  use u₃, split, assumption,
  use ∅, split, apply simplicial_complex_empty_simplex,
  use ∅, split, apply simplicial_complex_empty_simplex,
  use u₂, split, rw [simplex_boundary_mem_iff_subset], assumption,
  
  split, symmetry, apply finset.union_empty,
  split, symmetry, apply finset.empty_union,
  split, rw [finset.union_empty], assumption,
  
  rw [finset.empty_union, simplex_boundary_mem_iff_subset],
  assumption,
  
  use u₁, split, split, split,
  assumption,

  split,
  rw [t_decomp],
  apply X.subset_closed (s ∪ t₁ ∪ u₁),
  rw [finset.union_assoc],
  assumption,
  simp only[finset.union_assoc],
  apply finset.union_subset_union_left,
  rw [finset.ssubset_def] at t₂_in_bd,
  choose t₂_ss_s s_nss_t₂ using t₂_in_bd,
  assumption,
  
  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ (t ∩ u),
  apply finset.inter_subset_inter_left,
  rw [u_decomp, finset.union_comm],
  apply finset.subset_union_left,
  rw [finset.subset_empty],
  assumption,
  
  split, split,
  apply X.subset_closed (s ∪ t₁ ∪ u₁),
  rw [finset.union_assoc],
  assumption,
  apply @finset.subset.trans _ _ (s ∪ u₁),
  apply finset.union_subset_union_left,
  apply finset.sdiff_subset,
  rw [finset.union_assoc, finset.union_comm t₁ u₁, ←finset.union_assoc],
  apply finset.subset_union_left,
  
  split,
  apply X.subset_closed (s ∪ t₁ ∪ u₁),
  rw [finset.union_assoc],
  assumption,
  rw [t_decomp, finset.sdiff_union_distrib, st₁_sdiff_ident, finset.inter_comm],
  rw [finset.inter_sdiff, finset.inter_self, ←finset.union_assoc, finset.union_assoc t₂ t₁],
  rw [finset.union_comm t₁ (s \ t₂), ←finset.union_assoc],
  rw [finset.union_assoc, finset.union_assoc s t₁],
  apply finset.union_subset_union_left,
  apply finset.subset_of_eq,
  apply finset.union_sdiff_of_subset,
  rw [finset.ssubset_def] at t₂_in_bd,
  choose t₂_ss_s s_nss_t₂ using t₂_in_bd,
  assumption,
  
  rw [finset.inter_distrib_left, finset.inter_comm, finset.sdiff_inter_self, finset.empty_union],
  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ (t ∩ u),
  apply finset.inter_subset_inter_left,
  rw [u_decomp],
  apply finset.subset_union_right,
  rw [finset.subset_empty],
  assumption,
  
  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ (s ∩ u₁),
  apply finset.inter_subset_inter_right,
  apply finset.sdiff_subset,
  rw [finset.subset_empty],
  assumption,
  
  assumption,
end

lemma stellar_subdiv_anticomm_link_left
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry).simplices ⊆ (σ((Lk(X, t) t_in_X), s\t, x; sorry, sorry, sorry)).simplices
:= begin
  simp only[stellar_subdivision, simplicial_union],
  simp only[set.subset_def],
  intros u u_in_link,
  simp only[link, set.mem_sep_iff] at u_in_link,
  choose u_in_subdiv tu_in_subdiv tu_disj using u_in_link,

  cases u_in_subdiv with u_in_star_comp u_in_join; -- Cases A, B resp.
  cases tu_in_subdiv with tu_in_star_comp tu_in_join, -- Cases C, D resp.

  apply stellar_subdiv_anticomm_link_left_ac; assumption,
  apply stellar_subdiv_anticomm_link_left_ad; assumption,
  apply stellar_subdiv_anticomm_link_left_bc; assumption,
  apply stellar_subdiv_anticomm_link_left_bd; assumption,
end

lemma stellar_subdiv_anticomm_link_right_e
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ (@star_complement _ _ (Lk(X, t) t_in_X) (s \ t) sorry sorry).simplices) →
        (u ∈ (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry).simplices)
:= begin
  intros u u_in_star_comp,
  simp only[link, star_complement, stellar_subdivision, simplicial_union] at u_in_star_comp ⊢,
  simp only[set.mem_union, set.mem_sep_iff] at u_in_star_comp ⊢,
  choose u_in_link st_nss_u using u_in_star_comp,
  choose u_in_X tu_in_X tu_disj using u_in_link,

  split, left, split,
  assumption,
  revert st_nss_u,
  contrapose,
  simp only[not_not],
  intro s_ss_u,
  apply @finset.subset.trans _ _ s,
  apply finset.sdiff_subset,
  assumption,
  
  split, left, split,
  assumption,
  
  simp only[finset.subset_iff, not_forall] at st_nss_u ⊢,
  choose y y_in_st y_nin_u using st_nss_u,
  simp only[finset.mem_sdiff] at y_in_st,
  choose y_in_s y_nin_t using y_in_st,
  use y, split, assumption,
  simp only[finset.mem_union, not_or_distrib],
  split; assumption,
  
  assumption,
end

lemma stellar_subdiv_anticomm_link_right_f
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : ∀ (u : finset α),
      (u ∈ ((π₁ sorry)[((π₁ sorry)[(simplex {x}) ⋆ ∂(s \ t)]) ⋆ (Lk(Lk(X, t) t_in_X, s \ t) sorry)]).simplices) →
        (u ∈ (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry).simplices)
:= begin
  intros u u_in_join,
  simp only[link, star_complement, stellar_subdivision, simplicial_union] at u_in_join ⊢,
  simp only[set.mem_union, set.mem_sep_iff],

  rw [join_proj_mem] at u_in_join,
  choose u'₂ u'₂_in_join u₁ u₁_in_link u_decomp using u_in_join,
  rw [join_proj_mem] at u'₂_in_join,
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'₂_decomp using u'₂_in_join,
  subst u'₂_decomp,

  let u₁_in_link := u₁_in_link,
  let u₂_in_bd' := u₂_in_bd,

  rw [simplex_boundary_mem_iff_subset] at u₂_in_bd,
  simp only[set.mem_sep_iff] at u₁_in_link,
  choose u₁_in_t_link stu₁_in_t_link stu₁_disj using u₁_in_link,
  choose u₁_in_X tu₁_in_X tu₁_disj using u₁_in_t_link,
  choose stu₁_in_X tstu₁_in_X tstu₁_disj using stu₁_in_t_link,

  rw [join_proj_mem] at t_in_star_bd,
  choose t₁ t₁_in_link t₂ t₂_in_bd t_decomp using t_in_star_bd,

  let t₁_in_link := t₁_in_link,
  let t₁_in_bd' := t₂_in_bd,

  simp only[link, set.mem_sep_iff] at t₁_in_link,
  choose t₁_in_X st₁_in_X st₁_disj using t₁_in_link,

  rw [simplex_boundary_mem_iff_subset] at t₂_in_bd,

  have st₁_sdiff_ident : s \ t₁ = s, from
  begin
    apply finset.sdiff_eq_self_of_disjoint,
    rw [finset.disjoint_iff_inter_eq_empty],
    assumption,
  end,

  split, right,
  rw [join_proj_mem],

  use (u₃ ∪ u₂), split,
  rw [join_proj_mem],
  use u₃, split, assumption,
  use u₂, split,
  rw [simplex_boundary_mem_iff_subset],
  apply @finset.ssubset_of_ssubset_of_subset _ _ (s \ t),
  assumption,
  apply finset.sdiff_subset,
  refl,
  
  use u₁, split,
  simp only[set.mem_sep_iff],
  split, assumption,
  split,
  apply X.subset_closed (t ∪ (s \ t ∪ u₁)),
  assumption,
  rw [←finset.union_assoc, finset.union_sdiff_self_eq_union, finset.union_assoc],
  apply finset.subset_union_right,

  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ ((t ∪ (s \ t)) ∩ u₁),
  rw [finset.union_sdiff_self_eq_union, finset.inter_distrib_right],
  apply finset.subset_union_right,
  rw [finset.subset_empty, finset.inter_distrib_right, finset.union_eq_empty_iff],
  split; assumption,

  assumption,
  
  split, right,
  rw [join_proj_disj_union_mem],

  use t₂, split,
  rw [join_proj_mem],
  use ∅, split, apply simplicial_complex_empty_simplex,
  use t₂, split,
  assumption,
  symmetry,
  apply finset.empty_union,
  
  use (u₃ ∪ u₂), split,
  rw [join_proj_mem],
  use u₃, split, assumption,
  use u₂, split,
  rw [simplex_boundary_mem_iff_subset],
  apply @finset.ssubset_of_ssubset_of_subset _ _ (s \ t),
  assumption,
  apply finset.sdiff_subset,
  refl,

  use t₁, split, assumption,

  use u₁, split,
  simp only[set.mem_sep_iff],
  split, assumption,
  split,
  apply X.subset_closed (t ∪ (s \ t ∪ u₁)),
  assumption,
  rw [←finset.union_assoc, finset.union_sdiff_self_eq_union, finset.union_assoc],
  apply finset.subset_union_right,

  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ ((t ∪ (s \ t)) ∩ u₁),
  rw [finset.union_sdiff_self_eq_union, finset.inter_distrib_right],
  apply finset.subset_union_right,
  rw [finset.subset_empty, finset.inter_distrib_right, finset.union_eq_empty_iff],
  split; assumption,

  split,
  rw [finset.union_comm],
  assumption,

  split, assumption,

  split,
  rw [join_proj_disj_union_mem],
  use ∅, split, apply simplicial_complex_empty_simplex,
  use u₃, split, assumption,
  use t₂, split,
  assumption,
  use u₂, split,
  rw [simplex_boundary_mem_iff_subset],
  apply @finset.ssubset_of_ssubset_of_subset _ _ (s \ t),
  assumption,
  apply finset.sdiff_subset,

  split,
  symmetry,
  apply finset.empty_union,

  split, refl,
  
  split,
  rw [finset.empty_union],
  assumption,

  rw [simplex_boundary_mem_iff_subset],
  rw [t_decomp, finset.sdiff_union_distrib, st₁_sdiff_ident, finset.inter_sdiff, finset.inter_self] at u₂_in_bd,
  rw [finset.ssubset_iff_subset_ne] at t₂_in_bd u₂_in_bd ⊢,
  choose t₂_ss_s t₂_ne_s using t₂_in_bd,
  choose u₂_ss_st₂ u₂_ne_st₂ using u₂_in_bd,
  split,
  apply finset.union_subset,
  assumption,
  apply @finset.subset.trans _ _ (s \ t₂),
  assumption,
  apply finset.sdiff_subset,

  have st₂u₂_ne : s \ (t₂ ∪ u₂) ≠ ∅, from
  begin
    rw [ne.def, finset.sdiff_union_distrib, ←finset.sdiff_sdiff_left', finset.sdiff_eq_empty_iff_subset],
    rw [←finset.le_iff_subset] at u₂_ss_st₂ ⊢,
    have H : u₂ < s \ t₂, from
    begin
      rw [lt_iff_le_and_ne],
      split; assumption,
    end,
    rw [finset.partial_order.lt_iff_le_not_le] at H,
    choose H1 H2 using H,
    assumption,
  end,

  rw [ne.def, finset.ext_iff, not_forall],
  rw [ne.def, finset.eq_empty_iff_forall_not_mem, not_forall] at st₂u₂_ne,
  choose y y_nin_st₂u₂ using st₂u₂_ne,
  use y,
  simp only[not_iff, finset.mem_sdiff, finset.mem_union, not_and_distrib, not_or_distrib, not_not] at y_nin_st₂u₂ ⊢,
  choose y_in_s y_nin_t₂u₂ using y_nin_st₂u₂,
  split; intros; assumption,

  simp only[set.mem_sep_iff],
  split,
  apply X.subset_closed (t ∪ u₁),
  assumption,
  rw [t_decomp, finset.union_comm t₁ t₂, finset.union_assoc],
  apply finset.subset_union_right,

  split,
  apply X.subset_closed (t ∪ (s \ t ∪ u₁)),
  assumption,
  rw [←finset.union_assoc t (s \ t), finset.union_sdiff_self_eq_union, t_decomp],
  rw [finset.union_comm (t₁ ∪ t₂) s, finset.union_comm t₁ t₂],
  rw [←finset.union_assoc s t₂, finset.union_assoc (s ∪ t₂)],
  apply finset.union_subset_union_left,
  apply finset.subset_union_left,

  rw [finset.inter_distrib_left, finset.union_eq_empty_iff],
  split, assumption,
  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ ((t ∪ (s \ t)) ∩ u₁),
  rw [finset.union_sdiff_self_eq_union, finset.inter_distrib_right],
  apply finset.subset_union_right,
  rw [finset.subset_empty, finset.inter_distrib_right, finset.union_eq_empty_iff],
  split; assumption,

  simp only[t_decomp, u_decomp, finset.inter_distrib_left, finset.inter_distrib_right, finset.union_eq_empty_iff],
  split, split, split,
  
  rw [←finset.disjoint_iff_inter_eq_empty],
  apply @disjoint_complexes_disjoint_simplices _ _ (Lk(X, s) s_in_X) (simplex {x}),
  simp only[link, set.mem_sep_iff],
  split, assumption,
  split; assumption,
  assumption,

  apply barycenter_disjoint_link X s x s_in_X x_nin_X,
  
  rw [←finset.disjoint_iff_inter_eq_empty],
  apply @disjoint_complexes_disjoint_simplices _ _ (Lk(X, s) s_in_X) (∂s),
  simp only[link, set.mem_sep_iff],
  split, assumption,
  split; assumption,
  apply @set.mem_of_subset_of_mem _ (∂(s \ t)).simplices,
  apply subsimplex_boundary_subcomplex,
  apply finset.sdiff_subset,
  assumption,
  apply boundary_disjoint_link,

  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ (t ∩ u₁),
  rw [t_decomp, finset.union_comm, finset.inter_distrib_right],
  apply finset.subset_union_right,
  rw [finset.subset_empty],
  assumption,
  
  split, split,
  rw [←finset.disjoint_iff_inter_eq_empty],
  apply @disjoint_complexes_disjoint_simplices _ _ (∂s) (simplex {x}),
  rw [simplex_boundary_mem_iff_subset],
  assumption,
  assumption,
  apply @disjoint.symm _ _ _ (vertices (simplex {x})) (vertices (∂s)),
  apply barycenter_disjoint_boundary X s x s_in_X x_nin_X,

  rw [t_decomp, finset.sdiff_union_distrib, st₁_sdiff_ident, finset.inter_sdiff, finset.inter_self, finset.ssubset_iff_subset_ne] at u₂_in_bd,
  choose u₂_ss_st₂ u₂_ne_st₂ using u₂_in_bd,
  rw [finset.subset_iff] at u₂_ss_st₂,
  rw [finset.eq_empty_iff_forall_not_mem],
  intro y,
  by_cases H : y ∈ u₂,

  specialize u₂_ss_st₂ H,
  simp only[finset.mem_sdiff] at u₂_ss_st₂,
  choose y_in_s y_nin_t₂ using u₂_ss_st₂,
  simp only[finset.mem_inter, not_and_distrib],
  left, assumption,
  
  simp only[finset.mem_inter, not_and_distrib],
  right, assumption,
  
  rw [←finset.disjoint_iff_inter_eq_empty],
  apply @disjoint_complexes_disjoint_simplices _ _ (∂s) (Lk(X, s) s_in_X),
  rw [simplex_boundary_mem_iff_subset],
  assumption,

  simp only[link, set.mem_sep_iff],
  split, assumption,
  split,
  apply X.subset_closed (t ∪ (s \ t ∪ u₁)),
  assumption,
  rw [←finset.union_assoc, finset.union_sdiff_self_eq_union, finset.union_assoc],
  apply finset.subset_union_right,

  rw [←finset.subset_empty],
  apply @finset.subset.trans _ _ ((t ∪ (s \ t)) ∩ u₁),
  rw [finset.union_sdiff_self_eq_union, finset.inter_distrib_right],
  apply finset.subset_union_right,
  rw [finset.subset_empty, finset.inter_distrib_right, finset.union_eq_empty_iff],
  split; assumption,
  
  apply @disjoint.symm _ _ _ (vertices (Lk(X, s) s_in_X)) (vertices (∂s)),
  apply boundary_disjoint_link X s s_in_X,
end

lemma stellar_subdiv_anticomm_link_right
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : (σ((Lk(X, t) t_in_X), s\t, x; sorry, sorry, sorry)).simplices ⊆ (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry).simplices
:= begin
  simp only[stellar_subdivision, simplicial_union],
  simp only[set.subset_def],
  intros u u_in_subdiv,

  simp only[set.mem_union] at u_in_subdiv,
  cases u_in_subdiv with u_in_star_comp u_in_join, -- Cases E + F, resp.

  apply stellar_subdiv_anticomm_link_right_e; assumption,
  apply stellar_subdiv_anticomm_link_right_f; assumption,
end

lemma stellar_subdiv_anticomm_link
    (X : simplicial_complex α)
    (s t : finset α) [s_ne : nonempty s]
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (t_in_X : t ∈ X.simplices)
    (t_in_star_bd : t ∈ (π₁ (boundary_disjoint_link X s s_in_X)[(Lk(X, s) s_in_X) ⋆ ∂s]).simplices)
  : (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry).simplices = (σ((Lk(X, t) t_in_X), s\t, x; sorry, sorry, sorry)).simplices
:= begin
  apply set.eq_of_subset_of_subset,
  apply stellar_subdiv_anticomm_link_left,
  assumption,
  apply stellar_subdiv_anticomm_link_right,
  assumption,
end