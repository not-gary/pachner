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
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [set.mem_diff],
      split,

      rw [finset.mem_coe],
      apply finset.empty_mem_powerset,

      rw [set.mem_singleton_iff],
      apply ne.symm,
      apply finset.nonempty.ne_empty,
      rw [finset.nonempty_range_iff],
      tauto,
    end)
    (begin
      simp only[is_subset_closed],
      intros s s_sphere t t_sset_s,

      rw [set.mem_diff, finset.mem_coe, finset.mem_powerset, set.mem_singleton_iff] at *,
      cases s_sphere with s_in_power s_ne_range,
      split,

      apply @subset_trans _ _ _ t s (finset.range(n + 2));
      assumption,

      have Hs : s ⊂ finset.range (n + 2), from
      begin
        apply ssubset_of_ne_of_subset;
        assumption,
      end,
      apply ne_of_ssubset,
      apply @ssubset_of_subset_of_ssubset _ _ _ _ t s (finset.range(n + 2));
      assumption,
    end)
notation `S(` n `)` := stellar_n_sphere n

def stellar_n_disk
    (n : ℕ)
  : simplicial_complex ℕ
:= simplicial_complex.mk
    (finset.powerset (finset.range (n + 1)))
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [finset.mem_coe],
      apply finset.empty_mem_powerset,
    end)
    (by { simp, tauto })
notation `D(` n `)` := stellar_n_disk n

@[simp]
def is_stellar_sphere
    (X : simplicial_complex α)
  : Prop
:= X ≅ @empty_sc α ∨ ∃ (n : ℕ) (Y : simplicial_complex α), X ≅ₛₜ Y ∧ Y ≅ S(n)

@[simp]
def is_stellar_n_sphere
    (X : simplicial_complex α)
    (n : ℕ)
  : Prop
:= X ≅ @empty_sc α ∨ ∃ Y : simplicial_complex α, X ≅ₛₜ Y ∧ Y ≅ S(n)

@[simp]
def is_stellar_ball
    (X : simplicial_complex α)
  : Prop
:= X ≅ @empty_sc α ∨ ∃ (n : ℕ) (Y : simplicial_complex α), X ≅ₛₜ Y ∧ Y ≅ D(n)

@[simp]
def is_stellar_n_ball
    (X : simplicial_complex α)
    (n : ℕ)
  : Prop
:= X ≅ @empty_sc α ∨ ∃ Y : simplicial_complex α, X ≅ₛₜ Y ∧ Y ≅ D(n)

@[simp]
def is_stellar_manifold
    (X : simplicial_complex α)
  : Prop
:= ∀ x : α,
    ({x} ∈ X.simplices) →
      is_stellar_sphere (Lk(X, {x}) (by assumption)) ∨
      is_stellar_ball (Lk(X, {x}) (by assumption))

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

lemma link_zero_disk_empty
    (x : ℕ)
    (x_in_disk : {x} ∈ D(0).simplices)
  : Lk(D(0), {x}) x_in_disk ≅ @empty_sc ℕ
:= begin
  apply simplicial_iso_preserves_equiv,
  simp only[link, stellar_n_disk, empty_sc, simplicial_complex.simplices],
  simp only[stellar_n_disk] at x_in_disk,
  rw [set.ext_iff],
  intro s,
  split,

  intro s_in_link,
  rw [set.mem_sep_iff] at s_in_link,
  choose s_in_power xs_in_power xs_empty using s_in_link,
  rw [finset.mem_coe] at *,
  rw [finset.mem_powerset] at *,
  have H_range : finset.range (0 + 1) = {0}, by tauto,
  rw [H_range] at *,
  have Hx_0 : {x} = {0}, by finish,
  rw [finset.singleton_inj] at Hx_0,
  rw [Hx_0] at *,
  have : s = ∅ ∨ s = {0}, by finish,
  have Hs_empty : s = ∅, by finish,
  rw [set.mem_singleton_iff],
  assumption,

  intro s_empty,
  rw [set.mem_singleton_iff] at s_empty,
  rw [set.mem_sep_iff],
  rw [finset.mem_coe, finset.mem_powerset] at x_in_disk,
  have H_range : finset.range (0 + 1) = {0}, by tauto,
  rw [H_range, finset.singleton_subset_iff, finset.mem_singleton] at x_in_disk,
  split,

  rw [finset.mem_coe, s_empty],
  apply finset.empty_mem_powerset,
  split,

  rw [finset.mem_coe, s_empty, x_in_disk, finset.union_empty, H_range],
  apply finset.mem_powerset_self,

  rw [s_empty, x_in_disk, finset.inter_empty],
end

-- Lemma 3.2 (1), p.10
lemma stellar_n_ball_is_stellar_mfd
  : ∀ (n : ℕ), is_stellar_manifold D(n)
:= begin
  intro n,
  induction n,

  dsimp only[is_stellar_manifold, is_stellar_sphere, is_stellar_ball],
  intros x x_in_disk,
  right, left,
  apply link_zero_disk_empty,

  dsimp only[is_stellar_manifold, is_stellar_sphere, is_stellar_ball],
  intros x x_in_disk,
  set m := n_n.succ,
  set n := n_n,
  right, right,
  use n, use D(n),
  split,

  rotate, refl,

  apply iso_stellar_equiv,
  unfold is_simplicially_iso,

  let f : ℕ → ℕ := λ i : ℕ, if (i < x) then i else (i - 1),
  have f_simpl : is_simplicial_map (Lk(D(m), {x}) x_in_disk) D(n) f, from
  begin
    unfold is_simplicial_map,
    intros s s_in_link,
    simp only[link, stellar_n_disk, simplicial_complex.simplices] at x_in_disk s_in_link ⊢,
    rw [set.mem_sep_iff] at s_in_link,
    choose s_in_power xs_in_power xs_empty using s_in_link,
    rw [finset.mem_coe, finset.mem_powerset, finset.subset_iff] at *,
    intros y y_in_img,
    rw [finset.mem_image] at y_in_img,
    choose b Hb fb_eq_y using y_in_img,
    specialize s_in_power Hb,
    have Hbs : b ∈ {x} ∪ s, by { apply finset.mem_union_right, assumption },
    specialize xs_in_power Hbs,
    have Hx : x ∈ {x}, by { rw [finset.mem_singleton], },
    specialize x_in_disk Hx, 
    simp only[f] at fb_eq_y,
    revert fb_eq_y,
    split_ifs,

    intro b_eq_y,
    rw [finset.mem_range] at *,
    subst b,
    have Hmn : n + 1 = m, by tauto,
    rw [Hmn] at *,
    omega,

    intro b_pred_eq_y,
    rw [finset.mem_range] at *,
    subst y,
    have Hmn : n + 1 = m, by tauto,
    rw [Hmn] at *,
    omega,
  end,

  let g : ℕ → ℕ := λ i : ℕ, if (i < x) then i else i + 1,
  have g_simpl : is_simplicial_map D(n) (Lk(D(m), {x}) x_in_disk) g, from
  begin
    unfold is_simplicial_map,
    intros s s_in_disk,
    simp only[link, stellar_n_disk, simplicial_complex.simplices] at x_in_disk s_in_disk ⊢,
    rw [set.mem_sep_iff],
    repeat { rw [finset.mem_coe, finset.mem_powerset, finset.subset_iff] at *, },
    split,

    intros y y_in_img,
    rw [finset.mem_image] at y_in_img,
    choose a Ha ga_eq_x using y_in_img,
    specialize s_in_disk Ha,
    have Hx : x ∈ {x}, by { rw [finset.mem_singleton] },
    specialize x_in_disk Hx,
    rw [finset.mem_range] at *,
    revert ga_eq_x,
    simp only[g],
    split_ifs,

    intro a_eq_y,
    subst y,
    omega,

    intro a_succ_eq_y,
    subst y,
    have Hmn : n + 1 = m, by tauto,
    rw [Hmn] at *,
    omega,

    split,
    intros y y_in_ximg,
    rw [finset.mem_union] at y_in_ximg,
    cases y_in_ximg,

    specialize x_in_disk y_in_ximg,
    assumption,

    rw [finset.mem_image] at y_in_ximg,
    choose a Ha ga_eq_y using y_in_ximg,
    specialize s_in_disk Ha,
    rw [finset.mem_range] at *,
    simp only[g] at ga_eq_y,
    revert ga_eq_y,
    split_ifs,

    intro a_eq_y,
    subst y,
    have Hmn : n + 1 = m, by tauto,
    rw [Hmn] at *,
    omega,

    intro a_succ_eq_y,
    subst y,
    have Hmn : n + 1 = m, by tauto,
    rw [Hmn] at *,
    omega,

    apply finset.singleton_inter_of_not_mem,
    rw [finset.mem_image],
    simp,
    intros y y_in_s,
    simp only[g],
    split_ifs;
    omega,
  end,

  let fs : simplicial_map (Lk(D(m), {x}) x_in_disk) D(n) := simplicial_map.mk f f_simpl,
  let gs : simplicial_map D(n) (Lk(D(m), {x}) x_in_disk) := simplicial_map.mk g g_simpl,

  use fs,
  unfold is_simplicial_iso,
  use gs,
  unfold is_inverse_simplicial_iso,
  split,

  { simp only[simplicial_map.comp, simplicial_map.map],
    simp,
    unfold set.eq_on,
    intros y y_in_vert_link,
    simp only[vertices] at y_in_vert_link,
    rw [set.mem_Union] at y_in_vert_link,
    choose s y_in_vert_link using y_in_vert_link,
    rw [set.mem_Union] at y_in_vert_link,
    choose Hs y_in_s using y_in_vert_link,
    
    simp only[simplicial_complex.simplices] at Hs,
    rw [set.mem_inter_iff] at Hs,
    cases Hs with Hs_union Hs_inter,
    rw [set.mem_sep_iff] at Hs_union Hs_inter,
    cases Hs_union with s_in_disk xs_in_disk,
    cases Hs_inter with s_in_disk xs_empty,
    rw [finset.mem_coe] at *,

    have y_nin_xs : y ∉ {x} ∩ s, from
    begin
      rw [xs_empty],
      tauto,
    end,
    rw [finset.mem_inter] at y_nin_xs,
    simp at y_nin_xs,
    have y_ne_x : y ≠ x, from
    begin
      revert y_in_s,
      contrapose,
      tauto,
    end,

    rw [function.comp_apply],
    simp only[f, g],
    split_ifs,
    
    simp,
    
    have : y = x, by omega,
    contradiction,
    
    have : 1 ≤ y, by omega,
    rw [nat.sub_add_cancel],
    simp,
    assumption, },

  { simp only[simplicial_map.comp, simplicial_map.map],
    simp,
    unfold set.eq_on,
    intros y y_in_vert_disk,
    simp only[vertices] at y_in_vert_disk,
    rw [set.mem_Union] at y_in_vert_disk,
    choose s y_in_vert_disk using y_in_vert_disk,
    rw [set.mem_Union] at y_in_vert_disk,
    choose Hs y_in_s using y_in_vert_disk,
    
    simp only[stellar_n_disk, simplicial_complex.simplices] at Hs,
    rw [finset.mem_coe] at *,
    rw [finset.mem_powerset, finset.subset_iff] at Hs,
    specialize Hs y_in_s,
    rw [finset.mem_range] at Hs,
    
    rw [function.comp_apply],
    simp only[f, g],
    split_ifs,
    
    simp,
    
    have : y < x, by omega,
    contradiction,
    
    simp, }
end

-- TODO: Finish lemma.
lemma link_zero_sphere_empty
    (x : ℕ)
    (x_in_sphere : {x} ∈ S(0).simplices)
  : Lk(S(0), {x}) x_in_sphere ≅ @empty_sc ℕ
:= begin
  apply simplicial_iso_preserves_equiv,
  simp only[link, stellar_n_sphere, empty_sc, simplicial_complex.simplices],
  simp only[stellar_n_sphere, simplicial_complex.simplices] at x_in_sphere,
  rw [set.ext_iff],
  intro s,
  split,

  { intro s_in_link,
    rw [set.mem_sep_iff] at s_in_link,
    choose s_in_power xs_in_power xs_empty using s_in_link,
    rw [set.mem_diff] at *,
    
    cases s_in_power with s_in_power s_nin_int,
    cases xs_in_power with xs_in_power xs_nin_int,
    cases x_in_sphere with x_in_power x_nin_int,
    
    rw [finset.mem_coe, finset.mem_powerset] at *,
    rw [set.mem_singleton_iff] at *,
    have H_range : finset.range (0 + 2) = {0, 1}, by tauto,
    rw [H_range] at *,
    have Hx : x ∈ {x}, by { rw [finset.mem_singleton], },
    rw [finset.subset_iff] at x_in_power,
    specialize x_in_power Hx,
    simp at x_in_power,
    cases x_in_power,
    
    subst x,
    have s_sset : s ⊂ {0, 1}, from
    begin
      rw [finset.ssubset_iff_subset_ne],
      split; assumption,
    end,
    have s0_sset : {0} ∪ s ⊂ {0, 1}, from
    begin
      rw [finset.ssubset_iff_subset_ne],
      split; assumption,
    end,
    rw [finset.ssubset_iff_subset_ne] at s0_sset,
    cases s0_sset with s0_subset s0_ne,
    have s0_diff_sset : ({0} ∪ s) \ {0} ⊂ {0, 1} \ {0}, from
    begin
      rw [finset.union_sdiff_left],
      rw [finset.ssubset_iff_subset_ne],
      split,

      apply finset.sdiff_subset_sdiff; tauto,

      simp,
      rw [finset.ext_iff],
      simp, use 1,
      split; simp,

      sorry,
    end,
    all_goals {sorry}, },

  { sorry, }
end

-- Lemma 3.2 (2), p.10
-- TODO: Prove maps are simplicial. Should be almost identical to disk.
lemma stellar_n_sphere_is_stellar_mfd
  : ∀ (n : ℕ), is_stellar_manifold S(n)
:= begin
  intro n,
  induction n;
  unfold is_stellar_manifold;
  intros x x_in_sphere;
  left,

  unfold is_stellar_sphere,
  left,
  apply link_zero_sphere_empty,

  set n := n_n,
  set m := n.succ,
  have Hmn : n + 1 = m, by tauto,

  unfold is_stellar_sphere,
  right,
  use n, use S(n),
  split,

  rotate, refl,

  apply iso_stellar_equiv,
  unfold is_simplicially_iso,

  let f : ℕ → ℕ := λ i : ℕ, if (i < x) then i else (i - 1),
  have f_simpl : is_simplicial_map (Lk(S(m), {x}) x_in_sphere) S(n) f, by sorry,

  let g : ℕ → ℕ := λ i : ℕ, if (i < x) then i else (i + 1),
  have g_simpl : is_simplicial_map S(n) (Lk(S(m), {x}) x_in_sphere) g, by sorry,

  let fs : simplicial_map (Lk(S(m), {x}) x_in_sphere) S(n) := simplicial_map.mk f f_simpl,
  let gs : simplicial_map S(n) (Lk(S(m), {x}) x_in_sphere) := simplicial_map.mk g g_simpl,

  use fs,
  unfold is_simplicial_iso,
  use gs,
  unfold is_inverse_simplicial_iso,
  split,

  { simp only[simplicial_map.comp, simplicial_map.map],
    simp,
    unfold set.eq_on,
    intros y y_in_vert,

    simp only[vertices] at y_in_vert,
    rw [set.mem_Union] at y_in_vert,
    choose s y_in_vert using y_in_vert,
    rw [set.mem_Union] at y_in_vert,
    choose s_in_link y_in_s using y_in_vert,
    
    simp only[simplicial_complex.simplices] at s_in_link,
    rw [set.mem_inter_iff] at s_in_link,
    cases s_in_link with s_in_union s_in_inter,
    rw [set.mem_sep_iff] at s_in_union s_in_inter,
    cases s_in_union with s_in_sphere xs_in_sphere,
    cases s_in_inter with s_in_sphere xs_empty,
    
    simp only[stellar_n_sphere] at *,
    rw [set.mem_diff] at *,
    cases s_in_sphere with s_in_power s_nin_int,
    cases xs_in_sphere with xs_in_power xs_nin_int,
    cases x_in_sphere with x_in_power x_nin_int,
    rw [finset.mem_coe] at *,
    
    rw [finset.mem_powerset, finset.subset_iff] at *,
    specialize s_in_power y_in_s,
    have Hx : x ∈ {x}, by { rw [finset.mem_singleton] },
    specialize x_in_power Hx,
    have Hxs : x ∈ {x} ∪ s, by { rw [finset.mem_union], left, apply Hx },
    specialize xs_in_power Hxs,
    rw [finset.mem_range] at *,

    have y_nin_xs : y ∉ {x} ∩ s, from
    begin
      rw [xs_empty],
      tauto,
    end,
    rw [finset.mem_inter] at y_nin_xs,
    simp at y_nin_xs,
    have y_ne_x : y ≠ x, from
    begin
      revert y_in_s,
      contrapose,
      tauto,
    end,
    
    rw [function.comp_apply],
    simp only[f, g],
    split_ifs,
    
    simp,
    
    have : y = x, by omega,
    contradiction,
    
    have : 1 ≤ y, by omega,
    rw [nat.sub_add_cancel],
    simp,
    assumption, },

  { simp only[simplicial_map.comp, simplicial_map.map],
    simp,
    unfold set.eq_on,
    intros y y_in_vert,

    simp only[vertices] at y_in_vert,
    rw [set.mem_Union] at y_in_vert,
    choose s y_in_vert using y_in_vert,
    rw [set.mem_Union] at y_in_vert,
    choose s_in_sphere y_in_s using y_in_vert,
    
    simp only[stellar_n_sphere, simplicial_complex.simplices] at s_in_sphere x_in_sphere,
    rw [set.mem_diff] at s_in_sphere x_in_sphere,
    cases s_in_sphere with s_in_power s_nin_int,
    cases x_in_sphere with x_in_power x_nin_int,
    rw [finset.mem_coe] at *,
    
    rw [finset.mem_powerset, finset.subset_iff] at *,
    specialize s_in_power y_in_s,
    have Hx : x ∈ {x}, by { rw [finset.mem_singleton] },
    specialize x_in_power Hx,
    rw [finset.mem_range] at *,

    rw [function.comp_apply],
    simp only[f, g],
    split_ifs,

    simp,

    have : y < x, by omega,
    contradiction,

    simp, },
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

