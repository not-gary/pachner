import tactic          -- standard proof tactics
import data.set.basic        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset.basic     -- type-level finite sets
import .simplicial_complex
import .simplicial_map

variables {α β : Type*}
variables [decidable_eq α] [decidable_eq β]

-- Boundary of a single simplex.
def simplex_boundary
    (s : finset α)
  : simplicial_complex α
:= simplicial_complex.mk
    (((finset.powerset s) \ {s}) ∪ {∅})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],

      use ∅,
      rw [set.mem_union],
      right,
      tauto,
    end)
    (begin
      simp,
      split,

      intros t t_sset_empty,
      left,
      rw [←finset.subset_empty],
      assumption,

      intros s_1 _ _ t _,

      have : s_1 ⊆ t -> t ⊆ s_1 -> s_1 = t, from
      begin
        exact subset_antisymm,
      end,

      have : t ⊆ s_1 -> s_1 ⊆ s -> t ⊆ s, from
      begin
        exact subset_trans,
      end,
      finish,
    end)
prefix `∂`:75 := simplex_boundary

instance simplex_boundary.fintype
    (s : finset α)
  : fintype (∂s).simplices
:= begin
  unfold simplex_boundary,
  dsimp only [simplicial_complex.simplices],
  apply set.fintype_union,
end

lemma simplex_boundary_subcomplex_simplex
    (s : finset α)
  : ∂s ⊆ simplex s
:= begin
  simp only [is_subcomplex, simplex, simplex_boundary, set.subset_def],
  intros t t_in_bd,

  simp only [set.mem_diff, set.mem_union, finset.mem_coe, finset.mem_powerset] at t_in_bd,
  simp only [finset.mem_coe, finset.mem_powerset],
  cases t_in_bd with t_ss_s t_empty,

  choose t_ss_s t_ne_s using t_ss_s,
  assumption,

  rw [set.mem_singleton_iff] at t_empty,
  rw [t_empty],
  apply set.empty_subset,
end

lemma simplex_boundary_iso
    (s : finset α) [nonempty s]
    (t : finset β) [nonempty t]
  : simplex s ≅ simplex t → ∂s ≅ ∂t
:= begin
  intro s_iso_t,
  unfold is_simplicially_iso at s_iso_t ⊢,
  choose f f_iso using s_iso_t,

  let f_iso' := f_iso,
  unfold is_simplicial_iso at f_iso',
  choose g gf_inv using f_iso',

  have g_iso : is_simplicial_iso g, by apply iso_inv_is_iso f g f_iso gf_inv,
  unfold is_inverse_simplicial_iso at gf_inv,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at gf_inv,
  choose gf_id fg_id using gf_inv,

  have f_inj : set.inj_on f.map s, from
  begin
    apply @set.left_inv_on.inj_on _ _ _ _ g.map,
    simp only [set.left_inv_on],
    intros x x_in_s,
    have x_in_vert : x ∈ vertices (simplex s), from
    begin
      rw [vertex_iff_in_simplex],
      use s, split,
      simp only [simplex, finset.mem_coe],
      apply finset.mem_powerset_self,
      rw [←finset.mem_coe],
      assumption,
    end,
    specialize gf_id x_in_vert,
    assumption,
  end,

  have g_inj : set.inj_on g.map t, from
  begin
    apply @set.left_inv_on.inj_on _ _ _ _ f.map,
    simp only [set.left_inv_on],
    intros x x_in_s,
    have x_in_vert : x ∈ vertices (simplex t), from
    begin
      rw [vertex_iff_in_simplex],
      use t, split,
      simp only [simplex, finset.mem_coe],
      apply finset.mem_powerset_self,
      rw [←finset.mem_coe],
      assumption,
    end,
    specialize fg_id x_in_vert,
    assumption,
  end,

  have f_simp : is_simplicial_map (∂s) (∂t) f.map, from
  begin
    simp only [is_simplicial_map, simplex_boundary],
    simp only [set.mem_union, set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset],
    intros u u_in_s,
    cases u_in_s with u_ss_s u_empty,

    left,
    choose u_ss_s u_ne_s using u_ss_s,
    simp only [←finset.coe_subset, ←finset.coe_inj, ←simplex_vertices t],
    split,

    apply simplex_subset_vertices,
    apply f.is_simplicial,
    simp only [simplex, finset.mem_coe, finset.mem_powerset],
    assumption,

    rw [simplicial_iso_vertices (simplex s) (simplex t) f, simplex_vertices s, finset.coe_image],
    revert u_ne_s,
    contrapose,
    simp only [not_not, set.ext_iff, finset.ext_iff, set.mem_image],
    intros fu_eq_fs a,
    specialize fu_eq_fs (f.map a),
    cases fu_eq_fs with fu_ss_fs fs_ss_fu,
    split,

    intro a_in_u,
    rw [finset.subset_iff] at u_ss_s,
    specialize u_ss_s a_in_u,
    assumption,

    intro a_in_s,
    apply set.inj_on.mem_of_mem_image f_inj u_ss_s,
    rw [finset.mem_coe],
    assumption,
    have Hs : ∃ x : α, x ∈ ↑s ∧ f.map x = f.map a, from
    begin
      use a, split,
      rw [finset.mem_coe],
      assumption,
      refl,
    end,
    specialize fs_ss_fu Hs,
    simp only [finset.mem_val, set.mem_image],
    assumption,
    assumption,

    simp only [u_empty, finset.image_empty],
    right, refl,
  end,

  have g_simp : is_simplicial_map (∂t) (∂s) g.map, from
  begin
    simp only [is_simplicial_map, simplex_boundary],
    simp only [set.mem_union, set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset],
    intros u u_in_t,
    cases u_in_t with u_ss_t u_empty,

    left,
    choose u_ss_t u_ne_t using u_ss_t,
    simp only [←finset.coe_subset, ←finset.coe_inj, ←simplex_vertices s],
    split,

    apply simplex_subset_vertices,
    apply g.is_simplicial,
    simp only [simplex, finset.mem_coe, finset.mem_powerset],
    assumption,

    rw [simplicial_iso_vertices (simplex t) (simplex s) g, simplex_vertices t, finset.coe_image],
    revert u_ne_t,
    contrapose,
    simp only [not_not, set.ext_iff, finset.ext_iff, set.mem_image],
    intros gu_eq_gt a,
    specialize gu_eq_gt (g.map a),
    cases gu_eq_gt with gu_ss_gt gs_ss_gt,
    split,

    intro a_in_u,
    rw [finset.subset_iff] at u_ss_t,
    specialize u_ss_t a_in_u,
    assumption,

    intro a_in_t,
    apply set.inj_on.mem_of_mem_image g_inj u_ss_t,
    rw [finset.mem_coe],
    assumption,
    have Ht : ∃ x : β, x ∈ ↑t ∧ g.map x = g.map a, from
    begin
      use a, split,
      rw [finset.mem_coe],
      assumption,
      refl,
    end,
    specialize gs_ss_gt Ht,
    simp only [finset.mem_val, set.mem_image],
    assumption,
    assumption,

    simp only [u_empty, finset.image_empty],
    right, refl,
  end,

  let f_bd : simplicial_map (∂s) (∂t) := simplicial_map.mk f.map f_simp,
  let g_bd : simplicial_map (∂t) (∂s) := simplicial_map.mk g.map g_simp,

  use f_bd, use g_bd,
  unfold is_inverse_simplicial_iso,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def],
  split,

  { intros x x_in_bd,
    have x_in_s : x ∈ vertices (simplex s), from
    begin
      apply is_subcomplex_vertices _ (∂s),
      apply simplex_boundary_subcomplex_simplex,
      assumption,
    end,
    specialize gf_id x_in_s,
    assumption, },

  { intros x x_in_bd,
    have x_in_t : x ∈ vertices (simplex t), from
    begin
      apply is_subcomplex_vertices _ (∂t),
      apply simplex_boundary_subcomplex_simplex,
      assumption,
    end,
    specialize fg_id x_in_t,
    assumption, },
end

lemma simplex_boundary_coe_image_left
    [nonempty α]
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
    (φ : simplicial_coe X β)
  : (∂(finset.image φ.coe s)).simplices ⊆ (simplicial_image (∂s) φ.coe).simplices
:= begin
  simp only [simplex_boundary, simplicial_image, set.subset_def],
  simp only [set.mem_set_of, set.mem_union, set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset],
  intros t t_in_bd,
  cases t_in_bd with t_in_bd t_empty,
    
  choose t_ss_φs t_ne_φs using t_in_bd,
  have inv_t : finset.image φ.coe (finset.image (φ⁻ᶜ.map) t) = t, from
  begin
    simp only [←finset.coe_inj, finset.coe_image, set.ext_iff, set.mem_image],
    intros y,
    split,

    intros y_in_img,
    choose a a_in_img φa_y using y_in_img,
    choose b b_in_t φb_a using a_in_img,
    subst φb_a,
    subst φa_y,

    have inv_b : φ.coe ((φ⁻ᶜ.map) b) = b, from
    begin
      apply set.inj_on.right_inv_on_of_left_inv_on,
      apply simplicial_coe_inv_inj,
      apply set.inj_on.left_inv_on_inv_fun_on,
      apply φ.injective,
      apply set.surj_on.maps_to_inv_fun_on,
      apply simplicial_coe_surjective_vertices,
      apply simplicial_coe_maps_to_vertices,

      rw [vertex_iff_in_simplex],
      use t, split,
      apply (φ[X]).subset_closed (finset.image φ.coe s),
      apply map_is_simplicial_onto_image,
      assumption,
      assumption,

      rw [←finset.mem_coe],
      assumption,
    end,
    rw [inv_b],
    assumption,

    intros y_in_t,
    use ((φ⁻ᶜ.map) y), split,
    use y, split,
    assumption,
    refl,

    apply set.inj_on.right_inv_on_of_left_inv_on,
    apply simplicial_coe_inv_inj,
    apply set.inj_on.left_inv_on_inv_fun_on,
    apply φ.injective,
    apply set.surj_on.maps_to_inv_fun_on,
    apply simplicial_coe_surjective_vertices,
    apply simplicial_coe_maps_to_vertices,

    rw [vertex_iff_in_simplex],
    use t, split,
    apply (φ[X]).subset_closed (finset.image φ.coe s),
    apply map_is_simplicial_onto_image,
    assumption,
    assumption,

    rw [←finset.mem_coe],
    assumption,
  end,

  use (finset.image (φ⁻ᶜ.map) t), split,

  have inv_s : finset.image (φ⁻ᶜ.map) (finset.image φ.coe s) = s, from
  begin
    simp only [←finset.coe_inj, finset.coe_image],
    apply set.inj_on.inv_fun_on_image,
    apply φ.injective,
    apply simplex_subset_vertices,
    assumption,
  end,

  left, split,
  have inv_t_ss_φs : finset.image (φ⁻ᶜ.map) t ⊆ finset.image (φ⁻ᶜ.map) (finset.image φ.coe s), from
  begin
    apply finset.image_subset_image,
    assumption,
  end,
  rw [inv_s] at inv_t_ss_φs,
  assumption,

  revert t_ne_φs,
  contrapose,
  simp only [not_not],
  intros φt_s,

  rw [←φt_s],
  symmetry,
  assumption,

  assumption,

  use ∅, split,
  right, refl,
  rw [t_empty],
  apply finset.image_empty,
end

lemma simplex_boundary_coe_image_right
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
    (φ : simplicial_coe X β)
  : (simplicial_image (∂s) φ.coe).simplices ⊆ (∂(finset.image φ.coe s)).simplices
:= begin
  simp only [simplex_boundary, simplicial_image, set.subset_def],
  simp only [set.mem_set_of, set.mem_union, set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset],
  intros t t_in_img,
  choose u u_in_bd φu_t using t_in_img,
  cases u_in_bd with u_in_bd u_empty,

  choose u_ss_s u_ne_s using u_in_bd,
  left, split,
  
  rw [←φu_t],
  apply finset.image_subset_image,
  assumption,

  rw [←φu_t],
  revert u_ne_s,
  contrapose,
  simp only [not_not],
  intros φu_eq_φs,

  simp only [←finset.coe_inj, finset.coe_image, set.ext_iff] at φu_eq_φs ⊢,
  intros a,
  specialize φu_eq_φs (φ.coe a),
  cases φu_eq_φs with φu_ss_φs φs_ss_φu,
  split,

  intros a_in_u,
  have a_in_X : a ∈ vertices X, from
  begin
    rw [vertex_iff_in_simplex],
    use u, split,
    apply X.subset_closed s;
    assumption,
    rw [←finset.mem_coe],
    assumption,
  end,
  rw [←set.inj_on.mem_image_iff φ.injective] at a_in_u ⊢,
  specialize φu_ss_φs a_in_u,
  assumption,

  apply simplex_subset_vertices,
  assumption,
  assumption,

  apply simplex_subset_vertices,
  apply X.subset_closed s;
  assumption,
  assumption,

  intros a_in_s,
  have a_in_X : a ∈ vertices X, from
  begin
    rw [vertex_iff_in_simplex],
    use s, split; assumption,
  end,
  rw [←set.inj_on.mem_image_iff φ.injective] at a_in_s ⊢,
  specialize φs_ss_φu a_in_s,
  assumption,

  apply simplex_subset_vertices,
  apply X.subset_closed s;
  assumption,
  assumption,

  apply simplex_subset_vertices,
  assumption,
  assumption,

  right,
  rw [u_empty, finset.image_empty] at φu_t,
  symmetry,
  assumption,
end

lemma simplex_boundary_coe_image
    [nonempty α]
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
    (φ : simplicial_coe X β)
  : (∂(finset.image φ.coe s)).simplices = (simplicial_image (∂s) φ.coe).simplices
:= begin
  rw [set.subset.antisymm_iff],
  split,

  apply simplex_boundary_coe_image_left,
  assumption,

  apply simplex_boundary_coe_image_right,
  assumption,
end

lemma simplex_boundary_subcomplex_simplices
    (X : simplicial_complex α)
    (s t : finset α)
    (s_in_X : s ∈ X.simplices)
  : t ∈ (∂s).simplices → t ∈ X.simplices
:= begin
  intro t_in_bd,
  simp only [simplex_boundary, set.mem_union, set.mem_diff, finset.mem_coe, finset.mem_powerset] at t_in_bd,
  cases t_in_bd with t_ss_s t_empty,

  choose t_ss_s t_ne_s using t_ss_s,
  apply X.subset_closed; assumption,

  rw [set.mem_singleton_iff] at t_empty,
  rw [t_empty],
  apply simplicial_complex_empty_simplex,
end

lemma simplex_boundary_subcomplex
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : ∂s ⊆ X
:= begin
  simp only [is_subcomplex, set.subset_def],
  intro u,
  apply simplex_boundary_subcomplex_simplices,
  assumption,
end

lemma simplex_boundary_subcomplex_vert
    (X : simplicial_complex α)
    (s : finset α)
    (x : α)
    (s_in_X : s ∈ X.simplices)
  : x ∈ vertices (∂s) → x ∈ vertices X
:= begin
  intro x_in_bd,
  simp only [vertices_set_of, set.mem_set_of] at x_in_bd ⊢,
  choose t t_in_bd x_in_t using x_in_bd,

  use t, split,
  apply simplex_boundary_subcomplex_simplices X s t s_in_X t_in_bd,
  assumption,
end

lemma simplex_boundary_mem_iff_subset
    (s t : finset α) [nonempty s]
  : t ∈ (∂s).simplices ↔ t ⊂ s
:= begin
  simp only [simplex_boundary, set.mem_union, set.mem_diff, finset.mem_coe, finset.mem_powerset, set.mem_singleton_iff, finset.ssubset_iff_subset_ne],
  split,

  intro t_in_bd,
  cases t_in_bd with t_ss_s t_empty,
  assumption,

  rw [t_empty],
  split,
  apply set.empty_subset,
  symmetry,
  rw [←finset.nonempty_iff_ne_empty, ←finset.nonempty_coe_sort],
  assumption,

  intro t_ss_s,
  rw [ne.def] at t_ss_s,
  left, assumption,
end

lemma subsimplex_boundary_subcomplex
    (s t : finset α)
  : s ⊆ t → ∂s ⊆ ∂t
:= begin
  simp only [is_subcomplex, simplex_boundary, set.subset_def, finset.subset_iff],
  intros s_ss_t u u_in_bd_s,
  simp only [set.mem_union, set.mem_diff, finset.mem_coe, finset.mem_powerset, set.mem_singleton_iff] at u_in_bd_s ⊢,
  cases u_in_bd_s with u_ss_s u_empty,

  left,
  choose u_ss_s u_ne_s using u_ss_s,
  simp only [finset.subset_iff] at u_ss_s ⊢,
  split,

  intros x x_in_u,
  specialize u_ss_s x_in_u,
  specialize s_ss_t u_ss_s,
  assumption,

  revert u_ne_s,
  contrapose,
  simp only [not_not],
  intro u_eq_t,
  subst u_eq_t,
  rw [finset.ext_iff],
  intro x, split,
  intro x_in_u,
  specialize u_ss_s x_in_u,
  assumption,
  intro x_in_s,
  specialize s_ss_t x_in_s,
  assumption,

  right,
  assumption,
end

-- Star of a complex wrt a simplex.
@[simp]
def star
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : simplicial_complex α
:= simplicial_complex.mk
    ({t ∈ X.simplices | (s ∪ t) ∈ X.simplices})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [set.mem_sep_iff],
      split,

      apply simplicial_complex_empty_simplex,

      rw [finset.union_empty],
      assumption,
    end)
    (begin
      simp,
      intros s_1 _ _ t _,

      have : t ⊆ s_1 -> t ∈ X.simplices, from
      begin
        apply X.subset_closed, assumption
      end,

      have : s ⊆ s -> t ⊆ s_1 -> s ∪ t ⊆ s ∪ s_1, from
      begin
        exact finset.union_subset_union,
      end,

      have : s ∪ t ⊆ s ∪ s_1 -> s ∪ t ∈ X.simplices, from
      begin
        apply X.subset_closed, assumption,
      end,
      finish,
    end)
notation `St(` X `, ` s `)` := star X s

instance star.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : fintype (star X s s_in_X).simplices
:= begin
  unfold star,
  dsimp only [simplicial_complex.simplices],

  have H_dec : decidable_pred (λ a : finset α, s ∪ a ∈ X.simplices), from
  begin
    unfold decidable_pred,
    intros a,
    apply set.decidable_mem_of_fintype,
  end,

  apply @set.fintype_sep _ _ _ _ H_dec,
  assumption,
end

lemma star_subcomplex_simplices
    (X : simplicial_complex α)
    (s t : finset α)
    (s_in_X : s ∈ X.simplices)
  : t ∈ (St(X, s) s_in_X).simplices → t ∈ X.simplices
:= begin
  intros t_in_star,
  simp only [star, set.mem_sep_iff] at t_in_star,
  choose t_in_X st_in_X using t_in_star,
  assumption,
end

lemma star_subcomplex
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : St(X, s) s_in_X ⊆ X
:= begin
  simp only [is_subcomplex, set.subset_def],
  intro t,
  apply star_subcomplex_simplices,
end

lemma star_iso
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (s : finset α)
    (t : finset β)
    (f : simplicial_map X Y)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
    (f_iso : is_simplicial_iso f)
  : finset.image f.map s = t → St(X, s) s_in_X ≅ St(Y, t) t_in_Y
:= begin
  intro fs_eq_t,
  unfold is_simplicially_iso,

  have f_simp : is_simplicial_map (St(X, s) s_in_X) (St(Y, t) t_in_Y) f.map, from
  begin
    simp only [is_simplicial_map, star, set.mem_sep_iff],
    intros u u_in_X_star,
    choose u_in_X su_in_X using u_in_X_star,
    split,

    apply f.is_simplicial,
    assumption,

    rw [←fs_eq_t, ←finset.image_union],
    apply f.is_simplicial,
    assumption,
  end,
  let f_star := simplicial_map.mk f.map f_simp,

  unfold is_simplicial_iso at f_iso,
  choose g gf_inv using f_iso,
  unfold is_inverse_simplicial_iso at gf_inv,
  choose gf_id fg_id using gf_inv,

  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at gf_id fg_id,

  have gt_eq_s : finset.image g.map t = s, from
  begin
    rw [←fs_eq_t, finset.ext_iff, finset.image_image],
    intro x,
    split,

    intro x_in_img,
    simp only [finset.mem_image, function.comp_app] at x_in_img,
    choose y y_in_s gfy_eq_x using x_in_img,
    have y_in_X : y ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use s, split; assumption,
    end,
    specialize gf_id y_in_X,
    rw [←gfy_eq_x, gf_id],
    assumption,

    intro x_in_s,
    simp only [finset.mem_image, function.comp_app],
    use x, split, assumption,
    have x_in_X : x ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use s, split; assumption,
    end,
    specialize gf_id x_in_X,
    assumption,
  end,

  have g_simp : is_simplicial_map (St(Y, t) t_in_Y) (St(X, s) s_in_X) g.map, from
  begin
    simp only [is_simplicial_map, star, set.mem_sep_iff],
    intros u u_in_Y_star,
    choose u_in_Y tu_in_Y using u_in_Y_star,
    split,

    apply g.is_simplicial,
    assumption,

    rw [←gt_eq_s, ←finset.image_union],
    apply g.is_simplicial,
    assumption,
  end,
  let g_star := simplicial_map.mk g.map g_simp,

  use f_star,
  unfold is_simplicial_iso,

  use g_star,
  unfold is_inverse_simplicial_iso,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def],
  split,

  { intros x x_in_star,
    have x_in_X : x ∈ vertices X, from
    begin
      apply is_subcomplex_vertices X (St(X, s) s_in_X) (star_subcomplex X s s_in_X),
      assumption,
    end,
    specialize gf_id x_in_X,
    assumption, },

  { intros x x_in_star,
    have x_in_Y : x ∈ vertices Y, from
    begin
      apply is_subcomplex_vertices Y (St(Y, t) t_in_Y) (star_subcomplex Y t t_in_Y),
      assumption,
    end,
    specialize fg_id x_in_Y,
    assumption, },
end

-- Link of a complex wrt a simplex.
@[simp]
def link
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : simplicial_complex α
:= simplicial_complex.mk
    ({t ∈ X.simplices | (s ∪ t) ∈ X.simplices ∧ (s ∩ t) = ∅})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [set.mem_sep_iff],
      split,

      apply simplicial_complex_empty_simplex,

      split,

      rw [finset.union_empty],
      assumption,

      rw [finset.inter_empty],
    end)
    (begin
      simp,
      intros s_1 _ _ _ Hss1_inter t Ht_sset,

      split; split; try
      { revert Ht_sset,
        apply X.subset_closed,
        assumption, },
      
      { suffices : s ∪ t ⊆ s ∪ s_1,
        revert this,
        apply X.subset_closed,
        assumption,
        
        apply finset.union_subset_union; tauto, },

      { rw [←finset.disjoint_iff_inter_eq_empty],
        apply finset.disjoint_of_subset_right Ht_sset,
        rw [finset.disjoint_iff_inter_eq_empty],
        assumption, },
    end)
notation `Lk(` X `, ` s `)` := link X s

instance link.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : fintype (link X s s_in_X).simplices
:= begin
  simp only[link, simplicial_complex.simplices],
  rw [set.sep_and],

  have dec_left : decidable_pred (λ x : finset α, s ∪ x ∈ X.simplices), from
  begin
    unfold decidable_pred,
    intro x,
    apply set.decidable_mem_of_fintype,
  end,

  have fin_left : fintype ↥{x ∈ X.simplices | s ∪ x ∈ X.simplices}, from
  begin
    apply @set.fintype_sep _ _ _ _ dec_left,
    assumption,
  end,

  have dec_right : decidable_pred (λ x : finset α, s ∩ x = ∅), from
  begin
    unfold decidable_pred,
    intro x,
    apply set.decidable_mem_of_fintype,
  end,

  have fin_right : fintype ↥{x ∈ X.simplices | s ∩ x = ∅}, from
  begin
    apply @set.fintype_sep _ _ _ _ dec_right,
    assumption,
  end,

  apply @set.fintype_inter _ _ _ _ fin_left fin_right,
end

lemma link_coe_image_left
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
    (φ : simplicial_coe X β)
  : (Lk(φ[X], finset.image φ.coe s) (by { apply map_is_simplicial_onto_image, assumption, })).simplices
      ⊆ (simplicial_image (Lk(X, s) s_in_X) φ.coe).simplices
:= begin
  simp only [link, simplicial_image, set.subset_def],
  simp only [set.mem_sep_iff, set.mem_set_of],
  intros t t_in_link,
  choose t_in_φX st_in_φX st_disj using t_in_link,
  choose u u_in_X φu_t using t_in_φX,
  choose v v_in_X φv_st using st_in_φX,

  use u, split, split,
  assumption,

  split,
  rw [←φu_t, ←finset.image_union] at φv_st,
  have v_su : v = s ∪ u, from
  begin
    simp only [←finset.coe_inj, finset.coe_image, set.ext_iff] at φv_st ⊢,
    intros a,
    specialize φv_st (φ.coe a),
    cases φv_st with φv_ss_φsu φsu_ss_φv,
    split,

    intros a_in_v,
    have a_in_X : a ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use v, split; assumption,
    end,
    rw [←set.inj_on.mem_image_iff φ.injective] at a_in_v ⊢,
    specialize φv_ss_φsu a_in_v,
    assumption,

    rw [finset.coe_union],
    apply set.union_subset;
    { apply simplex_subset_vertices,
      assumption, },
    assumption,

    apply simplex_subset_vertices,
    assumption,
    assumption,

    intros a_in_su,
    have a_in_X : a ∈ vertices X, from
    begin
      rw [finset.coe_union, set.mem_union] at a_in_su,
      cases a_in_su with a_in_s a_in_u,

      rw [vertex_iff_in_simplex],
      use s, split; assumption,

      rw [vertex_iff_in_simplex],
      use u, split; assumption,
    end,
    rw [←set.inj_on.mem_image_iff φ.injective] at a_in_su ⊢,
    specialize φsu_ss_φv a_in_su,
    assumption,

    apply simplex_subset_vertices,
    assumption,
    assumption,

    rw [finset.coe_union],
    apply set.union_subset;
    { apply simplex_subset_vertices,
      assumption, },
    assumption,
  end,
  rw [←v_su],
  assumption,

  simp only [←φu_t, ←finset.coe_inj, finset.coe_image, finset.coe_inter] at st_disj,
  rw [←set.inj_on.image_inter, ←finset.coe_inter, ←finset.coe_image, finset.coe_inj, finset.image_eq_empty] at st_disj,
  assumption,

  apply φ.injective,
  apply simplex_subset_vertices,
  assumption,
  apply simplex_subset_vertices,
  assumption,

  assumption,
end

lemma link_coe_image_right
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
    (φ : simplicial_coe X β)
  : (simplicial_image (Lk(X, s) s_in_X) φ.coe).simplices
      ⊆ (Lk(φ[X], finset.image φ.coe s) (by { apply map_is_simplicial_onto_image, assumption, })).simplices
:= begin
  simp only [link, simplicial_image, set.subset_def],
  simp only [set.mem_sep_iff, set.mem_set_of],
  intros t t_in_img,
  choose u u_in_link φu_t using t_in_img,
  choose u_in_X su_in_X su_disj using u_in_link,

  split,
  use u, split; assumption,

  use (s ∪ u), split, assumption,
  rw [←φu_t, finset.image_union],

  simp only [←φu_t, ←finset.coe_inj, finset.coe_image, finset.coe_inter],
  rw [←set.inj_on.image_inter, ←finset.coe_inter, ←finset.coe_image, finset.coe_inj, finset.image_eq_empty],
  assumption,

  apply φ.injective,
  apply simplex_subset_vertices,
  assumption,
  apply simplex_subset_vertices,
  assumption,
end

lemma link_coe_image
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
    (φ : simplicial_coe X β)
  : (Lk(φ[X], finset.image φ.coe s) (by { apply map_is_simplicial_onto_image, assumption, })).simplices
      = (simplicial_image (Lk(X, s) s_in_X) φ.coe).simplices
:= begin
  rw [set.subset.antisymm_iff],
  split,

  apply link_coe_image_left,
  apply link_coe_image_right,
end

lemma link_subcomplex_simplices
    (X : simplicial_complex α)
    (s t : finset α)
    (s_in_X : s ∈ X.simplices)
  : t ∈ (Lk(X, s) s_in_X).simplices → t ∈ X.simplices
:= begin
  intros t_in_link,
  simp only [link, set.mem_sep_iff] at t_in_link,
  choose t_in_X st_in_X st_disj using t_in_link,
  assumption,
end

lemma link_subcomplex
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : Lk(X, s) s_in_X ⊆ X
:= begin
  simp only [is_subcomplex, set.subset_def],
  intro t,
  apply link_subcomplex_simplices,
end

lemma link_iso
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (s : finset α)
    (t : finset β)
    (f : simplicial_map X Y)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
    (f_iso : is_simplicial_iso f)
  : finset.image f.map s = t → Lk(X, s) s_in_X ≅ Lk(Y, t) t_in_Y
:= begin
  intro fs_eq_t,
  unfold is_simplicially_iso,

  have f_simp : is_simplicial_map (Lk(X, s) s_in_X) (Lk(Y, t) t_in_Y) f.map, from
  begin
    simp only [is_simplicial_map, link, set.mem_sep_iff],
    intros u u_in_X_link,
    choose u_in_X su_in_X su_disj using u_in_X_link,
    split,

    apply f.is_simplicial,
    assumption,

    simp only [←fs_eq_t, ←finset.image_union],
    split,
    apply f.is_simplicial,
    assumption,

    rw [←finset.image_inter_of_inj_on, finset.image_eq_empty],
    assumption,
    rw [←finset.coe_union],
    apply iso_is_injective_simplices f f_iso (s ∪ u),
    assumption,
  end,
  let f_link := simplicial_map.mk f.map f_simp,

  let f_iso' := f_iso,
  unfold is_simplicial_iso at f_iso',
  choose g gf_inv using f_iso',

  let gf_inv' := gf_inv,
  unfold is_inverse_simplicial_iso at gf_inv',
  choose gf_id fg_id using gf_inv',

  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at gf_id fg_id,

  have gt_eq_s : finset.image g.map t = s, from
  begin
    rw [←fs_eq_t, finset.ext_iff, finset.image_image],
    intro x,
    split,

    intro x_in_img,
    simp only [finset.mem_image, function.comp_app] at x_in_img,
    choose y y_in_s gfy_eq_x using x_in_img,
    have y_in_X : y ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use s, split; assumption,
    end,
    specialize gf_id y_in_X,
    rw [←gfy_eq_x, gf_id],
    assumption,

    intro x_in_s,
    simp only [finset.mem_image, function.comp_app],
    use x, split, assumption,
    have x_in_X : x ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use s, split; assumption,
    end,
    specialize gf_id x_in_X,
    assumption,
  end,

  have g_simp : is_simplicial_map (Lk(Y, t) t_in_Y) (Lk(X, s) s_in_X) g.map, from
  begin
    simp only [is_simplicial_map, link, set.mem_sep_iff],
    intros u u_in_Y_link,
    choose u_in_Y su_in_Y su_disj using u_in_Y_link,
    split,

    apply g.is_simplicial,
    assumption,

    simp only [←gt_eq_s, ←finset.image_union],
    split,
    apply g.is_simplicial,
    assumption,

    rw [←finset.image_inter_of_inj_on, finset.image_eq_empty],
    assumption,
    rw [←finset.coe_union],
    apply iso_is_injective_simplices g,

    apply iso_inv_is_iso f;
    assumption,

    assumption,
  end,
  let g_link := simplicial_map.mk g.map g_simp,

  use f_link,
  unfold is_simplicial_iso,

  use g_link,
  unfold is_inverse_simplicial_iso,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def],
  split,

  { intros x x_in_X_link,
    have x_in_X : x ∈ vertices X, from
    begin
      apply is_subcomplex_vertices X (Lk(X, s) s_in_X),
      apply link_subcomplex,
      assumption,
    end,
    specialize gf_id x_in_X,
    assumption, },

  { intros x x_in_Y_link,
    have x_in_Y : x ∈ vertices Y, from
    begin
      apply is_subcomplex_vertices Y (Lk(Y, t) t_in_Y),
      apply link_subcomplex,
      assumption,
    end,
    specialize fg_id x_in_Y,
    assumption, },
end

lemma link_fact_inter
    (X Y : simplicial_complex α)
    (s : finset α)
    (s_in_XY : s ∈ (X ∩ Y).simplices)
  : (Lk(X ∩ Y, s) s_in_XY).simplices =
      (Lk(X, s) (subcomplex_simplicial_inter_left_simplices X Y s s_in_XY)).simplices
        ∩ (Lk(Y, s) (subcomplex_simplicial_inter_right_simplices X Y s s_in_XY)).simplices
:= begin
  simp only [link, simplicial_inter, set.ext_iff, set.mem_inter_iff, set.mem_sep_iff],
  intro t,
  split,

  { intro t_in_link,
    choose t_in_XY st_in_XY st_disj using t_in_link,
    choose t_in_X t_in_Y using t_in_XY,
    choose st_in_X st_in_Y using st_in_XY,
    
    split, split,
    assumption,
    
    split; assumption,
    
    split, assumption,
    split; assumption, },

  { intro t_in_inter,
    choose t_in_X t_in_Y using t_in_inter,
    choose t_in_X st_in_X st_disj using t_in_X,
    choose t_in_Y st_in_Y st_disj using t_in_Y,
    
    split, split; assumption,
    split, split; assumption,
    assumption, },
end

lemma link_fact_union_left
    (X Y : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
    (s_nin_Y : s ∉ Y.simplices)
  : (Lk(X ∪ Y, s) (subcomplex_simplicial_union_left_simplices X Y s s_in_X)).simplices
      = (Lk(X, s) s_in_X).simplices
:= begin
  simp only [link, simplicial_union, set.ext_iff, set.mem_sep_iff, set.mem_union],
  intro t,
  split,

  { intro t_in_XY,
    choose t_in_XY st_in_XY st_disj using t_in_XY,
    cases t_in_XY with t_in_X contra;
    cases st_in_XY with st_in_X contra,
    
    split, assumption,
    split; assumption,
    
    have s_in_Y : s ∈ Y.simplices, from
    begin
      apply Y.subset_closed (s ∪ t),
      assumption,
      apply finset.subset_union_left,
    end,
    contradiction,
    
    split,
    apply X.subset_closed (s ∪ t),
    assumption,
    apply finset.subset_union_right,
    split; assumption,
    
    have s_in_Y : s ∈ Y.simplices, from
    begin
      apply Y.subset_closed (s ∪ t),
      assumption,
      apply finset.subset_union_left,
    end,
    contradiction, },

  { intro t_in_X,
    choose t_in_X st_in_X st_disj using t_in_X,
    
    split, left, assumption,
    split, left, assumption,
    assumption, },
end

lemma link_fact_union_right
    (X Y : simplicial_complex α)
    (s : finset α)
    (s_nin_X : s ∉ X.simplices)
    (s_in_Y : s ∈ Y.simplices)
  : (Lk(X ∪ Y, s) (subcomplex_simplicial_union_right_simplices X Y s s_in_Y)).simplices
      = (Lk(Y, s) s_in_Y).simplices
:= begin
  simp only [link, simplicial_union, set.ext_iff, set.mem_sep_iff, set.mem_union],
  intro t,
  split,

  { intro t_in_XY,
    choose t_in_XY st_in_XY st_disj using t_in_XY,
    cases t_in_XY with contra t_in_Y;
    cases st_in_XY with contra st_in_X,

    have s_in_X : s ∈ X.simplices, from
    begin
      apply X.subset_closed (s ∪ t),
      assumption,
      apply finset.subset_union_left,
    end,
    contradiction,

    split,
    apply Y.subset_closed (s ∪ t),
    assumption,
    apply finset.subset_union_right,
    split; assumption,

    have s_in_X : s ∈ X.simplices, from
    begin
      apply X.subset_closed (s ∪ t),
      assumption,
      apply finset.subset_union_left,
    end,
    contradiction,
    
    split, assumption,
    split; assumption, },

  { intro t_in_Y,
    choose t_in_Y st_in_Y st_disj using t_in_Y,
    
    split, right, assumption,
    split, right, assumption,
    assumption, },
end

lemma link_fact_union
    (X Y : simplicial_complex α)
    (s : finset α)
    (s_in_XY : s ∈ (X ∩ Y).simplices)
  : (Lk(X ∪ Y, s) (by { apply simplex_if_in_subcomplex (X ∩ Y),
                        assumption,
                        simp only [is_subcomplex, simplicial_inter, simplicial_union],
                        apply set.subset_union_of_subset_left,
                        apply set.inter_subset_left, })).simplices
        = (Lk(X, s) (by { apply subcomplex_simplicial_inter_left_simplices X Y s s_in_XY, })).simplices
          ∪ (Lk(Y, s) (by { apply subcomplex_simplicial_inter_right_simplices X Y s s_in_XY, })).simplices
:= begin
  simp only [link, simplicial_union, set.ext_iff, set.mem_sep_iff, set.mem_union],
  intro t,
  split,

  { intro t_in_XY,
    choose t_in_XY st_in_XY st_disj using t_in_XY,
    cases t_in_XY with t_in_X t_in_Y;
    cases st_in_XY with st_in_X st_in_Y,
    
    left,
    split, assumption,
    split; assumption,
    
    right,
    split,
    apply Y.subset_closed (s ∪ t),
    assumption,
    apply finset.subset_union_right,
    split; assumption,
    
    left,
    split,
    apply X.subset_closed (s ∪ t),
    assumption,
    apply finset.subset_union_right,
    split; assumption,
    
    right,
    split, assumption,
    split; assumption, },

  { intro t_in_inter,
    cases t_in_inter with t_in_X t_in_Y,
    
    choose t_in_X st_in_X st_disj using t_in_X,
    split, left, assumption,
    split, left, assumption,
    assumption,
    
    choose t_in_Y st_in_Y st_disj using t_in_Y,
    split, right, assumption,
    split, right, assumption,
    assumption, },
end

-- Complement of the star of a complex wrt a simplex.
@[simp]
def star_complement
    (X : simplicial_complex α)
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
  : simplicial_complex α
:= simplicial_complex.mk
    ({t ∈ X.simplices | ¬(s ⊆ t)})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [set.mem_sep_iff],
      split,

      apply simplicial_complex_empty_simplex,

      rw [finset.subset_empty],
      apply finset.nonempty.ne_empty,
      rw [←finset.nonempty_coe_sort],
      assumption,
    end)
    (begin
      simp,
      intros s_1 s1_in_X s_nsset_s1 t t_sset_s,
      split,

      apply X.subset_closed s_1;
      assumption,

      rw [finset.not_subset] at *,
      choose x Hx x_nin_s1 using s_nsset_s1,
      use x, split, assumption,
      revert x_nin_s1,
      contrapose,
      simp,
      apply finset.mem_of_subset,
      assumption,
    end)
notation X `\St(` X `, ` s `)` := star_complement X s

instance star_complement.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
  : fintype (star_complement X s s_in_X).simplices
:= begin
  simp only[star_complement, simplicial_complex.simplices],

  have H_dec : decidable_pred (λ t : finset α, ¬s ⊆ t), from
  begin
    unfold decidable_pred,
    intro t,
    simp only [finset.subset_iff, not_forall],
    apply finset.decidable_dexists_finset,
  end,

  apply @set.fintype_sep _ _ _ _ H_dec,
  assumption,
end

lemma star_complement_subcomplex_simplices
    (X : simplicial_complex α)
    (s t : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
  : t ∈ (X\St(X, s) s_in_X).simplices → t ∈ X.simplices
:= begin
  simp only [star_complement, set.mem_sep_iff],
  intro t_in_star_comp,
  choose t_in_X s_nss_t using t_in_star_comp,
  assumption,
end

lemma star_complement_subcomplex
    (X : simplicial_complex α)
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
  : X\St(X, s) s_in_X ⊆ X
:= begin
  simp only [is_subcomplex, set.subset_def],
  intro t,
  apply star_complement_subcomplex_simplices,
end

lemma star_complement_iso
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (s : finset α) [nonempty s]
    (t : finset β) [nonempty t]
    (f : simplicial_map X Y)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
    (f_iso : is_simplicial_iso f)
  : finset.image f.map s = t → (X\St(X, s) s_in_X) ≅ (Y\St(Y, t) t_in_Y)
:= begin
  intro fs_eq_t,
  unfold is_simplicially_iso,

  have f_simp : is_simplicial_map (X\St(X, s) s_in_X) (Y\St(Y, t) t_in_Y) f.map, from
  begin
    simp only [is_simplicial_map, star_complement, set.mem_sep_iff],
    intros u u_in_X_comp,
    choose u_in_X s_nss_u using u_in_X_comp,
    split,

    apply f.is_simplicial,
    assumption,

    simp only [←fs_eq_t, finset.image_subset_iff, not_forall, finset.mem_image, not_exists],
    simp only [finset.subset_iff, not_forall] at s_nss_u,
    choose x x_in_s x_nin_u using s_nss_u,
    use x, split,
    use x_in_s,

    intros y y_in_u,
    rw [@set.inj_on.eq_iff _ _ (vertices X)],
    revert y_in_u x_nin_u,
    contrapose,
    simp only [not_forall, not_not, exists_prop, and_imp],
    intros x_nin_u y_eq_x,
    rw [y_eq_x],
    assumption,

    apply iso_is_injective_vertices,
    assumption,

    rw [vertex_iff_in_simplex],
    use u, split; assumption,

    rw [vertex_iff_in_simplex],
    use s, split; assumption,
  end,
  let f_comp := simplicial_map.mk f.map f_simp,

  let f_iso' := f_iso,
  unfold is_simplicial_iso at f_iso',
  choose g gf_inv using f_iso',

  let gf_inv' := gf_inv,
  unfold is_inverse_simplicial_iso at gf_inv',
  choose gf_id fg_id using gf_inv',

  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at gf_id fg_id,

  have gt_eq_s : finset.image g.map t = s, from
  begin
    rw [←fs_eq_t, finset.ext_iff, finset.image_image],
    intro x,
    split,

    intro x_in_img,
    simp only [finset.mem_image, function.comp_app] at x_in_img,
    choose y y_in_s gfy_eq_x using x_in_img,
    have y_in_X : y ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use s, split; assumption,
    end,
    specialize gf_id y_in_X,
    rw [←gfy_eq_x, gf_id],
    assumption,

    intro x_in_s,
    simp only [finset.mem_image, function.comp_app],
    use x, split, assumption,
    have x_in_X : x ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use s, split; assumption,
    end,
    specialize gf_id x_in_X,
    assumption,
  end,

  have g_simp : is_simplicial_map (Y\St(Y, t) t_in_Y) (X\St(X, s) s_in_X) g.map, from
  begin
    simp only [is_simplicial_map, star_complement, set.mem_sep_iff],
    intros u u_in_Y_comp,
    choose u_in_X t_nss_u using u_in_Y_comp,
    split,

    apply g.is_simplicial,
    assumption,

    simp only [←gt_eq_s, finset.image_subset_iff, not_forall, finset.mem_image, not_exists],
    simp only [finset.subset_iff, not_forall] at t_nss_u,
    choose x x_in_t x_nin_u using t_nss_u,
    use x, split,
    use x_in_t,

    intros y y_in_u,
    rw [@set.inj_on.eq_iff _ _ (vertices Y)],
    revert y_in_u x_nin_u,
    contrapose,
    simp only [not_forall, not_not, exists_prop, and_imp],
    intros x_nin_u y_eq_x,
    rw [y_eq_x],
    assumption,

    apply iso_is_injective_vertices,
    apply iso_inv_is_iso f;
    assumption,

    rw [vertex_iff_in_simplex],
    use u, split; assumption,

    rw [vertex_iff_in_simplex],
    use t, split; assumption,
  end,
  let g_comp := simplicial_map.mk g.map g_simp,

  use f_comp,
  unfold is_simplicial_iso,

  use g_comp,
  unfold is_inverse_simplicial_iso,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def],
  split,

  { intros x x_in_X_comp,
    have x_in_X : x ∈ vertices X, from
    begin
      apply is_subcomplex_vertices X (X\St(X, s) s_in_X),
      apply star_complement_subcomplex,
      assumption,
    end,
    specialize gf_id x_in_X,
    assumption, },

  { intros x x_in_Y_comp,
    have x_in_Y : x ∈ vertices Y, from
    begin
      apply is_subcomplex_vertices Y (Y\St(Y, t) t_in_Y),
      apply star_complement_subcomplex,
      assumption,
    end,
    specialize fg_id x_in_Y,
    assumption, },
end

lemma star_complement_coe_image_left
    (X : simplicial_complex α)
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
    (φ : simplicial_coe X β)
  : (star_complement (φ[X]) (finset.image φ.coe s) (by { apply map_is_simplicial_onto_image, assumption, })).simplices
      ⊆ (simplicial_image (X\St(X, s) s_in_X) φ.coe).simplices
:= begin
  simp only [star_complement, simplicial_image, set.subset_def],
  simp only [set.mem_sep_iff, set.mem_set_of],
  intros t t_in_star_comp,
  choose t_in_φX φs_nss_t using t_in_star_comp,
  choose u u_in_X φu_t using t_in_φX,

  use u, split, split,
  assumption,

  rw [←φu_t] at φs_nss_t,
  revert φs_nss_t,
  contrapose,
  simp only [not_not],
  intros s_ss_u,
  apply finset.image_subset_image,
  assumption,

  assumption,
end

lemma star_complement_coe_image_right
    (X : simplicial_complex α)
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
    (φ : simplicial_coe X β)
  : (simplicial_image (X\St(X, s) s_in_X) φ.coe).simplices
      ⊆ (star_complement (φ[X]) (finset.image φ.coe s) (by { apply map_is_simplicial_onto_image, assumption, })).simplices
:= begin
  simp only [star_complement, simplicial_image, set.subset_def],
  simp only [set.mem_sep_iff, set.mem_set_of],
  intros t t_in_img,
  choose u u_in_star_comp φu_t using t_in_img,
  choose u_in_X s_nss_u using u_in_star_comp,

  split,
  use u, split; assumption,

  rw [←φu_t],
  revert s_nss_u,
  contrapose,
  simp only [not_not, finset.subset_iff],
  intros φs_ss_φu x x_in_s,

  have φx_in_φs : φ.coe x ∈ finset.image φ.coe s, from
  begin
    apply finset.mem_image_of_mem,
    assumption,
  end,
  specialize φs_ss_φu φx_in_φs,

  rw [←finset.mem_coe, finset.coe_image, set.inj_on.mem_image_iff, finset.mem_coe] at φs_ss_φu,
  assumption,

  apply φ.injective,
  apply simplex_subset_vertices,
  assumption,

  rw [vertex_iff_in_simplex],
  use s, split; assumption,
end

lemma star_complement_coe_image
    (X : simplicial_complex α)
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
    (φ : simplicial_coe X β)
  : (star_complement (φ[X]) (finset.image φ.coe s) (by { apply map_is_simplicial_onto_image, assumption, })).simplices =
      (simplicial_image (X\St(X, s) s_in_X) φ.coe).simplices
:= begin
  rw [set.subset.antisymm_iff],
  split,

  apply star_complement_coe_image_left,
  apply star_complement_coe_image_right,
end

@[simp]
def is_neg_one_sphere
    {X : simplicial_complex α}
    {s : finset α}
    {s_in_X : s ∈ X.simplices}
    (Y : simplicial_complex α)
    (Y_link_X : Y = Lk(X, s) s_in_X)
  : Prop
:= Y = empty_sc

@[simp]
def neg_one_ball
    {X : simplicial_complex α}
    (x : α)
    (x_nin_X : x ∉ vertices X)
  : simplicial_complex α
:= simplicial_complex.mk
    ({{x}, ∅})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      simp,
    end)
    (begin
      simp,
      intros t t_sset_empty,
      rw [finset.subset_empty] at t_sset_empty,
      tauto,
    end)

instance neg_one_ball.fintype
    {X : simplicial_complex α}
    (x : α)
    (x_nin_X : x ∉ vertices X)
  : fintype (neg_one_ball x x_nin_X).simplices
:= begin
  simp only [neg_one_ball],
  apply set.fintype_insert {x} {∅},
  apply finset.has_decidable_eq,
  apply set.fintype_singleton,
end

lemma dim_of_neg_one_ball
    {X : simplicial_complex α}
    (x : α)
    (x_nin_X : x ∉ vertices X)
  : dim_of_complex (neg_one_ball x x_nin_X) = 0
:= begin
  simp only [dim_of_complex, neg_one_ball, dim, set.to_finset_insert, set.to_finset_singleton, finset.image_insert, finset.card_singleton, nat.cast_one, sub_self],
  simp only [dim, finset.image_singleton, finset.card_empty, nat.cast_zero, zero_sub],
  unfold finset.max',
  simp only [finset.singleton_nonempty, id.def, finset.sup'_insert, finset.sup'_singleton, sup_of_le_left, right.neg_nonpos_iff, zero_le_one],
end

-- The ball around a simplex.
def m_ball
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : simplicial_complex α
:= simplicial_complex.mk
    (finset.powerset (vertices (Lk(X, s) s_in_X)).to_finset)
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      existsi ∅,
      apply finset.empty_mem_powerset,
    end)
    (begin
      unfold is_subset_closed,
      intros t t_in_link u u_ss_t,
      simp only [finset.mem_coe, finset.mem_powerset] at t_in_link ⊢,
      apply finset.subset.trans u_ss_t t_in_link,
    end)
notation `B(` X `, ` s `)` := m_ball X s

instance ball.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : fintype (m_ball X s s_in_X).simplices
:= begin
  simp only[m_ball, simplicial_complex.simplices],
  apply finset_coe.fintype,
end

-- The cone of a complex.
@[simp]
def cone
    (X : simplicial_complex α)
    (x : α)
    (x_nin_X : x ∉ vertices X)
  : simplicial_complex (α × ℕ)
:= (neg_one_ball x x_nin_X) ⋆ X
notation `Cone(` X `, ` x `)` := cone X x

instance cone.fintype
    (X : simplicial_complex α) [fintype X.simplices]
    (x : α)
    (x_nin_X : x ∉ vertices X)
  : fintype (Cone(X, x) x_nin_X).simplices
:= begin
  simp only [cone],
  apply simplicial_join.fintype,
end

def cone_iso_map
    (y : β)
    (f : α → β)
  : α × ℕ → β × ℕ
:= λ x : α × ℕ, if (x.snd = 0) then (y, 0) else (f x.fst, x.snd)

lemma cone_iso_simplicial
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (x : α)
    (y : β)
    (x_nin_X : x ∉ vertices X)
    (y_nin_Y : y ∉ vertices Y)
    (f : simplicial_map X Y)
  : is_simplicial_map (Cone(X, x) x_nin_X) (Cone(Y, y) y_nin_Y) (cone_iso_map y f.map)
:= begin
  simp only [is_simplicial_map, cone, neg_one_ball, simplicial_join_mem],
  intros u u_in_X_cone,
  choose s s_in_ball t t_in_X u_eq_st using u_in_X_cone,
  rw [set.mem_insert_iff, set.mem_singleton_iff] at s_in_ball,
  cases s_in_ball with s_eq_x s_empty,

  -- s = {x} case.
  use {y}, split,
  rw [set.mem_insert_iff],
  left, refl,

  use (finset.image f.map t), split,
  apply f.is_simplicial,
  assumption,

  simp only [u_eq_st, s_eq_x, simplex_disjoint_union, finset.image_union, cone_iso_map, finset.ext_iff],
  intro v,
  simp only [finset.mem_union, finset.mem_image, finset.mem_product, finset.mem_singleton],
  split,

  { intro v_in_img,
    cases v_in_img with v_in_lhs v_in_rhs,
    
    choose w w_in_lhs w_eq_v using v_in_lhs,
    choose w_eq_x w_zero using w_in_lhs,
    revert w_eq_v,
    split_ifs,
    
    intro y_eq_v,
    simp only [prod.ext_iff] at y_eq_v,
    choose y_eq_v v_zero using y_eq_v,
    rw [@comm _ eq] at y_eq_v v_zero,
    left, split; assumption,
    
    choose w w_in_rhs w_eq_v using v_in_rhs,
    choose w_in_t w_one using w_in_rhs,
    revert w_eq_v,
    split_ifs,
    
    have contra : w.snd ≠ 0, by omega,
    contradiction,
    
    intro w_eq_v,
    simp only [prod.ext_iff] at w_eq_v,
    choose w_eq_v v_one using w_eq_v,
    rw [w_one, @comm _ eq] at v_one,
    right, use w.fst, split; assumption,
    assumption, },

  { intro v_in_union,
    cases v_in_union with v_in_lhs v_in_rhs,
    
    choose v_eq_y v_zero using v_in_lhs,
    left, use (x, 0), split,
    simp only [prod.fst, prod.snd],
    split; refl,
    
    simp only [eq_self_iff_true, if_true, prod.ext_iff],
    rw [@comm _ eq] at v_eq_y v_zero,
    split; assumption,
    
    choose w_eq_v v_one using v_in_rhs,
    choose w w_in_t w_eq_v using w_eq_v,
    right, use (w, 1), split,
    simp only [prod.fst, prod.snd],
    split, assumption, refl,
    
    simp only [nat.one_ne_zero, if_false, prod.ext_iff],
    rw [@comm _ eq] at v_one,
    split; assumption, },

  -- s = ∅ case.
  use ∅, split, apply simplicial_complex_empty_simplex,
  use (finset.image f.map t), split,
  apply f.is_simplicial,
  assumption,

  simp only [u_eq_st, s_empty, simplex_disjoint_union, finset.image_union, cone_iso_map, finset.ext_iff],
  intro v,
  simp only [finset.mem_union, finset.mem_image, finset.mem_product, finset.mem_singleton],
  split,

  { intro v_in_img,
    cases v_in_img with v_empty v_in_t,

    choose w contra w_eq_v using v_empty,
    choose contra w_zero using contra,
    have H : w.fst ∉ ∅, by apply set.not_mem_empty,
    contradiction,
    
    choose w w_in_t w_eq_v using v_in_t,
    choose w_in_t w_one using w_in_t,
    revert w_eq_v,
    split_ifs,
    
    have contra : w.snd ≠ 0, by omega,
    contradiction,
    
    intro w_eq_v,
    simp only [prod.ext_iff] at w_eq_v,
    choose w_eq_v v_one using w_eq_v,
    rw [w_one, @comm _ eq] at v_one,
    right, use w.fst, split; assumption,
    assumption, },

  { intro v_in_union,
    cases v_in_union with contra v_in_t,
    
    choose contra v_zero using contra,
    have H : v.fst ∉ ∅, by apply set.not_mem_empty,
    contradiction,
    
    choose w_eq_v v_one using v_in_t,
    choose w w_in_t w_eq_v using w_eq_v,
    right, use (w, 1), split,
    simp only [prod.fst, prod.snd],
    split, assumption, refl,
    
    simp only [nat.one_ne_zero, if_false, prod.ext_iff],
    rw [@comm _ eq] at v_one,
    split; assumption, },
end

lemma cone_iso
    (X : simplicial_complex α)
    (Y : simplicial_complex β)
    (x : α)
    (y : β)
    (x_nin_X : x ∉ vertices X)
    (y_nin_Y : y ∉ vertices Y)
  : X ≅ Y → Cone(X, x) x_nin_X ≅ Cone(Y, y) y_nin_Y
:= begin
  intro X_iso_Y,
  unfold is_simplicially_iso at X_iso_Y ⊢,
  choose f f_iso using X_iso_Y,
  unfold is_simplicial_iso at f_iso ⊢,
  choose g gf_inv using f_iso,

  let f_cone : simplicial_map (Cone(X, x) x_nin_X) (Cone(Y, y) y_nin_Y) :=
    simplicial_map.mk (cone_iso_map y f.map) (cone_iso_simplicial X Y x y x_nin_X y_nin_Y f),

  let g_cone : simplicial_map (Cone(Y, y) y_nin_Y) (Cone(X, x) x_nin_X) :=
    simplicial_map.mk (cone_iso_map x g.map) (cone_iso_simplicial Y X y x y_nin_Y x_nin_X g),

  use f_cone, use g_cone,
  unfold is_inverse_simplicial_iso at gf_inv ⊢,
  simp only [set.restrict_eq_restrict_iff, set.eq_on, simplicial_map.comp, function.comp_app, id.def] at gf_inv ⊢,
  choose gf_id fg_id using gf_inv,
  split,

  { intros z z_in_X_cone,
    rw [vertex_iff_in_simplex] at z_in_X_cone,
    choose u u_in_cone z_in_u using z_in_X_cone,
    
    simp only [cone, neg_one_ball, simplicial_join] at u_in_cone,
    simp only [set.mem_set_of, set.mem_insert_iff, set.mem_singleton_iff] at u_in_cone,
    choose s s_in_ball t t_in_x st_eq_u using u_in_cone,
    rw [←st_eq_u, simplex_disjoint_mem] at z_in_u,
    cases z_in_u with z_in_ball z_in_t,
    
    cases s_in_ball with s_eq_x contra,
    rw [s_eq_x, finset.mem_singleton] at z_in_ball,
    choose z_eq_x z_zero using z_in_ball,
    simp only [cone_iso_map, prod.ext_iff, z_zero, eq_self_iff_true, if_true],
    split, symmetry, assumption,
    trivial,
    
    rw [contra] at z_in_ball,
    choose contra z_zero using z_in_ball,
    have H : z.fst ∉ ∅, by apply set.not_mem_empty,
    contradiction,
    
    choose z_in_t z_one using z_in_t,
    have z_in_X : z.fst ∈ vertices X, from
    begin
      rw [vertex_iff_in_simplex],
      use t, split; assumption,
    end,
    specialize gf_id z_in_X,
    
    simp only [cone_iso_map, z_one, nat.one_ne_zero, if_false, prod.ext_iff],
    split, assumption, refl, },

  { intros z z_in_Y_cone,
    rw [vertex_iff_in_simplex] at z_in_Y_cone,
    choose u u_in_cone z_in_u using z_in_Y_cone,
    
    simp only [cone, neg_one_ball, simplicial_join] at u_in_cone,
    simp only [set.mem_set_of, set.mem_insert_iff, set.mem_singleton_iff] at u_in_cone,
    choose s s_in_ball t t_in_x st_eq_u using u_in_cone,
    rw [←st_eq_u, simplex_disjoint_mem] at z_in_u,
    cases z_in_u with z_in_ball z_in_t,
    
    cases s_in_ball with s_eq_x contra,
    rw [s_eq_x, finset.mem_singleton] at z_in_ball,
    choose z_eq_x z_zero using z_in_ball,
    simp only [cone_iso_map, prod.ext_iff, z_zero, eq_self_iff_true, if_true],
    split, symmetry, assumption,
    trivial,
    
    rw [contra] at z_in_ball,
    choose contra z_zero using z_in_ball,
    have H : z.fst ∉ ∅, by apply set.not_mem_empty,
    contradiction,
    
    choose z_in_t z_one using z_in_t,
    have z_in_Y : z.fst ∈ vertices Y, from
    begin
      rw [vertex_iff_in_simplex],
      use t, split; assumption,
    end,
    specialize fg_id z_in_Y,
    
    simp only [cone_iso_map, z_one, nat.one_ne_zero, if_false, prod.ext_iff],
    split, assumption, refl, },
end

lemma dim_of_cone
    (X : simplicial_complex α) [fintype X.simplices]
    (x : α)
    (x_nin_X : x ∉ vertices X)
  : dim_of_complex (cone X x x_nin_X) = dim_of_complex X + 1
:= begin
  dsimp only [cone],
  rw [dim_of_join, dim_of_neg_one_ball],
  simp only [zero_add],
end

/-
# Subcomplexes Under Simplicial Join
-/

-- Distributive properties of join over certain subcomplexes.

-- Lemma 2.2 (1), p.7
lemma join_distl_link
    (X Y : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : Y ⋆ (Lk(X, s) s_in_X) ≅ Lk((X ⋆ Y), (s ⊔ₛ ∅)) (by { apply simplicial_join_incl_left, assumption, })
:= begin
  apply simplicial_iso_trans (Y ⋆ (Lk(X, s) s_in_X)) ((Lk(X, s) s_in_X) ⋆ Y),
  apply simplicial_join_comm,

  apply simplicial_iso_preserves_equiv,
  dsimp only[simplicial_join, link, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },

  split,
  { intro H,
    rcases H with ⟨t, Ht, u, Hu, Hx⟩,
    rw [set.mem_sep_iff] at Ht,
    rcases Ht with ⟨Ht, Hst, Hst_empty⟩,
    
    split,
    use t, split, tauto,
    use u, tauto,
    
    split,
    subst Hx,
    rw [simplex_disjoint_distr_union],
    use (s ∪ t), split, tauto,
    use u, split, tauto,
    simp,
    
    subst Hx,
    rw [simplex_disjoint_distr_inter],
    simp, tauto, },
  { intro H,
    rcases H with ⟨Hx, Hx_union, Hsx_empty⟩,
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩,
    rcases Hx_union with ⟨t', Ht', u', Hu', Hx_union⟩,
    
    subst Hx,
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at Hx_union,
    cases Hx_union with Ht' Hu',
    simp at Hu', subst Hu',

    rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at Hsx_empty,
    cases Hsx_empty with Hst_empty Hu'_trivial,
    
    use t, split,
    rw [set.mem_sep_iff],
    split; try { subst Ht' }; tauto,
    
    use u', tauto, }
end

-- Lemma 2.2 (2), p.7
lemma join_distl_star
    {a : Type*} [decidable_eq a]
    (X Y : simplicial_complex a)
    (s : finset a)
    (s_in_X : s ∈ X.simplices)
  : (Y ⋆ (St(X, s) s_in_X)) ≅ (St((X ⋆ Y), (s ⊔ₛ ∅)) (by { apply simplicial_join_incl_left, assumption }))
:= begin
  apply simplicial_iso_trans (Y ⋆ (St(X, s) s_in_X)) ((St(X, s) s_in_X) ⋆ Y),
  apply simplicial_join_comm,

  apply simplicial_iso_preserves_equiv,
  dsimp only[simplicial_join, star, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },

  split,
  { intro H,
    rcases H with ⟨t, Ht, u, Hu, Hx⟩,
    rw [set.mem_sep_iff] at Ht,
    cases Ht with Ht Hst,
    
    split,
    use t, split, tauto,
    use u, tauto,
    
    subst Hx,
    use (s ∪ t), split, tauto,
    use u,
    split; try { rw [simplex_disjoint_distr_union], simp, }; tauto, },
  { intro H,
    cases H with Hx Hx_union,
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩,
    rcases Hx_union with ⟨t', Ht', u', Hu', Hx_union⟩,
    
    subst Hx,
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at Hx_union,
    cases Hx_union with Ht' Hu',
    simp at Hu',
    subst Ht', subst Hu',
    
    use t, split,
    rw [set.mem_sep_iff]; try { simp }; tauto,
    use u', split; tauto, }
end

lemma join_distr_star_complement_simplices
    (X Y : simplicial_complex α)
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
  : ((star_complement X s s_in_X) ⋆ Y).simplices
      = (star_complement (X ⋆ Y) (s ⊔ₛ ∅) (by { apply simplicial_join_incl_left, assumption })).simplices
:= begin
  dsimp only[simplicial_join, star_complement, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },

  split,
  { intro H,
    rcases H with ⟨t, Ht, u, Hu, Hx⟩,
    rw [set.mem_sep_iff] at Ht,
    cases Ht with Ht Hs_not_sset_t,
    
    split,
    use t, split, tauto,
    use u, tauto,
    
    subst Hx,
    rw [simplex_disjoint_subset_unique],
    simp, tauto, },
  { intro H,
    cases H with Hx Hs_not_sset_x,
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩,
    
    subst Hx,
    rw [simplex_disjoint_subset_unique] at Hs_not_sset_x,
    simp at Hs_not_sset_x,
    
    use t, split,
    rw [set.mem_sep_iff], tauto,
    use u, split; tauto, }
end

lemma join_distr_star_complement
    (X Y : simplicial_complex α)
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
  : (star_complement X s s_in_X) ⋆ Y
      ≅ star_complement (X ⋆ Y) (s ⊔ₛ ∅) (by { apply simplicial_join_incl_left, assumption })
:= begin
  apply simplicial_iso_preserves_equiv,
  apply join_distr_star_complement_simplices,
end

-- Lemma 2.2 (3), p.7
lemma join_distl_star_complement
    (X Y : simplicial_complex α)
    (s : finset α) [nonempty s]
    (s_in_X : s ∈ X.simplices)
  : Y ⋆ (star_complement X s s_in_X) ≅ star_complement (X ⋆ Y) (s ⊔ₛ ∅) (by { apply simplicial_join_incl_left, assumption })
:= begin
  apply simplicial_iso_trans (Y ⋆ (star_complement X s s_in_X)) ((star_complement X s s_in_X) ⋆ Y),
  apply simplicial_join_comm,
  apply join_distr_star_complement,
end

-- Lemma 2.3, p.8
lemma join_fact_link
    (X Y : simplicial_complex α)
    (s t : finset α)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
  : Lk(X ⋆ Y, s ⊔ₛ t) (by { rw [simplicial_join_sep], tauto }) ≅ Lk(X, s) s_in_X ⋆ Lk(Y, t) t_in_Y
:= begin
  apply simplicial_iso_preserves_equiv,
  dsimp only[link, simplicial_join, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },
  
  split,
  { intros H,
    cases H,
    rcases H_left with ⟨s', Hs', t', Ht', Hx⟩,
    cases H_right with H_left H_inter,
    rcases H_left with ⟨s'', Hs'', t'', Ht'', H_union⟩,
    
    subst Hx,
    rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at H_inter,
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at H_union,
    cases H_union with H_s_union H_t_union,
    subst H_s_union, subst H_t_union,
    
    use s', split,
    rw [set.mem_sep_iff],
    split; tauto,
    
    use t',
    rw [set.mem_sep_iff],
    split; tauto, },
  { intros H,
    rcases H with ⟨s', Hs', t', Ht', Hx⟩,
    rw [set.mem_sep_iff] at Hs' Ht',

    split,
    { use s', split, tauto,
      use t', tauto, },
    { use (s ∪ s'), split, tauto,
      use (t ∪ t'), split, tauto,
      
      subst Hx,
      rw [simplex_disjoint_distr_union],
      
      subst Hx,
      rw [simplex_disjoint_distr_inter, simplex_disjoint_empty],
      tauto, } },
end

-- Lemma 2.4 (1), p.8
lemma join_distr_union_left
    (X Y Z : simplicial_complex α)
  : X ⋆ (Y ∪ Z) ≅ (X ⋆ Y) ∪ (X ⋆ Z)
:= begin
  apply simplicial_iso_preserves_equiv,
  dsimp only[simplicial_join, simplicial_union, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },

  split,
  { intro H,
    rcases H with ⟨s, Hs, t, Ht, Hx⟩,
    
    rw [←set.set_of_or, set.mem_set_of],
    rw [set.mem_union] at Ht,
    
    destruct Ht,
    
    intro Hy,
    left,
    use s, split, tauto,
    use t, tauto,
    
    intro Hz,
    right,
    use s, split, tauto,
    use t, tauto, },
  { intro H,
    rw [←set.set_of_or, set.mem_set_of] at H,
    destruct H,
    
    intro Hy,
    rcases Hy with ⟨s, Hs, t, Ht, Hx⟩,
    use s, split, tauto,
    use t, rw [set.mem_union], tauto,
    
    intro Hz,
    rcases Hz with ⟨s, Hs, t, Ht, Hx⟩,
    use s, split, tauto,
    use t, rw [set.mem_union], tauto, }
end

-- Lemma 2.4 (2), p.8
lemma join_distr_inter_left
    (X Y Z : simplicial_complex α)
  : X ⋆ (Y ∩ Z) ≅ (X ⋆ Y) ∩ (X ⋆ Z)
:= begin
  apply simplicial_iso_preserves_equiv,
  dsimp only[simplicial_join, simplicial_inter, simplicial_complex.simplices],

  rw [set.ext_iff],
  intro x,
  repeat { rw [set.mem_set_of] },

  split,
  { intro H,
    rcases H with ⟨s, Hs, t, Ht, Hx⟩,
    
    rw [←set.set_of_and, set.mem_set_of],
    rw [set.mem_inter_iff] at Ht,
    cases Ht with Hy Hz,
    
    split,
    
    use s, split, tauto,
    use t, tauto,
    
    use s, split, tauto,
    use t, tauto, },
  { intro H,
    rw [←set.set_of_and, set.mem_set_of] at H,
    cases H with Hy Hz,
    
    rcases Hy with ⟨sy, Hsy, ty, Hty, Hxy⟩,
    rcases Hz with ⟨sz, Hsz, tz, Htz, Hxz⟩,
    subst Hxy,
    rw [simplex_disjoint_eq_unique] at Hxz,
    cases Hxz with Hsz Htz,
    subst Hsz, subst Htz,
    
    use sz, split, tauto,
    use tz, rw [set.mem_inter_iff], tauto, }
end

/-
# Properties of Links
-/

lemma link_ident
    (X : simplicial_complex α)
  : (Lk(X, ∅) (by { apply simplicial_complex_empty_simplex })).simplices
      = X.simplices
:= begin
  simp only [link, set.ext_iff, set.mem_sep_iff],
  simp only [finset.empty_union, finset.empty_inter],
  simp only [eq_self_iff_true, and_true, and_self, iff_self, forall_const],
end

lemma link_ident_iso
    (X : simplicial_complex α)
  : Lk(X, ∅) (by { apply simplicial_complex_empty_simplex }) ≅ X
:= begin
  apply simplicial_iso_preserves_equiv,
  apply link_ident,
end

lemma link_disjoint_base
    (X : simplicial_complex α)
    (s t : finset α)
    (s_in_X : s ∈ X.simplices)
  : t ∈ (Lk(X, s) s_in_X).simplices → disjoint s t
:= begin
  intro t_in_link,
  simp only [link, set.mem_sep_iff] at t_in_link,
  choose t_in_X st_in_X st_disj using t_in_link,

  rw [finset.disjoint_iff_inter_eq_empty],
  assumption,
end

lemma face_in_link_of_complement
    (X : simplicial_complex α)
    (s t : finset α)
    (s_in_X : s ∈ X.simplices)
    (t_sset_s : t ⊆ s)
  : s \ t ∈ (Lk(X, t) (by { apply X.subset_closed s; assumption, })).simplices
:= begin
  simp only [link, set.mem_sep_iff],
  split,

  apply X.subset_closed s,
  assumption,
  apply finset.sdiff_subset,

  split,
  rw [finset.union_comm, finset.sdiff_union_self_eq_union, finset.union_eq_left_iff_subset.mpr];
  assumption,

  apply finset.inter_sdiff_self,
end

-- Lemma 3.5, p.14
lemma link_of_face_complement
    (X : simplicial_complex α)
    (s t : finset α)
    (s_in_X : s ∈ X.simplices)
    (t_sset_s : t ⊆ s)
  : Lk(X, s) s_in_X ≅ Lk(Lk(X, t) (by { apply X.subset_closed s; assumption }), s \ t) (by { apply face_in_link_of_complement })
:= begin
  by_cases (s = t),

  simp only [h, finset.sdiff_self],
  rw [simplicial_iso_symm],
  apply link_ident_iso,

  apply simplicial_iso_preserves_equiv,
  simp only [link, set.ext_iff],
  intro u,
  split,

  { intro u_in_link,
    rw [set.mem_sep_iff] at *,
    choose u_in_X su_in_X su_empty using u_in_link,
    repeat { rw [set.mem_sep_iff] },
    split,

    split, assumption,
    split,

    apply X.subset_closed (s ∪ u),
    assumption,
    apply finset.union_subset_union,
    assumption,
    apply finset.subset.refl,
    
    rw [←su_empty],
    apply finset.inter_congr_right,
    rw [su_empty],
    apply finset.empty_subset,
    apply @finset.subset.trans _ (t ∩ u) t s,
    apply finset.inter_subset_left,
    assumption,
    
    split, split,
    apply X.subset_closed (s ∪ u),
    assumption,
    apply finset.union_subset_union,
    apply finset.sdiff_subset,
    apply finset.subset.refl,
    
    split,
    rw [←finset.union_assoc, finset.union_comm t, finset.sdiff_union_self_eq_union],
    have Hts : s ∪ t = s, by { rw [finset.union_eq_left_iff_subset], assumption },
    rw [Hts],
    assumption,
    
    rw [finset.inter_distrib_left, finset.inter_sdiff_self, finset.union_comm, finset.union_empty],
    rw [←su_empty],
    apply finset.inter_congr_right,
    rw [su_empty],
    apply finset.empty_subset,
    apply @finset.subset.trans _ (t ∩ u) t s,
    apply finset.inter_subset_left,
    assumption,
    
    rw [←finset.subset_empty, ←su_empty],
    apply finset.inter_subset_inter_right,
    apply finset.sdiff_subset, },

  { intro u_in_link_of_link,
    rw [set.mem_sep_iff] at *,
    choose u_in_t_link stu_in_t_link stu_empty using u_in_link_of_link,
    rw [set.mem_sep_iff] at *,
    choose u_in_X tu_in_X tu_empty using u_in_t_link,
    choose stu_in_X t_stu_in_X t_stu_empty using stu_in_t_link,
    
    split, assumption,
    split,
    
    rw [←finset.union_assoc, finset.union_comm t, finset.sdiff_union_self_eq_union] at t_stu_in_X,
    have Hts : s ∪ t = s, by { rw [finset.union_eq_left_iff_subset], assumption },
    rw [Hts] at t_stu_in_X,
    assumption,
    
    have Hst : s \ t ∪ t = s, by { apply finset.sdiff_union_of_subset, assumption },
    have Hstu : (s \ t ∩ u) ∪ (t ∩ u) = ∅, from
    begin
      rw [finset.union_eq_empty_iff],
      split; assumption,
    end,
    rw [←Hst, finset.inter_distrib_right],
    assumption, },
end

lemma barycenter_disjoint_boundary
    (X : simplicial_complex α)
    (s : finset α)
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : disjoint (vertices (simplex {x})) (vertices (∂s))
:= begin
  rw [set.disjoint_left],
  intros y y_in_barycenter,
  apply @set.not_mem_subset _ _ _ (vertices X),
  rw [set.subset_def],
  intro z,
  apply simplex_boundary_subcomplex_vert X s z s_in_X,

  dsimp only [vertices, simplex, simplicial_complex.simplices] at y_in_barycenter,
  simp only [set.mem_Union] at y_in_barycenter,
  choose t Ht y_in_t using y_in_barycenter,

  simp only [finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at Ht,
  cases Ht with t_empty t_ne,
  rw [←finset.coe_eq_empty, set.eq_empty_iff_forall_not_mem] at t_empty,
  specialize t_empty y,
  contradiction,

  rw [finset.eq_singleton_iff_unique_mem] at t_ne,
  cases t_ne with x_in_t y_eq_x,
  specialize y_eq_x y,
  rw [finset.mem_coe] at y_in_t,
  specialize y_eq_x y_in_t,
  rw [y_eq_x],
  apply x_nin_X,
end

lemma barycenter_join_boundary_disjoint_link
    (X : simplicial_complex α)
    (s : finset α)
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : disjoint (vertices ((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)]))
              (vertices (Lk(X, s) s_in_X))
:= begin
  rw [set.disjoint_left],
  intros y y_in_join,
  rw [join_proj_vertices_mem] at y_in_join,

  dsimp only [vertices, link, simplicial_complex.simplices],
  simp only [set.mem_Union, not_exists],
  intros u u_in_link,
  simp only [set.mem_sep_iff] at u_in_link,
  rcases u_in_link with ⟨u_in_X, su_in_X, su_empty⟩,

  cases y_in_join with y_in_barycenter y_in_bd,

  -- y ∈ {x}
  dsimp only [vertices, simplex, simplicial_complex.simplices] at y_in_barycenter,
  simp only [set.mem_Union] at y_in_barycenter,
  choose t Ht y_in_t using y_in_barycenter,
  
  rw [finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at Ht,
  cases Ht with t_empty t_ne,
  rw [←finset.coe_eq_empty, set.eq_empty_iff_forall_not_mem] at t_empty,
  specialize t_empty y,
  contradiction,

  rw [finset.mem_coe, t_ne, finset.mem_singleton] at y_in_t,
  simp only [vertices, set.mem_Union, not_exists] at x_nin_X,
  specialize x_nin_X u,
  specialize x_nin_X u_in_X,
  rw [y_in_t],
  apply x_nin_X,

  -- y ∈ ∂s
  dsimp only [vertices, simplex_boundary, simplicial_complex.simplices] at y_in_bd,
  simp only [set.mem_Union] at y_in_bd,
  choose t Ht y_in_t using y_in_bd,

  rw [set.mem_union, set.mem_diff, finset.mem_coe, finset.mem_powerset, finset.subset_iff] at Ht,
  cases Ht with t_ne t_empty,

  cases t_ne with y_in_s t_eq_s,
  rw [finset.mem_coe] at y_in_t,
  specialize y_in_s y_in_t,
  rw [←finset.coe_eq_empty, set.eq_empty_iff_forall_not_mem] at su_empty,
  specialize su_empty y,
  rw [finset.mem_coe, finset.mem_inter, not_and_distrib] at su_empty,
  cases su_empty with contra y_nin_u,
  contradiction,
  rw [finset.mem_coe],
  apply y_nin_u,

  rw [set.mem_singleton_iff, ←finset.coe_eq_empty, set.eq_empty_iff_forall_not_mem] at t_empty,
  specialize t_empty y,
  contradiction,
end

lemma boundary_disjoint_link
    (X : simplicial_complex α)
    (s : finset α)
    (s_in_X : s ∈ X.simplices)
  : disjoint (vertices (Lk(X, s) s_in_X)) (vertices (∂s))
:= begin
  rw [set.disjoint_iff_inter_eq_empty, set.eq_empty_iff_forall_not_mem],
  intro x,
  simp only [set.mem_inter_iff, not_and, vertex_iff_in_simplex, not_exists],
  intros t_in_link u u_in_bd,

  simp only [link, set.mem_sep_iff] at t_in_link,
  choose t t_in_link x_in_t using t_in_link,
  choose t_in_X st_in_X st_disj using t_in_link,
  
  simp only [simplex_boundary, set.mem_union, set.mem_diff, finset.mem_coe, finset.mem_powerset] at u_in_bd,
  cases u_in_bd with u_in_bd u_empty,

  choose u_ss_s u_ne_s using u_in_bd,
  have ut_disj : u ∩ t = ∅, from
  begin
    rw [←finset.subset_empty],
    apply @finset.subset.trans _ _ (s ∩ t),
    apply finset.inter_subset_inter_right u_ss_s,

    rw [finset.subset_empty],
    assumption,
  end,
  rw [finset.eq_empty_iff_forall_not_mem] at ut_disj,
  specialize ut_disj x,
  rw [finset.mem_inter, not_and] at ut_disj,

  by_cases x_in_u : x ∈ u,
  specialize ut_disj x_in_u,
  contradiction,
  assumption,

  rw [set.mem_singleton_iff] at u_empty,
  rw [u_empty],
  apply finset.not_mem_empty,
end

lemma barycenter_disjoint_link
    (X : simplicial_complex α)
    (s : finset α)
    (x : α)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : disjoint (vertices (Lk(X, s) s_in_X)) (vertices (simplex {x}))
:= begin
  rw [set.disjoint_iff_inter_eq_empty, set.eq_empty_iff_forall_not_mem],
  intro y,
  simp only [set.mem_inter_iff, not_and, vertex_iff_in_simplex, not_exists],
  intros t_in_link u u_in_barycenter,

  simp only [link, set.mem_sep_iff] at t_in_link,
  choose t t_in_link y_in_t using t_in_link,
  choose t_in_X st_in_X st_disj using t_in_link,

  simp only [simplex, finset.mem_coe, finset.mem_powerset, finset.subset_singleton_iff] at u_in_barycenter,
  cases u_in_barycenter with u_empty u_eq_x,

  rw [u_empty],
  apply finset.not_mem_empty,

  have ut_disj : u ∩ t = ∅, from
  begin
    rw [←finset.coe_inj, finset.coe_empty, ←set.subset_empty_iff, finset.coe_inter],
    apply @set.subset.trans _ _ ({x} ∩ (vertices X)),

    apply set.inter_subset_inter,
    simp only [u_eq_x, finset.coe_singleton],
    apply simplex_subset_vertices,
    assumption,

    rw [set.subset_empty_iff, set.eq_empty_iff_forall_not_mem],
    intro y,
    simp only [set.mem_inter_iff, set.mem_singleton_iff, not_and],
    intro y_eq_x,
    subst y_eq_x,
    assumption,
  end,

  simp only [finset.eq_empty_iff_forall_not_mem, finset.mem_inter, not_and] at ut_disj,
  specialize ut_disj y,

  by_cases y_in_u : y ∈ u,
  specialize ut_disj y_in_u,
  contradiction,
  assumption,
end

lemma disjoint_complexes_disjoint_simplices
    (X Y : simplicial_complex α)
    (s t : finset α)
    (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices)
    (XY_disj : disjoint (vertices X) (vertices Y))
  : disjoint s t
:= begin
  rw [←finset.disjoint_coe],
  apply @set.disjoint_of_subset _ _ (vertices X) _ (vertices Y),

  apply simplex_subset_vertices,
  assumption,

  apply simplex_subset_vertices,
  assumption,

  assumption,
end