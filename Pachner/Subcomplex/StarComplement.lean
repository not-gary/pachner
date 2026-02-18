import Pachner.Maps.SimplicialCoercion

variable {E F : Type _}
variable [DecidableEq E] [DecidableEq F]
variable {X : AbstractSimplicialComplex E}

-- Complement of the star of a complex wrt a simplex.
@[simp]
def StarComplement
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
  : AbstractSimplicialComplex E :=
    AbstractSimplicialComplex.mk ({t ∈ X.faces | ¬s ⊆ t})
    (by
      rw [Set.mem_setOf, not_and_or, not_not]
      left; apply X.empty_notMem)
    (by
      intro t u t_in_comp u_sset_t u_ne
      rw [Set.mem_setOf] at ⊢ t_in_comp
      choose t_in_X s_nsset_t using t_in_comp
      constructor
      apply X.down_closed t_in_X u_sset_t u_ne

      rw [Finset.not_subset] at *
      choose x Hx x_nin_t using s_nsset_t
      use x; constructor; assumption
      revert x_nin_t
      contrapose
      simp
      apply Finset.mem_of_subset
      assumption)

notation X "\\St(" X ", " s ")" => StarComplement X s

instance StarComplement.fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (s : Finset E)
  : Fintype (X\St(X, s)).faces :=
by
  simp only [StarComplement]
  have H_dec : DecidablePred fun t : Finset E => ¬s ⊆ t :=
  by
    unfold DecidablePred
    intro t
    simp only [Finset.subset_iff, Classical.not_forall]
    apply Finset.decidableDExistsFinset
  apply @Set.fintypeSep _ _ _ _ H_dec

theorem starComplement_subcomplex_simplices
    (s t : Finset E)
  : t ∈ X\St(X, s).faces → t ∈ X.faces :=
by
  simp only [StarComplement, Set.mem_sep_iff]
  intro t_in_star_comp
  choose t_in_X s_nss_t using t_in_star_comp
  assumption

theorem starComplement_subcomplex (s : Finset E) : X\St(X, s) ⊆ X := by
  simp only [IsSubcomplex, AbstractSimplicialComplex.instHasSubset, Set.subset_def]
  intro t
  apply starComplement_subcomplex_simplices

theorem starComplement_simplicialIso
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
    {s : Finset E}
    {t : Finset F}
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces)
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : Finset.image f.map s = t → X\St(X, s) ≅ Y\St(Y, t) :=
by
  intro fs_eq_t
  unfold IsSimpliciallyIso
  have f_simp : IsSimplicialMap (X\St(X, s)) (Y\St(Y, t)) f.map :=
  by
    simp only [IsSimplicialMap, StarComplement, Set.mem_sep_iff]
    intro u u_in_X_comp
    choose u_in_X s_nss_u using u_in_X_comp
    constructor
    apply f.is_simplicial
    assumption
    simp only [← fs_eq_t, Finset.image_subset_iff, Classical.not_forall, Finset.mem_image,
      not_exists]
    simp only [Finset.subset_iff, Classical.not_forall] at s_nss_u
    choose x x_in_s x_nin_u using s_nss_u
    use x
    use x_in_s
    intro y
    rw [not_and_or]
    by_cases y_in_u : y ∈ u

    rw [@Set.InjOn.eq_iff _ _ X.vertices]
    revert y_in_u x_nin_u
    contrapose
    simp only [Classical.not_forall, Classical.not_not, exists_prop, and_imp, not_or, not_not]
    intro y_in_u _ y_eq_x
    rw [← y_eq_x]
    assumption

    apply simplicialIso_injective_vertices
    assumption
    rw [vertex_iff_in_face]
    use u
    rw [vertex_iff_in_face]
    use s

    left; assumption
  let f_comp := SimplicialMap.mk f.map f_simp
  let f_iso' := f_iso
  unfold IsSimplicialIso at f_iso'
  choose g gf_inv using f_iso'
  let gf_inv' := gf_inv
  unfold IsInverseSimplicialIso at gf_inv'
  choose gf_id fg_id using gf_inv'
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id] at gf_id fg_id
  have gt_eq_s : Finset.image g.map t = s :=
    by
    rw [← fs_eq_t, Finset.ext_iff, Finset.image_image]
    intro x
    constructor
    intro x_in_img
    simp only [Finset.mem_image, Function.comp_apply] at x_in_img
    choose y y_in_s gfy_eq_x using x_in_img
    have y_in_X : y ∈ X.vertices := by
      rw [vertex_iff_in_face]
      use s
    specialize gf_id y_in_X
    rw [← gfy_eq_x, gf_id]
    assumption
    intro x_in_s
    simp only [Finset.mem_image, Function.comp_apply]
    use x; constructor; assumption
    have x_in_X : x ∈ X.vertices := by
      rw [vertex_iff_in_face]
      use s
    specialize gf_id x_in_X
    assumption
  have g_simp : IsSimplicialMap (Y\St(Y, t)) (X\St(X, s)) g.map :=
  by
    simp only [IsSimplicialMap, StarComplement, Set.mem_sep_iff]
    intro u u_in_Y_comp
    choose u_in_X t_nss_u using u_in_Y_comp
    constructor
    apply g.is_simplicial
    assumption
    simp only [← gt_eq_s, Finset.image_subset_iff, Classical.not_forall, Finset.mem_image,
      not_exists, not_and_or]
    simp only [Finset.subset_iff, Classical.not_forall] at t_nss_u
    choose x x_in_t x_nin_u using t_nss_u
    use x
    use x_in_t
    intro y
    by_cases y_in_u : y ∈ u

    right
    rw [@Set.InjOn.eq_iff _ _ Y.vertices]
    revert y_in_u x_nin_u
    contrapose
    simp only [Classical.not_forall, Classical.not_not, exists_prop, and_imp]
    intro x_nin_u y_eq_x
    rw [← y_eq_x]
    assumption
    apply simplicialIso_injective_vertices
    apply simplicialIso_inverse_is_simplicialIso f <;> assumption
    rw [vertex_iff_in_face]
    use u
    rw [vertex_iff_in_face]
    use t; constructor; assumption
  let g_comp := SimplicialMap.mk g.map g_simp
  use f_comp
  unfold IsSimplicialIso
  use g_comp
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id]
  constructor
  · intro x x_in_X_comp
    have x_in_X : x ∈ X.vertices := isSubcomplex_vertices (starComplement_subcomplex s) x x_in_X_comp
    specialize gf_id x_in_X
    assumption
  · intro x x_in_Y_comp
    have x_in_Y : x ∈ Y.vertices := isSubcomplex_vertices (starComplement_subcomplex t) x x_in_Y_comp
    specialize fg_id x_in_Y
    assumption

theorem starComplement_simplicialCoe_image_left
    {s : Finset E}
    {φ : SimplicialCoe X F}
  : (StarComplement (φ.coe ''ˢ X) (Finset.image φ.coe s)) ⊆ (φ.coe ''ˢ X\St(X, s)) :=
by
  simp only [StarComplement, SimplicialImage, Set.subset_def]
  intro t t_in_star_comp
  choose t_in_φX φs_nss_t using t_in_star_comp
  choose u u_in_X φu_t using t_in_φX
  use u; constructor; constructor
  assumption
  rw [← φu_t] at φs_nss_t
  revert φs_nss_t
  contrapose
  simp only [Classical.not_not]
  intro s_ss_u
  apply Finset.image_subset_image
  assumption
  assumption

theorem starComplement_simplicialCoe_image_right
    {s : Finset E}
    {φ : SimplicialCoe X F}
    (s_in_X : s ∈ X.faces)
  : (φ.coe ''ˢ X\St(X, s)) ⊆ (StarComplement (φ.coe ''ˢ X) (Finset.image φ.coe s)) :=
by
  simp only [StarComplement, SimplicialImage, Set.subset_def]
  intro t t_in_img
  choose u u_in_star_comp φu_t using t_in_img
  choose u_in_X s_nss_u using u_in_star_comp
  constructor
  use u
  rw [← φu_t]
  revert s_nss_u
  contrapose
  simp only [Classical.not_not, Finset.subset_iff]
  intro φs_ss_φu x x_in_s
  have φx_in_φs : φ.coe x ∈ Finset.image φ.coe s :=
    by
    apply Finset.mem_image_of_mem
    assumption
  specialize φs_ss_φu φx_in_φs
  rw [← Finset.mem_coe, Finset.coe_image, Set.InjOn.mem_image_iff, Finset.mem_coe] at φs_ss_φu
  assumption
  apply φ.Injective
  apply face_subset_vertices
  assumption
  rw [vertex_iff_in_face]
  use s

-- TODO: werid assymetry in ..._left and ..._right with hypothesis s_in_X
theorem starComplement_simplicialCoe_image
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
    (φ : SimplicialCoe X F)
  : (StarComplement (φ.coe ''ˢ X) (Finset.image φ.coe s)) = (φ.coe ''ˢ (X\St(X, s))) :=
by
  rw [AbstractSimplicialComplex.ext_iff, Set.Subset.antisymm_iff]
  exact ⟨starComplement_simplicialCoe_image_left, starComplement_simplicialCoe_image_right s_in_X⟩
