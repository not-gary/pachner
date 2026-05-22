import Pachner.Maps.SimplicialCoercion

variable
  {E F : Type _}
  [DecidableEq F]
  {X : AbstractSimplicialComplex E} {s t : Finset E} {x : E}

def FaceBoundary
    (s : Finset E)
  : AbstractSimplicialComplex E :=
    AbstractSimplicialComplex.mk (Finset.powerset s \ {s, ∅})
    (by
      simp only [Finset.coe_powerset, Set.mem_diff, Set.mem_preimage, Finset.coe_empty,
        Set.mem_powerset_iff, Set.empty_subset, Set.mem_insert_iff, Set.mem_singleton_iff, or_true,
        not_true_eq_false, and_false, not_false_eq_true])
    (by
      intro t u t_in_power u_sset_t u_ne
      rw [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, not_or] at ⊢ t_in_power
      choose t_sset_s t_ne_s t_ne using t_in_power
      constructor

      apply subset_trans u_sset_t t_sset_s
      constructor

      have t_ssset_s : t ⊂ s :=
      by
        rw [Finset.ssubset_iff_subset_ne]
        constructor <;> assumption
      have u_ssset_s : u ⊂ s :=
      by
        apply ssubset_of_subset_of_ssubset u_sset_t t_ssset_s
      rw [Finset.ssubset_iff_subset_ne] at u_ssset_s
      choose u_sset_s u_ne_s using u_ssset_s
      assumption

      assumption)

prefix:75 "∂" => FaceBoundary

instance FaceBoundary.fintype [DecidableEq E] (s : Finset E) : Fintype (∂s).faces :=
by
  unfold FaceBoundary
  apply Set.fintypeDiff

theorem faceBoundary_subcomplex_simplex : ∂s ⊆ Simplex s := by
  simp only [IsSubcomplex, Simplex, FaceBoundary, Set.subset_def]
  intro t t_in_bd
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, not_or] at t_in_bd
  simp only [Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
  choose t_sset_s t_ne_s t_ne using t_in_bd
  constructor <;> assumption

def faceBoundary_simplicialIso'  [DecidableEq E] (f : Simplex s ≅' Simplex t) : ∂s ≅' ∂t where
  toFun := {
    map := f.toFun.map
    is_simplicial := (by
      have fs_ss_t : f.toFun.map '' s ⊆ t := by
        rw [← simplex_vertices t, AbstractSimplicialComplex.vertices]
        intro y y_in_fs
        rw [Set.mem_image] at y_in_fs
        choose x x_in_s fx_eq_y using y_in_fs
        subst fx_eq_y
        simp only [Set.mem_setOf, ← Finset.image_singleton]
        apply f.toFun.is_simplicial
        simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
        constructor
        rw [Finset.singleton_subset_iff]; assumption
        apply Finset.singleton_ne_empty

      have f_inj : Set.InjOn f.toFun.map s := by
        rw [← simplex_vertices]
        exact f.injective_vertices

      simp only [IsSimplicialMap, FaceBoundary]
      simp only [Set.mem_union, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
        Finset.mem_powerset, not_or]
      intro u u_in_s
      choose u_sset_s u_ne_s u_ne using u_in_s
      constructor
      simp only [← Finset.coe_subset, ← Finset.coe_inj, ← simplex_vertices t]
      apply face_subset_vertices
      apply f.toFun.is_simplicial
      simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
      constructor <;> assumption

      constructor
      simp only [Finset.ext_iff, not_forall, not_iff] at ⊢ u_ne_s
      choose x x_nin_u using u_ne_s
      rw [iff_def] at x_nin_u
      choose x_in_s x_nin_u using x_nin_u
      use f.toFun.map x
      constructor

      intro fx_nin_fu
      have x_nin_u : x ∉ u :=
      by
        revert fx_nin_fu
        contrapose
        simp only [not_not, Finset.mem_image]
        intro x_in_u; use x
      specialize x_in_s x_nin_u
      rw [Set.subset_def] at fs_ss_t
      have fx_in_fs : f.toFun.map x ∈ f.toFun.map '' ↑s :=
      by
        rw [Set.mem_image]
        use x; constructor
        assumption
        rfl
      specialize fs_ss_t (f.toFun.map x) fx_in_fs
      assumption

      have u_sset_s' : u ⊆ s := by assumption
      rw [← Finset.coe_subset, Set.subset_def] at u_sset_s
      specialize u_sset_s x
      rw [Finset.mem_coe] at u_sset_s
      have x_in_s : x ∈ s :=
      by
        by_cases H : x ∈ u
        specialize u_sset_s H; assumption
        specialize x_in_s H; assumption
      specialize x_nin_u x_in_s
      intro fx_in_t
      revert x_nin_u
      contrapose
      simp only [not_not]
      simp only [not_not, Finset.mem_image]
      intro x_in_u
      choose a a_in_u fa_eq_fx using x_in_u
      simp only [Set.InjOn] at f_inj
      specialize f_inj x_in_s
      have a_in_s : a ∈ s :=
      by
        revert a_in_u
        apply Finset.mem_of_subset u_sset_s'
      symm at fa_eq_fx
      specialize f_inj a_in_s fa_eq_fx
      subst f_inj
      assumption

      rw [Finset.image_eq_empty]; assumption) }
  invFun := {
    map := f.invFun.map
    is_simplicial := (by
      have gt_ss_s : f.invFun.map '' t ⊆ s := by
        rw [← simplex_vertices s, AbstractSimplicialComplex.vertices]
        intro y y_in_gt
        rw [Set.mem_image] at y_in_gt
        choose x x_in_s gx_eq_y using y_in_gt
        subst gx_eq_y
        simp only [Set.mem_setOf, ← Finset.image_singleton]
        apply f.invFun.is_simplicial
        simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
        constructor
        rw [Finset.singleton_subset_iff]; assumption
        apply Finset.singleton_ne_empty
      have g_inj : Set.InjOn f.invFun.map t := by
        rw [← simplex_vertices]
        exact f.symm.injective_vertices

      simp only [IsSimplicialMap, FaceBoundary]
      simp only [Set.mem_union, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
        Finset.mem_powerset, not_or]
      intro u u_in_t
      choose u_sset_t u_ne_t u_ne using u_in_t
      constructor
      simp only [← Finset.coe_subset, ← Finset.coe_inj, ← simplex_vertices s]
      apply face_subset_vertices
      apply f.invFun.is_simplicial
      simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
      constructor <;> assumption

      constructor
      simp only [Finset.ext_iff, not_forall, not_iff] at ⊢ u_ne_t
      choose x x_nin_u using u_ne_t
      rw [iff_def] at x_nin_u
      choose x_in_t x_nin_u using x_nin_u
      use f.invFun.map x
      constructor

      intro gx_nin_gu
      have x_nin_u : x ∉ u :=
      by
        revert gx_nin_gu
        contrapose
        simp only [not_not, Finset.mem_image]
        intro x_in_u; use x
      specialize x_in_t x_nin_u
      rw [Set.subset_def] at gt_ss_s
      have gx_in_gt : f.invFun.map x ∈ f.invFun.map '' ↑t :=
      by
        rw [Set.mem_image]
        use x; constructor
        assumption
        rfl
      specialize gt_ss_s (f.invFun.map x) gx_in_gt
      assumption

      have u_sset_t' : u ⊆ t := by assumption
      rw [← Finset.coe_subset, Set.subset_def] at u_sset_t
      specialize u_sset_t x
      rw [Finset.mem_coe] at u_sset_t
      have x_in_t : x ∈ t :=
      by
        by_cases H : x ∈ u
        specialize u_sset_t H; assumption
        specialize x_in_t H; assumption
      specialize x_nin_u x_in_t
      intro gx_in_s
      revert x_nin_u
      contrapose
      simp only [not_not]
      simp only [not_not, Finset.mem_image]
      intro x_in_u
      choose a a_in_u ga_eq_gx using x_in_u
      simp only [Set.InjOn] at g_inj
      specialize g_inj x_in_t
      have a_in_t : a ∈ t :=
      by
        revert a_in_u
        apply Finset.mem_of_subset u_sset_t'
      symm at ga_eq_gx
      specialize g_inj a_in_t ga_eq_gx
      subst g_inj
      assumption

      rw [Finset.image_eq_empty]; assumption) }
  left_inv x_in_bd := f.left_inv (faceBoundary_subcomplex_simplex x_in_bd)
  right_inv x_in_bd := f.right_inv (faceBoundary_subcomplex_simplex x_in_bd)

@[deprecated faceBoundary_simplicialIso' (since := "")]
theorem faceBoundary_simplicialIso  [DecidableEq E] : (Simplex s ≅ Simplex t) → ∂s ≅ ∂t := by
  intro s_iso_t
  unfold IsSimpliciallyIso at s_iso_t ⊢
  choose f f_iso using s_iso_t
  let f_iso' := f_iso
  unfold IsSimplicialIso at f_iso'
  choose g gf_inv using f_iso'
  have g_iso : IsSimplicialIso g := by apply simplicialIso_inverse_is_simplicialIso f g f_iso gf_inv
  unfold IsInverseSimplicialIso at gf_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id] at gf_inv
  choose gf_id fg_id using gf_inv

  have fs_ss_t : f.map '' s ⊆ t :=
  by
    rw [← simplex_vertices t, AbstractSimplicialComplex.vertices]
    intro y y_in_fs
    rw [Set.mem_image] at y_in_fs
    choose x x_in_s fx_eq_y using y_in_fs
    subst fx_eq_y
    simp only [Set.mem_setOf, ← Finset.image_singleton]
    apply f.is_simplicial
    simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
    constructor
    rw [Finset.singleton_subset_iff]; assumption
    apply Finset.singleton_ne_empty

  have gt_ss_s : g.map '' t ⊆ s :=
  by
    rw [← simplex_vertices s, AbstractSimplicialComplex.vertices]
    intro y y_in_gt
    rw [Set.mem_image] at y_in_gt
    choose x x_in_s gx_eq_y using y_in_gt
    subst gx_eq_y
    simp only [Set.mem_setOf, ← Finset.image_singleton]
    apply g.is_simplicial
    simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
    constructor
    rw [Finset.singleton_subset_iff]; assumption
    apply Finset.singleton_ne_empty

  have f_inj : Set.InjOn f.map s :=
  by
    rw [← simplex_vertices]
    apply simplicialIso_injective_vertices
    assumption

  have g_inj : Set.InjOn g.map t :=
  by
    rw [← simplex_vertices]
    apply simplicialIso_injective_vertices
    assumption

  have f_simp : IsSimplicialMap (∂s) (∂t) f.map :=
  by
    simp only [IsSimplicialMap, FaceBoundary]
    simp only [Set.mem_union, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
      Finset.mem_powerset, not_or]
    intro u u_in_s
    choose u_sset_s u_ne_s u_ne using u_in_s
    constructor
    simp only [← Finset.coe_subset, ← Finset.coe_inj, ← simplex_vertices t]
    apply face_subset_vertices
    apply f.is_simplicial
    simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
    constructor <;> assumption

    constructor
    simp only [Finset.ext_iff, not_forall, not_iff] at ⊢ u_ne_s
    choose x x_nin_u using u_ne_s
    rw [iff_def] at x_nin_u
    choose x_in_s x_nin_u using x_nin_u
    use f.map x
    constructor

    intro fx_nin_fu
    have x_nin_u : x ∉ u :=
    by
      revert fx_nin_fu
      contrapose
      simp only [not_not, Finset.mem_image]
      intro x_in_u; use x
    specialize x_in_s x_nin_u
    rw [Set.subset_def] at fs_ss_t
    have fx_in_fs : f.map x ∈ f.map '' ↑s :=
    by
      rw [Set.mem_image]
      use x; constructor
      assumption
      rfl
    specialize fs_ss_t (f.map x) fx_in_fs
    assumption

    have u_sset_s' : u ⊆ s := by assumption
    rw [← Finset.coe_subset, Set.subset_def] at u_sset_s
    specialize u_sset_s x
    rw [Finset.mem_coe] at u_sset_s
    have x_in_s : x ∈ s :=
    by
      by_cases H : x ∈ u
      specialize u_sset_s H; assumption
      specialize x_in_s H; assumption
    specialize x_nin_u x_in_s
    intro fx_in_t
    revert x_nin_u
    contrapose
    simp only [not_not]
    simp only [not_not, Finset.mem_image]
    intro x_in_u
    choose a a_in_u fa_eq_fx using x_in_u
    simp only [Set.InjOn] at f_inj
    specialize f_inj x_in_s
    have a_in_s : a ∈ s :=
    by
      revert a_in_u
      apply Finset.mem_of_subset u_sset_s'
    symm at fa_eq_fx
    specialize f_inj a_in_s fa_eq_fx
    subst f_inj
    assumption

    rw [Finset.image_eq_empty]; assumption

  have g_simp : IsSimplicialMap (∂t) (∂s) g.map :=
  by
    simp only [IsSimplicialMap, FaceBoundary]
    simp only [Set.mem_union, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
      Finset.mem_powerset, not_or]
    intro u u_in_t
    choose u_sset_t u_ne_t u_ne using u_in_t
    constructor
    simp only [← Finset.coe_subset, ← Finset.coe_inj, ← simplex_vertices s]
    apply face_subset_vertices
    apply g.is_simplicial
    simp only [Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
    constructor <;> assumption

    constructor
    simp only [Finset.ext_iff, not_forall, not_iff] at ⊢ u_ne_t
    choose x x_nin_u using u_ne_t
    rw [iff_def] at x_nin_u
    choose x_in_t x_nin_u using x_nin_u
    use g.map x
    constructor

    intro gx_nin_gu
    have x_nin_u : x ∉ u :=
    by
      revert gx_nin_gu
      contrapose
      simp only [not_not, Finset.mem_image]
      intro x_in_u; use x
    specialize x_in_t x_nin_u
    rw [Set.subset_def] at gt_ss_s
    have gx_in_gt : g.map x ∈ g.map '' ↑t :=
    by
      rw [Set.mem_image]
      use x; constructor
      assumption
      rfl
    specialize gt_ss_s (g.map x) gx_in_gt
    assumption

    have u_sset_t' : u ⊆ t := by assumption
    rw [← Finset.coe_subset, Set.subset_def] at u_sset_t
    specialize u_sset_t x
    rw [Finset.mem_coe] at u_sset_t
    have x_in_t : x ∈ t :=
    by
      by_cases H : x ∈ u
      specialize u_sset_t H; assumption
      specialize x_in_t H; assumption
    specialize x_nin_u x_in_t
    intro gx_in_s
    revert x_nin_u
    contrapose
    simp only [not_not]
    simp only [not_not, Finset.mem_image]
    intro x_in_u
    choose a a_in_u ga_eq_gx using x_in_u
    simp only [Set.InjOn] at g_inj
    specialize g_inj x_in_t
    have a_in_t : a ∈ t :=
    by
      revert a_in_u
      apply Finset.mem_of_subset u_sset_t'
    symm at ga_eq_gx
    specialize g_inj a_in_t ga_eq_gx
    subst g_inj
    assumption

    rw [Finset.image_eq_empty]; assumption

  let f_bd : SimplicialMap (∂s) (∂t) := SimplicialMap.mk f.map f_simp
  let g_bd : SimplicialMap (∂t) (∂s) := SimplicialMap.mk g.map g_simp
  use f_bd; use g_bd
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id]
  constructor
  · intro x x_in_bd
    have x_in_s : x ∈ (Simplex s).vertices := isSubcomplex_vertices (faceBoundary_subcomplex_simplex) x x_in_bd
    specialize gf_id x_in_s
    assumption
  · intro x x_in_bd
    have x_in_t : x ∈ (Simplex t).vertices := isSubcomplex_vertices (faceBoundary_subcomplex_simplex) x x_in_bd
    specialize fg_id x_in_t
    assumption

theorem faceBoundary_simplicialCoe_image_left
    [Nonempty E] [DecidableEq E]
    {φ : SimplicialCoe X F}
    (s_in_X : s ∈ X.faces)
  : (∂Finset.image φ.coe s) ⊆ (SimplicialImage φ.coe (∂s)) :=
by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex]
  simp only [FaceBoundary, SimplicialImage, Set.subset_def]
  simp only [Set.mem_setOf, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset]
  intro t t_in_bd
  choose t_ss_φs t_ne_φs_ne_empty using t_in_bd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at t_ne_φs_ne_empty
  choose t_ne_φs t_ne_empty using t_ne_φs_ne_empty
  have inv_t : Finset.image φ.coe (Finset.image (φ⁻ᶜ).map t) = t :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image, Set.ext_iff, Set.mem_image]
    have inv_b (x : F) (H : x ∈ ↑t) : φ.coe (φ⁻ᶜ.map x) = x :=
      by
      apply Set.InjOn.rightInvOn_of_leftInvOn
      apply simplicialCoeInv_injective
      apply Set.InjOn.leftInvOn_invFunOn
      apply φ.Injective
      apply Set.SurjOn.mapsTo_invFunOn
      apply simplicialCoe_surjective_vertices
      apply simplicialCoe_mapsTo_vertices
      rw [vertex_iff_in_face]
      use t
      exact ⟨(φ.coe ''ˢ X).down_closed (isSimplicialMap_onto_image _ _ _ s_in_X) t_ss_φs t_ne_empty, H⟩
    intro y
    constructor
    intro y_in_img
    choose a a_in_img φa_y using y_in_img
    choose b b_in_t φb_a using a_in_img
    subst φb_a
    subst φa_y
    rw [inv_b]
    assumption
    assumption
    intro y_in_t
    use φ⁻ᶜ.map y
    constructor
    use y
    rw [inv_b]
    assumption
  use Finset.image (φ⁻ᶜ).map t
  constructor
  have inv_s : Finset.image (φ⁻ᶜ).map (Finset.image φ.coe s) = s :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.Injective
    apply face_subset_vertices
    assumption
  constructor
  have inv_t_ss_φs : Finset.image (φ⁻ᶜ).map t ⊆ Finset.image (φ⁻ᶜ).map (Finset.image φ.coe s) :=
    by
    apply Finset.image_subset_image
    assumption
  rw [inv_s] at inv_t_ss_φs
  simp only [Finset.mem_coe, Finset.mem_powerset, inv_t_ss_φs]
  revert t_ne_φs
  contrapose
  simp only [Classical.not_not]
  intro φt_eq_s_or_empty
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.image_eq_empty] at φt_eq_s_or_empty
  cases' φt_eq_s_or_empty with φt_eq_s t_empty
  · apply_fun fun x => Finset.image φ.coe x at φt_eq_s
    rw [inv_t] at φt_eq_s
    assumption
  · rw [t_empty] at t_ne_empty
    simp only [not_true_eq_false] at t_ne_empty
  assumption

theorem faceBoundary_simplicialCoe_image_right
    {φ : SimplicialCoe X F}
    (s_in_X : s ∈ X.faces)
  : (SimplicialImage φ.coe (∂s)) ⊆ (∂Finset.image φ.coe s) :=
by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex]
  simp only [FaceBoundary, SimplicialImage, Set.subset_def]
  simp only [Set.mem_setOf, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset]
  intro t t_in_img
  choose u u_in_bd φu_t using t_in_img
  choose u_ss_s u_ne_s_ne_empty using u_in_bd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at u_ne_s_ne_empty
  choose u_ne_s u_not_empty using u_ne_s_ne_empty
  constructor
  rw [← φu_t]
  apply Finset.image_subset_image
  simp only [Finset.mem_coe, Finset.mem_powerset] at u_ss_s
  assumption
  rw [← φu_t]
  revert u_ne_s
  contrapose
  simp only [Classical.not_not]
  intro φu_eq_φs

  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.image_eq_empty] at φu_eq_φs
  cases' φu_eq_φs with φu_eq_φs u_empty
  · simp only [← Finset.coe_inj, Finset.coe_image, Set.ext_iff] at φu_eq_φs ⊢
    intro a
    specialize φu_eq_φs (φ.coe a)
    constructor
    simp
    intro a_in_u
    rw [Finset.mem_coe, Finset.mem_powerset] at u_ss_s
    specialize u_ss_s a_in_u
    assumption
    intro a_in_s
    rw [Set.InjOn.mem_image_iff] at φu_eq_φs
    rw [φu_eq_φs]
    rw [Set.mem_image]
    use a
    apply φ.Injective
    apply face_subset_vertices
    apply X.down_closed
    apply s_in_X
    rw [Finset.mem_coe, Finset.mem_powerset] at u_ss_s
    assumption
    assumption
    rw [vertex_iff_in_face]
    use s
    constructor <;> assumption
  · rw [u_empty] at u_not_empty
    simp only [not_true_eq_false] at u_not_empty

theorem faceBoundary_simplicialCoe_image
    [Nonempty E] [DecidableEq E]
    (s_in_X : s ∈ X.faces)
    (φ : SimplicialCoe X F)
  : (∂(Finset.image φ.coe s)) = (SimplicialImage φ.coe (∂s)) :=
by
  rw [AbstractSimplicialComplex.ext_iff, Set.Subset.antisymm_iff]
  exact ⟨faceBoundary_simplicialCoe_image_left s_in_X, faceBoundary_simplicialCoe_image_right s_in_X ⟩

theorem faceBoundary_subcomplex (s_in_X : s ∈ X.faces) : ∂s ⊆ X := by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def]
  intro t t_in_bd
  simp only [FaceBoundary, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at t_in_bd
  choose t_ss_s _ t_nonempty using t_in_bd
  exact X.down_closed s_in_X t_ss_s t_nonempty

theorem faceBoundary_subcomplex_vertices (s_in_X : s ∈ X.faces) : x ∈ (∂s).vertices → x ∈ X.vertices :=
by
  apply isSubcomplex_vertices (faceBoundary_subcomplex s_in_X)

theorem faceBoundary_mem_iff_subset : t ∈ (∂s).faces ↔ t ⊂ s ∧ t ≠ ∅ := by
  simp only [FaceBoundary, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, not_or,
    Set.mem_insert_iff, Finset.ssubset_iff_subset_ne, and_assoc, Set.notMem_singleton_iff]

theorem faceBoundary_subface_subcomplex : s ⊆ t → ∂s ⊆ ∂t := by
  simp only [IsSubcomplex, FaceBoundary, Set.subset_def, Finset.subset_iff]
  intro s_ss_t u u_in_bd_s
  simp only [Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
    Set.mem_singleton_iff] at u_in_bd_s ⊢
  choose u_ss_s u_ne_s_empty using u_in_bd_s
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at u_ne_s_empty
  choose u_ne_s u_ne_empty using u_ne_s_empty
  constructor
  simp only [Finset.subset_iff] at u_ss_s ⊢
  intro x x_in_u
  specialize u_ss_s x_in_u
  specialize s_ss_t u_ss_s
  assumption
  simp
  constructor
  revert u_ne_s
  contrapose
  simp only [Classical.not_not]
  intro u_eq_t
  subst u_eq_t
  rw [Finset.ext_iff]
  intro x; constructor
  intro x_in_u
  specialize u_ss_s x_in_u
  assumption
  intro x_in_s
  specialize s_ss_t x_in_s
  assumption
  assumption
