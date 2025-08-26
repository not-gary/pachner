import Mathlib.Tactic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Pachner.SimplicialComplex
import Pachner.SimplicialMap

variable {E F : Type _}
variable [DecidableEq E] [DecidableEq F]

-- Boundary of a single simplex.
def simplexBoundary
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

prefix:75 "∂" => simplexBoundary

instance simplexBoundary.fintype (s : Finset E) : Fintype (∂s).faces :=
by
  unfold simplexBoundary
  dsimp only [AbstractSimplicialComplex.faces]
  apply Set.fintypeDiff

theorem simplexBoundary_subcomplex_simplex
    (s : Finset E)
  : ∂s ⊆ simplex s :=
by
  simp only [IsSubcomplex, simplex, simplexBoundary, Set.subset_def]
  intro t t_in_bd
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset, not_or] at t_in_bd
  simp only [Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
  choose t_sset_s t_ne_s t_ne using t_in_bd
  constructor <;> assumption

theorem simplexBoundary_iso
    (s : Finset E) [Nonempty s]
    (t : Finset F) [Nonempty t]
  : (simplex s ≅ simplex t) → ∂s ≅ ∂t :=
by
  intro s_iso_t
  unfold IsSimpliciallyIso at s_iso_t ⊢
  choose f f_iso using s_iso_t
  let f_iso' := f_iso
  unfold IsSimplicialIso at f_iso'
  choose g gf_inv using f_iso'
  have g_iso : IsSimplicialIso g := by apply iso_inv_is_iso f g f_iso gf_inv
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
    simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
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
    simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
    constructor
    rw [Finset.singleton_subset_iff]; assumption
    apply Finset.singleton_ne_empty

  have f_inj : Set.InjOn f.map s :=
  by
    rw [← simplex_vertices]
    apply iso_is_injective_vertices
    assumption

  have g_inj : Set.InjOn g.map t :=
  by
    rw [← simplex_vertices]
    apply iso_is_injective_vertices
    assumption

  have f_simp : IsSimplicialMap (∂s) (∂t) f.map :=
  by
    simp only [IsSimplicialMap, simplexBoundary]
    simp only [Set.mem_union, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
      Finset.mem_powerset, not_or]
    intro u u_in_s
    choose u_sset_s u_ne_s u_ne using u_in_s
    constructor
    simp only [← Finset.coe_subset, ← Finset.coe_inj, ← simplex_vertices t]
    apply simplex_subset_vertices
    apply f.is_simplicial
    simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
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
    simp only [IsSimplicialMap, simplexBoundary]
    simp only [Set.mem_union, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
      Finset.mem_powerset, not_or]
    intro u u_in_t
    choose u_sset_t u_ne_t u_ne using u_in_t
    constructor
    simp only [← Finset.coe_subset, ← Finset.coe_inj, ← simplex_vertices s]
    apply simplex_subset_vertices
    apply g.is_simplicial
    simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_powerset]
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
    have x_in_s : x ∈ AbstractSimplicialComplex.vertices E (simplex s) :=
      by
      apply is_subcomplex_vertices _ (∂s)
      apply simplexBoundary_subcomplex_simplex
      assumption
    specialize gf_id x_in_s
    assumption
  · intro x x_in_bd
    have x_in_t : x ∈ AbstractSimplicialComplex.vertices F (simplex t) :=
      by
      apply is_subcomplex_vertices _ (∂t)
      apply simplexBoundary_subcomplex_simplex
      assumption
    specialize fg_id x_in_t
    assumption

theorem simplexBoundary_coe_image_left
    [Nonempty E]
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
    (φ : SimplicialCoe X F)
  : (∂Finset.image φ.coe s).faces ⊆ (simplicialImage φ.coe (∂s)).faces :=
by
  simp only [simplexBoundary, simplicialImage, Set.subset_def]
  simp only [Set.mem_setOf, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset]
  intro t t_in_bd
  choose t_ss_φs t_ne_φs_ne_empty using t_in_bd
  simp at t_ne_φs_ne_empty
  choose t_ne_φs t_ne_empty using t_ne_φs_ne_empty
  have inv_t : Finset.image φ.coe (Finset.image (φ⁻ᶜ).map t) = t :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image, Set.ext_iff, Set.mem_image]
    have inv_b (x : F) (H : x ∈ ↑t) : φ.coe (φ⁻ᶜ.map x) = x :=
      by
      apply Set.InjOn.rightInvOn_of_leftInvOn
      apply simplicialCoeInv_inj
      apply Set.InjOn.leftInvOn_invFunOn
      apply φ.Injective
      apply Set.SurjOn.mapsTo_invFunOn
      apply simplicialCoe_surjective_vertices
      apply simplicialCoe_mapsTo_vertices
      rw [vertex_iff_in_simplex]
      use t
      constructor
      apply (φ.coe ''ˢ X).down_closed
      apply map_is_simplicial_onto_image
      assumption
      assumption
      assumption
      assumption
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
    apply simplex_subset_vertices
    assumption
  constructor
  have inv_t_ss_φs : Finset.image (φ⁻ᶜ).map t ⊆ Finset.image (φ⁻ᶜ).map (Finset.image φ.coe s) :=
    by
    apply Finset.image_subset_image
    assumption
  rw [inv_s] at inv_t_ss_φs
  assumption
  revert t_ne_φs
  contrapose
  simp only [Classical.not_not]
  intro φt_eq_s_or_empty
  simp at φt_eq_s_or_empty
  cases' φt_eq_s_or_empty with φt_eq_s t_empty
  · apply_fun fun x => Finset.image φ.coe x at φt_eq_s
    rw [inv_t] at φt_eq_s
    assumption
  · rw [t_empty] at t_ne_empty
    simp at t_ne_empty
  assumption

theorem simplexBoundary_coe_image_right
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
    (φ : SimplicialCoe X F)
  : (simplicialImage φ.coe (∂s)).faces ⊆ (∂Finset.image φ.coe s).faces :=
by
  simp only [simplexBoundary, simplicialImage, Set.subset_def]
  simp only [Set.mem_setOf, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset]
  intro t t_in_img
  choose u u_in_bd φu_t using t_in_img
  choose u_ss_s u_ne_s_ne_empty using u_in_bd
  simp at u_ne_s_ne_empty
  choose u_ne_s u_not_empty using u_ne_s_ne_empty
  constructor
  rw [← φu_t]
  apply Finset.image_subset_image
  assumption
  rw [← φu_t]
  revert u_ne_s
  contrapose
  simp only [Classical.not_not]
  intro φu_eq_φs

  simp at φu_eq_φs
  cases' φu_eq_φs with φu_eq_φs u_empty
  · simp only [← Finset.coe_inj, Finset.coe_image, Set.ext_iff] at φu_eq_φs ⊢
    intro a
    specialize φu_eq_φs (φ.coe a)
    constructor
    simp
    intro a_in_u
    rw [Finset.subset_iff] at u_ss_s
    specialize u_ss_s a_in_u
    assumption
    intro a_in_s
    rw [Set.InjOn.mem_image_iff] at φu_eq_φs
    rw [φu_eq_φs]
    rw [Set.mem_image]
    use a
    apply φ.Injective
    apply simplex_subset_vertices
    apply X.down_closed
    apply s_in_X
    assumption
    assumption
    rw [vertex_iff_in_simplex]
    use s
    constructor <;> assumption
  · rw [u_empty] at u_not_empty
    simp at u_not_empty

theorem simplexBoundary_coe_image
    [Nonempty E]
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
    (φ : SimplicialCoe X F)
  : (∂(Finset.image φ.coe s)).faces = (simplicialImage φ.coe (∂s)).faces :=
by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply simplexBoundary_coe_image_left
  assumption
  apply simplexBoundary_coe_image_right
  assumption

theorem simplexBoundary_subcomplex_simplices
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (s_in_X : s ∈ X.faces)
  : t ∈ (∂s).faces → t ∈ X.faces :=
by
  intro t_in_bd
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset]
      at t_in_bd
  choose t_ss_s t_ne_s_empty using t_in_bd
  simp at t_ne_s_empty
  choose t_ne_s t_ne_empty using t_ne_s_empty
  apply X.down_closed <;> assumption

theorem simplexBoundary_subcomplex
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
  : IsSubcomplex (∂s) X := -- Note: could not get Lean to unfold `∂s ⊆ X`
by
  simp only [IsSubcomplex, Set.subset_def]
  intro u
  apply simplexBoundary_subcomplex_simplices
  assumption

theorem simplexBoundary_subcomplex_vert
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
  : x ∈ (∂s).vertices → x ∈ X.vertices :=
by
  intro x_in_bd
  simp only [vertices_setOf, Set.mem_setOf] at x_in_bd ⊢
  choose t t_in_bd x_in_t using x_in_bd
  use t; constructor
  apply simplexBoundary_subcomplex_simplices X s t s_in_X t_in_bd
  assumption

theorem simplexBoundary_mem_iff_subset
    (s t : Finset E)
    [Nonempty s]
  : t ∈ (∂s).faces ↔ t ⊂ s ∧ t ≠ ∅ :=
by
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
    Set.mem_singleton_iff, Finset.ssubset_iff_subset_ne]
  constructor
  intro t_in_bd
  choose t_ss_s t_ne_s_ne_empty using t_in_bd
  simp at t_ne_s_ne_empty
  choose t_ne_s t_ne_empty using t_ne_s_ne_empty
  constructor
  constructor <;> assumption
  assumption
  intro t_ss_s
  choose t_ss_s t_ne_empty using t_ss_s
  choose t_ss_s t_ne_s using t_ss_s
  constructor
  assumption
  simp
  constructor <;> assumption

theorem subsimplex_boundary_subcomplex
    (s t : Finset E)
  : s ⊆ t → ∂s ⊆ ∂t :=
by
  simp only [IsSubcomplex, simplexBoundary, Set.subset_def, Finset.subset_iff]
  intro s_ss_t u u_in_bd_s
  simp only [Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
    Set.mem_singleton_iff] at u_in_bd_s ⊢
  choose u_ss_s u_ne_s_empty using u_in_bd_s
  simp at u_ne_s_empty
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

-- Star of a complex wrt a simplex.
@[simp]
def star
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    -- I am slightly concerned that this is not required for the proofs so something might be wrong here
    -- even if it's not required in the proofs, it probably still makes sense to have it
    -- since it _is_ part of the ''mathematical'' definition
    -- The point was to avoid the empty cpx being ∅ instead of {∅}. This is obviously obsolete now.
  : AbstractSimplicialComplex E :=
    AbstractSimplicialComplex.mk ({t ∈ X.faces | s ∪ t ∈ X.faces})
    (by
      simp
      by_contra empty_in_X
      simp at empty_in_X
      choose empty_in_X _ using empty_in_X
      apply X.empty_notMem
      assumption)
    (by
      simp
      intro s_1 t s_1_in_X s_s_1_in_X t_ss_s1 t_nonempty
      constructor
      · apply X.down_closed s_1_in_X t_ss_s1 t_nonempty
      · apply X.down_closed s_s_1_in_X
        apply Finset.union_subset_union
        rfl
        assumption
        simp
        intro
        assumption)

notation "St(" X ", " s ")" => star X s

instance star.fintype
    (X : AbstractSimplicialComplex E)
    [Fintype X.faces]
    (s : Finset E)
  : Fintype (star X s).faces :=
by
  unfold _root_.star
  dsimp only [AbstractSimplicialComplex.faces]
  have H_dec : DecidablePred fun a : Finset E => s ∪ a ∈ X.faces :=
    by
    unfold DecidablePred
    intro a
    apply Set.decidableMemOfFintype
  apply Set.fintypeSep

theorem star_subcomplex_simplices
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
  : t ∈ St(X, s).faces → t ∈ X.faces :=
by
  intro t_in_star
  simp only [_root_.star, Set.mem_sep_iff] at t_in_star
  choose t_in_X st_in_X using t_in_star
  assumption

theorem star_subcomplex
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
  : IsSubcomplex St(X, s) X := -- something with '⊆' notation seems to be a problem again
                               -- You have to call the explicit "AbstractSimplicialComplex.instHadSubset" or equivalent.
by
  simp only [IsSubcomplex, Set.subset_def]
  intro t
  apply star_subcomplex_simplices

theorem star_iso
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (s : Finset E)
    (t : Finset F)
    (f : SimplicialMap X Y)
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces)
    (f_iso : IsSimplicialIso f) : Finset.image f.map s = t → St(X, s) ≅ St(Y, t) :=
  by
  intro fs_eq_t
  unfold IsSimpliciallyIso
  have f_simp : IsSimplicialMap St(X, s) St(Y, t) f.map :=
  by
    simp only [IsSimplicialMap, _root_.star, Set.mem_sep_iff]
    intro u u_in_X_star
    choose u_in_X su_in_X using u_in_X_star
    constructor
    apply f.is_simplicial
    assumption
    rw [← fs_eq_t, ← Finset.image_union]
    apply f.is_simplicial
    assumption
  let f_star := SimplicialMap.mk f.map f_simp
  unfold IsSimplicialIso at f_iso
  choose g gf_inv using f_iso
  unfold IsInverseSimplicialIso at gf_inv
  choose gf_id fg_id using gf_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply] at gf_id fg_id
  have gt_eq_s : Finset.image g.map t = s :=
    by
    rw [← fs_eq_t, Finset.ext_iff, Finset.image_image]
    intro x
    constructor
    intro x_in_img
    simp only [Finset.mem_image, Function.comp_apply] at x_in_img
    choose y y_in_s gfy_eq_x using x_in_img
    have y_in_X : y ∈ X.vertices := by
      rw [vertex_iff_in_simplex]
      use s
    specialize gf_id y_in_X
    rw [← gfy_eq_x, gf_id]
    assumption
    intro x_in_s
    simp only [Finset.mem_image, Function.comp_apply]
    use x; constructor; assumption
    have x_in_X : x ∈ X.vertices := by
      rw [vertex_iff_in_simplex]
      use s
    specialize gf_id x_in_X
    assumption
  have g_simp : IsSimplicialMap St(Y, t) St(X, s) g.map :=
  by
    simp only [IsSimplicialMap, _root_.star, Set.mem_sep_iff]
    intro u u_in_Y_star
    choose u_in_Y tu_in_Y using u_in_Y_star
    constructor
    apply g.is_simplicial
    assumption
    rw [← gt_eq_s, ← Finset.image_union]
    apply g.is_simplicial
    assumption
  let g_star := SimplicialMap.mk g.map g_simp
  use f_star
  unfold IsSimplicialIso
  use g_star
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply]
  constructor
  · intro x x_in_star
    have x_in_X : x ∈ X.vertices :=
    by
      apply is_subcomplex_vertices X St(X, s) (star_subcomplex X s)
      assumption
    specialize gf_id x_in_X
    assumption
  · intro x x_in_star
    have x_in_Y : x ∈ Y.vertices :=
    by
      apply is_subcomplex_vertices Y St(Y, t) (star_subcomplex Y t)
      assumption
    specialize fg_id x_in_Y
    assumption

-- Link of a complex wrt a simplex.
@[simp]
def link
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
  : AbstractSimplicialComplex E :=
    AbstractSimplicialComplex.mk
    ({t ∈ X.faces | s ∪ t ∈ X.faces ∧ s ∩ t = ∅})
    (by
      simp only [Set.mem_setOf, not_and_or]
      left; apply X.empty_notMem)
    (by
      intro t u t_in_link u_sset_t u_ne
      simp only [Set.mem_setOf] at ⊢ t_in_link
      choose t_in_X st_in_X st_disj using t_in_link
      constructor
      apply X.down_closed t_in_X u_sset_t u_ne

      constructor
      apply X.down_closed st_in_X
      apply Finset.union_subset_union_right u_sset_t
      rw [ne_eq, Finset.union_eq_empty, not_and_or]
      right; assumption

      rw [← Finset.subset_empty] at ⊢ st_disj
      have su_sset_st : s ∩ u ⊆ s ∩ t :=
      by
        apply Finset.inter_subset_inter_left u_sset_t
      apply subset_trans su_sset_st st_disj)

notation "Lk(" X ", " s ")" => link X s

instance link.fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (s : Finset E)
  : Fintype (link X s).faces :=
by
  simp only [link, AbstractSimplicialComplex.faces]
  rw [Set.sep_and]
  have dec_left : DecidablePred fun x : Finset E => s ∪ x ∈ X.faces :=
    by
    unfold DecidablePred
    intro x
    apply Set.decidableMemOfFintype
  have fin_left : Fintype ↥({x ∈ X.faces | s ∪ x ∈ X.faces}) :=
    by
    apply @Set.fintypeSep _ _ _ _ dec_left
  have dec_right : DecidablePred fun x : Finset E => s ∩ x = ∅ :=
  by
    unfold DecidablePred
    intro x
    apply Finset.decidableEq
  have fin_right : Fintype ↥({x ∈ X.faces | s ∩ x = ∅}) :=
  by
    apply @Set.fintypeSep _ _ _ _ dec_right
  apply @Set.fintypeInter _ _ _ _ fin_left fin_right

theorem link_coe_image_left
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
    (φ : SimplicialCoe X F)
  : Lk(φ.coe ''ˢ X, Finset.image φ.coe s).faces ⊆
      (φ.coe ''ˢ Lk(X, s)).faces :=
by
  simp only [link, simplicialImage, Set.subset_def]
  simp only [Set.mem_sep_iff, Set.mem_setOf]
  intro t t_in_link
  choose t_in_φX st_in_φX st_disj using t_in_link
  choose u u_in_X φu_t using t_in_φX
  choose v v_in_X φv_st using st_in_φX
  use u; constructor; constructor
  assumption
  constructor
  rw [← φu_t, ← Finset.image_union] at φv_st
  have v_su : v = s ∪ u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image, Set.ext_iff] at φv_st ⊢
    intro a
    specialize φv_st (φ.coe a)
    cases' φv_st with φv_ss_φsu φsu_ss_φv
    constructor
    intro a_in_v
    have a_in_X : a ∈ X.vertices := by
      rw [vertex_iff_in_simplex]
      use v; constructor <;> assumption
    rw [← Set.InjOn.mem_image_iff φ.Injective] at a_in_v ⊢
    specialize φv_ss_φsu a_in_v
    assumption
    rw [Finset.coe_union]
    apply Set.union_subset <;>
      · apply simplex_subset_vertices
        assumption
    assumption
    apply simplex_subset_vertices
    assumption
    assumption
    intro a_in_su
    have a_in_X : a ∈ X.vertices :=
      by
      rw [Finset.coe_union, Set.mem_union] at a_in_su
      cases' a_in_su with a_in_s a_in_u
      rw [vertex_iff_in_simplex]
      use s; constructor <;> assumption
      rw [vertex_iff_in_simplex]
      use u; constructor <;> assumption
    rw [← Set.InjOn.mem_image_iff φ.Injective] at a_in_su ⊢
    specialize φsu_ss_φv a_in_su
    assumption
    apply simplex_subset_vertices
    assumption
    assumption
    rw [Finset.coe_union]
    apply Set.union_subset <;>
      · apply simplex_subset_vertices
        assumption
    assumption
  rw [← v_su]
  assumption
  simp only [← φu_t, ← Finset.coe_inj, Finset.coe_image, Finset.coe_inter] at st_disj
  rw [← Set.InjOn.image_inter, ← Finset.coe_inter, ← Finset.coe_image, Finset.coe_inj,
    Finset.image_eq_empty] at st_disj
  assumption
  apply φ.Injective
  apply simplex_subset_vertices
  assumption
  apply simplex_subset_vertices
  assumption
  assumption

theorem link_coe_image_right
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
    (φ : SimplicialCoe X F)
  :
    (φ.coe ''ˢ Lk(X, s)).faces ⊆
      Lk(φ.coe ''ˢ X, Finset.image φ.coe s).faces :=
by
  simp only [link, simplicialImage, Set.subset_def]
  simp only [Set.mem_sep_iff, Set.mem_setOf]
  intro t t_in_img
  choose u u_in_link φu_t using t_in_img
  choose u_in_X su_in_X su_disj using u_in_link
  constructor
  use u; constructor
  use s ∪ u; constructor; assumption
  rw [← φu_t, Finset.image_union]
  simp only [← φu_t, ← Finset.coe_inj, Finset.coe_image, Finset.coe_inter]
  rw [← Set.InjOn.image_inter, ← Finset.coe_inter, ← Finset.coe_image, Finset.coe_inj,
    Finset.image_eq_empty]
  assumption
  apply φ.Injective
  apply simplex_subset_vertices
  assumption
  apply simplex_subset_vertices
  assumption

theorem link_coe_image
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
    (φ : SimplicialCoe X F)
  : Lk(φ.coe ''ˢ X, Finset.image φ.coe s).faces =
      (φ.coe ''ˢ Lk(X, s)).faces :=
by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply link_coe_image_left; assumption
  apply link_coe_image_right; assumption

theorem link_subcomplex_simplices
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
  : t ∈ Lk(X, s).faces → t ∈ X.faces :=
by
  intro t_in_link
  simp only [link, Set.mem_sep_iff] at t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  assumption

theorem link_subcomplex
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
  : Lk(X, s) ⊆ X :=
by
  simp only [IsSubcomplex, AbstractSimplicialComplex.instHasSubset, Set.subset_def]
  intro t
  apply link_subcomplex_simplices

theorem link_iso
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (s : Finset E)
    (t : Finset F)
    (f : SimplicialMap X Y)
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces)
    (f_iso : IsSimplicialIso f)
  : Finset.image f.map s = t → Lk(X, s) ≅ Lk(Y, t) :=
by
  intro fs_eq_t
  unfold IsSimpliciallyIso
  have f_simp : IsSimplicialMap Lk(X, s) Lk(Y, t) f.map :=
  by
    simp only [IsSimplicialMap, link, Set.mem_sep_iff]
    intro u u_in_X_link
    choose u_in_X su_in_X su_disj using u_in_X_link
    constructor
    apply f.is_simplicial
    assumption
    simp only [← fs_eq_t, ← Finset.image_union]
    constructor
    apply f.is_simplicial
    assumption
    rw [← Finset.image_inter_of_injOn, Finset.image_eq_empty]
    assumption
    rw [← Finset.coe_union]
    apply iso_is_injective_simplices f f_iso (s ∪ u)
    assumption
  let f_link := SimplicialMap.mk f.map f_simp
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
      rw [vertex_iff_in_simplex]
      use s
    specialize gf_id y_in_X
    rw [← gfy_eq_x, gf_id]
    assumption
    intro x_in_s
    simp only [Finset.mem_image, Function.comp_apply]
    use x; constructor; assumption
    have x_in_X : x ∈ X.vertices := by
      rw [vertex_iff_in_simplex]
      use s
    specialize gf_id x_in_X
    assumption
  have g_simp : IsSimplicialMap Lk(Y, t) Lk(X, s) g.map :=
  by
    simp only [IsSimplicialMap, link, Set.mem_sep_iff]
    intro u u_in_Y_link
    choose u_in_Y su_in_Y su_disj using u_in_Y_link
    constructor
    apply g.is_simplicial
    assumption
    simp only [← gt_eq_s, ← Finset.image_union]
    constructor
    apply g.is_simplicial
    assumption
    rw [← Finset.image_inter_of_injOn, Finset.image_eq_empty]
    assumption
    rw [← Finset.coe_union]
    apply iso_is_injective_simplices g
    apply iso_inv_is_iso f <;> assumption
    assumption
  let g_link := SimplicialMap.mk g.map g_simp
  use f_link
  unfold IsSimplicialIso
  use g_link
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id]
  constructor
  · intro x x_in_X_link
    have x_in_X : x ∈ X.vertices :=
    by
      apply is_subcomplex_vertices X Lk(X, s)
      apply link_subcomplex
      assumption
    specialize gf_id x_in_X
    assumption
  · intro x x_in_Y_link
    have x_in_Y : x ∈ Y.vertices :=
    by
      apply is_subcomplex_vertices Y Lk(Y, t)
      apply link_subcomplex
      assumption
    specialize fg_id x_in_Y
    assumption

theorem link_fact_inter
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E)
  : Lk(X ∩ Y, s).faces = Lk(X, s).faces ∩ Lk(Y, s).faces :=
by
  simp only [link, simplicialInter, Set.ext_iff, Set.mem_inter_iff, Set.mem_sep_iff]
  intro t
  constructor
  · intro t_in_link
    choose t_in_XY st_in_XY st_disj using t_in_link
    choose t_in_X t_in_Y using t_in_XY
    choose st_in_X st_in_Y using st_in_XY
    constructor; constructor
    assumption
    constructor <;> assumption
    constructor; assumption
    constructor <;> assumption
  · intro t_in_inter
    choose t_in_X t_in_Y using t_in_inter
    choose t_in_X st_in_X st_disj using t_in_X
    choose t_in_Y st_in_Y st_disj using t_in_Y
    constructor; constructor <;> assumption
    constructor; constructor <;> assumption
    assumption

theorem link_fact_union_left
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
    (s_nin_Y : s ∉ Y.faces)
  : Lk(X ∪ Y, s).faces = Lk(X, s).faces :=
by
  simp only [link, simplicialUnion, Set.ext_iff, Set.mem_sep_iff, Set.mem_union]
  intro t
  constructor
  · intro t_in_XY
    choose t_in_XY st_in_XY st_disj using t_in_XY
    cases' t_in_XY with t_in_X contra <;> cases' st_in_XY with st_in_X contra
    constructor; assumption
    constructor <;> assumption
    have s_in_Y : s ∈ Y.faces :=
    by
      apply Y.down_closed
      assumption
      apply Finset.subset_union_left
      apply face_nonempty X s s_in_X
    contradiction
    constructor
    apply X.down_closed st_in_X
    apply Finset.subset_union_right
    apply face_nonempty Y t contra
    constructor <;> assumption
    have s_in_Y : s ∈ Y.faces := by
      apply Y.down_closed contra
      apply Finset.subset_union_left
      apply face_nonempty X s s_in_X
    contradiction
  · intro t_in_X
    choose t_in_X st_in_X st_disj using t_in_X
    constructor; left; assumption
    constructor; left; assumption
    assumption

theorem link_fact_union_right
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_nin_X : s ∉ X.faces)
    (s_in_Y : s ∈ Y.faces)
  : Lk(X ∪ Y, s).faces = Lk(Y, s).faces :=
by
  simp only [link, simplicialUnion, Set.ext_iff, Set.mem_sep_iff, Set.mem_union]
  intro t
  constructor
  · intro t_in_XY
    choose t_in_XY st_in_XY st_disj using t_in_XY
    cases' t_in_XY with contra t_in_Y <;> cases' st_in_XY with contra st_in_X
    have s_in_X : s ∈ X.faces := by
      apply X.down_closed contra
      apply Finset.subset_union_left
      apply face_nonempty Y s s_in_Y
    contradiction
    constructor
    apply Y.down_closed st_in_X
    apply Finset.subset_union_right
    apply face_nonempty X t contra
    constructor <;> assumption
    have s_in_X : s ∈ X.faces := by
      apply X.down_closed contra
      apply Finset.subset_union_left
      apply face_nonempty Y s s_in_Y
    contradiction
    constructor; assumption
    constructor <;> assumption
  · intro t_in_Y
    choose t_in_Y st_in_Y st_disj using t_in_Y
    constructor; right; assumption
    constructor; right; assumption
    assumption

theorem link_fact_union
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_XY : s ∈ (X ∩ Y).faces)
  : Lk(X ∪ Y, s).faces = Lk(X, s).faces ∪ Lk(Y, s).faces :=
by
  simp only [link, simplicialUnion, Set.ext_iff, Set.mem_sep_iff, Set.mem_union]
  intro t
  constructor
  · intro t_in_XY
    choose t_in_XY st_in_XY st_disj using t_in_XY
    cases' t_in_XY with t_in_X t_in_Y <;> cases' st_in_XY with st_in_X st_in_Y
    left
    constructor; assumption
    constructor <;> assumption
    right
    constructor
    apply Y.down_closed st_in_Y
    apply Finset.subset_union_right
    apply face_nonempty X t t_in_X
    constructor <;> assumption
    left
    constructor
    apply X.down_closed st_in_X
    apply Finset.subset_union_right
    apply face_nonempty Y t t_in_Y
    constructor <;> assumption
    right
    constructor; assumption
    constructor <;> assumption
  · intro t_in_inter
    cases' t_in_inter with t_in_X t_in_Y
    choose t_in_X st_in_X st_disj using t_in_X
    constructor; left; assumption
    constructor; left; assumption
    assumption
    choose t_in_Y st_in_Y st_disj using t_in_Y
    constructor; right; assumption
    constructor; right; assumption
    assumption

-- Complement of the star of a complex wrt a simplex.
@[simp]
def starComplement
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

notation X "\\St(" X ", " s ")" => starComplement X s

instance starComplement.fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (s : Finset E)
  : Fintype (starComplement X s).faces :=
by
  simp only [starComplement, AbstractSimplicialComplex.faces]
  have H_dec : DecidablePred fun t : Finset E => ¬s ⊆ t :=
  by
    unfold DecidablePred
    intro t
    simp only [Finset.subset_iff, Classical.not_forall]
    apply Finset.decidableDExistsFinset
  apply @Set.fintypeSep _ _ _ _ H_dec

theorem starComplement_subcomplex_simplices
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
  : t ∈ X\St(X, s).faces → t ∈ X.faces :=
by
  simp only [starComplement, Set.mem_sep_iff]
  intro t_in_star_comp
  choose t_in_X s_nss_t using t_in_star_comp
  assumption

theorem starComplement_subcomplex
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
  : X\St(X, s) ⊆ X :=
by
  simp only [IsSubcomplex, AbstractSimplicialComplex.instHasSubset, Set.subset_def]
  intro t
  apply starComplement_subcomplex_simplices

theorem starComplement_iso
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (s : Finset E)
    (t : Finset F)
    (f : SimplicialMap X Y)
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces)
    (f_iso : IsSimplicialIso f)
  : Finset.image f.map s = t → X\St(X, s) ≅ Y\St(Y, t) :=
by
  intro fs_eq_t
  unfold IsSimpliciallyIso
  have f_simp : IsSimplicialMap (X\St(X, s)) (Y\St(Y, t)) f.map :=
  by
    simp only [IsSimplicialMap, starComplement, Set.mem_sep_iff]
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

    apply iso_is_injective_vertices
    assumption
    rw [vertex_iff_in_simplex]
    use u
    rw [vertex_iff_in_simplex]
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
      rw [vertex_iff_in_simplex]
      use s
    specialize gf_id y_in_X
    rw [← gfy_eq_x, gf_id]
    assumption
    intro x_in_s
    simp only [Finset.mem_image, Function.comp_apply]
    use x; constructor; assumption
    have x_in_X : x ∈ X.vertices := by
      rw [vertex_iff_in_simplex]
      use s
    specialize gf_id x_in_X
    assumption
  have g_simp : IsSimplicialMap (Y\St(Y, t)) (X\St(X, s)) g.map :=
  by
    simp only [IsSimplicialMap, starComplement, Set.mem_sep_iff]
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
    apply iso_is_injective_vertices
    apply iso_inv_is_iso f <;> assumption
    rw [vertex_iff_in_simplex]
    use u
    rw [vertex_iff_in_simplex]
    use t; constructor <;> assumption
  let g_comp := SimplicialMap.mk g.map g_simp
  use f_comp
  unfold IsSimplicialIso
  use g_comp
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id]
  constructor
  · intro x x_in_X_comp
    have x_in_X : x ∈ X.vertices :=
    by
      apply is_subcomplex_vertices X (X\St(X, s))
      apply starComplement_subcomplex
      assumption
    specialize gf_id x_in_X
    assumption
  · intro x x_in_Y_comp
    have x_in_Y : x ∈ Y.vertices :=
    by
      apply is_subcomplex_vertices Y (Y\St(Y, t))
      apply starComplement_subcomplex
      assumption
    specialize fg_id x_in_Y
    assumption

theorem starComplement_coe_image_left
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (φ : SimplicialCoe X F)
  : (starComplement (φ.coe ''ˢ X) (Finset.image φ.coe s)).faces ⊆
      (φ.coe ''ˢ X\St(X, s)).faces :=
by
  simp only [starComplement, simplicialImage, Set.subset_def]
  simp only [Set.mem_sep_iff, Set.mem_setOf]
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

theorem starComplement_coe_image_right
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
    (φ : SimplicialCoe X F)
  : (φ.coe ''ˢ X\St(X, s)).faces ⊆
      (starComplement (φ.coe ''ˢ X) (Finset.image φ.coe s)).faces :=
by
  simp only [starComplement, simplicialImage, Set.subset_def]
  simp only [Set.mem_sep_iff, Set.mem_setOf]
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
  apply simplex_subset_vertices
  assumption
  rw [vertex_iff_in_simplex]
  use s

theorem starComplement_coe_image
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
    (φ : SimplicialCoe X F)
  : (starComplement (φ.coe ''ˢ X) (Finset.image φ.coe s)).faces =
      (φ.coe ''ˢ (X\St(X, s))).faces :=
by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply starComplement_coe_image_left
  apply starComplement_coe_image_right
  assumption

@[simp]
def IsNegOneSphere
    {X : AbstractSimplicialComplex E}
    {s : Finset E}
    (Y : AbstractSimplicialComplex E)
    (Y_link_X : Y = Lk(X, s))
  : Prop := Y = ⊥

@[simp]
def negOneBall (x : E) : AbstractSimplicialComplex E :=
  AbstractSimplicialComplex.mk {{x}}
  (by
    rw [Set.mem_singleton_iff, ← ne_eq]
    symm
    apply Finset.singleton_ne_empty)
  (by
    intro s t s_eq_x t_sset_s t_ne
    rw [Set.mem_singleton_iff] at ⊢ s_eq_x
    subst s_eq_x
    rw [Finset.subset_singleton_iff] at t_sset_s
    cases t_sset_s
    contradiction
    assumption)

instance negOneBall.fintype (x : α) : Fintype (negOneBall x).faces :=
by
  simp only [negOneBall]
  apply Set.fintypeSingleton

theorem dim_of_negOneBall (x : α) : (negOneBall x).dim = 0 :=
by
  simp only [AbstractSimplicialComplex.dim, negOneBall]
  unfold face_dim
  simp only [Set.toFinset_singleton, Finset.image_singleton, Finset.card_singleton, Nat.cast_one,
    sub_self, Int.reduceNeg]
  unfold Finset.max'
  rw [Finset.sup'_union]
  simp only [id_eq, Finset.singleton_nonempty, Finset.sup'_singleton,
    Int.reduceNeg, Left.neg_nonpos_iff, zero_le_one, sup_of_le_left]
  all_goals { apply Finset.singleton_nonempty }

-- The ball around a simplex.
def mBall
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (s : Finset E)
  : AbstractSimplicialComplex E :=
    AbstractSimplicialComplex.mk
    ((Finset.powerset (Lk(X, s)).vertices.toFinset) \ {∅})
    (by
      rw [Set.mem_diff, not_and_or, not_not]
      right; apply Set.mem_singleton)
    (by
      intro t u t_in_ball u_sset_t u_ne
      simp only [Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at ⊢ t_in_ball
      choose t_in_power t_ne using t_in_ball
      constructor

      rw [Finset.mem_powerset] at ⊢ t_in_power
      apply subset_trans u_sset_t t_in_power

      assumption)

notation "B(" X ", " s ")" => mBall X s

instance Ball.fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (s : Finset E)
  : Fintype (mBall X s).faces :=
by
  simp only [mBall, AbstractSimplicialComplex.faces, Finset.coe_sdiff]
  have fin_power : Fintype ↑(AbstractSimplicialComplex.vertices E Lk(X, s)).toFinset.powerset :=
  by
    apply FinsetCoe.fintype
  apply Set.fintypeDiff

-- The cone of a complex.
variable {𝕜 : Type*} [DecidableEq 𝕜] [Ring 𝕜] [Nontrivial 𝕜]
variable [AddCommGroup E] [DecidableEq F] [AddCommGroup F]

@[simp]
def cone
  (X : AbstractSimplicialComplex E)
  (x : E)
  (x_nin_X : x ∉ X.vertices) -- Ensure that we use a new point for projection purposes.
: AbstractSimplicialComplex (E × 𝕜) := (negOneBall x) ⋆ X

notation "Cone(" X ", " x ")" => cone X x

instance cone.Fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (x : E)
    (x_nin_X : x ∉ X.vertices)
  : Fintype ((Cone(X, x) x_nin_X) : AbstractSimplicialComplex (E × 𝕜)).faces :=
by
  simp only [cone]
  apply simplicialJoin.fintype

def coneIsoMap
    (y : F)
    (f : E → F)
  : E × 𝕜 → F × 𝕜 :=
    fun x : E × 𝕜 =>
      if x.snd = 0 then (y, 0) else (f x.fst, x.snd)

theorem cone_iso_simplicial
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (x : E)
    (y : F)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_Y : y ∉ Y.vertices)
    (f : SimplicialMap X Y)
  : IsSimplicialMap (Cone(X, x) x_nin_X) (Cone(Y, y) y_nin_Y : AbstractSimplicialComplex (F × 𝕜)) (coneIsoMap y f.map) :=
by
  simp only [IsSimplicialMap, cone, negOneBall, simplicialJoin_mem]
  intro u u_in_X_cone
  choose s s_in_ball t t_in_X u_eq_st using u_in_X_cone
  rw [Set.mem_union, Set.mem_singleton_iff] at s_in_ball
  cases' s_in_ball with s_eq_x s_empty
  -- s = {x} case.
  use{y};
  constructor
  rw [Set.mem_union]
  left; rfl
  use Finset.image f.map t; constructor
  rw [Set.mem_union] at t_in_X ⊢
  cases' t_in_X with t_in_X t_empty
  left
  apply f.is_simplicial
  assumption
  right
  rw [Set.mem_singleton_iff, Finset.image_eq_empty]
  assumption
  constructor
  simp only [u_eq_st, s_eq_x, simplexDisjointUnion, Finset.image_union, coneIsoMap, Finset.ext_iff]
  intro v
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_singleton]
  constructor
  · intro v_in_img
    cases' v_in_img with v_in_lhs v_in_rhs
    choose w w_in_lhs w_eq_v using v_in_lhs
    choose w_eq_x w_zero using w_in_lhs
    revert w_eq_v
    unfold coneIsoMap
    split_ifs
    intro y_eq_v
    simp only [Prod.ext_iff] at y_eq_v
    choose y_eq_v v_zero using y_eq_v
    rw [@comm _ Eq] at y_eq_v v_zero
    left
    constructor <;> assumption
    choose w w_in_rhs w_eq_v using v_in_rhs
    choose w_in_t w_one using w_in_rhs
    revert w_eq_v
    unfold coneIsoMap
    split_ifs with w_zero
    rw [w_one] at w_zero
    simp at w_zero
    intro w_eq_v
    simp only [Prod.ext_iff] at w_eq_v
    choose w_eq_v v_one using w_eq_v
    rw [w_one, @comm _ Eq] at v_one
    right
    constructor
    use w.fst
    assumption
  · intro v_in_union
    cases' v_in_union with v_in_lhs v_in_rhs
    choose v_eq_y v_zero using v_in_lhs
    left; use(x, 0); constructor
    simp only [Prod.fst, Prod.snd]
    constructor <;> trivial
    unfold coneIsoMap
    simp only [eq_self_iff_true, if_true, Prod.ext_iff]
    rw [@comm _ Eq] at v_eq_y v_zero
    constructor <;> assumption
    choose w_eq_v v_one using v_in_rhs
    choose w w_in_t w_eq_v using w_eq_v
    right; use(w, 1); constructor
    simp only [Prod.fst, Prod.snd]
    constructor; assumption; trivial
    unfold coneIsoMap
    simp only [Nat.one_ne_zero, if_false, Prod.ext_iff]
    rw [@comm _ Eq] at v_one
    constructor
    split_ifs with one_ne_zero
    simp at one_ne_zero
    simp only [Prod.ext_iff]
    assumption
    split_ifs with one_ne_zero
    simp at one_ne_zero
    simp only [Prod.ext_iff]
    assumption

  simp [Finset.image_nonempty]
  choose u_eq_st e_nonempty using u_eq_st
  assumption
  -- s = ∅ case.
  use∅
  constructor
  simp
  use Finset.image f.map t
  constructor
  simp only [Set.mem_union] at t_in_X ⊢
  cases' t_in_X with t_in_X t_empty
  left
  apply f.is_simplicial
  assumption
  right
  rw [Set.mem_singleton_iff, Finset.image_eq_empty]
  assumption
  simp only [u_eq_st, s_empty, simplexDisjointUnion, Finset.image_union, coneIsoMap, Finset.ext_iff]
  constructor
  intro v
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_singleton]
  constructor
  · intro v_in_img
    cases' v_in_img with v_empty v_in_t
    choose w contra w_eq_v using v_empty
    choose contra w_zero using contra
    simp only [Set.mem_singleton_iff] at s_empty
    rw [s_empty] at contra
    simp at contra
    choose w w_in_t w_eq_v using v_in_t
    choose w_in_t w_one using w_in_t
    revert w_eq_v
    unfold coneIsoMap
    split_ifs with w_zero
    rw [w_one] at w_zero
    simp at w_zero
    intro w_eq_v
    simp only [Prod.ext_iff] at w_eq_v
    choose w_eq_v v_one using w_eq_v
    rw [w_one, @comm _ Eq] at v_one
    right
    constructor
    use w.fst
    assumption
  · intro v_in_union
    cases' v_in_union with contra v_in_t
    choose contra v_zero using contra
    simp at contra
    choose w_eq_v v_one using v_in_t
    choose w w_in_t w_eq_v using w_eq_v
    right; use(w, 1); constructor
    simp only [Prod.fst, Prod.snd]
    constructor; assumption; trivial
    unfold coneIsoMap
    simp only [Nat.one_ne_zero, if_false, Prod.ext_iff]
    rw [@comm _ Eq] at v_one
    constructor
    split_ifs with one_ne_zero
    simp at one_ne_zero
    simp only [Prod.ext_iff]
    assumption
    split_ifs with one_ne_zero
    simp at one_ne_zero
    simp only [Prod.ext_iff]
    assumption
  simp [Set.union_nonempty]
  intro s_empty
  choose u_eq_st u_nonempty using u_eq_st
  rw [s_empty] at u_eq_st
  revert u_nonempty
  contrapose
  rw [Classical.not_not]
  intro t_empty
  rw [t_empty] at u_eq_st
  unfold simplexDisjointUnion at u_eq_st
  simp at u_eq_st
  simp [u_eq_st]

theorem cone_iso
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (x : E)
    (y : F)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_Y : y ∉ Y.vertices)
    (X_iso_Y : X ≅ Y)
  : (Cone(X, x) x_nin_X : AbstractSimplicialComplex (E × 𝕜)) ≅ (Cone(Y, y) y_nin_Y : AbstractSimplicialComplex (F × 𝕜)) :=
by
  --intro X_iso_Y
  unfold IsSimpliciallyIso at X_iso_Y ⊢
  choose f f_iso using X_iso_Y
  unfold IsSimplicialIso at f_iso ⊢
  choose g gf_inv using f_iso
  let f_cone : SimplicialMap (Cone(X, x) x_nin_X) (Cone(Y, y) y_nin_Y : AbstractSimplicialComplex (F × 𝕜)) :=
    SimplicialMap.mk (coneIsoMap y f.map) (cone_iso_simplicial X Y x y x_nin_X y_nin_Y f)
  let g_cone : SimplicialMap (Cone(Y, y) y_nin_Y) (Cone(X, x) x_nin_X : AbstractSimplicialComplex (E × 𝕜)) :=
    SimplicialMap.mk (coneIsoMap x g.map) (cone_iso_simplicial Y X y x y_nin_Y x_nin_X g)
  use f_cone; use g_cone
  unfold IsInverseSimplicialIso at gf_inv ⊢
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply, id] at gf_inv ⊢
  choose gf_id fg_id using gf_inv
  constructor
  · intro z z_in_X_cone
    rw [vertex_iff_in_simplex] at z_in_X_cone
    choose u u_in_cone z_in_u using z_in_X_cone
    simp only [cone, negOneBall, simplicialJoin] at u_in_cone
    simp only [Set.mem_diff, Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff] at u_in_cone
    choose u_in_cone u_nonempty using u_in_cone
    choose s s_in_ball t t_in_x st_eq_u using u_in_cone
    rw [← st_eq_u, simplex_disjoint_mem] at z_in_u
    cases' z_in_u with z_in_ball z_in_t
    cases' s_in_ball with s_eq_x contra
    rw [s_eq_x, Finset.mem_singleton] at z_in_ball
    choose z_eq_x z_zero using z_in_ball
    simp only [coneIsoMap, Prod.ext_iff, z_zero, eq_self_iff_true, if_true, f_cone, g_cone]
    constructor
    symm
    assumption
    trivial
    rw [contra] at z_in_ball
    choose contra z_zero using z_in_ball
    simp at contra
    choose z_in_t z_one using z_in_t
    have z_in_X : z.fst ∈ X.vertices :=
      by
      rw [vertex_iff_in_simplex]
      use t
      constructor
      simp only [Set.mem_union] at t_in_x
      cases' t_in_x with t_in_X t_empty
      assumption
      rw [Set.mem_singleton_iff] at t_empty
      rw [t_empty] at z_in_t
      simp at z_in_t
      assumption
    specialize gf_id z_in_X
    simp [coneIsoMap, z_one, Nat.one_ne_zero, if_false, Prod.ext_iff, f_cone, g_cone]
    assumption
  · intro z z_in_Y_cone
    rw [vertex_iff_in_simplex] at z_in_Y_cone
    choose u u_in_cone z_in_u using z_in_Y_cone
    simp only [cone, negOneBall, simplicialJoin] at u_in_cone
    simp only [Set.mem_diff, Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff] at u_in_cone
    choose u_in_cone u_nonempty using u_in_cone
    choose s s_in_ball t t_in_x st_eq_u using u_in_cone
    rw [← st_eq_u, simplex_disjoint_mem] at z_in_u
    cases' z_in_u with z_in_ball z_in_t
    cases' s_in_ball with s_eq_x contra
    rw [s_eq_x, Finset.mem_singleton] at z_in_ball
    choose z_eq_x z_zero using z_in_ball
    simp only [coneIsoMap, Prod.ext_iff, z_zero, eq_self_iff_true, if_true, f_cone, g_cone]
    constructor; symm; assumption
    trivial
    rw [contra] at z_in_ball
    choose contra z_zero using z_in_ball
    simp at contra
    choose z_in_t z_one using z_in_t
    have z_in_Y : z.fst ∈ Y.vertices :=
      by
      rw [vertex_iff_in_simplex]
      use t
      constructor
      simp only [Set.mem_union] at t_in_x
      cases' t_in_x with t_in_X t_empty
      assumption
      rw [Set.mem_singleton_iff] at t_empty
      rw [t_empty] at z_in_t
      simp at z_in_t
      assumption
    specialize fg_id z_in_Y
    simp [coneIsoMap, z_one, Nat.one_ne_zero, if_false, Prod.ext_iff, f_cone, g_cone]
    assumption

theorem dim_of_cone
    (X : AbstractSimplicialComplex E)
    [Fintype X.faces]
    (x : E)
    (x_nin_X : x ∉ X.vertices)
  : (Cone(X, x) x_nin_X : AbstractSimplicialComplex (E × 𝕜)).dim = X.dim + 1 :=
by
  dsimp only [cone]
  rw [dim_of_join, dim_of_negOneBall]
  simp only [zero_add]

/-
# Subcomplexes Under Simplicial Join
-/
-- Distributive properties of join over certain subcomplexes.
-- Lemma 2.2 (1), p.7
theorem join_distl_link
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
  : (Y ⋆ Lk(X, s) : AbstractSimplicialComplex (E × 𝕜)) ≅ (Lk(X ⋆ Y, s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  apply simplicial_iso_trans (Y ⋆ Lk(X, s) : AbstractSimplicialComplex (E × 𝕜)) (Lk(X, s) ⋆ Y : AbstractSimplicialComplex (E × 𝕜))
  apply simplicialJoin_comm
  apply simplicial_iso_preserves_equiv
  dsimp only [simplicialJoin, link, AbstractSimplicialComplex.faces]
  rw [Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf]
  constructor
  · intro H
    rw [Set.mem_diff] at H
    choose H x_nonempty using H
    rcases H with ⟨t, Ht, u, Hu, Hx⟩
    rw [Set.mem_union] at Ht
    rw [Set.mem_sep_iff] at Ht
    cases' Ht with Ht t_empty
    · rcases Ht with ⟨Ht, Hst, Hst_empty⟩
      constructor
      rw [Set.mem_diff]
      constructor
      · use t; constructor; tauto
        use u
      · assumption
      constructor
      rw [Set.mem_diff]
      constructor
      · subst Hx
        rw [simplex_disjoint_distr_union]
        use s ∪ t; constructor; tauto
        use u; constructor; tauto
        simp
      · simp at x_nonempty ⊢
        intro s_empty
        assumption
      subst Hx
      rw [simplex_disjoint_distr_inter]
      simp; tauto
    · constructor
      rw [Set.mem_diff]
      constructor
      · use t; constructor; tauto
        use u
      · assumption
      constructor
      rw [Set.mem_diff]
      constructor
      · subst Hx
        rw [simplex_disjoint_distr_union]
        use s ∪ t
        constructor
        simp at t_empty
        simp [t_empty]
        right
        assumption
        use u; constructor; tauto
        simp
      · simp at x_nonempty ⊢
        intro s_empty
        assumption
      subst Hx
      rw [simplex_disjoint_distr_inter]
      simp
      simp at t_empty
      simp [t_empty]
  · intro H
    rcases H with ⟨Hx, Hx_union, Hsx_empty⟩
    rw [Set.mem_diff] at Hx
    choose Hx x_nonempty using Hx
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩
    rw [Set.mem_diff] at Hx_union
    choose Hx_union x_union_nonempty using Hx_union
    rcases Hx_union with ⟨t', Ht', u', Hu', Hx_union⟩
    subst Hx
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at Hx_union
    choose a b using Hx_union
    simp at b
    symm at b
    subst b
    subst a
    rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at Hsx_empty
    rw [simplex_disjoint_distr_union] at x_union_nonempty
    simp at x_union_nonempty
    cases' Hsx_empty with Hst_empty Hu'_trivial
    rw [Set.mem_diff]
    cases' Ht with t_in_X t_empty
    · constructor
      use t
      constructor
      simp
      right
      constructor
      constructor
      assumption
      cases' Ht' with st_in_X st_empty
      · assumption
      · simp at st_empty
        choose s_empty t_empty using st_empty
        subst s_empty t_empty
        revert s_in_X
        contrapose
        intro empty_in_X
        simp at empty_in_X
        assumption
      constructor
      assumption
      assumption
      use u
      assumption
    · constructor
      use ∅
      constructor
      simp
      use u
      constructor
      assumption
      rw [simplex_disjoint_eq_unique]
      constructor
      rw [Set.mem_singleton_iff] at t_empty
      symm
      assumption
      trivial
      assumption

-- Lemma 2.2 (2), p.7
theorem join_distl_star
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
  : (Y ⋆ St(X, s) : AbstractSimplicialComplex (E × 𝕜)) ≅ (St(X ⋆ Y, s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  apply simplicial_iso_trans (Y ⋆ St(X, s)) (St(X, s) ⋆ Y : AbstractSimplicialComplex (E × 𝕜))
  apply simplicialJoin_comm
  apply simplicial_iso_preserves_equiv
  dsimp only [simplicialJoin, _root_.star, AbstractSimplicialComplex.faces]
  rw [Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · intro H
    choose H x_nonempty using H
    rcases H with ⟨t, Ht, u, Hu, Hx⟩
    rw [Set.mem_union] at Ht
    cases' Ht with Ht t_empty
    rw [Set.mem_sep_iff] at Ht
    cases' Ht with Ht Hst
    constructor
    constructor
    use t; constructor; tauto
    use u; tauto
    subst Hx
    constructor
    use s ∪ t; constructor; tauto
    use u
    constructor <;> try rw [simplex_disjoint_distr_union]; simp
    assumption
    simp
    intro s_empty
    intro t_empty
    subst t_empty
    simp at x_nonempty
    assumption
    rw [Set.mem_singleton_iff] at t_empty
    subst t_empty
    constructor
    constructor
    use ∅
    constructor
    tauto
    use u
    assumption
    subst Hx
    constructor
    use s
    constructor
    tauto
    use u
    constructor
    assumption
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique]
    constructor
    rw [Finset.union_empty]
    rw [Finset.empty_union]
    simp
    intro
    simp at x_nonempty
    assumption
  · intro H
    cases' H with Hx Hx_union
    choose Hx x_nonempty using Hx
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩
    choose Hx_union x_union_nonempty using Hx_union
    rcases Hx_union with ⟨t', Ht', u', Hu', Hx_union⟩
    subst Hx
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at Hx_union
    cases' Hx_union with Ht' Hu'
    simp at Hu'
    subst Ht'; subst Hu'
    cases' Ht with t_in_X t_empty
    · constructor
      use t
      constructor
      rw [Set.mem_union, Set.mem_sep_iff]
      left
      constructor; assumption
      cases' Ht' with st_in_X st_empty
      · assumption
      · simp at st_empty
        choose s_empty t_empty using st_empty
        subst s_empty t_empty
        revert s_in_X
        contrapose
        intro empty_in_X
        simp at empty_in_X
        assumption
      use u'
      assumption
    · constructor
      use ∅
      constructor; tauto
      use u'
      constructor; assumption
      rw [Set.mem_singleton_iff] at t_empty
      subst t_empty
      trivial
      assumption

theorem join_distr_starComplement_simplices
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E)
    [Nonempty s]
    (s_in_X : s ∈ X.faces)
  : (starComplement X s ⋆ Y).faces =
      (starComplement (X ⋆ Y) (s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)).faces :=
by
  dsimp only [simplicialJoin, starComplement, AbstractSimplicialComplex.faces]
  rw [Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · intro H
    choose H x_nonempty using H
    rcases H with ⟨t, Ht, u, Hu, Hx⟩
    rw [Set.mem_union] at Ht
    rw [Set.mem_sep_iff] at Ht
    cases' Ht with Ht t_empty
    cases' Ht with Ht Hs_not_sset_t
    constructor
    constructor
    use t; constructor; tauto
    use u; tauto
    subst Hx
    rw [simplex_disjoint_subset_unique]
    simp; tauto
    rw [Set.mem_singleton_iff] at t_empty
    subst t_empty
    constructor
    constructor
    use ∅
    constructor; tauto
    use u; tauto
    subst Hx
    rw [simplex_disjoint_subset_unique]
    simp
    revert s_in_X
    contrapose
    rw [Classical.not_not]
    intro s_empty
    subst s_empty
    apply X.empty_notMem
  · intro H
    cases' H with Hx Hs_not_sset_x
    cases' Hx with Hx x_nonempty
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩
    subst Hx
    rw [simplex_disjoint_subset_unique] at Hs_not_sset_x
    simp at Hs_not_sset_x
    cases' Ht with Ht t_empty
    · constructor
      use t; constructor
      rw [Set.mem_union, Set.mem_sep_iff]
      left
      constructor <;> assumption
      use u; assumption
    · constructor
      use ∅
      constructor
      tauto
      use u
      constructor
      assumption
      rw [t_empty]
      assumption

theorem join_distr_starComplement
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E)
    [Nonempty s]
    (s_in_X : s ∈ X.faces)
  : ((starComplement X s) ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) ≅
      (starComplement (X ⋆ Y) (s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  apply simplicial_iso_preserves_equiv
  apply join_distr_starComplement_simplices
  assumption

-- Lemma 2.2 (3), p.7
theorem join_distl_starComplement
    (X Y : AbstractSimplicialComplex E)
    (s : Finset E)
    [Nonempty s]
    (s_in_X : s ∈ X.faces)
  : (Y ⋆ (starComplement X s) : AbstractSimplicialComplex (E × 𝕜)) ≅
      (starComplement (X ⋆ Y) (s ⊔ₛ ∅) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  apply simplicial_iso_trans (Y ⋆ starComplement X s) (starComplement X s ⋆ Y : AbstractSimplicialComplex (E × 𝕜))
  apply simplicialJoin_comm
  apply join_distr_starComplement
  assumption

-- Lemma 2.3, p.8
theorem join_fact_link
    (X Y : AbstractSimplicialComplex E)
    (s t : Finset E)
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces)
  : (Lk(X ⋆ Y, s ⊔ₛ t) : AbstractSimplicialComplex (E × 𝕜))
      ≅ (Lk(X, s) ⋆ Lk(Y, t) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  apply simplicial_iso_preserves_equiv
  dsimp only [link, simplicialJoin, AbstractSimplicialComplex.faces]
  rw [Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · intro H
    cases' H with H_left H_right
    cases' H_left with H_left x_nonempty
    rcases H_left with ⟨s', Hs', t', Ht', Hx⟩
    cases' H_right with H_left H_inter
    cases' H_left with H_left st_x_nonempty
    rcases H_left with ⟨s'', Hs'', t'', Ht'', H_union⟩
    subst Hx
    rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at H_inter
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at H_union
    cases' H_union with H_s_union H_t_union
    subst H_s_union; subst H_t_union
    constructor
    cases' Hs' with Hs' s_empty
    use s'; constructor
    rw [Set.mem_union, Set.mem_sep_iff]
    left
    constructor; assumption
    constructor
    cases' Hs'' with Hs'' s''_empty
    assumption
    simp at s''_empty
    choose s_empty s'_empty using s''_empty
    subst s_empty s'_empty
    simp
    assumption
    tauto
    use t'
    constructor
    rw [Set.mem_union, Set.mem_sep_iff]
    cases' Ht' with Ht' t_empty
    left
    constructor; assumption
    constructor
    cases' Ht'' with Ht'' t''_empty
    assumption
    simp at t''_empty
    choose t_empty t'_empty using t''_empty
    subst t_empty t'_empty
    iterate 4 tauto
    use s'
    constructor; tauto
    use t'
    constructor
    cases' Ht' with Ht' t_empty
    rw [Set.mem_union, Set.mem_sep_iff]
    left
    constructor; assumption
    constructor
    cases' Ht'' with Ht'' t''_empty
    assumption
    simp at t''_empty
    choose t_empty t'_empty using t''_empty
    subst t_empty t'_empty
    iterate 5 tauto
  · intro H
    cases' H with H x_nonempty
    rcases H with ⟨s', Hs', t', Ht', Hx⟩
    constructor
    · constructor
      use s'
      constructor
      cases' Hs' with Hs' s_empty
      rw [Set.mem_sep_iff] at Hs'
      tauto
      tauto
      use t'
      constructor
      cases' Ht' with Ht' t_empty
      rw [Set.mem_sep_iff] at Ht'
      tauto
      tauto
      assumption
      assumption
    · constructor
      constructor
      use s ∪ s'
      constructor
      cases' Hs' with Hs' s_empty
      rw [Set.mem_sep_iff] at Hs'
      tauto
      rw[ Set.mem_singleton_iff] at s_empty
      subst s_empty
      simp; tauto
      use t ∪ t'
      constructor
      cases' Ht' with Ht' t_empty
      rw [Set.mem_sep_iff] at Ht'
      tauto
      rw [Set.mem_singleton_iff] at t_empty
      subst t_empty
      simp; tauto
      subst Hx
      rw [simplex_disjoint_distr_union]
      subst Hx
      simp
      intro s_empty t_empty s'_empty
      subst s_empty t_empty s'_empty
      simp at x_nonempty
      assumption
      subst Hx
      rw [simplex_disjoint_distr_inter, simplex_disjoint_empty]
      cases' Hs' with Hs' s_empty
      rw [Set.mem_sep_iff] at Hs'
      constructor; tauto
      cases' Ht' with Ht' t_empty
      rw [Set.mem_sep_iff] at Ht'
      tauto
      rw [Set.mem_singleton_iff] at t_empty
      subst t_empty
      simp
      constructor
      rw [Set.mem_singleton_iff] at s_empty
      subst s_empty
      simp
      cases' Ht' with Ht' t_empty
      rw [Set.mem_sep_iff] at Ht'
      tauto
      rw [Set.mem_singleton_iff] at t_empty
      subst t_empty
      simp

-- Lemma 2.4 (1), p.8
theorem join_distr_union_left
    (X Y Z : AbstractSimplicialComplex E)
  : (X ⋆ (Y ∪ Z) : AbstractSimplicialComplex (E × 𝕜)) ≅ (X ⋆ Y ∪ X ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) :=
by
  apply simplicial_iso_preserves_equiv
  dsimp only [simplicialJoin, simplicialUnion, AbstractSimplicialComplex.faces, AbstractSimplicialComplex.instHasUnion]
  rw [Set.ext_iff]
  intro x
  constructor
  · intro H
    rw [Set.mem_diff] at H
    cases' H with H x_empty
    rcases H with ⟨s, Hs, t, Ht, Hx⟩
    rw [Set.mem_union, Set.mem_diff, Set.mem_diff]
    iterate 2 rw [Set.mem_setOf]
    iterate 2 rw [Set.mem_union] at Ht
    cases' Ht with Ht t_empty
    cases' Ht with t_in_y t_in_Z
    left
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
    right
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
    right
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
  · intro H
    rw [Set.mem_union, Set.mem_diff, Set.mem_diff] at H
    cases' H with Hy Hz
    cases' Hy with Hy x_nonempty
    rcases Hy with ⟨s, Hs, t, Ht, Hx⟩
    rw [Set.mem_diff]
    constructor
    use s; constructor; tauto
    use t
    rw [Set.mem_union, Set.mem_union]
    rw [Set.mem_union] at Ht
    tauto
    assumption
    cases' Hz with Hz x_nonempty
    rcases Hz with ⟨s, Hs, t, Ht, Hx⟩
    rw [Set.mem_diff]
    constructor
    use s; constructor; tauto
    use t
    rw [Set.mem_union, Set.mem_union]
    constructor
    rw [Set.mem_union] at Ht
    tauto
    assumption
    assumption

-- Lemma 2.4 (2), p.8
theorem join_distr_inter_left
    (X Y Z : AbstractSimplicialComplex E)
  : (X ⋆ (Y ∩ Z) : AbstractSimplicialComplex (E × 𝕜)) ≅ (X ⋆ Y ∩ (X ⋆ Z) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  apply simplicial_iso_preserves_equiv
  dsimp only [simplicialJoin, simplicialInter, AbstractSimplicialComplex.faces, AbstractSimplicialComplex.instHasInter]
  rw [Set.ext_iff]
  intro x
  constructor
  · intro H
    rw [Set.mem_diff] at H
    cases' H with H x_empty
    rcases H with ⟨s, Hs, t, Ht, Hx⟩
    rw [Set.mem_inter_iff, Set.mem_diff, Set.mem_diff]
    iterate 2 rw [Set.mem_setOf]
    rw [Set.mem_union] at Ht
    rw [Set.mem_inter_iff] at Ht
    cases' Ht with Ht t_empty
    cases' Ht with Hy Hz
    constructor
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
    constructor
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
    constructor
    use s; constructor; tauto
    use t; tauto
    assumption
  · intro H
    rw [Set.mem_inter_iff, Set.mem_diff, Set.mem_diff] at H
    cases' H with Hy Hz
    cases' Hy with Hy x_nonempty
    cases' Hz with Hz x_nonempty
    rcases Hy with ⟨sy, Hsy, ty, Hty, Hxy⟩
    rcases Hz with ⟨sz, Hsz, tz, Htz, Hxz⟩
    subst Hxy
    rw [simplex_disjoint_eq_unique] at Hxz
    cases' Hxz with Hsz Htz
    subst Hsz; subst Htz
    rw [Set.mem_diff]
    constructor
    use sz; constructor; tauto
    use tz
    rw [Set.mem_union, Set.mem_inter_iff]
    constructor
    cases' Htz with Htz t_empty
    cases' Hty with Hty t_empty
    iterate 5 tauto

/-
# Properties of Links
-/
theorem link_ident
    (X : AbstractSimplicialComplex E)
  : (Lk(X, ∅)).faces = X.faces :=
by
  simp only [link, Set.ext_iff, Set.mem_sep_iff]
  simp only [Finset.empty_union, Finset.empty_inter]
  simp only [and_true, and_self, forall_const]

theorem link_ident_iso
    (X : AbstractSimplicialComplex E)
  : Lk(X, ∅) ≅ X :=
by
  apply simplicial_iso_preserves_equiv
  apply link_ident

theorem link_disjoint_base
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (s_in_X : s ∈ X.faces)
  : t ∈ Lk(X, s).faces → Disjoint s t :=
by
  intro t_in_link
  simp only [link, Set.mem_sep_iff] at t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  rw [Finset.disjoint_iff_inter_eq_empty]
  assumption

theorem face_in_link_of_complement
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (s_in_X : s ∈ X.faces)
    (t_sset_s : t ⊆ s)
    (t_ne_s : t ≠ s)
  : s \ t ∈ Lk(X, t).faces :=
by
  simp only [link, Set.mem_union, Set.mem_sep_iff]
  constructor
  apply X.down_closed s_in_X
  apply Finset.sdiff_subset
  by_contra s_t_empty
  rw [Finset.sdiff_eq_empty_iff_subset] at s_t_empty
  revert t_ne_s
  contrapose
  simp
  rw [subset_antisymm_iff]
  tauto
  constructor
  rw [Finset.union_comm, Finset.sdiff_union_self_eq_union]
  have H : s = s ∪ t := by simp [Set.union_eq_left]; assumption
  rw [← H]
  assumption
  apply Finset.inter_sdiff_self

-- Lemma 3.5, p.14
theorem link_of_face_complement
    (X : AbstractSimplicialComplex E)
    (s t : Finset E)
    (s_in_X : s ∈ X.faces)
    (t_sset_s : t ⊆ s)
  : Lk(X, s) ≅ Lk(Lk(X, t), s \ t) :=
by
  by_cases h : s = t
  simp only [h, Finset.sdiff_self]
  rw [simplicial_iso_symm]
  apply link_ident_iso
  apply simplicial_iso_preserves_equiv
  simp only [link, Set.ext_iff]
  intro u
  constructor
  · intro u_in_link
    rw [Set.mem_sep_iff] at *
    choose u_in_X su_in_X su_empty using u_in_link
    repeat' rw [Set.mem_sep_iff]
    constructor
    constructor; assumption
    constructor
    apply X.down_closed
    assumption
    apply Finset.union_subset_union
    assumption
    apply Finset.Subset.refl
    simp
    contrapose
    rw [Classical.not_not]
    intro u_empty
    subst u_empty
    simp [X.empty_notMem] at u_in_X
    rw [← su_empty]
    apply Finset.inter_congr_right
    rw [su_empty]
    apply Finset.empty_subset
    apply @Finset.Subset.trans _ (t ∩ u) t s
    apply Finset.inter_subset_left
    assumption
    constructor; constructor
    apply X.down_closed
    assumption
    apply Finset.union_subset_union
    apply Finset.sdiff_subset
    apply Finset.Subset.refl
    simp
    contrapose
    rw [Classical.not_not]
    intro u_empty
    subst u_empty
    simp [X.empty_notMem] at u_in_X
    constructor
    rw [← Finset.union_assoc, Finset.union_comm t, Finset.sdiff_union_self_eq_union]
    have Hts : s ∪ t = s := by rw [Finset.union_eq_left]; assumption
    rw [Hts]
    assumption
    rw [Finset.inter_union_distrib_left, Finset.inter_sdiff_self, Finset.union_comm,
      Finset.union_empty]
    rw [← su_empty]
    apply Finset.inter_congr_right
    rw [su_empty]
    apply Finset.empty_subset
    apply @Finset.Subset.trans _ (t ∩ u) t s
    apply Finset.inter_subset_left
    assumption
    rw [← Finset.subset_empty, ← su_empty]
    apply Finset.inter_subset_inter_right
    apply Finset.sdiff_subset
  · intro u_in_link_of_link
    rw [Set.mem_sep_iff] at *
    choose u_in_t_link stu_in_t_link stu_empty using u_in_link_of_link
    rw [Set.mem_sep_iff] at *
    choose u_in_X tu_in_X tu_empty using u_in_t_link
    choose stu_in_X t_stu_in_X t_stu_empty using stu_in_t_link
    constructor; assumption
    constructor
    rw [← Finset.union_assoc, Finset.union_comm t, Finset.sdiff_union_self_eq_union] at t_stu_in_X
    have Hts : s ∪ t = s := by rw [Finset.union_eq_left]; assumption
    rw [Hts] at t_stu_in_X
    assumption
    have Hst : s \ t ∪ t = s := by apply Finset.sdiff_union_of_subset; assumption
    have Hstu : s \ t ∩ u ∪ t ∩ u = ∅ :=
      by
      rw [Finset.union_eq_empty]
      constructor <;> assumption
    rw [← Hst, Finset.union_inter_distrib_right]
    assumption

theorem barycenter_disjoint_boundary
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : Disjoint ((simplex {x}).vertices) ((∂s).vertices) :=
by
  rw [Set.disjoint_left]
  intro y y_in_barycenter
  apply @Set.notMem_subset _ _ _ (X.vertices)
  rw [Set.subset_def]
  intro z
  apply simplexBoundary_subcomplex_vert X s z s_in_X
  dsimp only [AbstractSimplicialComplex.vertices, simplex, AbstractSimplicialComplex.faces] at y_in_barycenter
  simp at y_in_barycenter
  subst y_in_barycenter
  assumption

theorem barycenter_join_boundary_disjoint_link
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : Disjoint ((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[(simplex {x}) ⋆ ∂s]).vertices)
       (Lk(X, s).vertices) :=
by
  rw [Set.disjoint_left]
  intro y y_in_join
  rw [join_proj_vertices_mem] at y_in_join
  dsimp only [vertices, link, SimplicialComplex.simplices]
  simp only [Set.mem_iUnion, not_exists]
  intro u u_in_link
  simp only [Set.mem_sep_iff] at u_in_link
  rcases u_in_link with ⟨u_in_X, su_in_X, su_empty⟩
  cases' y_in_join with y_in_barycenter y_in_bd
  -- y ∈ {x}
  dsimp only [vertices, simplex, SimplicialComplex.simplices] at y_in_barycenter
  simp only [Set.mem_iUnion] at y_in_barycenter
  choose t Ht y_in_t using y_in_barycenter
  rw [Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at Ht
  cases' Ht with t_empty t_ne
  rw [← Finset.coe_eq_empty, Set.eq_empty_iff_forall_not_mem] at t_empty
  specialize t_empty y
  contradiction
  rw [Finset.mem_coe, t_ne, Finset.mem_singleton] at y_in_t
  simp only [vertices, Set.mem_iUnion, not_exists] at x_nin_X
  specialize x_nin_X u
  specialize x_nin_X u_in_X
  rw [y_in_t]
  apply x_nin_X
  -- y ∈ ∂s
  dsimp only [vertices, simplexBoundary, SimplicialComplex.simplices] at y_in_bd
  simp only [Set.mem_iUnion] at y_in_bd
  choose t Ht y_in_t using y_in_bd
  rw [Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_iff] at Ht
  cases' Ht with t_ne t_empty
  cases' t_ne with y_in_s t_eq_s
  rw [Finset.mem_coe] at y_in_t
  specialize y_in_s y_in_t
  rw [← Finset.coe_eq_empty, Set.eq_empty_iff_forall_not_mem] at su_empty
  specialize su_empty y
  rw [Finset.mem_coe, Finset.mem_inter, not_and_or] at su_empty
  cases' su_empty with contra y_nin_u
  contradiction
  rw [Finset.mem_coe]
  apply y_nin_u
  rw [Set.mem_singleton_iff, ← Finset.coe_eq_empty, Set.eq_empty_iff_forall_not_mem] at t_empty
  specialize t_empty y
  contradiction

theorem boundary_disjoint_link
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (s_in_X : s ∈ X.faces)
  : Disjoint (Lk(X, s).vertices) ((∂s).vertices) :=
by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro x
  simp only [Set.mem_inter_iff, not_and, vertex_iff_in_simplex, not_exists]
  intro t_in_link u u_in_bd
  simp only [link, Set.mem_sep_iff] at t_in_link
  choose t t_in_link x_in_t using t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset] at u_in_bd
  cases' u_in_bd with u_ss_s u_empty
  simp at u_empty
  choose u_ne_s u_nonempty using u_empty
  have ut_disj : u ∩ t = ∅ := by
    rw [← Finset.subset_empty]
    apply @Finset.Subset.trans _ _ (s ∩ t)
    apply Finset.inter_subset_inter_right u_ss_s
    rw [Finset.subset_empty]
    assumption
  rw [Finset.eq_empty_iff_forall_notMem] at ut_disj
  specialize ut_disj x
  rw [Finset.mem_inter, not_and] at ut_disj
  by_cases x_in_u : x ∈ u
  specialize ut_disj x_in_u
  contradiction
  assumption

theorem barycenter_disjoint_link
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
    (x : E)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
  : Disjoint (Lk(X, s).vertices) ((simplex {x}).vertices) :=
by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro y
  simp only [Set.mem_inter_iff, not_and, vertex_iff_in_simplex, not_exists]
  intro t_in_link u u_in_barycenter
  simp only [link, Set.mem_sep_iff] at t_in_link
  choose t t_in_link y_in_t using t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  simp only [simplex, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u_in_barycenter
  cases' u_in_barycenter with u_eq_x u_nonempty
  rw [Set.mem_singleton_iff] at u_nonempty
  cases' u_eq_x with u_empty u_eq_x
  contradiction
  have ut_disj : u ∩ t = ∅ :=
    by
    rw [← Finset.coe_inj, Finset.coe_empty, ← Set.subset_empty_iff, Finset.coe_inter]
    apply @Set.Subset.trans _ _ ({x} ∩ X.vertices)
    apply Set.inter_subset_inter
    simp only [u_eq_x, Finset.coe_singleton]
    rfl
    apply simplex_subset_vertices
    assumption
    rw [Set.subset_empty_iff, Set.eq_empty_iff_forall_notMem]
    intro y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, not_and]
    intro y_eq_x
    subst y_eq_x
    assumption
  simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, not_and] at ut_disj
  specialize ut_disj y
  by_cases y_in_u : y ∈ u
  specialize ut_disj y_in_u
  contradiction
  assumption

theorem disjoint_complexes_disjoint_simplices
    (X Y : AbstractSimplicialComplex E)
    (s t : Finset E)
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces)
    (XY_disj : Disjoint (X.vertices) (Y.vertices))
  : Disjoint s t :=
by
  rw [← Finset.disjoint_coe]
  apply @Set.disjoint_of_subset _ _ (X.vertices) _ (Y.vertices)
  apply simplex_subset_vertices
  assumption
  apply simplex_subset_vertices
  assumption
  assumption
