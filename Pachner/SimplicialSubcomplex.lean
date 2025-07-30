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
  have f_inj : Set.InjOn f.map s :=
    by
    apply @Set.LeftInvOn.injOn _ _ _ _ g.map
    simp only [Set.LeftInvOn]
    intro x x_in_s
    have x_in_vert : x ∈ (simplex s).vertices :=
    by
      rw [vertex_iff_in_simplex]
      use s; constructor
      simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe]
      constructor
      apply Finset.mem_powerset_self
      rw [← ne_eq, ← Finset.nonempty_iff_ne_empty, ← Finset.nonempty_coe_sort]
      assumption
      assumption
    specialize gf_id x_in_vert
    assumption
  have g_inj : Set.InjOn g.map t :=
    by
    apply @Set.LeftInvOn.injOn _ _ _ _ f.map
    simp only [Set.LeftInvOn]
    intro x x_in_s
    have x_in_vert : x ∈ (simplex t).vertices :=
    by
      rw [vertex_iff_in_simplex]
      use t; constructor
      simp only [simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe]
      constructor
      apply Finset.mem_powerset_self
      rw [← ne_eq, ← Finset.nonempty_iff_ne_empty, ← Finset.nonempty_coe_sort]
      assumption
      assumption
    specialize fg_id x_in_vert
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
    intro fu_eq_fs a
    specialize fu_eq_fs (f.map a)
    cases' fu_eq_fs with fu_ss_fs fs_ss_fu
    constructor
    intro a_in_u
    rw [Finset.subset_iff] at u_ss_s
    specialize u_ss_s a_in_u
    assumption
    intro a_in_s
    apply Set.InjOn.mem_of_mem_image f_inj u_ss_s
    rw [Finset.mem_coe]
    assumption
    have Hs : ∃ x : α, x ∈ ↑s ∧ f.map x = f.map a :=
      by
      use a; constructor
      rw [Finset.mem_coe]
      assumption
      rfl
    specialize fs_ss_fu Hs
    simp only [Finset.mem_val, Set.mem_image]
    assumption
    assumption
    simp only [u_empty, Finset.image_empty]
    right; rfl
  have g_simp : IsSimplicialMap (∂t) (∂s) g.map :=
    by
    simp only [IsSimplicialMap, simplexBoundary]
    simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
      Finset.mem_powerset]
    intro u u_in_t
    cases' u_in_t with u_ss_t u_empty
    left
    choose u_ss_t u_ne_t using u_ss_t
    simp only [← Finset.coe_subset, ← Finset.coe_inj, ← simplex_vertices s]
    constructor
    apply simplex_subset_vertices
    apply g.is_simplicial
    simp only [simplex, Finset.mem_coe, Finset.mem_powerset]
    assumption
    rw [simplicial_iso_vertices (simplex t) (simplex s) g, simplex_vertices t, Finset.coe_image]
    revert u_ne_t
    contrapose
    simp only [Classical.not_not, Set.ext_iff, Finset.ext_iff, Set.mem_image]
    intro gu_eq_gt a
    specialize gu_eq_gt (g.map a)
    cases' gu_eq_gt with gu_ss_gt gs_ss_gt
    constructor
    intro a_in_u
    rw [Finset.subset_iff] at u_ss_t
    specialize u_ss_t a_in_u
    assumption
    intro a_in_t
    apply Set.InjOn.mem_of_mem_image g_inj u_ss_t
    rw [Finset.mem_coe]
    assumption
    have Ht : ∃ x : β, x ∈ ↑t ∧ g.map x = g.map a :=
      by
      use a; constructor
      rw [Finset.mem_coe]
      assumption
      rfl
    specialize gs_ss_gt Ht
    simp only [Finset.mem_val, Set.mem_image]
    assumption
    assumption
    simp only [u_empty, Finset.image_empty]
    right; rfl
  let f_bd : SimplicialMap (∂s) (∂t) := SimplicialMap.mk f.map f_simp
  let g_bd : SimplicialMap (∂t) (∂s) := SimplicialMap.mk g.map g_simp
  use f_bd; use g_bd
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def]
  constructor
  · intro x x_in_bd
    have x_in_s : x ∈ vertices (simplex s) :=
      by
      apply is_subcomplex_vertices _ (∂s)
      apply simplexBoundary_subcomplex_simplex
      assumption
    specialize gf_id x_in_s
    assumption
  · intro x x_in_bd
    have x_in_t : x ∈ vertices (simplex t) :=
      by
      apply is_subcomplex_vertices _ (∂t)
      apply simplexBoundary_subcomplex_simplex
      assumption
    specialize fg_id x_in_t
    assumption

theorem simplexBoundary_coe_image_left [Nonempty α] (X : SimplicialComplex α) (s : Finset α)
    (s_in_X : s ∈ X.simplices) (φ : SimplicialCoe X β) :
    (∂Finset.image φ.coe s).simplices ⊆ (simplicialImage (∂s) φ.coe).simplices :=
  by
  simp only [simplexBoundary, simplicialImage, Set.subset_def]
  simp only [Set.mem_setOf, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset]
  intro t t_in_bd
  cases' t_in_bd with t_in_bd t_empty
  choose t_ss_φs t_ne_φs using t_in_bd
  have inv_t : Finset.image φ.coe (Finset.image φ⁻ᶜ.map t) = t :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image, Set.ext_iff, Set.mem_image]
    intro y
    constructor
    intro y_in_img
    choose a a_in_img φa_y using y_in_img
    choose b b_in_t φb_a using a_in_img
    subst φb_a
    subst φa_y
    have inv_b : φ.coe (φ⁻ᶜ.map b) = b :=
      by
      apply Set.InjOn.rightInvOn_of_leftInvOn
      apply simplicialCoeInv_inj
      apply Set.InjOn.leftInvOn_invFunOn
      apply φ.injective
      apply Set.SurjOn.mapsTo_invFunOn
      apply simplicialCoe_surjective_vertices
      apply simplicialCoe_mapsTo_vertices
      rw [vertex_iff_in_simplex]
      use t; constructor
      apply φ[X].subset_closed (Finset.image φ.coe s)
      apply map_is_simplicial_onto_image
      assumption
      assumption
      rw [← Finset.mem_coe]
      assumption
    rw [inv_b]
    assumption
    intro y_in_t
    use φ⁻ᶜ.map y; constructor
    use y; constructor
    assumption
    rfl
    apply Set.InjOn.rightInvOn_of_leftInvOn
    apply simplicialCoeInv_inj
    apply Set.InjOn.leftInvOn_invFunOn
    apply φ.injective
    apply Set.SurjOn.mapsTo_invFunOn
    apply simplicialCoe_surjective_vertices
    apply simplicialCoe_mapsTo_vertices
    rw [vertex_iff_in_simplex]
    use t; constructor
    apply φ[X].subset_closed (Finset.image φ.coe s)
    apply map_is_simplicial_onto_image
    assumption
    assumption
    rw [← Finset.mem_coe]
    assumption
  use Finset.image φ⁻ᶜ.map t; constructor
  have inv_s : Finset.image φ⁻ᶜ.map (Finset.image φ.coe s) = s :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.injective
    apply simplex_subset_vertices
    assumption
  left; constructor
  have inv_t_ss_φs : Finset.image φ⁻ᶜ.map t ⊆ Finset.image φ⁻ᶜ.map (Finset.image φ.coe s) :=
    by
    apply Finset.image_subset_image
    assumption
  rw [inv_s] at inv_t_ss_φs
  assumption
  revert t_ne_φs
  contrapose
  simp only [Classical.not_not]
  intro φt_s
  rw [← φt_s]
  symm
  assumption
  assumption
  use∅; constructor
  right; rfl
  rw [t_empty]
  apply Finset.image_empty

theorem simplexBoundary_coe_image_right (X : SimplicialComplex α) (s : Finset α)
    (s_in_X : s ∈ X.simplices) (φ : SimplicialCoe X β) :
    (simplicialImage (∂s) φ.coe).simplices ⊆ (∂Finset.image φ.coe s).simplices :=
  by
  simp only [simplexBoundary, simplicialImage, Set.subset_def]
  simp only [Set.mem_setOf, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset]
  intro t t_in_img
  choose u u_in_bd φu_t using t_in_img
  cases' u_in_bd with u_in_bd u_empty
  choose u_ss_s u_ne_s using u_in_bd
  left; constructor
  rw [← φu_t]
  apply Finset.image_subset_image
  assumption
  rw [← φu_t]
  revert u_ne_s
  contrapose
  simp only [Classical.not_not]
  intro φu_eq_φs
  simp only [← Finset.coe_inj, Finset.coe_image, Set.ext_iff] at φu_eq_φs ⊢
  intro a
  specialize φu_eq_φs (φ.coe a)
  cases' φu_eq_φs with φu_ss_φs φs_ss_φu
  constructor
  intro a_in_u
  have a_in_X : a ∈ vertices X := by
    rw [vertex_iff_in_simplex]
    use u; constructor
    apply X.subset_closed s <;> assumption
    rw [← Finset.mem_coe]
    assumption
  rw [← Set.InjOn.mem_image_iff φ.injective] at a_in_u ⊢
  specialize φu_ss_φs a_in_u
  assumption
  apply simplex_subset_vertices
  assumption
  assumption
  apply simplex_subset_vertices
  apply X.subset_closed s <;> assumption
  assumption
  intro a_in_s
  have a_in_X : a ∈ vertices X := by
    rw [vertex_iff_in_simplex]
    use s; constructor <;> assumption
  rw [← Set.InjOn.mem_image_iff φ.injective] at a_in_s ⊢
  specialize φs_ss_φu a_in_s
  assumption
  apply simplex_subset_vertices
  apply X.subset_closed s <;> assumption
  assumption
  apply simplex_subset_vertices
  assumption
  assumption
  right
  rw [u_empty, Finset.image_empty] at φu_t
  symm
  assumption

theorem simplexBoundary_coe_image [Nonempty α] (X : SimplicialComplex α) (s : Finset α)
    (s_in_X : s ∈ X.simplices) (φ : SimplicialCoe X β) :
    (∂Finset.image φ.coe s).simplices = (simplicialImage (∂s) φ.coe).simplices :=
  by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply simplexBoundary_coe_image_left
  assumption
  apply simplexBoundary_coe_image_right
  assumption

theorem simplexBoundary_subcomplex_simplices (X : SimplicialComplex α) (s t : Finset α)
    (s_in_X : s ∈ X.simplices) : t ∈ (∂s).simplices → t ∈ X.simplices :=
  by
  intro t_in_bd
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset] at
    t_in_bd
  cases' t_in_bd with t_ss_s t_empty
  choose t_ss_s t_ne_s using t_ss_s
  apply X.subset_closed <;> assumption
  rw [Set.mem_singleton_iff] at t_empty
  rw [t_empty]
  apply simplicialComplex_empty_simplex

theorem simplexBoundary_subcomplex (X : SimplicialComplex α) (s : Finset α)
    (s_in_X : s ∈ X.simplices) : ∂s ⊆ X :=
  by
  simp only [IsSubcomplex, Set.subset_def]
  intro u
  apply simplexBoundary_subcomplex_simplices
  assumption

theorem simplexBoundary_subcomplex_vert (X : SimplicialComplex α) (s : Finset α) (x : α)
    (s_in_X : s ∈ X.simplices) : x ∈ vertices (∂s) → x ∈ vertices X :=
  by
  intro x_in_bd
  simp only [vertices_setOf, Set.mem_setOf] at x_in_bd ⊢
  choose t t_in_bd x_in_t using x_in_bd
  use t; constructor
  apply simplexBoundary_subcomplex_simplices X s t s_in_X t_in_bd
  assumption

theorem simplexBoundary_mem_iff_subset (s t : Finset α) [Nonempty s] : t ∈ (∂s).simplices ↔ t ⊂ s :=
  by
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
    Set.mem_singleton_iff, Finset.ssubset_iff_subset_ne]
  constructor
  intro t_in_bd
  cases' t_in_bd with t_ss_s t_empty
  assumption
  rw [t_empty]
  constructor
  apply Set.empty_subset
  symm
  rw [← Finset.nonempty_iff_ne_empty, ← Finset.nonempty_coe_sort]
  assumption
  intro t_ss_s
  rw [Ne.def] at t_ss_s
  left; assumption

theorem subsimplex_boundary_subcomplex (s t : Finset α) : s ⊆ t → ∂s ⊆ ∂t :=
  by
  simp only [IsSubcomplex, simplexBoundary, Set.subset_def, Finset.subset_iff]
  intro s_ss_t u u_in_bd_s
  simp only [Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
    Set.mem_singleton_iff] at u_in_bd_s ⊢
  cases' u_in_bd_s with u_ss_s u_empty
  left
  choose u_ss_s u_ne_s using u_ss_s
  simp only [Finset.subset_iff] at u_ss_s ⊢
  constructor
  intro x x_in_u
  specialize u_ss_s x_in_u
  specialize s_ss_t u_ss_s
  assumption
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
  right
  assumption

-- Star of a complex wrt a simplex.
@[simp]
def star (X : SimplicialComplex α) (s : Finset α) (s_in_X : s ∈ X.simplices) :
    SimplicialComplex α :=
  SimplicialComplex.mk ({t ∈ X.simplices | s ∪ t ∈ X.simplices})
    (by
      rw [Set.nonempty_coe_sort, Set.nonempty_def]
      use∅
      rw [Set.mem_sep_iff]
      constructor
      apply simplicialComplex_empty_simplex
      rw [Finset.union_empty]
      assumption)
    (by
      simp
      intro s_1 _ _ t _
      have : t ⊆ s_1 → t ∈ X.simplices := by apply X.subset_closed; assumption
      have : s ⊆ s → t ⊆ s_1 → s ∪ t ⊆ s ∪ s_1 := Finset.union_subset_union
      have : s ∪ t ⊆ s ∪ s_1 → s ∪ t ∈ X.simplices := by apply X.subset_closed; assumption
      finish)

notation "St(" X ", " s ")" => star X s

instance star.fintype (X : SimplicialComplex α) [Fintype X.simplices] (s : Finset α)
    (s_in_X : s ∈ X.simplices) : Fintype (star X s s_in_X).simplices :=
  by
  unfold star
  dsimp only [SimplicialComplex.simplices]
  have H_dec : DecidablePred fun a : Finset α => s ∪ a ∈ X.simplices :=
    by
    unfold DecidablePred
    intro a
    apply Set.decidableMemOfFintype
  apply @Set.fintypeSep _ _ _ _ H_dec
  assumption

theorem star_subcomplex_simplices (X : SimplicialComplex α) (s t : Finset α)
    (s_in_X : s ∈ X.simplices) : t ∈ (St(X, s) s_in_X).simplices → t ∈ X.simplices :=
  by
  intro t_in_star
  simp only [star, Set.mem_sep_iff] at t_in_star
  choose t_in_X st_in_X using t_in_star
  assumption

theorem star_subcomplex (X : SimplicialComplex α) (s : Finset α) (s_in_X : s ∈ X.simplices) :
    St(X, s) s_in_X ⊆ X := by
  simp only [IsSubcomplex, Set.subset_def]
  intro t
  apply star_subcomplex_simplices

theorem star_iso (X : SimplicialComplex α) (Y : SimplicialComplex β) (s : Finset α) (t : Finset β)
    (f : SimplicialMap X Y) (s_in_X : s ∈ X.simplices) (t_in_Y : t ∈ Y.simplices)
    (f_iso : IsSimplicialIso f) : Finset.image f.map s = t → St(X, s) s_in_X ≅ St(Y, t) t_in_Y :=
  by
  intro fs_eq_t
  unfold IsSimpliciallyIso
  have f_simp : IsSimplicialMap (St(X, s) s_in_X) (St(Y, t) t_in_Y) f.map :=
    by
    simp only [IsSimplicialMap, star, Set.mem_sep_iff]
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
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def] at gf_id fg_id
  have gt_eq_s : Finset.image g.map t = s :=
    by
    rw [← fs_eq_t, Finset.ext_iff, Finset.image_image]
    intro x
    constructor
    intro x_in_img
    simp only [Finset.mem_image, Function.comp_apply] at x_in_img
    choose y y_in_s gfy_eq_x using x_in_img
    have y_in_X : y ∈ vertices X := by
      rw [vertex_iff_in_simplex]
      use s; constructor <;> assumption
    specialize gf_id y_in_X
    rw [← gfy_eq_x, gf_id]
    assumption
    intro x_in_s
    simp only [Finset.mem_image, Function.comp_apply]
    use x; constructor; assumption
    have x_in_X : x ∈ vertices X := by
      rw [vertex_iff_in_simplex]
      use s; constructor <;> assumption
    specialize gf_id x_in_X
    assumption
  have g_simp : IsSimplicialMap (St(Y, t) t_in_Y) (St(X, s) s_in_X) g.map :=
    by
    simp only [IsSimplicialMap, star, Set.mem_sep_iff]
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
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def]
  constructor
  · intro x x_in_star
    have x_in_X : x ∈ vertices X :=
      by
      apply is_subcomplex_vertices X (St(X, s) s_in_X) (star_subcomplex X s s_in_X)
      assumption
    specialize gf_id x_in_X
    assumption
  · intro x x_in_star
    have x_in_Y : x ∈ vertices Y :=
      by
      apply is_subcomplex_vertices Y (St(Y, t) t_in_Y) (star_subcomplex Y t t_in_Y)
      assumption
    specialize fg_id x_in_Y
    assumption

-- Link of a complex wrt a simplex.
@[simp]
def link (X : SimplicialComplex α) (s : Finset α) (s_in_X : s ∈ X.simplices) :
    SimplicialComplex α :=
  SimplicialComplex.mk ({t ∈ X.simplices | s ∪ t ∈ X.simplices ∧ s ∩ t = ∅})
    (by
      rw [Set.nonempty_coe_sort, Set.nonempty_def]
      use∅
      rw [Set.mem_sep_iff]
      constructor
      apply simplicialComplex_empty_simplex
      constructor
      rw [Finset.union_empty]
      assumption
      rw [Finset.inter_empty])
    (by
      simp
      intro s_1 _ _ _ Hss1_inter t Ht_sset
      constructor <;> constructor <;>
        try
          revert Ht_sset
          apply X.subset_closed
          assumption
      · suffices : s ∪ t ⊆ s ∪ s_1
        revert this
        apply X.subset_closed
        assumption
        apply Finset.union_subset_union <;> tauto
      · rw [← Finset.disjoint_iff_inter_eq_empty]
        apply Finset.disjoint_of_subset_right Ht_sset
        rw [Finset.disjoint_iff_inter_eq_empty]
        assumption)

notation "Lk(" X ", " s ")" => link X s

instance link.fintype (X : SimplicialComplex α) [Fintype X.simplices] (s : Finset α)
    (s_in_X : s ∈ X.simplices) : Fintype (link X s s_in_X).simplices :=
  by
  simp only [link, SimplicialComplex.simplices]
  rw [Set.sep_and]
  have dec_left : DecidablePred fun x : Finset α => s ∪ x ∈ X.simplices :=
    by
    unfold DecidablePred
    intro x
    apply Set.decidableMemOfFintype
  have fin_left : Fintype ↥({x ∈ X.simplices | s ∪ x ∈ X.simplices}) :=
    by
    apply @Set.fintypeSep _ _ _ _ dec_left
    assumption
  have dec_right : DecidablePred fun x : Finset α => s ∩ x = ∅ :=
    by
    unfold DecidablePred
    intro x
    apply Set.decidableMemOfFintype
  have fin_right : Fintype ↥({x ∈ X.simplices | s ∩ x = ∅}) :=
    by
    apply @Set.fintypeSep _ _ _ _ dec_right
    assumption
  apply @Set.fintypeInter _ _ _ _ fin_left fin_right

theorem link_coe_image_left (X : SimplicialComplex α) (s : Finset α) (s_in_X : s ∈ X.simplices)
    (φ : SimplicialCoe X β) :
    (Lk(φ[X], Finset.image φ.coe s) (by apply map_is_simplicial_onto_image; assumption)).simplices ⊆
      (simplicialImage (Lk(X, s) s_in_X) φ.coe).simplices :=
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
    have a_in_X : a ∈ vertices X := by
      rw [vertex_iff_in_simplex]
      use v; constructor <;> assumption
    rw [← Set.InjOn.mem_image_iff φ.injective] at a_in_v ⊢
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
    have a_in_X : a ∈ vertices X :=
      by
      rw [Finset.coe_union, Set.mem_union] at a_in_su
      cases' a_in_su with a_in_s a_in_u
      rw [vertex_iff_in_simplex]
      use s; constructor <;> assumption
      rw [vertex_iff_in_simplex]
      use u; constructor <;> assumption
    rw [← Set.InjOn.mem_image_iff φ.injective] at a_in_su ⊢
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
  apply φ.injective
  apply simplex_subset_vertices
  assumption
  apply simplex_subset_vertices
  assumption
  assumption

theorem link_coe_image_right (X : SimplicialComplex α) (s : Finset α) (s_in_X : s ∈ X.simplices)
    (φ : SimplicialCoe X β) :
    (simplicialImage (Lk(X, s) s_in_X) φ.coe).simplices ⊆
      (Lk(φ[X], Finset.image φ.coe s)
          (by apply map_is_simplicial_onto_image; assumption)).simplices :=
  by
  simp only [link, simplicialImage, Set.subset_def]
  simp only [Set.mem_sep_iff, Set.mem_setOf]
  intro t t_in_img
  choose u u_in_link φu_t using t_in_img
  choose u_in_X su_in_X su_disj using u_in_link
  constructor
  use u; constructor <;> assumption
  use s ∪ u; constructor; assumption
  rw [← φu_t, Finset.image_union]
  simp only [← φu_t, ← Finset.coe_inj, Finset.coe_image, Finset.coe_inter]
  rw [← Set.InjOn.image_inter, ← Finset.coe_inter, ← Finset.coe_image, Finset.coe_inj,
    Finset.image_eq_empty]
  assumption
  apply φ.injective
  apply simplex_subset_vertices
  assumption
  apply simplex_subset_vertices
  assumption

theorem link_coe_image (X : SimplicialComplex α) (s : Finset α) (s_in_X : s ∈ X.simplices)
    (φ : SimplicialCoe X β) :
    (Lk(φ[X], Finset.image φ.coe s) (by apply map_is_simplicial_onto_image; assumption)).simplices =
      (simplicialImage (Lk(X, s) s_in_X) φ.coe).simplices :=
  by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply link_coe_image_left
  apply link_coe_image_right

theorem link_subcomplex_simplices (X : SimplicialComplex α) (s t : Finset α)
    (s_in_X : s ∈ X.simplices) : t ∈ (Lk(X, s) s_in_X).simplices → t ∈ X.simplices :=
  by
  intro t_in_link
  simp only [link, Set.mem_sep_iff] at t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  assumption

theorem link_subcomplex (X : SimplicialComplex α) (s : Finset α) (s_in_X : s ∈ X.simplices) :
    Lk(X, s) s_in_X ⊆ X := by
  simp only [IsSubcomplex, Set.subset_def]
  intro t
  apply link_subcomplex_simplices

theorem link_iso (X : SimplicialComplex α) (Y : SimplicialComplex β) (s : Finset α) (t : Finset β)
    (f : SimplicialMap X Y) (s_in_X : s ∈ X.simplices) (t_in_Y : t ∈ Y.simplices)
    (f_iso : IsSimplicialIso f) : Finset.image f.map s = t → Lk(X, s) s_in_X ≅ Lk(Y, t) t_in_Y :=
  by
  intro fs_eq_t
  unfold IsSimpliciallyIso
  have f_simp : IsSimplicialMap (Lk(X, s) s_in_X) (Lk(Y, t) t_in_Y) f.map :=
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
    id.def] at gf_id fg_id
  have gt_eq_s : Finset.image g.map t = s :=
    by
    rw [← fs_eq_t, Finset.ext_iff, Finset.image_image]
    intro x
    constructor
    intro x_in_img
    simp only [Finset.mem_image, Function.comp_apply] at x_in_img
    choose y y_in_s gfy_eq_x using x_in_img
    have y_in_X : y ∈ vertices X := by
      rw [vertex_iff_in_simplex]
      use s; constructor <;> assumption
    specialize gf_id y_in_X
    rw [← gfy_eq_x, gf_id]
    assumption
    intro x_in_s
    simp only [Finset.mem_image, Function.comp_apply]
    use x; constructor; assumption
    have x_in_X : x ∈ vertices X := by
      rw [vertex_iff_in_simplex]
      use s; constructor <;> assumption
    specialize gf_id x_in_X
    assumption
  have g_simp : IsSimplicialMap (Lk(Y, t) t_in_Y) (Lk(X, s) s_in_X) g.map :=
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
    id.def]
  constructor
  · intro x x_in_X_link
    have x_in_X : x ∈ vertices X :=
      by
      apply is_subcomplex_vertices X (Lk(X, s) s_in_X)
      apply link_subcomplex
      assumption
    specialize gf_id x_in_X
    assumption
  · intro x x_in_Y_link
    have x_in_Y : x ∈ vertices Y :=
      by
      apply is_subcomplex_vertices Y (Lk(Y, t) t_in_Y)
      apply link_subcomplex
      assumption
    specialize fg_id x_in_Y
    assumption

theorem link_fact_inter (X Y : SimplicialComplex α) (s : Finset α)
    (s_in_XY : s ∈ (X ∩ Y).simplices) :
    (Lk(X ∩ Y, s) s_in_XY).simplices =
      (Lk(X, s) (subcomplex_simplicial_inter_left_simplices X Y s s_in_XY)).simplices ∩
        (Lk(Y, s) (subcomplex_simplicial_inter_right_simplices X Y s s_in_XY)).simplices :=
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

theorem link_fact_union_left (X Y : SimplicialComplex α) (s : Finset α) (s_in_X : s ∈ X.simplices)
    (s_nin_Y : s ∉ Y.simplices) :
    (Lk(X ∪ Y, s) (subcomplex_simplicial_union_left_simplices X Y s s_in_X)).simplices =
      (Lk(X, s) s_in_X).simplices :=
  by
  simp only [link, simplicialUnion, Set.ext_iff, Set.mem_sep_iff, Set.mem_union]
  intro t
  constructor
  · intro t_in_XY
    choose t_in_XY st_in_XY st_disj using t_in_XY
    cases' t_in_XY with t_in_X contra <;> cases' st_in_XY with st_in_X contra
    constructor; assumption
    constructor <;> assumption
    have s_in_Y : s ∈ Y.simplices := by
      apply Y.subset_closed (s ∪ t)
      assumption
      apply Finset.subset_union_left
    contradiction
    constructor
    apply X.subset_closed (s ∪ t)
    assumption
    apply Finset.subset_union_right
    constructor <;> assumption
    have s_in_Y : s ∈ Y.simplices := by
      apply Y.subset_closed (s ∪ t)
      assumption
      apply Finset.subset_union_left
    contradiction
  · intro t_in_X
    choose t_in_X st_in_X st_disj using t_in_X
    constructor; left; assumption
    constructor; left; assumption
    assumption

theorem link_fact_union_right (X Y : SimplicialComplex α) (s : Finset α) (s_nin_X : s ∉ X.simplices)
    (s_in_Y : s ∈ Y.simplices) :
    (Lk(X ∪ Y, s) (subcomplex_simplicial_union_right_simplices X Y s s_in_Y)).simplices =
      (Lk(Y, s) s_in_Y).simplices :=
  by
  simp only [link, simplicialUnion, Set.ext_iff, Set.mem_sep_iff, Set.mem_union]
  intro t
  constructor
  · intro t_in_XY
    choose t_in_XY st_in_XY st_disj using t_in_XY
    cases' t_in_XY with contra t_in_Y <;> cases' st_in_XY with contra st_in_X
    have s_in_X : s ∈ X.simplices := by
      apply X.subset_closed (s ∪ t)
      assumption
      apply Finset.subset_union_left
    contradiction
    constructor
    apply Y.subset_closed (s ∪ t)
    assumption
    apply Finset.subset_union_right
    constructor <;> assumption
    have s_in_X : s ∈ X.simplices := by
      apply X.subset_closed (s ∪ t)
      assumption
      apply Finset.subset_union_left
    contradiction
    constructor; assumption
    constructor <;> assumption
  · intro t_in_Y
    choose t_in_Y st_in_Y st_disj using t_in_Y
    constructor; right; assumption
    constructor; right; assumption
    assumption

theorem link_fact_union (X Y : SimplicialComplex α) (s : Finset α)
    (s_in_XY : s ∈ (X ∩ Y).simplices) :
    (Lk(X ∪ Y, s)
          (by
            apply simplex_if_in_subcomplex (X ∩ Y)
            assumption
            simp only [IsSubcomplex, simplicialInter, simplicialUnion]
            apply Set.subset_union_of_subset_left
            apply Set.inter_subset_left)).simplices =
      (Lk(X, s) (by apply subcomplex_simplicial_inter_left_simplices X Y s s_in_XY)).simplices ∪
        (Lk(Y, s) (by apply subcomplex_simplicial_inter_right_simplices X Y s s_in_XY)).simplices :=
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
    apply Y.subset_closed (s ∪ t)
    assumption
    apply Finset.subset_union_right
    constructor <;> assumption
    left
    constructor
    apply X.subset_closed (s ∪ t)
    assumption
    apply Finset.subset_union_right
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
def starComplement (X : SimplicialComplex α) (s : Finset α) [Nonempty s]
    (s_in_X : s ∈ X.simplices) : SimplicialComplex α :=
  SimplicialComplex.mk ({t ∈ X.simplices | ¬s ⊆ t})
    (by
      rw [Set.nonempty_coe_sort, Set.nonempty_def]
      use∅
      rw [Set.mem_sep_iff]
      constructor
      apply simplicialComplex_empty_simplex
      rw [Finset.subset_empty]
      apply Finset.Nonempty.ne_empty
      rw [← Finset.nonempty_coe_sort]
      assumption)
    (by
      simp
      intro s_1 s1_in_X s_nsset_s1 t t_sset_s
      constructor
      apply X.subset_closed s_1 <;> assumption
      rw [Finset.not_subset] at *
      choose x Hx x_nin_s1 using s_nsset_s1
      use x; constructor; assumption
      revert x_nin_s1
      contrapose
      simp
      apply Finset.mem_of_subset
      assumption)

notation X "\\St(" X ", " s ")" => starComplement X s

instance starComplement.fintype (X : SimplicialComplex α) [Fintype X.simplices] (s : Finset α)
    [Nonempty s] (s_in_X : s ∈ X.simplices) : Fintype (starComplement X s s_in_X).simplices :=
  by
  simp only [starComplement, SimplicialComplex.simplices]
  have H_dec : DecidablePred fun t : Finset α => ¬s ⊆ t :=
    by
    unfold DecidablePred
    intro t
    simp only [Finset.subset_iff, Classical.not_forall]
    apply Finset.decidableDExistsFinset
  apply @Set.fintypeSep _ _ _ _ H_dec
  assumption

theorem starComplement_subcomplex_simplices (X : SimplicialComplex α) (s t : Finset α) [Nonempty s]
    (s_in_X : s ∈ X.simplices) : t ∈ ((X\St(X, s)) s_in_X).simplices → t ∈ X.simplices :=
  by
  simp only [starComplement, Set.mem_sep_iff]
  intro t_in_star_comp
  choose t_in_X s_nss_t using t_in_star_comp
  assumption

theorem starComplement_subcomplex (X : SimplicialComplex α) (s : Finset α) [Nonempty s]
    (s_in_X : s ∈ X.simplices) : (X\St(X, s)) s_in_X ⊆ X :=
  by
  simp only [IsSubcomplex, Set.subset_def]
  intro t
  apply starComplement_subcomplex_simplices

theorem starComplement_iso (X : SimplicialComplex α) (Y : SimplicialComplex β) (s : Finset α)
    [Nonempty s] (t : Finset β) [Nonempty t] (f : SimplicialMap X Y) (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices) (f_iso : IsSimplicialIso f) :
    Finset.image f.map s = t → (X\St(X, s)) s_in_X ≅ (Y\St(Y, t)) t_in_Y :=
  by
  intro fs_eq_t
  unfold IsSimpliciallyIso
  have f_simp : IsSimplicialMap ((X\St(X, s)) s_in_X) ((Y\St(Y, t)) t_in_Y) f.map :=
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
    use x; constructor
    use x_in_s
    intro y y_in_u
    rw [@Set.InjOn.eq_iff _ _ (vertices X)]
    revert y_in_u x_nin_u
    contrapose
    simp only [Classical.not_forall, Classical.not_not, exists_prop, and_imp]
    intro x_nin_u y_eq_x
    rw [y_eq_x]
    assumption
    apply iso_is_injective_vertices
    assumption
    rw [vertex_iff_in_simplex]
    use u; constructor <;> assumption
    rw [vertex_iff_in_simplex]
    use s; constructor <;> assumption
  let f_comp := SimplicialMap.mk f.map f_simp
  let f_iso' := f_iso
  unfold IsSimplicialIso at f_iso'
  choose g gf_inv using f_iso'
  let gf_inv' := gf_inv
  unfold IsInverseSimplicialIso at gf_inv'
  choose gf_id fg_id using gf_inv'
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def] at gf_id fg_id
  have gt_eq_s : Finset.image g.map t = s :=
    by
    rw [← fs_eq_t, Finset.ext_iff, Finset.image_image]
    intro x
    constructor
    intro x_in_img
    simp only [Finset.mem_image, Function.comp_apply] at x_in_img
    choose y y_in_s gfy_eq_x using x_in_img
    have y_in_X : y ∈ vertices X := by
      rw [vertex_iff_in_simplex]
      use s; constructor <;> assumption
    specialize gf_id y_in_X
    rw [← gfy_eq_x, gf_id]
    assumption
    intro x_in_s
    simp only [Finset.mem_image, Function.comp_apply]
    use x; constructor; assumption
    have x_in_X : x ∈ vertices X := by
      rw [vertex_iff_in_simplex]
      use s; constructor <;> assumption
    specialize gf_id x_in_X
    assumption
  have g_simp : IsSimplicialMap ((Y\St(Y, t)) t_in_Y) ((X\St(X, s)) s_in_X) g.map :=
    by
    simp only [IsSimplicialMap, starComplement, Set.mem_sep_iff]
    intro u u_in_Y_comp
    choose u_in_X t_nss_u using u_in_Y_comp
    constructor
    apply g.is_simplicial
    assumption
    simp only [← gt_eq_s, Finset.image_subset_iff, Classical.not_forall, Finset.mem_image,
      not_exists]
    simp only [Finset.subset_iff, Classical.not_forall] at t_nss_u
    choose x x_in_t x_nin_u using t_nss_u
    use x; constructor
    use x_in_t
    intro y y_in_u
    rw [@Set.InjOn.eq_iff _ _ (vertices Y)]
    revert y_in_u x_nin_u
    contrapose
    simp only [Classical.not_forall, Classical.not_not, exists_prop, and_imp]
    intro x_nin_u y_eq_x
    rw [y_eq_x]
    assumption
    apply iso_is_injective_vertices
    apply iso_inv_is_iso f <;> assumption
    rw [vertex_iff_in_simplex]
    use u; constructor <;> assumption
    rw [vertex_iff_in_simplex]
    use t; constructor <;> assumption
  let g_comp := SimplicialMap.mk g.map g_simp
  use f_comp
  unfold IsSimplicialIso
  use g_comp
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def]
  constructor
  · intro x x_in_X_comp
    have x_in_X : x ∈ vertices X :=
      by
      apply is_subcomplex_vertices X ((X\St(X, s)) s_in_X)
      apply starComplement_subcomplex
      assumption
    specialize gf_id x_in_X
    assumption
  · intro x x_in_Y_comp
    have x_in_Y : x ∈ vertices Y :=
      by
      apply is_subcomplex_vertices Y ((Y\St(Y, t)) t_in_Y)
      apply starComplement_subcomplex
      assumption
    specialize fg_id x_in_Y
    assumption

theorem starComplement_coe_image_left (X : SimplicialComplex α) (s : Finset α) [Nonempty s]
    (s_in_X : s ∈ X.simplices) (φ : SimplicialCoe X β) :
    (starComplement (φ[X]) (Finset.image φ.coe s)
          (by apply map_is_simplicial_onto_image; assumption)).simplices ⊆
      (simplicialImage ((X\St(X, s)) s_in_X) φ.coe).simplices :=
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

theorem starComplement_coe_image_right (X : SimplicialComplex α) (s : Finset α) [Nonempty s]
    (s_in_X : s ∈ X.simplices) (φ : SimplicialCoe X β) :
    (simplicialImage ((X\St(X, s)) s_in_X) φ.coe).simplices ⊆
      (starComplement (φ[X]) (Finset.image φ.coe s)
          (by apply map_is_simplicial_onto_image; assumption)).simplices :=
  by
  simp only [starComplement, simplicialImage, Set.subset_def]
  simp only [Set.mem_sep_iff, Set.mem_setOf]
  intro t t_in_img
  choose u u_in_star_comp φu_t using t_in_img
  choose u_in_X s_nss_u using u_in_star_comp
  constructor
  use u; constructor <;> assumption
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
  apply φ.injective
  apply simplex_subset_vertices
  assumption
  rw [vertex_iff_in_simplex]
  use s; constructor <;> assumption

theorem starComplement_coe_image (X : SimplicialComplex α) (s : Finset α) [Nonempty s]
    (s_in_X : s ∈ X.simplices) (φ : SimplicialCoe X β) :
    (starComplement (φ[X]) (Finset.image φ.coe s)
          (by apply map_is_simplicial_onto_image; assumption)).simplices =
      (simplicialImage ((X\St(X, s)) s_in_X) φ.coe).simplices :=
  by
  rw [Set.Subset.antisymm_iff]
  constructor
  apply starComplement_coe_image_left
  apply starComplement_coe_image_right

@[simp]
def IsNegOneSphere {X : SimplicialComplex α} {s : Finset α} {s_in_X : s ∈ X.simplices}
    (Y : SimplicialComplex α) (Y_link_X : Y = Lk(X, s) s_in_X) : Prop :=
  Y = emptySc

@[simp]
def negOneBall {X : SimplicialComplex α} (x : α) (x_nin_X : x ∉ vertices X) : SimplicialComplex α :=
  SimplicialComplex.mk {{x}, ∅}
    (by
      rw [Set.nonempty_coe_sort, Set.nonempty_def]
      use∅
      simp)
    (by
      simp
      intro t t_sset_empty
      rw [Finset.subset_empty] at t_sset_empty
      tauto)

instance negOneBall.fintype {X : SimplicialComplex α} (x : α) (x_nin_X : x ∉ vertices X) :
    Fintype (negOneBall x x_nin_X).simplices :=
  by
  simp only [negOneBall]
  apply Set.fintypeInsert {x} {∅}
  apply Finset.decidableEq
  apply Set.fintypeSingleton

theorem dim_of_negOneBall {X : SimplicialComplex α} (x : α) (x_nin_X : x ∉ vertices X) :
    dimOfComplex (negOneBall x x_nin_X) = 0 :=
  by
  simp only [dimOfComplex, negOneBall, dim, Set.toFinset_insert, Set.toFinset_singleton,
    Finset.image_insert, Finset.card_singleton, Nat.cast_one, sub_self]
  simp only [dim, Finset.image_singleton, Finset.card_empty, Nat.cast_zero, zero_sub]
  unfold Finset.max'
  simp only [Finset.singleton_nonempty, id.def, Finset.sup'_insert, Finset.sup'_singleton,
    sup_of_le_left, Right.neg_nonpos_iff, zero_le_one]

-- The ball around a simplex.
def mBall (X : SimplicialComplex α) [Fintype X.simplices] (s : Finset α)
    (s_in_X : s ∈ X.simplices) : SimplicialComplex α :=
  SimplicialComplex.mk (Finset.powerset (vertices (Lk(X, s) s_in_X)).toFinset)
    (by
      rw [Set.nonempty_coe_sort, Set.nonempty_def]
      exists ∅
      apply Finset.empty_mem_powerset)
    (by
      unfold IsSubsetClosed
      intro t t_in_link u u_ss_t
      simp only [Finset.mem_coe, Finset.mem_powerset] at t_in_link ⊢
      apply Finset.Subset.trans u_ss_t t_in_link)

notation "B(" X ", " s ")" => mBall X s

instance Ball.fintype (X : SimplicialComplex α) [Fintype X.simplices] (s : Finset α)
    (s_in_X : s ∈ X.simplices) : Fintype (mBall X s s_in_X).simplices :=
  by
  simp only [mBall, SimplicialComplex.simplices]
  apply FinsetCoe.fintype

-- The cone of a complex.
@[simp]
def cone (X : SimplicialComplex α) (x : α) (x_nin_X : x ∉ vertices X) : SimplicialComplex (α × ℕ) :=
  negOneBall x x_nin_X ⋆ X

notation "Cone(" X ", " x ")" => cone X x

instance cone.fintype (X : SimplicialComplex α) [Fintype X.simplices] (x : α)
    (x_nin_X : x ∉ vertices X) : Fintype (Cone(X, x) x_nin_X).simplices :=
  by
  simp only [cone]
  apply simplicialJoin.fintype

def coneIsoMap (y : β) (f : α → β) : α × ℕ → β × ℕ := fun x : α × ℕ =>
  if x.snd = 0 then (y, 0) else (f x.fst, x.snd)

theorem cone_iso_simplicial (X : SimplicialComplex α) (Y : SimplicialComplex β) (x : α) (y : β)
    (x_nin_X : x ∉ vertices X) (y_nin_Y : y ∉ vertices Y) (f : SimplicialMap X Y) :
    IsSimplicialMap (Cone(X, x) x_nin_X) (Cone(Y, y) y_nin_Y) (coneIsoMap y f.map) :=
  by
  simp only [IsSimplicialMap, cone, negOneBall, simplicialJoin_mem]
  intro u u_in_X_cone
  choose s s_in_ball t t_in_X u_eq_st using u_in_X_cone
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at s_in_ball
  cases' s_in_ball with s_eq_x s_empty
  -- s = {x} case.
  use{y};
  constructor
  rw [Set.mem_insert_iff]
  left; rfl
  use Finset.image f.map t; constructor
  apply f.is_simplicial
  assumption
  simp only [u_eq_st, s_eq_x, simplexDisjointUnion, Finset.image_union, coneIsoMap, Finset.ext_iff]
  intro v
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_singleton]
  constructor
  · intro v_in_img
    cases' v_in_img with v_in_lhs v_in_rhs
    choose w w_in_lhs w_eq_v using v_in_lhs
    choose w_eq_x w_zero using w_in_lhs
    revert w_eq_v
    split_ifs
    intro y_eq_v
    simp only [Prod.ext_iff] at y_eq_v
    choose y_eq_v v_zero using y_eq_v
    rw [@comm _ Eq] at y_eq_v v_zero
    left; constructor <;> assumption
    choose w w_in_rhs w_eq_v using v_in_rhs
    choose w_in_t w_one using w_in_rhs
    revert w_eq_v
    split_ifs
    have contra : w.snd ≠ 0 := by omega
    contradiction
    intro w_eq_v
    simp only [Prod.ext_iff] at w_eq_v
    choose w_eq_v v_one using w_eq_v
    rw [w_one, @comm _ Eq] at v_one
    right; use w.fst; constructor <;> assumption
    assumption
  · intro v_in_union
    cases' v_in_union with v_in_lhs v_in_rhs
    choose v_eq_y v_zero using v_in_lhs
    left; use(x, 0); constructor
    simp only [Prod.fst, Prod.snd]
    constructor <;> rfl
    simp only [eq_self_iff_true, if_true, Prod.ext_iff]
    rw [@comm _ Eq] at v_eq_y v_zero
    constructor <;> assumption
    choose w_eq_v v_one using v_in_rhs
    choose w w_in_t w_eq_v using w_eq_v
    right; use(w, 1); constructor
    simp only [Prod.fst, Prod.snd]
    constructor; assumption; rfl
    simp only [Nat.one_ne_zero, if_false, Prod.ext_iff]
    rw [@comm _ Eq] at v_one
    constructor <;> assumption
  -- s = ∅ case.
  use∅;
  constructor; apply simplicialComplex_empty_simplex
  use Finset.image f.map t; constructor
  apply f.is_simplicial
  assumption
  simp only [u_eq_st, s_empty, simplexDisjointUnion, Finset.image_union, coneIsoMap, Finset.ext_iff]
  intro v
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_singleton]
  constructor
  · intro v_in_img
    cases' v_in_img with v_empty v_in_t
    choose w contra w_eq_v using v_empty
    choose contra w_zero using contra
    have H : w.fst ∉ ∅ := by apply Set.not_mem_empty
    contradiction
    choose w w_in_t w_eq_v using v_in_t
    choose w_in_t w_one using w_in_t
    revert w_eq_v
    split_ifs
    have contra : w.snd ≠ 0 := by omega
    contradiction
    intro w_eq_v
    simp only [Prod.ext_iff] at w_eq_v
    choose w_eq_v v_one using w_eq_v
    rw [w_one, @comm _ Eq] at v_one
    right; use w.fst; constructor <;> assumption
    assumption
  · intro v_in_union
    cases' v_in_union with contra v_in_t
    choose contra v_zero using contra
    have H : v.fst ∉ ∅ := by apply Set.not_mem_empty
    contradiction
    choose w_eq_v v_one using v_in_t
    choose w w_in_t w_eq_v using w_eq_v
    right; use(w, 1); constructor
    simp only [Prod.fst, Prod.snd]
    constructor; assumption; rfl
    simp only [Nat.one_ne_zero, if_false, Prod.ext_iff]
    rw [@comm _ Eq] at v_one
    constructor <;> assumption

theorem cone_iso (X : SimplicialComplex α) (Y : SimplicialComplex β) (x : α) (y : β)
    (x_nin_X : x ∉ vertices X) (y_nin_Y : y ∉ vertices Y) :
    X ≅ Y → Cone(X, x) x_nin_X ≅ Cone(Y, y) y_nin_Y :=
  by
  intro X_iso_Y
  unfold IsSimpliciallyIso at X_iso_Y ⊢
  choose f f_iso using X_iso_Y
  unfold IsSimplicialIso at f_iso ⊢
  choose g gf_inv using f_iso
  let f_cone : SimplicialMap (Cone(X, x) x_nin_X) (Cone(Y, y) y_nin_Y) :=
    SimplicialMap.mk (coneIsoMap y f.map) (cone_iso_simplicial X Y x y x_nin_X y_nin_Y f)
  let g_cone : SimplicialMap (Cone(Y, y) y_nin_Y) (Cone(X, x) x_nin_X) :=
    SimplicialMap.mk (coneIsoMap x g.map) (cone_iso_simplicial Y X y x y_nin_Y x_nin_X g)
  use f_cone; use g_cone
  unfold IsInverseSimplicialIso at gf_inv ⊢
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def] at gf_inv ⊢
  choose gf_id fg_id using gf_inv
  constructor
  · intro z z_in_X_cone
    rw [vertex_iff_in_simplex] at z_in_X_cone
    choose u u_in_cone z_in_u using z_in_X_cone
    simp only [cone, negOneBall, simplicialJoin] at u_in_cone
    simp only [Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff] at u_in_cone
    choose s s_in_ball t t_in_x st_eq_u using u_in_cone
    rw [← st_eq_u, simplex_disjoint_mem] at z_in_u
    cases' z_in_u with z_in_ball z_in_t
    cases' s_in_ball with s_eq_x contra
    rw [s_eq_x, Finset.mem_singleton] at z_in_ball
    choose z_eq_x z_zero using z_in_ball
    simp only [coneIsoMap, Prod.ext_iff, z_zero, eq_self_iff_true, if_true]
    constructor; symm; assumption
    trivial
    rw [contra] at z_in_ball
    choose contra z_zero using z_in_ball
    have H : z.fst ∉ ∅ := by apply Set.not_mem_empty
    contradiction
    choose z_in_t z_one using z_in_t
    have z_in_X : z.fst ∈ vertices X :=
      by
      rw [vertex_iff_in_simplex]
      use t; constructor <;> assumption
    specialize gf_id z_in_X
    simp only [coneIsoMap, z_one, Nat.one_ne_zero, if_false, Prod.ext_iff]
    constructor; assumption; rfl
  · intro z z_in_Y_cone
    rw [vertex_iff_in_simplex] at z_in_Y_cone
    choose u u_in_cone z_in_u using z_in_Y_cone
    simp only [cone, negOneBall, simplicialJoin] at u_in_cone
    simp only [Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff] at u_in_cone
    choose s s_in_ball t t_in_x st_eq_u using u_in_cone
    rw [← st_eq_u, simplex_disjoint_mem] at z_in_u
    cases' z_in_u with z_in_ball z_in_t
    cases' s_in_ball with s_eq_x contra
    rw [s_eq_x, Finset.mem_singleton] at z_in_ball
    choose z_eq_x z_zero using z_in_ball
    simp only [coneIsoMap, Prod.ext_iff, z_zero, eq_self_iff_true, if_true]
    constructor; symm; assumption
    trivial
    rw [contra] at z_in_ball
    choose contra z_zero using z_in_ball
    have H : z.fst ∉ ∅ := by apply Set.not_mem_empty
    contradiction
    choose z_in_t z_one using z_in_t
    have z_in_Y : z.fst ∈ vertices Y :=
      by
      rw [vertex_iff_in_simplex]
      use t; constructor <;> assumption
    specialize fg_id z_in_Y
    simp only [coneIsoMap, z_one, Nat.one_ne_zero, if_false, Prod.ext_iff]
    constructor; assumption; rfl

theorem dim_of_cone (X : SimplicialComplex α) [Fintype X.simplices] (x : α)
    (x_nin_X : x ∉ vertices X) : dimOfComplex (cone X x x_nin_X) = dimOfComplex X + 1 :=
  by
  dsimp only [cone]
  rw [dim_of_join, dim_of_negOneBall]
  simp only [zero_add]

/-
# Subcomplexes Under Simplicial Join
-/
-- Distributive properties of join over certain subcomplexes.
-- Lemma 2.2 (1), p.7
theorem join_distl_link (X Y : SimplicialComplex α) (s : Finset α) (s_in_X : s ∈ X.simplices) :
    Y ⋆ Lk(X, s) s_in_X ≅ Lk(X ⋆ Y, s ⊔ₛ ∅) (by apply simplicialJoin_incl_left; assumption) :=
  by
  apply simplicial_iso_trans (Y ⋆ Lk(X, s) s_in_X) (Lk(X, s) s_in_X ⋆ Y)
  apply simplicialJoin_comm
  apply simplicial_iso_preserves_equiv
  dsimp only [simplicialJoin, link, SimplicialComplex.simplices]
  rw [Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf]
  constructor
  · intro H
    rcases H with ⟨t, Ht, u, Hu, Hx⟩
    rw [Set.mem_sep_iff] at Ht
    rcases Ht with ⟨Ht, Hst, Hst_empty⟩
    constructor
    use t; constructor; tauto
    use u; tauto
    constructor
    subst Hx
    rw [simplex_disjoint_distr_union]
    use s ∪ t; constructor; tauto
    use u; constructor; tauto
    simp
    subst Hx
    rw [simplex_disjoint_distr_inter]
    simp; tauto
  · intro H
    rcases H with ⟨Hx, Hx_union, Hsx_empty⟩
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩
    rcases Hx_union with ⟨t', Ht', u', Hu', Hx_union⟩
    subst Hx
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at Hx_union
    cases' Hx_union with Ht' Hu'
    simp at Hu'; subst Hu'
    rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at Hsx_empty
    cases' Hsx_empty with Hst_empty Hu'_trivial
    use t; constructor
    rw [Set.mem_sep_iff]
    constructor <;> try subst Ht' <;> tauto
    use u'; tauto

-- Lemma 2.2 (2), p.7
theorem join_distl_star {a : Type _} [DecidableEq a] (X Y : SimplicialComplex a) (s : Finset a)
    (s_in_X : s ∈ X.simplices) :
    Y ⋆ St(X, s) s_in_X ≅ St(X ⋆ Y, s ⊔ₛ ∅) (by apply simplicialJoin_incl_left; assumption) :=
  by
  apply simplicial_iso_trans (Y ⋆ St(X, s) s_in_X) (St(X, s) s_in_X ⋆ Y)
  apply simplicialJoin_comm
  apply simplicial_iso_preserves_equiv
  dsimp only [simplicialJoin, star, SimplicialComplex.simplices]
  rw [Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf]
  constructor
  · intro H
    rcases H with ⟨t, Ht, u, Hu, Hx⟩
    rw [Set.mem_sep_iff] at Ht
    cases' Ht with Ht Hst
    constructor
    use t; constructor; tauto
    use u; tauto
    subst Hx
    use s ∪ t; constructor; tauto
    use u
    constructor <;> try rw [simplex_disjoint_distr_union]; simp <;> tauto
  · intro H
    cases' H with Hx Hx_union
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩
    rcases Hx_union with ⟨t', Ht', u', Hu', Hx_union⟩
    subst Hx
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at Hx_union
    cases' Hx_union with Ht' Hu'
    simp at Hu'
    subst Ht'; subst Hu'
    use t; constructor
    rw [Set.mem_sep_iff] <;> try simp <;> tauto
    use u'; constructor <;> tauto

theorem join_distr_starComplement_simplices (X Y : SimplicialComplex α) (s : Finset α) [Nonempty s]
    (s_in_X : s ∈ X.simplices) :
    (starComplement X s s_in_X ⋆ Y).simplices =
      (starComplement (X ⋆ Y) (s ⊔ₛ ∅) (by apply simplicialJoin_incl_left; assumption)).simplices :=
  by
  dsimp only [simplicialJoin, starComplement, SimplicialComplex.simplices]
  rw [Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf]
  constructor
  · intro H
    rcases H with ⟨t, Ht, u, Hu, Hx⟩
    rw [Set.mem_sep_iff] at Ht
    cases' Ht with Ht Hs_not_sset_t
    constructor
    use t; constructor; tauto
    use u; tauto
    subst Hx
    rw [simplex_disjoint_subset_unique]
    simp; tauto
  · intro H
    cases' H with Hx Hs_not_sset_x
    rcases Hx with ⟨t, Ht, u, Hu, Hx⟩
    subst Hx
    rw [simplex_disjoint_subset_unique] at Hs_not_sset_x
    simp at Hs_not_sset_x
    use t; constructor
    rw [Set.mem_sep_iff]; tauto
    use u; constructor <;> tauto

theorem join_distr_starComplement (X Y : SimplicialComplex α) (s : Finset α) [Nonempty s]
    (s_in_X : s ∈ X.simplices) :
    starComplement X s s_in_X ⋆ Y ≅
      starComplement (X ⋆ Y) (s ⊔ₛ ∅) (by apply simplicialJoin_incl_left; assumption) :=
  by
  apply simplicial_iso_preserves_equiv
  apply join_distr_starComplement_simplices

-- Lemma 2.2 (3), p.7
theorem join_distl_starComplement (X Y : SimplicialComplex α) (s : Finset α) [Nonempty s]
    (s_in_X : s ∈ X.simplices) :
    Y ⋆ starComplement X s s_in_X ≅
      starComplement (X ⋆ Y) (s ⊔ₛ ∅) (by apply simplicialJoin_incl_left; assumption) :=
  by
  apply simplicial_iso_trans (Y ⋆ starComplement X s s_in_X) (starComplement X s s_in_X ⋆ Y)
  apply simplicialJoin_comm
  apply join_distr_starComplement

-- Lemma 2.3, p.8
theorem join_fact_link (X Y : SimplicialComplex α) (s t : Finset α) (s_in_X : s ∈ X.simplices)
    (t_in_Y : t ∈ Y.simplices) :
    Lk(X ⋆ Y, s ⊔ₛ t) (by rw [simplicialJoin_sep]; tauto) ≅ Lk(X, s) s_in_X ⋆ Lk(Y, t) t_in_Y :=
  by
  apply simplicial_iso_preserves_equiv
  dsimp only [link, simplicialJoin, SimplicialComplex.simplices]
  rw [Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf]
  constructor
  · intro H
    cases H
    rcases H_left with ⟨s', Hs', t', Ht', Hx⟩
    cases' H_right with H_left H_inter
    rcases H_left with ⟨s'', Hs'', t'', Ht'', H_union⟩
    subst Hx
    rw [simplex_disjoint_distr_inter, simplex_disjoint_empty] at H_inter
    rw [simplex_disjoint_distr_union, simplex_disjoint_eq_unique] at H_union
    cases' H_union with H_s_union H_t_union
    subst H_s_union; subst H_t_union
    use s'; constructor
    rw [Set.mem_sep_iff]
    constructor <;> tauto
    use t'
    rw [Set.mem_sep_iff]
    constructor <;> tauto
  · intro H
    rcases H with ⟨s', Hs', t', Ht', Hx⟩
    rw [Set.mem_sep_iff] at Hs' Ht'
    constructor
    · use s'; constructor; tauto
      use t'; tauto
    · use s ∪ s'; constructor; tauto
      use t ∪ t'; constructor; tauto
      subst Hx
      rw [simplex_disjoint_distr_union]
      subst Hx
      rw [simplex_disjoint_distr_inter, simplex_disjoint_empty]
      tauto

-- Lemma 2.4 (1), p.8
theorem join_distr_union_left (X Y Z : SimplicialComplex α) : X ⋆ (Y ∪ Z) ≅ X ⋆ Y ∪ X ⋆ Z :=
  by
  apply simplicial_iso_preserves_equiv
  dsimp only [simplicialJoin, simplicialUnion, SimplicialComplex.simplices]
  rw [Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf]
  constructor
  · intro H
    rcases H with ⟨s, Hs, t, Ht, Hx⟩
    rw [← Set.setOf_or, Set.mem_setOf]
    rw [Set.mem_union] at Ht
    destruct Ht
    intro Hy
    left
    use s; constructor; tauto
    use t; tauto
    intro Hz
    right
    use s; constructor; tauto
    use t; tauto
  · intro H
    rw [← Set.setOf_or, Set.mem_setOf] at H
    destruct H
    intro Hy
    rcases Hy with ⟨s, Hs, t, Ht, Hx⟩
    use s; constructor; tauto
    use t; rw [Set.mem_union]; tauto
    intro Hz
    rcases Hz with ⟨s, Hs, t, Ht, Hx⟩
    use s; constructor; tauto
    use t; rw [Set.mem_union]; tauto

-- Lemma 2.4 (2), p.8
theorem join_distr_inter_left (X Y Z : SimplicialComplex α) : X ⋆ (Y ∩ Z) ≅ X ⋆ Y ∩ (X ⋆ Z) :=
  by
  apply simplicial_iso_preserves_equiv
  dsimp only [simplicialJoin, simplicialInter, SimplicialComplex.simplices]
  rw [Set.ext_iff]
  intro x
  repeat' rw [Set.mem_setOf]
  constructor
  · intro H
    rcases H with ⟨s, Hs, t, Ht, Hx⟩
    rw [← Set.setOf_and, Set.mem_setOf]
    rw [Set.mem_inter_iff] at Ht
    cases' Ht with Hy Hz
    constructor
    use s; constructor; tauto
    use t; tauto
    use s; constructor; tauto
    use t; tauto
  · intro H
    rw [← Set.setOf_and, Set.mem_setOf] at H
    cases' H with Hy Hz
    rcases Hy with ⟨sy, Hsy, ty, Hty, Hxy⟩
    rcases Hz with ⟨sz, Hsz, tz, Htz, Hxz⟩
    subst Hxy
    rw [simplex_disjoint_eq_unique] at Hxz
    cases' Hxz with Hsz Htz
    subst Hsz; subst Htz
    use sz; constructor; tauto
    use tz; rw [Set.mem_inter_iff]; tauto

/-
# Properties of Links
-/
theorem link_ident (X : SimplicialComplex α) :
    (Lk(X, ∅) (by apply simplicialComplex_empty_simplex)).simplices = X.simplices :=
  by
  simp only [link, Set.ext_iff, Set.mem_sep_iff]
  simp only [Finset.empty_union, Finset.empty_inter]
  simp only [eq_self_iff_true, and_true_iff, and_self_iff, iff_self_iff, forall_const]

theorem link_ident_iso (X : SimplicialComplex α) :
    Lk(X, ∅) (by apply simplicialComplex_empty_simplex) ≅ X :=
  by
  apply simplicial_iso_preserves_equiv
  apply link_ident

theorem link_disjoint_base (X : SimplicialComplex α) (s t : Finset α) (s_in_X : s ∈ X.simplices) :
    t ∈ (Lk(X, s) s_in_X).simplices → Disjoint s t :=
  by
  intro t_in_link
  simp only [link, Set.mem_sep_iff] at t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  rw [Finset.disjoint_iff_inter_eq_empty]
  assumption

theorem face_in_link_of_complement (X : SimplicialComplex α) (s t : Finset α)
    (s_in_X : s ∈ X.simplices) (t_sset_s : t ⊆ s) :
    s \ t ∈ (Lk(X, t) (by apply X.subset_closed s <;> assumption)).simplices :=
  by
  simp only [link, Set.mem_sep_iff]
  constructor
  apply X.subset_closed s
  assumption
  apply Finset.sdiff_subset
  constructor
  rw [Finset.union_comm, Finset.sdiff_union_self_eq_union, finset.union_eq_left_iff_subset.mpr] <;>
    assumption
  apply Finset.inter_sdiff_self

-- Lemma 3.5, p.14
theorem link_of_face_complement (X : SimplicialComplex α) (s t : Finset α)
    (s_in_X : s ∈ X.simplices) (t_sset_s : t ⊆ s) :
    Lk(X, s) s_in_X ≅
      Lk(Lk(X, t) (by apply X.subset_closed s <;> assumption), s \ t)
        (by apply face_in_link_of_complement) :=
  by
  by_cases s = t
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
    apply X.subset_closed (s ∪ u)
    assumption
    apply Finset.union_subset_union
    assumption
    apply Finset.Subset.refl
    rw [← su_empty]
    apply Finset.inter_congr_right
    rw [su_empty]
    apply Finset.empty_subset
    apply @Finset.Subset.trans _ (t ∩ u) t s
    apply Finset.inter_subset_left
    assumption
    constructor; constructor
    apply X.subset_closed (s ∪ u)
    assumption
    apply Finset.union_subset_union
    apply Finset.sdiff_subset
    apply Finset.Subset.refl
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

theorem barycenter_disjoint_boundary (X : SimplicialComplex α) (s : Finset α) (x : α)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    Disjoint (vertices (simplex {x})) (vertices (∂s)) :=
  by
  rw [Set.disjoint_left]
  intro y y_in_barycenter
  apply @Set.not_mem_subset _ _ _ (vertices X)
  rw [Set.subset_def]
  intro z
  apply simplexBoundary_subcomplex_vert X s z s_in_X
  dsimp only [vertices, simplex, SimplicialComplex.simplices] at y_in_barycenter
  simp only [Set.mem_iUnion] at y_in_barycenter
  choose t Ht y_in_t using y_in_barycenter
  simp only [Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at Ht
  cases' Ht with t_empty t_ne
  rw [← Finset.coe_eq_empty, Set.eq_empty_iff_forall_not_mem] at t_empty
  specialize t_empty y
  contradiction
  rw [Finset.eq_singleton_iff_unique_mem] at t_ne
  cases' t_ne with x_in_t y_eq_x
  specialize y_eq_x y
  rw [Finset.mem_coe] at y_in_t
  specialize y_eq_x y_in_t
  rw [y_eq_x]
  apply x_nin_X

theorem barycenter_join_boundary_disjoint_link (X : SimplicialComplex α) (s : Finset α) (x : α)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    Disjoint (vertices (π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X)[simplex {x} ⋆ ∂s]))
      (vertices (Lk(X, s) s_in_X)) :=
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

theorem boundary_disjoint_link (X : SimplicialComplex α) (s : Finset α) (s_in_X : s ∈ X.simplices) :
    Disjoint (vertices (Lk(X, s) s_in_X)) (vertices (∂s)) :=
  by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_not_mem]
  intro x
  simp only [Set.mem_inter_iff, not_and, vertex_iff_in_simplex, not_exists]
  intro t_in_link u u_in_bd
  simp only [link, Set.mem_sep_iff] at t_in_link
  choose t t_in_link x_in_t using t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  simp only [simplexBoundary, Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset] at
    u_in_bd
  cases' u_in_bd with u_in_bd u_empty
  choose u_ss_s u_ne_s using u_in_bd
  have ut_disj : u ∩ t = ∅ := by
    rw [← Finset.subset_empty]
    apply @Finset.Subset.trans _ _ (s ∩ t)
    apply Finset.inter_subset_inter_right u_ss_s
    rw [Finset.subset_empty]
    assumption
  rw [Finset.eq_empty_iff_forall_not_mem] at ut_disj
  specialize ut_disj x
  rw [Finset.mem_inter, not_and] at ut_disj
  by_cases x_in_u : x ∈ u
  specialize ut_disj x_in_u
  contradiction
  assumption
  rw [Set.mem_singleton_iff] at u_empty
  rw [u_empty]
  apply Finset.not_mem_empty

theorem barycenter_disjoint_link (X : SimplicialComplex α) (s : Finset α) (x : α)
    (s_in_X : s ∈ X.simplices) (x_nin_X : x ∉ vertices X) :
    Disjoint (vertices (Lk(X, s) s_in_X)) (vertices (simplex {x})) :=
  by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_not_mem]
  intro y
  simp only [Set.mem_inter_iff, not_and, vertex_iff_in_simplex, not_exists]
  intro t_in_link u u_in_barycenter
  simp only [link, Set.mem_sep_iff] at t_in_link
  choose t t_in_link y_in_t using t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at
    u_in_barycenter
  cases' u_in_barycenter with u_empty u_eq_x
  rw [u_empty]
  apply Finset.not_mem_empty
  have ut_disj : u ∩ t = ∅ :=
    by
    rw [← Finset.coe_inj, Finset.coe_empty, ← Set.subset_empty_iff, Finset.coe_inter]
    apply @Set.Subset.trans _ _ ({x} ∩ vertices X)
    apply Set.inter_subset_inter
    simp only [u_eq_x, Finset.coe_singleton]
    apply simplex_subset_vertices
    assumption
    rw [Set.subset_empty_iff, Set.eq_empty_iff_forall_not_mem]
    intro y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, not_and]
    intro y_eq_x
    subst y_eq_x
    assumption
  simp only [Finset.eq_empty_iff_forall_not_mem, Finset.mem_inter, not_and] at ut_disj
  specialize ut_disj y
  by_cases y_in_u : y ∈ u
  specialize ut_disj y_in_u
  contradiction
  assumption

theorem disjoint_complexes_disjoint_simplices (X Y : SimplicialComplex α) (s t : Finset α)
    (s_in_X : s ∈ X.simplices) (t_in_Y : t ∈ Y.simplices)
    (XY_disj : Disjoint (vertices X) (vertices Y)) : Disjoint s t :=
  by
  rw [← Finset.disjoint_coe]
  apply @Set.disjoint_of_subset _ _ (vertices X) _ (vertices Y)
  apply simplex_subset_vertices
  assumption
  apply simplex_subset_vertices
  assumption
  assumption
