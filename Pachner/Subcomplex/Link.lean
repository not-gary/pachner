import Pachner.Maps.SimplicialCoercion
import Pachner.Subcomplex.Intersection

variable
  {E F : Type _}
  [DecidableEq E] [DecidableEq F]
  {X Y : AbstractSimplicialComplex E} {s t : Finset E} {x : E}

@[simp]
def Link
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
  : AbstractSimplicialComplex E :=
    AbstractSimplicialComplex.mk
    ({t ∈ X.faces | s ∪ t ∈ X.faces ∧ s ∩ t = ∅})
    (by simp only [Set.mem_setOf, not_and_or, X.empty_notMem, not_false_eq_true, true_or])
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

notation "Lk(" X ", " s ")" => Link X s

instance Link.fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (s : Finset E)
  : Fintype (Link X s).faces :=
by
  simp only [Link, Set.sep_and]
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

theorem link_simplicialCoe_image_left
    {φ : SimplicialCoe X F}
    (s_in_X : s ∈ X.faces)
  : Lk(φ.coe ''ˢ X, Finset.image φ.coe s) ⊆ (φ.coe ''ˢ Lk(X, s)) :=
by
  simp only [Link, SimplicialImage, AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def]
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
      rw [vertex_iff_in_face]
      use v; constructor <;> assumption
    rw [← Set.InjOn.mem_image_iff φ.Injective] at a_in_v ⊢
    specialize φv_ss_φsu a_in_v
    assumption
    rw [Finset.coe_union]
    apply Set.union_subset <;>
      · apply face_subset_vertices
        assumption
    assumption
    apply face_subset_vertices
    assumption
    assumption
    intro a_in_su
    have a_in_X : a ∈ X.vertices :=
      by
      rw [Finset.coe_union, Set.mem_union] at a_in_su
      cases' a_in_su with a_in_s a_in_u
      rw [vertex_iff_in_face]
      use s; constructor <;> assumption
      rw [vertex_iff_in_face]
      use u; constructor <;> assumption
    rw [← Set.InjOn.mem_image_iff φ.Injective] at a_in_su ⊢
    specialize φsu_ss_φv a_in_su
    assumption
    apply face_subset_vertices
    assumption
    assumption
    rw [Finset.coe_union]
    apply Set.union_subset <;>
      · apply face_subset_vertices
        assumption
    assumption
  rw [← v_su]
  assumption
  simp only [← φu_t, ← Finset.coe_inj, Finset.coe_image, Finset.coe_inter] at st_disj
  rw [← Set.InjOn.image_inter, ← Finset.coe_inter, ← Finset.coe_image, Finset.coe_inj,
    Finset.image_eq_empty] at st_disj
  assumption
  apply φ.Injective
  apply face_subset_vertices
  assumption
  apply face_subset_vertices
  assumption
  assumption

theorem link_simplicialCoe_image_right
    {φ : SimplicialCoe X F}
    (s_in_X : s ∈ X.faces)
  : (φ.coe ''ˢ Lk(X, s)) ⊆ Lk(φ.coe ''ˢ X, Finset.image φ.coe s) :=
by
  simp only [Link, SimplicialImage, AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def]
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
  apply face_subset_vertices
  assumption
  apply face_subset_vertices
  assumption

theorem link_coe_image
    (s_in_X : s ∈ X.faces)
    (φ : SimplicialCoe X F)
  : Lk(φ.coe ''ˢ X, Finset.image φ.coe s) = (φ.coe ''ˢ Lk(X, s)) :=
by
  rw [AbstractSimplicialComplex.ext_iff, Set.Subset.antisymm_iff]
  exact ⟨link_simplicialCoe_image_left s_in_X, link_simplicialCoe_image_right s_in_X⟩

theorem link_subcomplex : Lk(X, s) ⊆ X := by
  intro t t_in_link
  simp only [Link, Set.mem_sep_iff] at t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  assumption

theorem link_notMem_vertices : x ∉ X.vertices → x ∉ Lk(X, s).vertices := by
  contrapose
  simp only [Classical.not_not]
  apply isSubcomplex_vertices
  apply link_subcomplex

theorem link_simplicialIso
    {Y : AbstractSimplicialComplex F}
    {t : Finset F}
    (s_in_X : s ∈ X.faces)
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : Finset.image f.map s = t → Lk(X, s) ≅ Lk(Y, t) :=
by
  intro fs_eq_t
  unfold IsSimpliciallyIso
  have f_simp : IsSimplicialMap Lk(X, s) Lk(Y, t) f.map :=
  by
    simp only [IsSimplicialMap, Link, Set.mem_sep_iff]
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
    apply simplicialIso_injective_faces f f_iso (s ∪ u)
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
  have g_simp : IsSimplicialMap Lk(Y, t) Lk(X, s) g.map :=
  by
    simp only [IsSimplicialMap, Link, Set.mem_sep_iff]
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
    apply simplicialIso_injective_faces g
    apply simplicialIso_inverse_is_simplicialIso f <;> assumption
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
    have x_in_X : x ∈ X.vertices := isSubcomplex_vertices link_subcomplex x x_in_X_link
    specialize gf_id x_in_X
    assumption
  · intro x x_in_Y_link
    have x_in_Y : x ∈ Y.vertices := isSubcomplex_vertices link_subcomplex x x_in_Y_link
    specialize fg_id x_in_Y
    assumption

theorem link_simplicialInter : Lk(X ∩ Y, s) = Lk(X, s) ∩ Lk(Y, s) := by
  simp only [AbstractSimplicialComplex.ext_iff, Link, AbstractSimplicialComplex.instHasInter,
    SimplicialInter, Set.ext_iff, Set.mem_inter_iff, Set.mem_sep_iff, and_assoc]
  intro t
  constructor
  · intro t_in_link
    choose t_in_X t_in_Y st_in_X st_in_Y st_disj using t_in_link
    exact ⟨t_in_X, st_in_X, st_disj, t_in_Y, st_in_Y, st_disj⟩
  · intro t_in_inter
    choose t_in_X st_in_X st_disj t_in_Y st_in_Y _ using t_in_inter
    exact ⟨t_in_X, t_in_Y, st_in_X, st_in_Y, st_disj⟩

theorem link_simplicialUnion_left
    (s_in_X : s ∈ X.faces)
    (s_nin_Y : s ∉ Y.faces)
  : Lk(X ∪ Y, s) = Lk(X, s) :=
by
  simp only [AbstractSimplicialComplex.ext_iff, Link, SimplicialUnion, Set.ext_iff,
    Set.mem_sep_iff, Set.mem_union]
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
      exact face_nonempty s_in_X
    contradiction
    constructor
    apply X.down_closed st_in_X
    apply Finset.subset_union_right
    exact face_nonempty contra
    constructor <;> assumption
    have s_in_Y : s ∈ Y.faces := by
      apply Y.down_closed contra
      apply Finset.subset_union_left
      exact face_nonempty s_in_X
    contradiction
  · intro t_in_X
    choose t_in_X st_in_X st_disj using t_in_X
    constructor; left; assumption
    constructor; left; assumption
    assumption

theorem link_simplicialUnion_right
    (s_nin_X : s ∉ X.faces)
    (s_in_Y : s ∈ Y.faces)
  : Lk(X ∪ Y, s) = Lk(Y, s) :=
by
  rw [simplicialUnion_comm]
  exact link_simplicialUnion_left s_in_Y s_nin_X

theorem link_simplicialUnion : Lk(X ∪ Y, s) = Lk(X, s) ∪ Lk(Y, s) := by
  simp only [AbstractSimplicialComplex.ext_iff, Link, SimplicialUnion, Set.ext_iff,
    Set.mem_sep_iff, Set.mem_union]
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
    exact face_nonempty t_in_X
    constructor <;> assumption
    left
    constructor
    apply X.down_closed st_in_X
    apply Finset.subset_union_right
    exact face_nonempty t_in_Y
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

theorem link_empty_eq_self : Lk(X, ∅) = X := by
  simp only [AbstractSimplicialComplex.ext_iff, Link, Set.ext_iff, Set.mem_sep_iff,
    Finset.empty_union, Finset.empty_inter, and_true]
  simp only [and_self, forall_const]

theorem link_empty_eq_self_iso : Lk(X, ∅) ≅ X := by rw [link_empty_eq_self]

theorem link_disjoint_base : t ∈ Lk(X, s) → Disjoint s t := by
  intro t_in_link
  simp only [Link, Set.mem_sep_iff] at t_in_link
  choose t_in_X st_in_X st_disj using t_in_link
  rw [Finset.disjoint_iff_inter_eq_empty]
  assumption

theorem face_in_link_of_complement
    (s_in_X : s ∈ X.faces)
    (t_sset_s : t ⊆ s)
    (t_ne_s : t ≠ s)
  : s \ t ∈ Lk(X, t) :=
by
  simp only [Link, Set.mem_union, Set.mem_sep_iff]
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
theorem link_of_face_complement (t_sset_s : t ⊆ s) : Lk(X, s) = Lk(Lk(X, t), s \ t) := by
  by_cases h : s = t
  simp only [h, Finset.sdiff_self]
  rw [link_empty_eq_self]
  simp only [AbstractSimplicialComplex.ext_iff, Link, Set.ext_iff]
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
    simp only [X.empty_notMem] at u_in_X
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
    simp only [X.empty_notMem] at u_in_X
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
