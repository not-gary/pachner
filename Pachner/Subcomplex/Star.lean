import Pachner.Maps.SimplicialIsomorphism

variable
  {E F : Type _}
  [DecidableEq E] [DecidableEq F]
  {X : AbstractSimplicialComplex E} {s : Finset E}
  {Y : AbstractSimplicialComplex F} {t : Finset F}

-- TODO: should this include s ∈ X.faces as assumption?
@[simp]
def StarNeighborhood -- Note: the name "Star" is already taken by a certain Typeclass in mathlib
    (X : AbstractSimplicialComplex E)
    (s : Finset E)
  : AbstractSimplicialComplex E :=
    AbstractSimplicialComplex.mk ({t ∈ X.faces | s ∪ t ∈ X.faces})
    (by simp only [Set.mem_setOf_eq, Finset.union_empty, X.empty_notMem, not_and, false_implies])
    (by
      simp only [Set.mem_setOf_eq, ne_eq, and_imp]
      intro s_1 t s_1_in_X s_s_1_in_X t_ss_s1 t_nonempty
      constructor
      · apply X.down_closed s_1_in_X t_ss_s1 t_nonempty
      · apply X.down_closed s_s_1_in_X
        apply Finset.union_subset_union
        rfl
        assumption
        simp only [ne_eq, Finset.union_eq_empty, not_and]
        intro
        assumption)

notation "St(" X ", " s ")" => StarNeighborhood X s

instance StarNeighborhood.fintype
    (X : AbstractSimplicialComplex E)
    [Fintype X.faces]
    (s : Finset E)
  : Fintype (St(X, s)).faces :=
by
  unfold StarNeighborhood
  have H_dec : DecidablePred fun a : Finset E => s ∪ a ∈ X.faces :=
    by
    unfold DecidablePred
    intro a
    apply Set.decidableMemOfFintype
  apply Set.fintypeSep

theorem star_subcomplex : St(X, s) ⊆ X := by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def]
  intro t t_in_star
  simp only [StarNeighborhood, Set.mem_sep_iff] at t_in_star
  exact t_in_star.left

def star_simplicialIso' (s_in_X : s ∈ X.faces) (f : X ≅' Y) (fs_eq_t : Finset.image f.toFun.map s = t) : St(X, s) ≅' St(Y, t) where
  toFun := {
    map := f.toFun.map
    is_simplicial u u_in_star := (by
      choose u_in_X su_in_X using u_in_star
      constructor
      · exact f.toFun.is_simplicial u u_in_X
      · rw [← fs_eq_t, ← Finset.image_union]
        exact f.toFun.is_simplicial _ su_in_X) }
  invFun := {
    map := f.invFun.map
    is_simplicial u u_in_star := (by
      choose u_in_Y tu_in_Y using u_in_star
      constructor
      · exact f.invFun.is_simplicial u u_in_Y
      · rw [← f.face_mapsTo_face_inv s_in_X fs_eq_t, ← Finset.image_union]
        exact f.invFun.is_simplicial _ tu_in_Y) }
  left_inv x_in_star := f.left_inv (isSubcomplex_vertices star_subcomplex _ x_in_star)
  right_inv x_in_star := f.right_inv (isSubcomplex_vertices star_subcomplex _ x_in_star)

@[deprecated star_simplicialIso' (since := "")]
theorem star_simplicialIso
    (s_in_X : s ∈ X.faces)
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : Finset.image f.map s = t → St(X, s) ≅ St(Y, t) :=
by
  intro fs_eq_t
  unfold IsSimpliciallyIso
  have f_simp : IsSimplicialMap St(X, s) St(Y, t) f.map :=
  by
    simp only [IsSimplicialMap, StarNeighborhood, Set.mem_sep_iff]
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
  have g_simp : IsSimplicialMap St(Y, t) St(X, s) g.map :=
  by
    simp only [IsSimplicialMap, StarNeighborhood, Set.mem_sep_iff]
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
    have x_in_X : x ∈ X.vertices := isSubcomplex_vertices star_subcomplex x x_in_star
    specialize gf_id x_in_X
    assumption
  · intro x x_in_star
    have x_in_Y : x ∈ Y.vertices := isSubcomplex_vertices star_subcomplex x x_in_star
    specialize fg_id x_in_Y
    assumption
