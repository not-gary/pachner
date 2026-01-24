import Pachner.Maps.SimplicialIsomorphism

variable {E F : Type _}
variable [DecidableEq E] [DecidableEq F]

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
