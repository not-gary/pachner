import Pachner.Basic.Disjoint
import Pachner.Maps.SimplicialCoercion

variable
  {E F 𝕜 : Type _}
  [DecidableEq E] [DecidableEq F]
  [DecidableEq 𝕜] [Ring 𝕜] [Nontrivial 𝕜]
  {X Y Z W : AbstractSimplicialComplex E} {s t : Finset E} {x : E}

@[simp]
def SimplicialJoin (X Y : AbstractSimplicialComplex E) : AbstractSimplicialComplex (E × 𝕜) :=
  AbstractSimplicialComplex.mk
    ({(s ⊔ₛ t) | (s ∈ X.faces ∪ {∅}) (t ∈ Y.faces ∪ {∅})} \ {∅})
    (by
      rw [Set.mem_diff, not_and]
      intro h
      simp only [Set.mem_singleton_iff, not_true_eq_false, not_false_eq_true])
    (by
      intro s t s_in_XY t_sset_s t_ne
      rw [Set.mem_diff, Set.mem_setOf] at *
      choose s_in_XY s_ne using s_in_XY
      choose u Hu v Hv uv_eq_s using s_in_XY
      rw [← uv_eq_s, faceDisjoint_subset_sep] at t_sset_s
      choose z w t_eq_zw using t_sset_s
      choose t_eq_zw z_sset_u w_sset_v using t_eq_zw
      constructor
      use z; constructor

      rw [Set.mem_union] at ⊢ Hu
      by_cases z_empty : z = ∅
      right
      rw [Set.mem_singleton_iff]
      assumption

      cases' Hu with u_in_X u_empty
      left
      apply X.down_closed <;> assumption

      right
      rw [Set.mem_singleton_iff] at u_empty
      rw [u_empty, Finset.subset_empty] at z_sset_u
      contradiction

      use w; constructor
      rw [Set.mem_union] at ⊢ Hv
      by_cases w_empty : w = ∅
      right
      rw [Set.mem_singleton_iff]
      assumption

      cases' Hv with v_in_Y v_empty
      left
      apply Y.down_closed <;> assumption

      right
      rw [Set.mem_singleton_iff] at v_empty
      rw [v_empty, Finset.subset_empty] at w_sset_v
      contradiction

      symm; assumption
      rw [Set.mem_singleton_iff]
      assumption)

infixl:70 " ⋆ " => SimplicialJoin

theorem simplicialJoin_as_union
  : (X ⋆ Y).faces = ⋃ s ∈ (X.faces ∪ {∅}), ⋃ t ∈ (Y.faces ∪ {∅}), {(s ⊔ₛ t : Finset (E × 𝕜))} \ {∅} :=
by
  simp only [SimplicialJoin, Set.ext_iff, Set.mem_iUnion, Set.mem_setOf, Set.mem_singleton_iff]
  intro x
  constructor
  intro x_in_join
  rw [Set.mem_diff] at x_in_join
  choose x_in_join x_ne using x_in_join
  choose s s_in_X t t_in_Y st_eq_x using x_in_join
  use s; constructor
  use t; constructor
  rw [Set.mem_diff, Set.mem_singleton_iff]
  constructor
  symm; assumption
  assumption
  assumption
  assumption

  intro x_in_union
  choose s s_in_X t t_in_Y st_eq_x using x_in_union
  rw [Set.mem_diff] at ⊢ st_eq_x
  choose st_eq_x x_ne using st_eq_x
  constructor

  use s; constructor; assumption
  use t; constructor; assumption
  symm; assumption
  assumption

instance SimplicialJoin.fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (Y : AbstractSimplicialComplex E) [Fintype Y.faces]
  : Fintype (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).faces :=
by
  rw [simplicialJoin_as_union]
  apply Set.fintypeBiUnion
  intro s s_in_X
  apply Set.fintypeBiUnion
  intro t t_in_Y
  apply Set.fintypeDiff

theorem simplicialJoin_sep
  : (s ⊔ₛ t : Finset (E × 𝕜)) ∈ (X ⋆ Y).faces ↔ s ∈ X.faces ∪ {∅} ∧ t ∈ Y.faces ∪ {∅} ∧ (s ≠ ∅ ∨ t ≠ ∅) :=
by
  rw [SimplicialJoin, Set.mem_diff, Set.mem_setOf]
  constructor
  · intro st_in_XY
    choose st_in_XY st_ne using st_in_XY
    choose u Hu w Hw uw_eq_st using st_in_XY
    rw [faceDisjoint_eq_unique] at uw_eq_st
    cases' uw_eq_st with u_eq_s w_eq_t
    constructor
    rw [u_eq_s] at Hu
    assumption
    rw [w_eq_t] at Hw
    constructor
    assumption
    rw [Set.mem_singleton_iff, faceDisjoint_empty, not_and_or] at st_ne
    assumption
  · intro st_in_XY
    choose s_in_X t_in_Y st_ne using st_in_XY
    constructor
    use s; constructor; assumption
    use t
    rw [Set.mem_singleton_iff, faceDisjoint_empty, not_and_or]
    assumption

theorem simplicialJoin_mem
    {s : Finset (E × 𝕜)}
  : s ∈ (X ⋆ Y).faces ↔ ∃ t ∈ X.faces ∪ {∅}, ∃ u ∈ Y.faces ∪ {∅}, s = t ⊔ₛ u ∧ s ≠ ∅ :=
by
  rw [SimplicialJoin, Set.mem_diff, Set.mem_setOf]
  constructor
  · intro s_in_XY
    choose s_in_XY s_ne using s_in_XY
    choose t Ht u Hu s_eq_tu using s_in_XY
    use t; constructor; assumption
    use u; constructor; assumption
    constructor; symm; assumption
    rw [Set.mem_singleton_iff] at s_ne
    assumption
  · intro s_eq_tu
    choose t Ht u Hu s_eq_tu using s_eq_tu
    choose s_eq_tu s_ne using s_eq_tu
    constructor
    use t; constructor; assumption
    use u; constructor; assumption
    symm
    assumption
    rw [Set.mem_singleton_iff]
    assumption

theorem simplicialJoin_incl_left : s ∈ X.faces → (s ⊔ₛ ∅ : Finset (E × 𝕜)) ∈ (X ⋆ Y).faces := by
  intro s_in_X
  rw [simplicialJoin_sep]
  exact ⟨Set.mem_union_left _ s_in_X,
    Set.mem_union_right _ (Set.mem_singleton ∅),
    by left; exact face_nonempty s_in_X⟩

theorem simplicialJoin_incl_right : t ∈ Y.faces → (∅ ⊔ₛ t : Finset (E × 𝕜)) ∈ (X ⋆ Y).faces := by
  intro t_in_Y
  rw [simplicialJoin_sep]
  exact ⟨Set.mem_union_right _ (Set.mem_singleton ∅),
    Set.mem_union_left _ t_in_Y,
    by right; exact face_nonempty t_in_Y⟩

theorem simplicialJoin_mem_left
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces ∪ {∅})
  : s ⊔ₛ t ∈ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).faces :=
by
  cases' t_in_Y with t_in_Y t_empty
  · rw [simplicialJoin_mem]
    use s; constructor; left; assumption
    use t; constructor; left; assumption
    constructor; rfl
    rw [ne_eq, faceDisjoint_empty, not_and_or]
    left; exact face_nonempty s_in_X
  · subst t_empty
    exact simplicialJoin_incl_left s_in_X

theorem simplicialJoin_mem_right
    (s_in_X : s ∈ X.faces ∪ {∅})
    (t_in_Y : t ∈ Y.faces)
  : s ⊔ₛ t ∈ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).faces :=
by
  cases' s_in_X with s_in_X s_empty
  · rw [simplicialJoin_mem]
    use s; constructor; left; assumption
    use t; constructor; left; assumption
    constructor; rfl
    rw [ne_eq, faceDisjoint_empty, not_and_or]
    left; exact face_nonempty s_in_X
  · subst s_empty
    exact simplicialJoin_incl_right t_in_Y

theorem simplicialJoin_mem_vertices_left : (x, (0 : 𝕜)) ∈ (X ⋆ Y).vertices ↔ x ∈ X.vertices := by
  simp only [AbstractSimplicialComplex.vertices_eq, SimplicialJoin, Set.mem_iUnion, Set.mem_diff]
  constructor
  · intro x0_in_XY
    choose s Hs x0_in_s using x0_in_XY
    choose Hs s_ne using Hs
    rw [Set.mem_setOf] at Hs
    choose t Ht u Hu tu_eq_s using Hs
    use t
    cases' Ht with t_in_X t_empty

    use t_in_X
    have Hx_0 : (x, 0) ∈ s := by
      rw [← Finset.mem_coe]
      assumption
    rw [Finset.mem_coe]
    rw [← tu_eq_s, faceDisjoint_mem_iff_left] at Hx_0
    assumption

    rw [Set.mem_singleton_iff] at t_empty
    rw [Finset.mem_coe, ← tu_eq_s, t_empty, faceDisjoint_mem_iff_left] at x0_in_s
    contradiction
  · intro x_in_s
    choose s Hs x_in_s using x_in_s
    use s ⊔ₛ ∅
    rw [Set.mem_setOf]
    constructor

    rw [Finset.mem_coe, faceDisjoint_mem_iff_left]
    assumption

    constructor
    use s; constructor
    rw [Set.mem_union]; left; assumption
    use ∅; constructor
    rw [Set.mem_union]; right; apply Set.mem_singleton
    rfl

    rw [Set.mem_singleton_iff, faceDisjoint_empty, not_and_or]
    left
    revert Hs
    contrapose
    rw [not_not]
    intro s_empty
    rw [s_empty]
    apply X.empty_notMem

theorem simplicialJoin_notMem_vertices_left
  : x ∉ X.vertices → (x, 0) ∉ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).vertices :=
by
  contrapose
  simp only [Classical.not_not, simplicialJoin_mem_vertices_left]
  exact Set.mem_of_eq_of_mem rfl

theorem simplicialJoin_mem_vertices_right : (x, (1 : 𝕜)) ∈ (X ⋆ Y).vertices ↔ x ∈ Y.vertices := by
  simp only [AbstractSimplicialComplex.vertices_eq, SimplicialJoin, Set.mem_iUnion, Set.mem_diff]
  constructor
  · intro x1_in_XY
    choose s Hs x1_in_s using x1_in_XY
    rw [Set.mem_setOf] at Hs
    choose Hs s_ne using Hs
    choose t Ht u Hu tu_eq_s using Hs
    use u
    rw [Set.mem_union] at Hu
    cases' Hu with u_in_Y u_empty

    use u_in_Y
    rw [← tu_eq_s, Finset.mem_coe, faceDisjoint_mem_iff_right] at x1_in_s
    assumption

    rw [Set.mem_singleton_iff] at u_empty
    rw [← tu_eq_s, Finset.mem_coe, faceDisjoint_mem_iff_right, u_empty] at x1_in_s
    contradiction
  · intro x_in_s
    choose s Hs x_in_s using x_in_s
    use ∅ ⊔ₛ s
    constructor

    rw [Finset.mem_coe, faceDisjoint_mem_iff_right]
    assumption

    constructor
    rw [Set.mem_setOf]
    use ∅; constructor
    rw [Set.mem_union]; right; apply Set.mem_singleton

    use s; constructor
    rw [Set.mem_union]
    left; assumption
    rfl

    rw [Set.mem_singleton_iff, faceDisjoint_empty, not_and_or]
    right
    revert Hs
    contrapose
    rw [not_not]
    intro s_empty
    rw [s_empty]
    apply Y.empty_notMem

theorem simplicialJoin_notMem_vertices_right
  : x ∉ Y.vertices → (x, 1) ∉ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).vertices :=
by
  contrapose
  simp only [Classical.not_not, simplicialJoin_mem_vertices_right]
  exact Set.mem_of_eq_of_mem rfl

theorem simplicialJoin_mem_vertices
    (x : E × 𝕜)
  : x ∈ (X ⋆ Y).vertices ↔ x.fst ∈ X.vertices ∧ x.snd = 0 ∨ x.fst ∈ Y.vertices ∧ x.snd = 1 :=
by
  constructor
  · intro x_in_XY
    simp only [AbstractSimplicialComplex.vertices_eq, SimplicialJoin] at x_in_XY
    rw [Set.mem_iUnion] at x_in_XY
    choose y x_in_XY using x_in_XY
    rw [Set.mem_iUnion] at x_in_XY
    choose Hy x_in_y using x_in_XY
    rw [Set.mem_diff, Set.mem_setOf] at Hy
    choose Hy y_ne using Hy
    choose s Hy using Hy
    cases' Hy with Hs Hy
    choose t Hy using Hy
    cases' Hy with Ht st_eq_y
    rw [Finset.ext_iff] at st_eq_y
    specialize st_eq_y x
    cases' st_eq_y with st_imp_y y_imp_st
    rw [Finset.mem_coe] at x_in_y
    specialize y_imp_st x_in_y
    rw [faceDisjoint_mem_iff] at y_imp_st
    cases' y_imp_st with x_in_s x_in_t
    left
    cases' x_in_s with x_in_s x0
    constructor
    simp only [AbstractSimplicialComplex.vertices_eq]
    rw [Set.mem_iUnion]
    use s
    rw [Set.mem_iUnion]
    rw [Set.mem_union] at Hs
    cases' Hs with Hs s_empty
    use Hs
    rw [Finset.mem_coe]
    assumption

    rw [Set.mem_singleton_iff] at s_empty
    rw [s_empty] at x_in_s
    contradiction
    assumption

    right
    cases' x_in_t with x_in_t x1
    constructor
    simp only [AbstractSimplicialComplex.vertices_eq]
    rw [Set.mem_iUnion]
    use t
    rw [Set.mem_iUnion]
    rw [Set.mem_union] at Ht
    cases' Ht with Ht t_empty
    use Ht
    rw [Finset.mem_coe]
    assumption

    rw [Set.mem_singleton_iff] at t_empty
    rw [t_empty] at x_in_t
    contradiction
    assumption
  · intro x_in_X_or_Y
    cases' x_in_X_or_Y with x_in_X x_in_Y
    cases' x_in_X with x_in_X x0
    simp only [AbstractSimplicialComplex.vertices_eq] at *
    rw [Set.mem_iUnion] at *
    choose s x_in_X using x_in_X
    use s ⊔ₛ ∅
    rw [Set.mem_iUnion] at *
    choose s_in_X x_in_s using x_in_X
    use simplicialJoin_incl_left s_in_X
    rw [Finset.mem_coe, faceDisjoint_mem_iff]
    left
    rw [Finset.mem_coe] at x_in_s
    constructor <;> assumption
    cases' x_in_Y with x_in_Y x1
    simp only [AbstractSimplicialComplex.vertices_eq] at *
    rw [Set.mem_iUnion] at *
    choose t x_in_Y using x_in_Y
    use∅ ⊔ₛ t
    rw [Set.mem_iUnion] at *
    choose t_in_Y x_in_t using x_in_Y
    use simplicialJoin_incl_right t_in_Y
    rw [Finset.mem_coe, faceDisjoint_mem_iff]
    right
    rw [Finset.mem_coe] at x_in_t
    constructor <;> assumption

def SimplicialJoinIsoMap (f g : E → F) : E × 𝕜 → F × 𝕜
  := fun x : E × 𝕜
    => if x.snd = 0 then (f x.fst, x.snd) else (g x.fst, x.snd)

theorem simplicialJoin_simplicialMap
    {Z W : AbstractSimplicialComplex F}
    (f : SimplicialMap X Z)
    (g : SimplicialMap Y W)
  : IsSimplicialMap (X ⋆ Y) (Z ⋆ W : AbstractSimplicialComplex (F × 𝕜)) (SimplicialJoinIsoMap f.map g.map) :=
by
  unfold IsSimplicialMap
  intro s s_in_XY
  rw [simplicialJoin_mem] at *
  choose t Ht u Hu s_eq_tu s_ne using s_in_XY
  use Finset.image f.map t; constructor
  rw [Set.mem_union] at ⊢ Ht Hu
  cases' Ht with Ht t_empty

  left
  apply f.is_simplicial
  assumption

  rw [Set.mem_singleton_iff] at ⊢ t_empty
  right
  rw [t_empty, Finset.image_empty]

  use Finset.image g.map u; constructor
  cases' Hu with Hu u_empty

  left
  apply g.is_simplicial
  assumption

  rw [Set.mem_singleton_iff] at u_empty
  rw [Set.mem_union, Set.mem_singleton_iff]
  right
  rw [u_empty, Finset.image_empty]

  rw [s_eq_tu]
  simp only [FaceDisjointUnion]
  rw [Finset.image_union]
  rw [Finset.ext_iff]
  constructor

  intro x
  constructor
  · intro x_in_f
    rw [Finset.mem_union] at *
    cases' x_in_f with x_in_f x_in_f
    left
    rw [Finset.mem_product]
    rw [Finset.mem_image] at *
    choose y y_in_t0 using x_in_f
    cases' y_in_t0 with y_in_t0 fy_x
    constructor

    use y.fst
    rw [Finset.mem_product] at y_in_t0
    cases' y_in_t0 with y_in_t0 y_0
    constructor
    assumption
    simp only [SimplicialJoinIsoMap] at fy_x
    revert fy_x
    split_ifs
    intro y0_x
    rw [← y0_x]
    rw [Finset.mem_singleton] at y_0
    contradiction
    simp only [SimplicialJoinIsoMap] at fy_x
    revert fy_x
    split_ifs
    intro y0_x
    rw [Finset.mem_singleton, ← y0_x]
    rw [Finset.mem_product] at y_in_t0
    cases' y_in_t0 with y_in_t0 y_0
    rw [Finset.mem_singleton] at y_0
    assumption
    intro fy_x
    rw [Prod.eq_iff_fst_eq_snd_eq] at fy_x
    cases' fy_x with fy_x_fst fy_x_snd
    simp at fy_x_snd
    rw [Finset.mem_singleton, ← fy_x_snd]
    rw [Finset.mem_product] at y_in_t0
    choose y1_in_t y2_eq_0 using y_in_t0
    rw [Finset.mem_singleton] at y2_eq_0
    assumption

    simp only [Finset.mem_image, SimplicialJoinIsoMap] at x_in_f
    choose y y_in_u fy_eq_x using x_in_f
    revert fy_eq_x
    split_ifs
    rw [Finset.mem_product, Finset.mem_singleton] at y_in_u
    choose y_in_u y_one using y_in_u
    have contra : y.snd ≠ 0 := by simp only [y_one, ne_eq, one_ne_zero, not_false_eq_true]
    contradiction
    intro gy_eq_x
    simp only [Prod.ext_iff, Prod.fst, Prod.snd] at gy_eq_x
    choose gy_eq_x x_one using gy_eq_x
    rw [Finset.mem_product, Finset.mem_singleton] at y_in_u
    choose y_in_u y_one using y_in_u
    right
    rw [Finset.mem_product, Finset.mem_image]
    constructor

    use y.fst
    rw [←x_one, y_one, Finset.mem_singleton]
  · intro x_in_f_prod
    rw [Finset.mem_union] at *
    cases' x_in_f_prod with x_in_f_prod x_in_f_prod
    left
    rw [Finset.mem_product] at x_in_f_prod
    cases' x_in_f_prod with x_in_fxz x0
    rw [Finset.mem_image] at *
    choose y y_in_t fxz_y using x_in_fxz
    use(y, 0)
    constructor
    rw [Finset.mem_product]
    simp
    assumption
    simp only [SimplicialJoinIsoMap]
    split_ifs
    rw [Prod.eq_iff_fst_eq_snd_eq]
    constructor
    assumption
    rw [Finset.mem_singleton] at x0
    rw [x0]
    rw [Prod.eq_iff_fst_eq_snd_eq]
    constructor
    assumption
    rw [Finset.mem_singleton] at x0
    rw [x0]
    right
    rw [Finset.mem_product] at x_in_f_prod
    cases' x_in_f_prod with x_in_fyw x1
    rw [Finset.mem_singleton] at x1
    rw [Finset.mem_image] at *
    choose y y_in_u fyw_y using x_in_fyw
    use(y, 1)
    constructor
    rw [Finset.mem_product]
    constructor
    assumption
    simp
    simp only [SimplicialJoinIsoMap]
    split_ifs

    have contra : (1 : 𝕜) ≠ 0 := by simp only [ne_eq, one_ne_zero, not_false_eq_true]
    contradiction

    rw [Prod.eq_iff_fst_eq_snd_eq]
    constructor
    assumption
    rw [x1]

  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  rw [ne_eq, s_eq_tu, faceDisjoint_empty, not_and_or] at s_ne
  cases' s_ne with t_ne u_ne

  left
  rw [Finset.image_eq_empty, Finset.product_eq_empty, not_or]
  constructor
  assumption
  simp only [Finset.singleton_ne_empty, not_false_eq_true]

  right
  rw [Finset.image_eq_empty, Finset.product_eq_empty, not_or]
  constructor
  assumption
  simp only [Finset.singleton_ne_empty, not_false_eq_true]

def SimplicialJoinIsoInverseMap (f g : F → E) : F × 𝕜 → E × 𝕜
  := fun x : F × 𝕜
    => if x.snd = 0 then (f x.fst, x.snd) else (g x.fst, x.snd)

theorem simplicialJoin_simplicialIso
    {Z W : AbstractSimplicialComplex F}
  : (X ≅ Z) → Y ≅ W → (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) ≅ (Z ⋆ W : AbstractSimplicialComplex (F × 𝕜)) :=
by
  unfold IsSimpliciallyIso
  unfold IsSimplicialIso
  unfold IsInverseSimplicialIso
  simp only [SimplicialMap.comp, SimplicialMap.map]
  intro X_iso_Z Y_iso_W
  choose f_xz g_zx fxz_inv_gzx using X_iso_Z
  choose f_yw g_wy fyw_inv_gwy using Y_iso_W
  cases' fxz_inv_gzx with gzx_fxz_id fxz_gzx_id
  cases' fyw_inv_gwy with gwy_fyw_id fyw_gwy_id
  let fs : SimplicialMap (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) (Z ⋆ W) :=
    SimplicialMap.mk (SimplicialJoinIsoMap f_xz.map f_yw.map)
      (simplicialJoin_simplicialMap f_xz f_yw)
  let gs : SimplicialMap (Z ⋆ W : AbstractSimplicialComplex (F × 𝕜)) (X ⋆ Y) :=
    SimplicialMap.mk (SimplicialJoinIsoMap g_zx.map g_wy.map)
      (simplicialJoin_simplicialMap g_zx g_wy)
  use fs
  use gs
  constructor <;> simp only [Set.restrict_eq_restrict_iff, Set.EqOn, id, Function.comp] at *
  · intro x x_in_XY
    unfold gs
    unfold fs
    simp only [SimplicialMap.map, SimplicialJoinIsoMap]
    split_ifs with h <;> rw [Prod.eq_iff_fst_eq_snd_eq]

    constructor
    simp
    rw [gzx_fxz_id]
    rw [← @simplicialJoin_mem_vertices_left _ 𝕜]
    rw [← h]
    simp only [Prod.mk.eta]
    assumption

    constructor
    simp
    rw [gwy_fyw_id]

    rw [← @simplicialJoin_mem_vertices_right _ 𝕜 _ _ _ _ X]
    rw [simplicialJoin_mem_vertices] at x_in_XY
    cases' x_in_XY with x_in_XY x_in_XY
    cases' x_in_XY with x_in_X x0
    contradiction
    cases' x_in_XY with x_in_Y x1
    rw [← x1]
    simp only [Prod.mk.eta]
    rw [simplicialJoin_mem_vertices]
    right
    constructor <;> assumption
  · intro x x_in_ZW
    unfold gs
    unfold fs
    simp only [SimplicialMap.map, SimplicialJoinIsoMap]
    split_ifs with h <;> rw [Prod.eq_iff_fst_eq_snd_eq]

    constructor
    simp
    rw [fxz_gzx_id]
    rw [← @simplicialJoin_mem_vertices_left _ 𝕜]
    rw [← h]
    simp only [Prod.mk.eta]
    assumption

    constructor
    simp
    rw [fyw_gwy_id]
    rw [← @simplicialJoin_mem_vertices_right _ 𝕜 _ _ _ _ Z]
    rw [simplicialJoin_mem_vertices] at x_in_ZW
    cases' x_in_ZW with x_in_ZW x_in_ZW
    cases' x_in_ZW with x_in_X x0
    contradiction
    cases' x_in_ZW with x_in_W x1
    rw [← x1]
    simp only [Prod.mk.eta]
    rw [simplicialJoin_mem_vertices]
    right
    constructor <;> assumption

theorem simplicialJoin_simplicialIso_left
  : (X ≅ Y) → (X ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) ≅ (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) :=
by
  intro X_iso_Y
  apply simplicialJoin_simplicialIso
  assumption
  rfl

theorem simplicialJoin_simplicialIso_right
  : (X ≅ Y) → (Z ⋆ X : AbstractSimplicialComplex (E × 𝕜)) ≅ (Z ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) :=
by
  intro X_iso_Y
  apply simplicialJoin_simplicialIso
  rfl
  assumption

def SimplicialJoinAssocForwardAux
    (Y Z : AbstractSimplicialComplex E)
    (ψ : SimplicialCoe (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) E)
  : E × 𝕜 → E × 𝕜 := fun x : E × 𝕜 => if x.snd = 0 then x else (ψ.coe (x.fst, 0), x.snd)

def SimplicialJoinAssocForwardMap
    (X Y Z : AbstractSimplicialComplex E)
    (φ : SimplicialCoe (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) E)
    (ψ : SimplicialCoe (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) E)
    (f : SimplicialMap (φ.coe ''ˢ (X ⋆ Y)) (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)))
  : E × 𝕜 → E × 𝕜 :=
    fun x : E × 𝕜 =>
      if x.snd = 0 then (SimplicialJoinAssocForwardAux Y Z ψ) (f.map x.fst) else (ψ.coe x, x.snd)

theorem simplicialJoin_assoc_forward_simplicial_left
    (φ : SimplicialCoe (X ⋆ Y) E)
    (ψ : SimplicialCoe (Y ⋆ Z) E)
    (f : SimplicialMap (φ.coe ''ˢ (X ⋆ Y)) (X ⋆ Y))
    (f_inv : IsInverseSimplicialIso φ.simplicialMap f)
    (a b t : Finset E)
    (a_in_X : a ∈ X.faces ∪ {∅})
    (b_in_Y : b ∈ Y.faces ∪ {∅})
  : Finset.image (SimplicialJoinAssocForwardMap X Y Z φ ψ f) (Finset.image φ.coe (a ⊔ₛ b) ⊔ₛ t) ⊆
      a ⊔ₛ Finset.image ψ.coe (b ⊔ₛ t : Finset (E × 𝕜)) :=
by
  unfold SimplicialJoinAssocForwardMap
  rw [Set.mem_union] at a_in_X b_in_Y
  simp only [Finset.subset_iff]
  intro x x_in_img
  rw [Finset.mem_image] at x_in_img
  choose y y_in_u img_y_x using x_in_img
  unfold IsInverseSimplicialIso at f_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id] at f_inv
  choose fφ_id φf_id using f_inv
  simp only [FaceDisjointUnion, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_singleton]
  revert img_y_x
  split_ifs
  simp only [SimplicialJoinAssocForwardAux]
  have y_rw : y = (y.fst, 0) := by
    simp only [Prod.ext_iff]
    constructor; trivial; assumption
  rw [y_rw, faceDisjoint_mem_iff_left, Finset.mem_image] at y_in_u
  choose z z_in_ab coe_z_y using y_in_u
  have z_in_join : z ∈ (X ⋆ Y).vertices :=
    by
    rw [vertex_iff_in_face]
    use a ⊔ₛ b; constructor
    rw [simplicialJoin_mem]
    use a; constructor
    rw [Set.mem_union]
    assumption
    use b; constructor
    rw [Set.mem_union]
    assumption
    constructor
    rfl
    rw [ne_eq, Finset.eq_empty_iff_forall_notMem, not_forall]
    use z; tauto
    assumption
  specialize fφ_id z_in_join
  have coe_rw : φ.simplicialMap.map = φ.coe := by rfl
  rw [coe_rw] at fφ_id
  split_ifs with h_1
  intro fy_x
  left
  rw [← coe_z_y, fφ_id] at fy_x h_1
  subst fy_x
  rw [faceDisjoint_mem_iff] at z_in_ab
  cases' z_in_ab with z_in_a contra
  assumption
  choose z_in_b contra using contra
  have H : z.snd ≠ 0 := by simp only [contra, ne_eq, one_ne_zero, not_false_eq_true]
  contradiction
  intro ψfy_x
  right
  rw [← coe_z_y, fφ_id] at ψfy_x h_1
  subst ψfy_x
  simp only [Prod.fst, Prod.snd]
  rw [faceDisjoint_mem_iff] at z_in_ab
  cases' z_in_ab with contra z_in_b
  choose z_in_a contra using contra
  contradiction
  choose z_in_b z_one using z_in_b
  constructor
  use(z.fst, 0); constructor; left
  simp only [Prod.fst, Prod.snd]
  constructor; assumption; trivial
  apply congr_arg; rfl
  assumption
  intro ψy_x
  right
  rw [faceDisjoint_mem_iff] at y_in_u
  cases' y_in_u with contra y_in_t
  choose y_in_a contra using contra
  contradiction
  choose y_in_t y_one using y_in_t
  simp only [Prod.ext_iff] at ψy_x
  choose ψy_x x_one using ψy_x
  rw [y_one, @comm _ Eq] at x_one
  constructor
  use y; constructor
  right; constructor <;> assumption
  assumption
  assumption

theorem simplicialJoin_assoc_forward_simplicial_right
    (φ : SimplicialCoe (X ⋆ Y) E)
    (ψ : SimplicialCoe (Y ⋆ Z) E)
    (f : SimplicialMap (φ.coe ''ˢ (X ⋆ Y)) (X ⋆ Y))
    (f_inv : IsInverseSimplicialIso φ.simplicialMap f)
    (a b t : Finset E)
    (a_in_X : a ∈ X.faces ∪ {∅})
    (b_in_Y : b ∈ Y.faces ∪ {∅})
  : a ⊔ₛ Finset.image ψ.coe (b ⊔ₛ t) ⊆
      Finset.image (SimplicialJoinAssocForwardMap X Y Z φ ψ f) (Finset.image φ.coe (a ⊔ₛ b : Finset (E × 𝕜)) ⊔ₛ t) :=
by
  unfold SimplicialJoinAssocForwardMap
  simp only [Finset.subset_iff]
  intro x x_in_join
  unfold IsInverseSimplicialIso at f_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id] at f_inv
  choose fφ_id φf_id using f_inv
  simp only [faceDisjoint_mem_iff, Finset.mem_image] at x_in_join
  simp only [Finset.mem_image, SimplicialJoinAssocForwardAux]
  cases' x_in_join with x_in_a x_in_ψ
  have x_in_XY : x ∈ (X ⋆ Y).vertices :=
    by
    rw [vertex_iff_in_face]
    use a ⊔ₛ b; constructor
    rw [simplicialJoin_mem]
    use a; constructor
    assumption
    use b; constructor
    assumption
    constructor
    rfl
    rw [ne_eq, faceDisjoint_empty, not_and_or, Finset.eq_empty_iff_forall_notMem, not_forall]
    left; use x.1; rw [not_not]
    choose x_in_a x_zero using x_in_a
    assumption
    rw [faceDisjoint_mem_iff]
    left; assumption
  specialize fφ_id x_in_XY
  have coe_rw : φ.simplicialMap.map = φ.coe := by rfl
  rw [coe_rw] at fφ_id
  use(φ.coe x, 0); constructor
  rw [faceDisjoint_mem_iff_left]
  apply Finset.mem_image_of_mem
  rw [faceDisjoint_mem_iff]
  left; assumption
  choose x_in_a x_zero using x_in_a
  simp only [fφ_id, x_zero, eq_self_iff_true, if_true]
  choose x_in_ψ x_one using x_in_ψ
  choose y y_in_bt ψy_x using x_in_ψ
  cases' y_in_bt with y_in_b y_in_t
  choose y_in_b y_zero using y_in_b
  use(φ.coe (y.fst, 1), 0); constructor
  rw [faceDisjoint_mem_iff_left]
  apply Finset.mem_image_of_mem
  rw [faceDisjoint_mem_iff]
  right
  simp only [Prod.fst, Prod.snd]
  constructor; assumption; trivial
  have y_in_XY : (y.fst, (1 : 𝕜)) ∈ (X ⋆ Y).vertices :=
    by
    rw [vertex_iff_in_face]
    use a ⊔ₛ b; constructor
    rw [simplicialJoin_mem]
    use a; constructor
    assumption
    use b; constructor
    assumption
    constructor
    rfl
    rw [ne_eq, faceDisjoint_empty, not_and_or]
    right
    rw [Finset.eq_empty_iff_forall_notMem, not_forall]
    use y.1
    rw [not_not]
    assumption
    rw [faceDisjoint_mem_iff]
    simp only [Prod.fst, Prod.snd]
    right
    constructor; assumption; trivial
  specialize fφ_id y_in_XY
  have coe_rw : φ.simplicialMap.map = φ.coe := by rfl
  rw [coe_rw] at fφ_id
  simp only [fφ_id, y_zero, eq_self_iff_true, if_true, Nat.one_ne_zero, if_false]
  have y_rw : y = (y.fst, y.snd) := by
    simp only [Prod.ext_iff]
  rw [y_rw] at ψy_x
  rw [← y_zero, ← x_one, ψy_x]
  simp only [Prod.ext_iff]
  have H : x.2 = y.2 ↔ False := by simp only [x_one, y_zero, one_ne_zero, not_false_eq_true]
  simp only [H, if_false]
  trivial

  use y; constructor
  rw [faceDisjoint_mem_iff]
  right; assumption
  choose y_in_t y_one using y_in_t
  have H : y.2 = 0 ↔ False := by simp only [y_one, one_ne_zero]
  simp only [H, Nat.one_ne_zero, if_false, Prod.ext_iff]
  rw [@comm _ Eq] at x_one
  constructor; assumption
  rw [y_one]; assumption

theorem simplicialJoin_assoc_forward_simplicial
    (φ : SimplicialCoe (X ⋆ Y) E)
    (ψ : SimplicialCoe (Y ⋆ Z) E)
    (f : SimplicialMap (φ.coe ''ˢ (X ⋆ Y)) (X ⋆ Y))
    (f_inv : IsInverseSimplicialIso φ.simplicialMap f)
  : IsSimplicialMap (φ.coe ''ˢ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) ⋆ Z) (X ⋆ ψ.coe ''ˢ (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜))) (SimplicialJoinAssocForwardMap X Y Z φ ψ f) :=
by
  simp only [IsSimplicialMap]
  intro u u_in_join
  rw [simplicialJoin_mem] at u_in_join ⊢
  choose s s_in_coe t t_in_Z u_eq_st using u_in_join
  simp only [SimplicialImage, SimplicialJoin, Set.mem_union, Set.mem_setOf] at s_in_coe
  cases' s_in_coe with s_in_coe s_empty
  choose v v_in_join coe_v_s using s_in_coe
  simp only [Set.mem_diff] at v_in_join
  choose v_in_join v_ne using v_in_join
  choose a a_in_X b b_in_Y ab_eq_v using v_in_join
  subst ab_eq_v
  subst coe_v_s
  choose u_eq_st u_ne using u_eq_st
  subst u_eq_st
  use a; constructor; assumption
  use Finset.image ψ.coe (b ⊔ₛ t); constructor
  simp only [SimplicialImage, Set.mem_union, Set.mem_setOf, simplicialJoin_mem]

  rw [ne_eq, faceDisjoint_empty, not_and_or] at u_ne
  cases' u_ne with ab_ne t_ne
  rw [Finset.image_eq_empty, faceDisjoint_empty, not_and_or] at ab_ne
  simp only [Set.mem_union, Set.mem_singleton_iff] at t_in_Z b_in_Y a_in_X
  cases' b_in_Y with b_in_Y b_empty

  left; use b ⊔ₛ t; constructor
  exact simplicialJoin_mem_left b_in_Y t_in_Z
  rfl

  subst b_empty
  cases' t_in_Z with t_in_Z t_empty
  left; use ∅ ⊔ₛ t; constructor
  exact simplicialJoin_incl_right t_in_Z
  rfl

  subst t_empty
  right
  simp only [FaceDisjointUnion, Finset.empty_product, Finset.empty_union, Finset.image_empty]
  apply Set.mem_singleton

  constructor
  use b ⊔ₛ t; constructor
  cases' t_in_Z with t_in_Z t_empty
  exact simplicialJoin_mem_right b_in_Y t_in_Z
  subst t
  contradiction
  rfl

  constructor
  simp only [SimplicialJoinAssocForwardMap, Finset.ext_iff]
  intro x
  constructor
  apply simplicialJoin_assoc_forward_simplicial_left <;> assumption
  apply simplicialJoin_assoc_forward_simplicial_right <;> assumption

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  rw [Set.mem_singleton_iff] at s_empty
  subst s_empty
  use ∅; constructor
  rw [Set.mem_union]; right; apply Set.mem_singleton
  use Finset.image ψ.coe (∅ ⊔ₛ t); constructor
  rw [Set.mem_union]; left
  simp only [SimplicialImage, SimplicialJoin, Set.mem_setOf, Set.mem_diff, Set.mem_union]
  use (∅ ⊔ₛ t); constructor; constructor
  use ∅; constructor; right; apply Set.mem_singleton
  use t; constructor; assumption; rfl
  rw [Set.mem_singleton_iff]
  choose u_eq_st u_ne using u_eq_st
  rw [u_eq_st] at u_ne
  assumption
  rfl

  constructor
  simp only [Finset.ext_iff]
  intro x
  constructor

  intro x_in_img
  simp only [Finset.mem_image, SimplicialJoinAssocForwardMap, SimplicialJoinAssocForwardAux] at x_in_img
  choose a a_in_u fa_x using x_in_img
  choose u_eq_st u_ne using u_eq_st
  subst u_eq_st
  rw [faceDisjoint_mem_iff] at ⊢ a_in_u
  cases' a_in_u with contra a_in_t
  choose contra a2_zero using contra
  contradiction
  choose a1_in_t a2_one using a_in_t
  simp only [a2_one] at fa_x
  simp only [one_ne_zero, ↓reduceIte, SimplicialJoin, FaceDisjointUnion] at fa_x
  simp only [Prod.ext_iff] at fa_x
  choose fa_x x2_one using fa_x
  right; constructor
  rw [Finset.mem_image]
  use a; constructor
  rw [faceDisjoint_mem_iff]
  right; constructor <;> assumption
  assumption
  symm; assumption

  intro x_in_union
  rw [faceDisjoint_mem_iff] at x_in_union
  cases' x_in_union with contra x_in_img
  choose contra x2_zero using contra
  contradiction
  choose x1_in_img x2_one using x_in_img
  rw [Finset.mem_image] at ⊢ x1_in_img
  simp only [SimplicialJoinAssocForwardMap, SimplicialJoinAssocForwardAux]
  choose a a_in_t fa_x using x1_in_img
  choose u_eq_st u_ne using u_eq_st
  subst u_eq_st
  use a; constructor; assumption
  rw [faceDisjoint_mem_iff] at a_in_t
  cases' a_in_t with contra a_in_t
  choose contra a2_zero using contra
  contradiction
  choose a1_in_t a2_one using a_in_t
  simp only [a2_one]
  simp only [one_ne_zero, ↓reduceIte, SimplicialJoin, FaceDisjointUnion, Prod.ext_iff]
  constructor; assumption
  symm; assumption

  choose u_eq_st u_ne using u_eq_st
  rw [ne_eq, Finset.image_eq_empty]
  assumption

def SimplicialJoinAssocInvAux
    (X Y : AbstractSimplicialComplex E)
    (φ : SimplicialCoe (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) E)
  : E × 𝕜 → E × 𝕜 :=
      fun x : E × 𝕜 => if x.snd = 0 then (φ.coe (x.fst, 1), 0) else x

def SimplicialJoinAssocInvMap
    (X Y Z : AbstractSimplicialComplex E)
    (φ : SimplicialCoe (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) E)
    (ψ : SimplicialCoe (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) E)
    (g : SimplicialMap (ψ.coe ''ˢ (Y ⋆ Z)) (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜)))
  : E × 𝕜 → E × 𝕜 :=
      fun x : E × 𝕜 =>
        if x.snd = 0 then (φ.coe x, 0) else (SimplicialJoinAssocInvAux X Y φ) (g.map x.fst)

theorem simplicialJoin_assoc_inv_simplicial_left
    (φ : SimplicialCoe (X ⋆ Y) E)
    (ψ : SimplicialCoe (Y ⋆ Z) E)
    (g : SimplicialMap (ψ.coe ''ˢ (Y ⋆ Z)) (Y ⋆ Z))
    (g_inv : IsInverseSimplicialIso ψ.simplicialMap g)
    (s a b : Finset E)
    (a_in_Y : a ∈ Y.faces ∪ {∅})
    (b_in_Z : b ∈ Z.faces ∪ {∅})
  : Finset.image (SimplicialJoinAssocInvMap X Y Z φ ψ g) (s ⊔ₛ Finset.image ψ.coe (a ⊔ₛ b)) ⊆
      Finset.image φ.coe (s ⊔ₛ a : Finset (E × 𝕜)) ⊔ₛ b :=
by
  simp only [SimplicialJoinAssocInvMap, Finset.subset_iff]
  intro x x_in_img
  unfold IsInverseSimplicialIso at g_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id] at g_inv
  choose gψ_id ψg_id using g_inv
  simp only [Finset.mem_image, faceDisjoint_mem_iff, SimplicialJoinAssocInvMap] at x_in_img
  choose y y_in_join img_y_x using x_in_img
  simp only [FaceDisjointUnion, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_singleton]
  revert img_y_x
  split_ifs
  cases' y_in_join with y_in_s contra
  intro φy_x
  left
  simp only [Prod.ext_iff] at φy_x
  choose φy_x x_zero using φy_x
  rw [@comm _ Eq] at x_zero
  constructor
  use y; constructor
  left; assumption
  assumption
  assumption
  choose y_in_coe contra using contra
  have H : y.snd ≠ 0 := by simp only [contra, ne_eq, one_ne_zero, not_false_eq_true]
  contradiction
  cases' y_in_join with contra y_in_coe
  choose y_in_s contra using contra
  contradiction
  choose y_in_coe y_one using y_in_coe
  choose z z_in_join ψz_y using y_in_coe
  simp only [SimplicialJoinAssocInvAux]
  intro img_y_x
  have z_in_YZ : z ∈ (Y ⋆ Z).vertices :=
    by
    rw [vertex_iff_in_face]
    use a ⊔ₛ b; constructor
    rw [simplicialJoin_mem]
    use a; constructor; assumption
    use b; constructor; assumption
    constructor
    rfl

    rw [ne_eq, faceDisjoint_empty, not_and_or]
    cases' z_in_join with z_in_a z_in_b
    choose z1_in_a z2_zero using z_in_a
    left; apply Finset.ne_empty_of_mem z1_in_a
    choose z1_in_b z2_one using z_in_b
    right; apply Finset.ne_empty_of_mem z1_in_b

    rw [faceDisjoint_mem_iff]
    assumption
  specialize gψ_id z_in_YZ
  have coe_rw : ψ.simplicialMap.map = ψ.coe := by rfl
  rw [coe_rw] at gψ_id
  cases' z_in_join with z_in_a z_in_b
  left
  choose z_in_a z_zero using z_in_a
  simp only [← ψz_y, gψ_id, Prod.ext_iff, z_zero, eq_self_iff_true, if_true] at img_y_x
  choose φz_x x_zero using img_y_x
  rw [@comm _ Eq] at x_zero
  constructor
  use(z.fst, 1); constructor; right
  simp only [Prod.fst, Prod.snd]
  constructor; assumption; trivial
  assumption
  assumption
  right
  choose z_in_b z_one using z_in_b
  simp only [← ψz_y, gψ_id, Prod.ext_iff, z_one, Nat.one_ne_zero, if_false] at img_y_x
  choose z_eq_x x_one using img_y_x
  simp only [one_ne_zero, ↓reduceIte] at z_eq_x x_one
  constructor
  rw [z_eq_x] at z_in_b
  rw [@comm _ Eq] at x_one
  assumption
  rw [← x_one]
  assumption

theorem simplicialJoin_assoc_inv_simplicial_right
    (φ : SimplicialCoe (X ⋆ Y) E)
    (ψ : SimplicialCoe (Y ⋆ Z) E)
    (g : SimplicialMap (ψ.coe ''ˢ (Y ⋆ Z)) (Y ⋆ Z))
    (g_inv : IsInverseSimplicialIso ψ.simplicialMap g)
    (s a b : Finset E)
    (a_in_Y : a ∈ Y.faces ∪ {∅})
    (b_in_Z : b ∈ Z.faces ∪ {∅})
  : Finset.image φ.coe (s ⊔ₛ a) ⊔ₛ b ⊆
      Finset.image (SimplicialJoinAssocInvMap X Y Z φ ψ g) (s ⊔ₛ Finset.image ψ.coe (a ⊔ₛ b : Finset (E × 𝕜))) :=
by
  simp only [SimplicialJoinAssocInvMap, Finset.subset_iff]
  intro x x_in_join
  unfold IsInverseSimplicialIso at g_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id] at g_inv
  choose gψ_id ψg_id using g_inv
  simp only [faceDisjoint_mem_iff, Finset.mem_image] at x_in_join
  simp only [Finset.mem_image, SimplicialJoinAssocInvMap]
  cases' x_in_join with x_in_coe x_in_b
  choose x_in_coe x_zero using x_in_coe
  choose y y_in_join φy_x using x_in_coe
  simp only [SimplicialJoinAssocInvAux]
  cases' y_in_join with y_in_s y_in_a
  use y; constructor
  rw [faceDisjoint_mem_iff]
  left; assumption
  choose y_in_s y_zero using y_in_s
  rw [@comm _ Eq] at x_zero
  simp only [y_zero, eq_self_iff_true, if_true, Prod.ext_iff]
  constructor <;> assumption
  choose y_in_a y_one using y_in_a
  use(ψ.coe (y.fst, 0), 1); constructor
  rw [faceDisjoint_mem_iff_right]
  apply Finset.mem_image_of_mem
  rw [faceDisjoint_mem_iff_left]
  assumption
  have y_in_YZ : (y.fst, 0) ∈ (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜)).vertices :=
    by
    rw [vertex_iff_in_face]
    use (a ⊔ₛ b : Finset (E × 𝕜)); constructor
    rw [simplicialJoin_mem]
    use a; constructor; assumption
    use b; constructor; assumption
    constructor
    rfl

    rw [ne_eq, faceDisjoint_empty, not_and_or]
    left; apply Finset.ne_empty_of_mem y_in_a

    rw [faceDisjoint_mem_iff_left]
    assumption
  specialize gψ_id y_in_YZ
  have coe_rw : ψ.simplicialMap.map = ψ.coe := by rfl
  rw [coe_rw] at gψ_id
  simp only [y_one, gψ_id, Nat.one_ne_zero, if_false, eq_self_iff_true, if_true]
  have y_rw : y = (y.fst, y.snd) := by
    simp only [Prod.ext_iff]
  rw [y_rw] at φy_x
  rw [← y_one, ← x_zero, φy_x]
  simp only [Prod.ext_iff, x_zero, y_one, one_ne_zero, ↓reduceIte, and_self]
  use (ψ.coe x, 1); constructor
  rw [faceDisjoint_mem_iff_right]
  apply Finset.mem_image_of_mem
  rw [faceDisjoint_mem_iff]
  right; assumption
  have x_in_YZ : x ∈ (Y ⋆ Z).vertices :=
    by
    rw [vertex_iff_in_face]
    use a ⊔ₛ b; constructor
    rw [simplicialJoin_mem]
    use a; constructor; assumption
    use b; constructor; assumption
    constructor; rfl

    choose x_in_b x_one using x_in_b
    rw [ne_eq, faceDisjoint_empty, not_and_or]
    right; apply Finset.ne_empty_of_mem x_in_b

    rw [faceDisjoint_mem_iff]
    right; assumption
  specialize gψ_id x_in_YZ
  have coe_rw : ψ.simplicialMap.map = ψ.coe := by rfl
  rw [coe_rw] at gψ_id
  choose x_in_b x_one using x_in_b
  simp only [SimplicialJoinAssocInvAux]
  simp only [Prod.snd, x_one, gψ_id, Nat.one_ne_zero]
  simp only [one_ne_zero, ↓reduceIte]

theorem simplicialJoin_assoc_inv_simplicial
    (φ : SimplicialCoe (X ⋆ Y) E)
    (ψ : SimplicialCoe (Y ⋆ Z) E)
    (g : SimplicialMap (ψ.coe ''ˢ (Y ⋆ Z)) (Y ⋆ Z))
    (g_inv : IsInverseSimplicialIso ψ.simplicialMap g)
  : IsSimplicialMap (X ⋆ ψ.coe ''ˢ (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜))) (φ.coe ''ˢ (X ⋆ Y) ⋆ Z) (SimplicialJoinAssocInvMap X Y Z φ ψ g) :=
by
  simp only [IsSimplicialMap]
  intro u u_in_join
  rw [simplicialJoin_mem] at u_in_join ⊢
  choose s s_in_X t t_in_coe u_eq_st using u_in_join
  simp only [SimplicialImage, SimplicialJoin, Set.mem_diff, Set.mem_union, Set.mem_setOf] at t_in_coe
  cases' t_in_coe with t_in_coe t_empty

  choose v v_in_join coe_v_s using t_in_coe
  choose v_in_join v_ne using v_in_join
  choose a a_in_Y b b_in_Z ab_eq_v using v_in_join
  subst ab_eq_v
  subst coe_v_s
  choose u_eq_st u_ne using u_eq_st
  subst u_eq_st
  use Finset.image φ.coe (s ⊔ₛ a); constructor
  simp only [SimplicialImage, Set.mem_setOf, simplicialJoin_mem, Set.mem_union]

  simp only [Set.mem_union] at s_in_X a_in_Y
  cases' s_in_X with s_in_X s_empty
  left; use s ⊔ₛ a; constructor
  exact simplicialJoin_mem_left s_in_X a_in_Y
  rfl

  rw [Set.mem_singleton_iff] at s_empty
  subst s_empty
  cases' a_in_Y with a_in_Y a_empty
  left; use ∅ ⊔ₛ a; constructor
  exact simplicialJoin_incl_right a_in_Y
  rfl

  rw [Set.mem_singleton_iff] at a_empty
  subst a_empty
  right
  rw [Set.mem_singleton_iff, Finset.image_eq_empty, faceDisjoint_empty]
  constructor <;> rfl

  use b; constructor; assumption
  simp only [SimplicialJoinAssocForwardMap, Finset.ext_iff]
  constructor
  intro x
  constructor
  apply simplicialJoin_assoc_inv_simplicial_left <;> assumption
  apply simplicialJoin_assoc_inv_simplicial_right <;> assumption

  simp only [ne_eq, Finset.image_eq_empty, SimplicialJoinAssocInvMap]
  assumption

  simp only [Set.mem_singleton_iff, Set.mem_union] at s_in_X t_empty
  subst t_empty
  choose u_eq_st u_ne using u_eq_st
  subst u
  cases' s_in_X with s_in_X s_empty
  use Finset.image φ.coe (s ⊔ₛ ∅); constructor
  simp only [Set.mem_union, SimplicialImage, Set.mem_setOf]
  left; use s ⊔ₛ ∅; constructor
  simp only [SimplicialJoin, Set.mem_diff, Set.mem_setOf]
  constructor; use s; constructor
  rw [Set.mem_union]; left; assumption
  use ∅; constructor
  rw [Set.mem_union]; right; apply Set.mem_singleton
  rfl
  rw [Set.mem_singleton_iff]; assumption
  rfl

  use ∅; constructor
  rw [Set.mem_union]; right; apply Set.mem_singleton
  constructor
  rw [Finset.ext_iff]
  intro x; constructor

  intro x_in_img
  simp only [Finset.mem_image, SimplicialJoinAssocInvMap, SimplicialJoinAssocInvAux] at x_in_img
  choose a a_in_s fa_x using x_in_img
  rw [faceDisjoint_mem_iff] at a_in_s
  cases' a_in_s with a_in_s contra
  choose a1_in_s a2_zero using a_in_s
  simp only [a2_zero] at fa_x
  simp only [↓reduceIte, SimplicialJoin, FaceDisjointUnion] at fa_x
  simp only [Prod.ext_iff] at fa_x
  choose fa_x x2_zero using fa_x
  rw [faceDisjoint_mem_iff, Finset.mem_image]
  constructor; constructor
  use a; constructor
  rw [faceDisjoint_mem_iff]
  left; constructor <;> assumption
  assumption
  symm; assumption

  choose contra a2_one using contra
  contradiction

  intro x_in_union
  rw [faceDisjoint_mem_iff, Finset.mem_image] at x_in_union
  cases' x_in_union with x_in_union contra
  choose fa_x x2_zero using x_in_union
  choose a a_in_s fa_x using fa_x
  simp only [Finset.mem_image, SimplicialJoinAssocInvMap, SimplicialJoinAssocInvAux]
  use a; constructor; assumption
  rw [faceDisjoint_mem_iff] at a_in_s
  cases' a_in_s with a_in_s contra
  choose a1_in_s a2_zero using a_in_s
  simp only [a2_zero]
  simp only [↓reduceIte, SimplicialJoin, FaceDisjointUnion]
  simp only [Prod.ext_iff]
  constructor; assumption
  symm; assumption

  choose contra a2_one using contra
  contradiction
  choose contra x2_one using contra
  contradiction

  rw [ne_eq, Finset.image_eq_empty]; assumption

  subst s_empty
  rw [ne_eq, faceDisjoint_empty, not_and_or] at u_ne
  cases u_ne <;> contradiction

theorem simplicialJoin_assoc [Nonempty E]
    (φ : SimplicialCoe (X ⋆ Y) E)
    (ψ : SimplicialCoe (Y ⋆ Z) E)
  : (φ.coe ''ˢ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) ≅ (X ⋆ ψ.coe ''ˢ (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜)) : AbstractSimplicialComplex (E × 𝕜)) :=
by
  have φ_iso : IsSimplicialIso φ.simplicialMap := by apply simplicialCoe_is_simplicialIso
  have ψ_iso : IsSimplicialIso ψ.simplicialMap := by apply simplicialCoe_is_simplicialIso
  unfold IsSimplicialIso at φ_iso ψ_iso
  choose gXY gφ_inv using φ_iso
  choose gYZ gψ_inv using ψ_iso
  let f_assoc : SimplicialMap (φ.coe ''ˢ (X ⋆ Y) ⋆ Z) (X ⋆ ψ.coe ''ˢ (Y ⋆ Z)) :=
    SimplicialMap.mk (SimplicialJoinAssocForwardMap X Y Z φ ψ gXY)
      (simplicialJoin_assoc_forward_simplicial φ ψ gXY gφ_inv)
  let g_assoc : SimplicialMap (X ⋆ ψ.coe ''ˢ (Y ⋆ Z)) (φ.coe ''ˢ (X ⋆ Y) ⋆ Z) :=
    SimplicialMap.mk (SimplicialJoinAssocInvMap X Y Z φ ψ gYZ)
      (simplicialJoin_assoc_inv_simplicial φ ψ gYZ gψ_inv)
  unfold IsInverseSimplicialIso at gφ_inv gψ_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id] at gφ_inv gψ_inv
  have φ_rw : φ.simplicialMap.map = φ.coe := by rfl
  have ψ_rw : ψ.simplicialMap.map = ψ.coe := by rfl
  simp only [φ_rw] at gφ_inv
  simp only [ψ_rw] at gψ_inv
  choose gφ_id φg_id using gφ_inv
  choose gψ_id ψg_id using gψ_inv
  unfold IsSimpliciallyIso
  use f_assoc
  unfold IsSimplicialIso
  use g_assoc
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id]
  simp only [f_assoc, g_assoc, SimplicialJoinAssocForwardMap, SimplicialJoinAssocInvMap]
  constructor
  · intro x x_in_join
    rw [vertex_iff_in_face] at x_in_join
    choose u u_in_join x_in_u using x_in_join
    simp only [simplicialJoin_mem, SimplicialImage, Set.mem_setOf] at u_in_join
    choose s s_in_coe t t_in_Z u_eq_st using u_in_join
    rw [Set.mem_union] at s_in_coe
    cases' s_in_coe with s_in_coe s_empty
    choose v v_in_join coe_v_s using s_in_coe
    simp only [SimplicialJoin, Set.mem_diff, Set.mem_setOf] at v_in_join
    choose v_in_join v_ne using v_in_join
    choose a a_in_X b b_in_Y v_eq_ab using v_in_join
    subst v_eq_ab
    subst coe_v_s
    choose u_eq_st u_ne using u_eq_st
    subst u_eq_st
    simp only [Finset.mem_image, faceDisjoint_mem_iff] at x_in_u
    cases' x_in_u with x_in_coe x_in_t
    choose x_in_coe x_zero using x_in_coe
    choose y y_in_join φy_x using x_in_coe
    simp only [← φy_x, x_zero, eq_self_iff_true, if_true]
    simp only [SimplicialJoinAssocForwardAux, SimplicialJoinAssocInvAux]
    have y_in_XY : y ∈ (X ⋆ Y).vertices :=
    by
      rw [vertex_iff_in_face]
      use a ⊔ₛ b; constructor
      simp only [Set.notMem_singleton_iff, ne_eq, faceDisjoint_empty, not_and_or] at v_ne
      cases' v_ne with a_nonempty b_nonempty
      · cases' a_in_X with a_in_X a_empty
        exact simplicialJoin_mem_left a_in_X b_in_Y
        subst a
        contradiction
      · cases' b_in_Y with b_in_Y b_empty
        exact simplicialJoin_mem_right a_in_X b_in_Y
        subst b
        contradiction
      rw [faceDisjoint_mem_iff]; assumption
    specialize gφ_id y_in_XY
    simp only [gφ_id]
    cases' y_in_join with y_in_a y_in_b
    choose y_in_a y_zero using y_in_a
    simp only [y_zero, eq_self_iff_true, if_true, Prod.snd, Prod.ext_iff]
    rw [@comm _ Eq] at x_zero
    constructor <;> assumption
    choose y_in_b y_one using y_in_b
    have y_in_YZ : (y.fst, 0) ∈ (Y ⋆ Z : AbstractSimplicialComplex (E × 𝕜)).vertices :=
    by
      rw [simplicialJoin_mem_vertices_left, vertex_iff_in_face]
      use b; constructor
      rw [Set.mem_union] at b_in_Y
      cases' b_in_Y with b_in_Y contra
      assumption
      rw [Set.mem_singleton_iff] at contra
      rw [contra] at y_in_b
      contradiction
      assumption
    specialize gψ_id y_in_YZ
    simp only [gψ_id, y_one, eq_self_iff_true, if_true, Nat.one_ne_zero, if_false, Prod.snd,
      Prod.ext_iff]
    have y_rw : y = (y.fst, y.snd) := by
      simp only [Prod.ext_iff]
    rw [@comm _ Eq] at x_zero
    simp only [one_ne_zero, ↓reduceIte, SimplicialJoin, FaceDisjointUnion, f_assoc, g_assoc]
    simp only [← y_one, ← y_rw, gψ_id]
    simp only [↓reduceIte, f_assoc, g_assoc]
    constructor <;> assumption
    have x_in_YZ : x ∈ (Y ⋆ Z).vertices :=
    by
      rw [vertex_iff_in_face]
      use b ⊔ₛ t; constructor
      rw [simplicialJoin_mem]
      use b; constructor; assumption
      use t; constructor; assumption
      constructor; rfl
      choose x1_in_t x2_one using x_in_t
      rw [ne_eq, faceDisjoint_empty, not_and_or]
      right; apply Finset.ne_empty_of_mem x1_in_t
      rw [faceDisjoint_mem_iff]
      right; assumption
    choose x_in_t x_one using x_in_t
    specialize gψ_id x_in_YZ
    simp only [SimplicialJoinAssocInvAux]
    simp only [gψ_id, x_one, Nat.one_ne_zero, if_false]

    simp only [one_ne_zero, ↓reduceIte, SimplicialJoin, FaceDisjointUnion, f_assoc, g_assoc]
    simp only [gψ_id, x_one]
    simp only [one_ne_zero, ↓reduceIte, f_assoc, g_assoc]

    choose u_eq_st u_ne using u_eq_st
    subst u_eq_st
    rw [Set.mem_singleton_iff] at s_empty
    subst s_empty
    rw [faceDisjoint_mem_iff] at x_in_u
    cases' x_in_u with contra x_in_t
    choose contra x2_zero using contra
    contradiction
    choose x1_in_t x2_one using x_in_t
    simp only [x2_one]
    simp only [one_ne_zero, ↓reduceIte, SimplicialJoin, FaceDisjointUnion, f_assoc, g_assoc]
    have x_in_YZ : x ∈ (Y ⋆ Z).vertices :=
    by
      rw [vertex_iff_in_face]
      use ∅ ⊔ₛ t; constructor
      rw [simplicialJoin_mem]
      use ∅; constructor
      rw [Set.mem_union]
      right; apply Set.mem_singleton
      use t
      rw [faceDisjoint_mem_iff]
      right; constructor <;> assumption
    specialize gψ_id x_in_YZ
    simp only [gψ_id, SimplicialJoinAssocInvAux, x2_one]
    simp only [one_ne_zero, ↓reduceIte, f_assoc, g_assoc]
  · intro x x_in_join
    rw [vertex_iff_in_face] at x_in_join
    choose u u_in_join x_in_u using x_in_join
    simp only [simplicialJoin_mem, SimplicialImage, Set.mem_union, Set.mem_setOf] at u_in_join
    choose s s_in_X t t_in_coe u_eq_st using u_in_join
    cases' t_in_coe with t_in_coe t_empty
    choose v v_in_join coe_v_t using t_in_coe
    simp only [SimplicialJoin, Set.mem_diff, Set.mem_setOf] at v_in_join
    choose v_in_join v_ne using v_in_join
    choose a a_in_X b b_in_Y v_eq_ab using v_in_join
    subst v_eq_ab
    subst coe_v_t
    choose u_eq_st u_ne using u_eq_st
    subst u_eq_st
    simp only [Finset.mem_image, faceDisjoint_mem_iff] at x_in_u
    cases' x_in_u with x_in_s x_in_coe
    have x_in_XY : x ∈ (X ⋆ Y).vertices :=
    by
      rw [vertex_iff_in_face]
      use s ⊔ₛ a; constructor
      rw [simplicialJoin_mem]
      use s; constructor; assumption
      use a; constructor; assumption
      constructor; rfl
      choose x1_in_s x2_zero using x_in_s
      rw [ne_eq, faceDisjoint_empty, not_and_or]
      left; apply Finset.ne_empty_of_mem x1_in_s
      rw [faceDisjoint_mem_iff]
      left; assumption
    choose x_in_s x_one using x_in_s
    specialize gφ_id x_in_XY
    simp only [SimplicialJoinAssocForwardAux]
    simp only [gφ_id, x_one, eq_self_iff_true, if_true]
    choose x_in_coe x_one using x_in_coe
    choose y y_in_join ψy_x using x_in_coe
    cases' y_in_join with y_in_a y_in_b
    have y_in_YZ : y ∈ (Y ⋆ Z).vertices :=
    by
      rw [vertex_iff_in_face]
      use a ⊔ₛ b; constructor
      rw [simplicialJoin_mem]
      use a; constructor; assumption
      use b; constructor; assumption
      constructor; rfl
      choose y1_in_a y2_zero using y_in_a
      rw [ne_eq, faceDisjoint_empty, not_and_or]
      left; apply Finset.ne_empty_of_mem y1_in_a
      rw [faceDisjoint_mem_iff]
      left; assumption
    choose y_in_a y_zero using y_in_a
    specialize gψ_id y_in_YZ
    have y_in_XY : (y.fst, 1) ∈ (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).vertices :=
      by
      rw [simplicialJoin_mem_vertices_right, vertex_iff_in_face]
      use a; constructor
      cases' a_in_X with a_in_Y contra
      assumption
      rw [Set.mem_singleton_iff] at contra
      rw [contra] at y_in_a
      contradiction
      assumption
    specialize gφ_id y_in_XY
    simp only [SimplicialJoinAssocForwardAux, SimplicialJoinAssocInvAux]
    simp only [← ψy_x, gψ_id, gφ_id, y_zero, x_one, eq_self_iff_true, if_true, Nat.one_ne_zero,
      if_false, Prod.snd]
    have y_rw : y = (y.fst, y.snd) := by
      simp only [Prod.ext_iff]
    simp only [one_ne_zero, ↓reduceIte, SimplicialJoin, FaceDisjointUnion, f_assoc, g_assoc, gφ_id]
    simp only [Prod.ext_iff, ← y_zero, ← y_rw]
    rw [@comm _ Eq] at x_one
    constructor <;> assumption
    have y_in_YZ : y ∈ (Y ⋆ Z).vertices :=
      by
      rw [vertex_iff_in_face]
      use a ⊔ₛ b; constructor
      rw [simplicialJoin_mem]
      use a; constructor; assumption
      use b; constructor; assumption
      constructor; rfl
      choose y1_in_b y2_one using y_in_b
      rw [ne_eq, faceDisjoint_empty, not_and_or]
      right; apply Finset.ne_empty_of_mem y1_in_b
      rw [faceDisjoint_mem_iff]
      right; assumption
    choose y_in_b y_one using y_in_b
    specialize gψ_id y_in_YZ
    simp only [SimplicialJoinAssocForwardAux, SimplicialJoinAssocInvAux]
    simp only [← ψy_x, gψ_id, y_one, x_one, Nat.one_ne_zero, if_false, Prod.ext_iff]
    simp only [one_ne_zero, ↓reduceIte, SimplicialJoin, FaceDisjointUnion, f_assoc, g_assoc]
    simp only [y_one]
    simp only [one_ne_zero, ↓reduceIte, and_self, f_assoc, g_assoc]

    rw [Set.mem_singleton_iff] at t_empty
    subst t_empty
    choose u_eq_st u_ne using u_eq_st
    subst u_eq_st
    rw [faceDisjoint_mem_iff] at x_in_u
    cases' x_in_u with x_in_s contra
    choose x1_in_s x2_zero using x_in_s
    simp only [x2_zero]
    simp only [↓reduceIte, SimplicialJoin, FaceDisjointUnion, f_assoc, g_assoc]
    have x_in_XY : x ∈ (X ⋆ Y).vertices :=
    by
      rw [vertex_iff_in_face]
      use s ⊔ₛ ∅; constructor
      rw [simplicialJoin_mem]
      use s; constructor; assumption
      use ∅; constructor
      rw [Set.mem_union]
      right; apply Set.mem_singleton
      constructor; rfl
      rw [ne_eq, faceDisjoint_empty, not_and_or]
      left; apply Finset.ne_empty_of_mem x1_in_s
      rw [faceDisjoint_mem_iff]
      left; constructor <;> assumption
    specialize gφ_id x_in_XY
    simp only [gφ_id, SimplicialJoinAssocForwardAux, x2_zero]
    simp only [↓reduceIte, f_assoc, g_assoc]

    choose contra x2_one using contra
    contradiction

def SimplicialJoinCommMap : E × 𝕜 → E × 𝕜 := fun x : E × 𝕜 => if x.snd = 0 then (x.fst, 1) else (x.fst, 0)

theorem simplicialJoin_comm_simplicial
  : IsSimplicialMap (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) (Y ⋆ X) SimplicialJoinCommMap :=
by
  simp only [IsSimplicialMap, SimplicialJoin, Set.mem_diff, Set.mem_setOf]
  intro u u_in_XY
  choose u_in_XY u_ne using u_in_XY
  choose s s_in_X t t_in_Y st_eq_u using u_in_XY
  constructor
  use t; constructor; assumption
  use s; constructor; assumption
  simp only [Finset.ext_iff]
  intro x; constructor
  · intro x_in_ts
    rw [faceDisjoint_mem_iff] at x_in_ts
    rw [Finset.mem_image]
    cases' x_in_ts with x_in_t x_in_s
    choose x_in_t x_zero using x_in_t
    use(x.fst, 1); constructor
    rw [← st_eq_u, faceDisjoint_mem_iff_right]
    assumption
    simp only [SimplicialJoinCommMap, Nat.one_ne_zero]
    simp only [one_ne_zero, ↓reduceIte]
    simp only [← x_zero, Prod.ext_iff]
    choose x_in_s x_one using x_in_s
    use(x.fst, 0); constructor
    rw [← st_eq_u, faceDisjoint_mem_iff_left]
    assumption

    simp only [SimplicialJoinCommMap, eq_self_iff_true, ↓reduceIte]
    simp only [← x_one, Prod.ext_iff]
  · intro x_in_img
    rw [Finset.mem_image] at x_in_img
    rw [faceDisjoint_mem_iff]
    choose y y_in_u fy_eq_x using x_in_img
    revert fy_eq_x
    simp only [SimplicialJoinCommMap]
    split_ifs
    intro y_one_x
    simp only [Prod.ext_iff, Prod.fst, Prod.snd] at y_one_x
    choose y_eq_x x_one using y_one_x
    rw [@comm _ Eq] at x_one
    rw [← st_eq_u, faceDisjoint_mem_iff] at y_in_u
    cases' y_in_u with y_in_s contra
    choose y_in_s y_zero using y_in_s
    rw [y_eq_x] at y_in_s
    right; constructor <;> assumption
    choose y_in_t contra using contra
    have H : y.snd ≠ 0 := by simp only [contra, ne_eq, one_ne_zero, not_false_eq_true]
    contradiction
    intro y_zero_x
    simp only [Prod.ext_iff, Prod.fst, Prod.snd] at y_zero_x
    choose y_eq_x x_zero using y_zero_x
    rw [@comm _ Eq] at x_zero
    rw [← st_eq_u, faceDisjoint_mem_iff] at y_in_u
    cases' y_in_u with contra y_in_t
    choose y_in_s contra using contra
    contradiction
    choose y_in_t y_one using y_in_t
    rw [y_eq_x] at y_in_t
    left; constructor <;> assumption

  rw [Set.mem_singleton_iff] at ⊢ u_ne
  rw [Finset.image_eq_empty]
  assumption

theorem simplicialJoin_comm : (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) ≅ (Y ⋆ X : AbstractSimplicialComplex (E × 𝕜)) := by
  let f : SimplicialMap (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)) (Y ⋆ X) :=
    SimplicialMap.mk SimplicialJoinCommMap simplicialJoin_comm_simplicial
  let g : SimplicialMap (Y ⋆ X : AbstractSimplicialComplex (E × 𝕜)) (X ⋆ Y) :=
    SimplicialMap.mk SimplicialJoinCommMap simplicialJoin_comm_simplicial
  unfold IsSimpliciallyIso
  use f
  unfold IsSimplicialIso
  use g
  unfold IsInverseSimplicialIso
  constructor <;>
    · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
      intro x x_in_XY
      rw [simplicialJoin_mem_vertices] at x_in_XY
      simp only [f, g, SimplicialMap.comp, SimplicialJoinCommMap, id, Function.comp_apply]
      cases' x_in_XY with x_in_X x_in_Y
      choose x_in_X x_zero using x_in_X
      simp only [x_zero, eq_self_iff_true, if_true, Nat.one_ne_zero]
      simp only [one_ne_zero, ↓reduceIte, g, f]
      simp only [← x_zero, Prod.ext_iff, Prod.fst, Prod.snd]
      choose x_in_Y x_one using x_in_Y
      simp only [x_one, eq_self_iff_true, if_true, Nat.one_ne_zero]
      simp only [one_ne_zero, ↓reduceIte, g, f]
      simp only [← x_one, Prod.ext_iff, Prod.fst, Prod.snd]

def SimplicialJoinBotIsoIdForwardMap : E × 𝕜 → E := fun x : E × 𝕜 => x.fst

theorem simplicialJoin_bot_iso_id_forward_simplicial
  : IsSimplicialMap (X ⋆ ⊥ : AbstractSimplicialComplex (E × 𝕜)) X SimplicialJoinBotIsoIdForwardMap :=
by
  simp only [IsSimplicialMap, AbstractSimplicialComplex.hasBot]
  intro u u_in_X_empty
  rw [simplicialJoin_mem] at u_in_X_empty
  choose s s_in_X t t_in_empty st_eq_u using u_in_X_empty
  simp only [Set.union_singleton, insert_empty_eq, Set.mem_singleton_iff] at t_in_empty
  simp only [t_in_empty, FaceDisjointUnion, Finset.empty_product, Finset.union_empty] at st_eq_u
  choose st_eq_u u_ne using st_eq_u
  simp only [st_eq_u]
  have s_img : Finset.image SimplicialJoinBotIsoIdForwardMap (s ×ˢ {(0 : 𝕜)}) = s :=
    by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro x
    constructor
    intro x_in_img
    choose y y_in_prod proj_y_x using x_in_img
    rw [Finset.mem_product] at y_in_prod
    choose y_in_s y_zero using y_in_prod
    rw [← proj_y_x]
    assumption
    intro x_in_s
    use(x, 0); constructor
    simp only [Finset.mem_product, Prod.fst, Prod.snd]
    constructor
    assumption
    apply Finset.mem_singleton_self
    simp only [SimplicialJoinBotIsoIdForwardMap, Prod.fst]
  cases' s_in_X with s_in_X contra
  rw [← s_img] at s_in_X
  assumption

  rw [Set.mem_singleton_iff] at contra
  subst contra
  rw [Finset.empty_product] at st_eq_u
  contradiction

def SimplicialJoinBotIsoIdLeftInverseMap : E → E × 𝕜 := fun x : E => (x, 0)

theorem simplicialJoin_bot_iso_id_inverse_simplicial
  : IsSimplicialMap X (X ⋆ ⊥ : AbstractSimplicialComplex (E × 𝕜)) SimplicialJoinBotIsoIdLeftInverseMap :=
by
  simp only [IsSimplicialMap]
  intro u u_in_X
  simp only [SimplicialJoin, AbstractSimplicialComplex.hasBot, Set.mem_diff, Set.mem_setOf]
  constructor
  use u; constructor
  rw [Set.mem_union]; left; assumption
  use ∅; constructor
  rw [Set.mem_union]; right; apply Set.mem_singleton
  have u_img : Finset.image SimplicialJoinBotIsoIdLeftInverseMap u = u ×ˢ {(0 : 𝕜)} :=
  by
    simp only [SimplicialJoinBotIsoIdLeftInverseMap, Finset.ext_iff, Finset.mem_image, Finset.mem_product]
    intro x
    constructor
    intro x_in_img
    choose y y_in_u inj_y_x using x_in_img
    simp only [Prod.ext_iff, Prod.fst, Prod.snd] at inj_y_x
    choose y_eq_x x_zero using inj_y_x
    rw [@comm _ Eq, ← Finset.mem_singleton] at x_zero
    rw [y_eq_x] at y_in_u
    constructor <;> assumption
    intro x_in_prod
    choose x_in_u x_zero using x_in_prod
    rw [Finset.mem_singleton, @comm _ Eq] at x_zero
    use x.fst; constructor; assumption
    simp only [Prod.ext_iff, Prod.fst, Prod.snd]
    constructor; trivial; assumption
  simp only [u_img, FaceDisjointUnion, Finset.empty_product, Finset.union_empty]

  rw [Set.mem_singleton_iff, Finset.image_eq_empty]
  revert u_in_X
  contrapose
  rw [not_not]
  intro u_empty
  rw [u_empty]
  apply X.empty_notMem

theorem simplicialJoin_bot_iso_id : (X ⋆ ⊥ : AbstractSimplicialComplex (E × 𝕜)) ≅ X := by
  let f : SimplicialMap (X ⋆ ⊥ : AbstractSimplicialComplex (E × 𝕜)) X :=
    SimplicialMap.mk SimplicialJoinBotIsoIdForwardMap simplicialJoin_bot_iso_id_forward_simplicial
  let g : SimplicialMap X (X ⋆ ⊥ : AbstractSimplicialComplex (E × 𝕜)) :=
    SimplicialMap.mk SimplicialJoinBotIsoIdLeftInverseMap simplicialJoin_bot_iso_id_inverse_simplicial
  unfold IsSimpliciallyIso
  use f
  unfold IsSimplicialIso
  use g
  unfold IsInverseSimplicialIso
  constructor
  · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
    intro x x_in_X_empty
    rw [simplicialJoin_mem_vertices] at x_in_X_empty
    simp only [f, g, SimplicialJoinBotIsoIdForwardMap]
    simp only [SimplicialMap.comp, Function.comp_apply, id, Prod.ext_iff, Prod.fst, Prod.snd]
    cases' x_in_X_empty with x_in_X contra
    choose x_in_X x_zero using x_in_X
    rw [@comm _ Eq] at x_zero
    constructor
    rfl
    assumption
    choose contra x_one using contra
    simp only [SimplicialJoinBotIsoIdLeftInverseMap]
    simp only [AbstractSimplicialComplex.vertices, Set.mem_setOf, AbstractSimplicialComplex.hasBot] at contra
    contradiction
  · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
    intro x x_in_X
    simp only [f, g, SimplicialMap.comp, Function.comp_apply, id]
    simp only [SimplicialJoinBotIsoIdForwardMap, SimplicialJoinBotIsoIdLeftInverseMap]

theorem simplicialJoin_bot_iso_right_forward_simplicial
  : IsSimplicialMap (⊥ ⋆ X : AbstractSimplicialComplex (E × 𝕜)) X SimplicialJoinBotIsoIdForwardMap :=
by
  simp only [IsSimplicialMap, SimplicialJoinBotIsoIdForwardMap, AbstractSimplicialComplex.hasBot]
  intro u u_in_empty_X
  rw [simplicialJoin_mem] at u_in_empty_X
  choose s s_in_empty t t_in_X st_eq_u using u_in_empty_X
  simp only [AbstractSimplicialComplex.hasBot, Set.mem_union, Set.mem_singleton_iff] at s_in_empty
  cases' s_in_empty with contra s_in_empty
  contradiction
  simp only [s_in_empty, FaceDisjointUnion, Finset.empty_product, Finset.empty_union] at st_eq_u
  simp only [st_eq_u]
  have t_img : Finset.image SimplicialJoinBotIsoIdForwardMap (t ×ˢ {(1 : 𝕜)}) = t :=
    by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro x
    constructor
    intro x_in_img
    choose y y_in_prod proj_y_x using x_in_img
    rw [Finset.mem_product] at y_in_prod
    choose y_in_s y_zero using y_in_prod
    rw [← proj_y_x]
    assumption
    intro x_in_t
    use(x, 1); constructor
    simp only [Finset.mem_product, Prod.fst, Prod.snd]
    constructor
    assumption
    apply Finset.mem_singleton_self
    simp only [SimplicialJoinBotIsoIdForwardMap, Prod.fst]
  simp only [SimplicialJoinBotIsoIdForwardMap, t_img]
  cases' t_in_X with t_in_X contra
  assumption

  rw [Set.mem_singleton_iff] at contra
  subst contra
  choose st_eq_u u_ne using st_eq_u
  rw [Finset.empty_product] at st_eq_u
  contradiction

def SimplicialJoinBotIsoIdRightInverseMap : E → E × 𝕜 := fun x : E => (x, 1)

theorem simplicialJoin_bot_iso_right_inverse_simplicial
  : IsSimplicialMap X (⊥ ⋆ X : AbstractSimplicialComplex (E × 𝕜)) SimplicialJoinBotIsoIdRightInverseMap :=
by
  simp only [IsSimplicialMap]
  intro u u_in_X
  simp only [SimplicialJoin, AbstractSimplicialComplex.hasBot, Set.mem_diff, Set.mem_setOf]
  constructor
  use ∅; constructor
  rw [Set.mem_union]; right; apply Set.mem_singleton
  use u; constructor
  rw [Set.mem_union]; left; assumption
  have u_img : Finset.image SimplicialJoinBotIsoIdRightInverseMap u = u ×ˢ {(1 : 𝕜)} :=
  by
    simp only [SimplicialJoinBotIsoIdRightInverseMap, Finset.ext_iff, Finset.mem_image,
      Finset.mem_product]
    intro x
    constructor
    intro x_in_img
    choose y y_in_u inj_y_x using x_in_img
    simp only [Prod.ext_iff, Prod.fst, Prod.snd] at inj_y_x
    choose y_eq_x x_zero using inj_y_x
    rw [@comm _ Eq, ← Finset.mem_singleton] at x_zero
    rw [y_eq_x] at y_in_u
    constructor <;> assumption
    intro x_in_prod
    choose x_in_u x_zero using x_in_prod
    rw [Finset.mem_singleton, @comm _ Eq] at x_zero
    use x.fst; constructor; assumption
    simp only [Prod.ext_iff, Prod.fst, Prod.snd]
    constructor; trivial; assumption
  simp only [u_img, FaceDisjointUnion, Finset.empty_product, Finset.empty_union]

  rw [Set.mem_singleton_iff, Finset.image_eq_empty]
  revert u_in_X
  contrapose
  rw [not_not]
  intro u_empty
  rw [u_empty]
  apply X.empty_notMem

theorem simplicialJoin_bot_iso_right : (⊥ ⋆ X : AbstractSimplicialComplex (E × 𝕜)) ≅ X := by
  let f : SimplicialMap (⊥ ⋆ X : AbstractSimplicialComplex (E × 𝕜)) X :=
    SimplicialMap.mk SimplicialJoinBotIsoIdForwardMap simplicialJoin_bot_iso_right_forward_simplicial
  let g : SimplicialMap X (⊥ ⋆ X : AbstractSimplicialComplex (E × 𝕜)) :=
    SimplicialMap.mk SimplicialJoinBotIsoIdRightInverseMap simplicialJoin_bot_iso_right_inverse_simplicial
  unfold IsSimpliciallyIso
  use f
  unfold IsSimplicialIso
  use g
  unfold IsInverseSimplicialIso
  constructor
  · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
    intro x x_in_empty_X
    rw [simplicialJoin_mem_vertices] at x_in_empty_X
    simp only [f, g, SimplicialJoinBotIsoIdForwardMap, SimplicialJoinBotIsoIdRightInverseMap]
    simp only [SimplicialMap.comp, Function.comp_apply, id, Prod.ext_iff, Prod.fst, Prod.snd]
    cases' x_in_empty_X with contra x_in_X
    choose contra x_one using contra
    simp only [AbstractSimplicialComplex.vertices, Set.mem_setOf, AbstractSimplicialComplex.hasBot] at contra
    contradiction
    choose x_in_X x_zero using x_in_X
    rw [@comm _ Eq] at x_zero
    constructor
    rfl
    assumption
  · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
    intro x x_in_X
    simp only [f, g, SimplicialMap.comp, Function.comp_apply, id]
    simp only [SimplicialJoinBotIsoIdForwardMap, SimplicialJoinBotIsoIdRightInverseMap]

theorem simplicialJoin_subcomplex
    (X_subcomp_Z : X ⊆ Z)
    (Y_subcomp_W : Y ⊆ W)
  : X ⋆ Y ⊆ (Z ⋆ W : AbstractSimplicialComplex (E × 𝕜)) :=
by
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex] at *
  simp only [SimplicialJoin]
  simp only [Set.subset_def] at *
  intro s s_in_XY
  simp only [Set.mem_diff, Set.mem_setOf] at *
  choose s_in_XY s_ne using s_in_XY
  choose t Ht u Hu tu_eq_s using s_in_XY

  rw [Set.mem_union] at Ht Hu
  cases' Ht with Ht t_empty <;>
  cases' Hu with Hu u_empty

  specialize X_subcomp_Z t Ht
  specialize Y_subcomp_W u Hu
  constructor
  use t; constructor
  rw [Set.mem_union]; left; apply X_subcomp_Z
  use u; constructor
  rw [Set.mem_union]; left; apply Y_subcomp_W
  apply tu_eq_s
  assumption

  rw [Set.mem_singleton_iff] at u_empty
  subst u_empty
  specialize X_subcomp_Z t Ht
  constructor
  use t; constructor
  rw [Set.mem_union]; left; assumption
  use ∅; constructor
  rw [Set.mem_union]; right; apply Set.mem_singleton
  assumption
  assumption

  rw [Set.mem_singleton_iff] at t_empty
  subst t_empty
  specialize Y_subcomp_W u Hu
  constructor
  use ∅; constructor
  rw [Set.mem_union]; right; apply Set.mem_singleton
  use u; constructor
  rw [Set.mem_union]; left; assumption
  assumption
  assumption

  rw [Set.mem_singleton_iff] at s_ne t_empty u_empty
  subst t_empty u_empty
  simp only [FaceDisjointUnion, Finset.product_singleton, Finset.map_empty,
    Finset.union_idempotent] at tu_eq_s
  rw [@comm _ Eq] at tu_eq_s
  contradiction

-- Lemma 2.1, p.5
theorem dim_of_join
    [Fintype X.faces] [Fintype Y.faces]
  : (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).dim = X.dim + Y.dim + 1 :=
by
  set k := (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).dim
  set n := X.dim
  set m := Y.dim
  rw [le_antisymm_iff]
  constructor
  · have k_dim : k ∈ Finset.image face_dim (X ⋆ Y : AbstractSimplicialComplex (E × 𝕜)).faces.toFinset ∪ {-1} :=
    by
      simp only [k, AbstractSimplicialComplex.dim]
      apply Finset.max'_mem
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, Set.mem_toFinset] at k_dim
    cases' k_dim with k_dim k_empty

    choose u u_in_XY dim_u_k using k_dim
    rw [simplicialJoin_mem] at u_in_XY
    choose s s_in_X t t_in_Y u_eq_st using u_in_XY
    choose u_eq_st u_ne using u_eq_st
    rw [← dim_u_k, face_dim, u_eq_st, faceDisjoint_card]
    have st_dim : ↑(s.card + t.card) - 1 = face_dim s + face_dim t + 1 := by simp; linarith
    rw [st_dim]
    have s_le_dim : face_dim s ≤ X.dim :=
    by
      apply Finset.le_max'
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, Set.mem_toFinset]
      rw [Set.mem_union, Set.mem_singleton_iff] at s_in_X
      cases' s_in_X with s_in_X s_empty

      left; use s
      right; subst s_empty
      simp only [face_dim, Finset.card_empty, CharP.cast_eq_zero, zero_sub, Int.reduceNeg, k]
    have t_le_dim : face_dim t ≤ Y.dim :=
    by
      apply Finset.le_max'
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, Set.mem_toFinset]
      rw [Set.mem_union, Set.mem_singleton_iff] at t_in_Y
      cases' t_in_Y with t_in_Y t_empty

      left; use t
      right; subst t_empty
      simp only [face_dim, Finset.card_empty, CharP.cast_eq_zero, zero_sub, Int.reduceNeg, k]
    linarith

    have Hn : -1 ≤ n :=
    by
      simp only [n, AbstractSimplicialComplex.dim]
      apply Finset.le_max'
      rw [Finset.mem_union]
      right; apply Finset.mem_singleton_self
    have Hm : -1 ≤ m :=
    by
      simp only [m, AbstractSimplicialComplex.dim]
      apply Finset.le_max'
      rw [Finset.mem_union]
      right; apply Finset.mem_singleton_self
    linarith
  · have n_dim : n ∈ Finset.image face_dim X.faces.toFinset ∪ {-1} :=
    by
      apply Finset.max'_mem
    have m_dim : m ∈ Finset.image face_dim Y.faces.toFinset ∪ {-1} :=
    by
      apply Finset.max'_mem
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_singleton, Set.mem_toFinset] at n_dim m_dim
    cases' n_dim with n_dim n_empty <;>
    cases' m_dim with m_dim m_empty

    choose s s_in_X dim_s_n using n_dim
    choose t t_in_Y dim_t_m using m_dim
    have st_dim : ↑(s.card + t.card) - 1 = face_dim s + face_dim t + 1 := by simp; linarith
    simp only [← dim_s_n, ← dim_t_m, ← st_dim, ← faceDisjoint_card]
    apply Finset.le_max'
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, Set.mem_toFinset]
    left; use s ⊔ₛ t; constructor
    rw [simplicialJoin_mem]
    use s; constructor
    rw [Set.mem_union]; left; assumption
    use t; constructor
    rw [Set.mem_union]; left; assumption
    constructor; rfl
    rw [ne_eq, faceDisjoint_empty, not_and_or]
    left
    revert s_in_X
    contrapose
    rw [not_not]
    intro s_empty
    rw [s_empty]
    apply X.empty_notMem
    unfold face_dim
    rw [faceDisjoint_card]

    choose s s_in_X dim_s_n using n_dim
    simp only [← dim_s_n, m_empty, Int.reduceNeg, neg_add_cancel_right, ge_iff_le, n, m, k]
    apply Finset.le_max'
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, Set.mem_toFinset]
    left; use s ⊔ₛ ∅; constructor
    rw [simplicialJoin_mem]
    use s; constructor
    rw [Set.mem_union]; left; assumption
    use ∅; constructor
    rw [Set.mem_union]; right; apply Set.mem_singleton
    constructor; rfl
    rw [ne_eq, faceDisjoint_empty, not_and_or]
    left
    revert s_in_X
    contrapose
    rw [not_not]
    intro s_empty
    rw [s_empty]
    apply X.empty_notMem
    unfold face_dim
    rw [faceDisjoint_card, Finset.card_empty]
    simp only [add_zero, n, m, k]

    choose t t_in_Y dim_t_m using m_dim
    simp only [← dim_t_m, n_empty, Int.reduceNeg, neg_add_cancel_comm, ge_iff_le, n, m, k]
    apply Finset.le_max'
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, Set.mem_toFinset]
    left; use ∅ ⊔ₛ t; constructor
    rw [simplicialJoin_mem]
    use ∅; constructor
    rw [Set.mem_union]; right; apply Set.mem_singleton
    use t; constructor
    rw [Set.mem_union]; left; assumption
    constructor; rfl
    rw [ne_eq, faceDisjoint_empty, not_and_or]
    right
    revert t_in_Y
    contrapose
    rw [not_not]
    intro t_empty
    rw [t_empty]
    apply Y.empty_notMem
    unfold face_dim
    rw [faceDisjoint_card, Finset.card_empty]
    simp only [zero_add, n, m, k]

    simp only [n_empty, m_empty]
    simp only [Int.reduceNeg, Int.reduceAdd, ge_iff_le, n, m, k]
    apply Finset.le_max'
    rw [Finset.mem_union]
    right; apply Finset.mem_singleton_self
