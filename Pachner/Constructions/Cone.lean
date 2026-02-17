import Pachner.Subcomplex.Link
import Pachner.Constructions.Join

variable {E : Type _}
variable [DecidableEq E]

@[simp]
def IsNegOneSphere
    {X : AbstractSimplicialComplex E}
    {s : Finset E}
    (Y : AbstractSimplicialComplex E)
    (Y_link_X : Y = Lk(X, s))
  : Prop := Y = ⊥

@[simp]
def NegOneBall (x : E) : AbstractSimplicialComplex E :=
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

instance NegOneBall.fintype (x : E) : Fintype (NegOneBall x).faces :=
by
  simp only [NegOneBall]
  apply Set.fintypeSingleton

theorem negOneBall_dim (x : E) : (NegOneBall x).dim = 0 :=
by
  simp only [AbstractSimplicialComplex.dim, NegOneBall]
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
  simp only [mBall, Finset.coe_sdiff]
  have fin_power : Fintype ↑(Lk(X, s).vertices).toFinset.powerset :=
  by
    apply FinsetCoe.fintype
  apply Set.fintypeDiff


-- The cone of a complex.

variable {F : Type _}
variable [AddCommGroup E] [DecidableEq F] [AddCommGroup F]
variable {𝕜 : Type _}
variable [DecidableEq 𝕜] [Ring 𝕜] [Nontrivial 𝕜]
variable {X : AbstractSimplicialComplex E} {Y : AbstractSimplicialComplex F} {x : E} {y : F}


@[simp]
def Cone
  (X : AbstractSimplicialComplex E)
  (x : E)
  (x_nin_X : x ∉ X.vertices) -- Ensure that we use a new point for projection purposes.
: AbstractSimplicialComplex (E × 𝕜) := (NegOneBall x) ⋆ X

notation "Cone(" X ", " x ")" => Cone X x

instance Cone.Fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (x : E)
    (x_nin_X : x ∉ X.vertices)
  : Fintype ((Cone(X, x) x_nin_X) : AbstractSimplicialComplex (E × 𝕜)).faces :=
by
  simp only [Cone]
  apply SimplicialJoin.fintype

def ConeIsoMap
    (y : F)
    (f : E → F)
  : E × 𝕜 → F × 𝕜 :=
    fun x : E × 𝕜 =>
      if x.snd = 0 then (y, 0) else (f x.fst, x.snd)

theorem cone_simplicialMap
    (x_nin_X : x ∉ X.vertices)
    (y_nin_Y : y ∉ Y.vertices)
    (f : SimplicialMap X Y)
  : IsSimplicialMap (Cone(X, x) x_nin_X) (Cone(Y, y) y_nin_Y : AbstractSimplicialComplex (F × 𝕜)) (ConeIsoMap y f.map) :=
by
  simp only [IsSimplicialMap, Cone, NegOneBall, simplicialJoin_mem]
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
  simp only [u_eq_st, s_eq_x, SimplexDisjointUnion, Finset.image_union, ConeIsoMap, Finset.ext_iff]
  intro v
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_singleton]
  constructor
  · intro v_in_img
    cases' v_in_img with v_in_lhs v_in_rhs
    choose w w_in_lhs w_eq_v using v_in_lhs
    choose w_eq_x w_zero using w_in_lhs
    revert w_eq_v
    unfold ConeIsoMap
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
    unfold ConeIsoMap
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
    unfold ConeIsoMap
    simp only [eq_self_iff_true, if_true, Prod.ext_iff]
    rw [@comm _ Eq] at v_eq_y v_zero
    constructor <;> assumption
    choose w_eq_v v_one using v_in_rhs
    choose w w_in_t w_eq_v using w_eq_v
    right; use(w, 1); constructor
    simp only [Prod.fst, Prod.snd]
    constructor; assumption; trivial
    unfold ConeIsoMap
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
  simp only [u_eq_st, s_empty, SimplexDisjointUnion, Finset.image_union, ConeIsoMap, Finset.ext_iff]
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
    unfold ConeIsoMap
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
    unfold ConeIsoMap
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
  unfold SimplexDisjointUnion at u_eq_st
  simp at u_eq_st
  simp [u_eq_st]

theorem cone_simplicialIso
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
    SimplicialMap.mk (ConeIsoMap y f.map) (cone_simplicialMap x_nin_X y_nin_Y f)
  let g_cone : SimplicialMap (Cone(Y, y) y_nin_Y) (Cone(X, x) x_nin_X : AbstractSimplicialComplex (E × 𝕜)) :=
    SimplicialMap.mk (ConeIsoMap x g.map) (cone_simplicialMap y_nin_Y x_nin_X g)
  use f_cone; use g_cone
  unfold IsInverseSimplicialIso at gf_inv ⊢
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply, id] at gf_inv ⊢
  choose gf_id fg_id using gf_inv
  constructor
  · intro z z_in_X_cone
    rw [vertex_iff_in_simplex] at z_in_X_cone
    choose u u_in_cone z_in_u using z_in_X_cone
    simp only [Cone, NegOneBall, SimplicialJoin] at u_in_cone
    simp only [Set.mem_diff, Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff] at u_in_cone
    choose u_in_cone u_nonempty using u_in_cone
    choose s s_in_ball t t_in_x st_eq_u using u_in_cone
    rw [← st_eq_u, simplexDisjoint_mem_iff] at z_in_u
    cases' z_in_u with z_in_ball z_in_t
    cases' s_in_ball with s_eq_x contra
    rw [s_eq_x, Finset.mem_singleton] at z_in_ball
    choose z_eq_x z_zero using z_in_ball
    simp only [ConeIsoMap, Prod.ext_iff, z_zero, eq_self_iff_true, if_true, f_cone, g_cone]
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
    simp [ConeIsoMap, z_one, Nat.one_ne_zero, if_false, Prod.ext_iff, f_cone, g_cone]
    assumption
  · intro z z_in_Y_cone
    rw [vertex_iff_in_simplex] at z_in_Y_cone
    choose u u_in_cone z_in_u using z_in_Y_cone
    simp only [Cone, NegOneBall, SimplicialJoin] at u_in_cone
    simp only [Set.mem_diff, Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff] at u_in_cone
    choose u_in_cone u_nonempty using u_in_cone
    choose s s_in_ball t t_in_x st_eq_u using u_in_cone
    rw [← st_eq_u, simplexDisjoint_mem_iff] at z_in_u
    cases' z_in_u with z_in_ball z_in_t
    cases' s_in_ball with s_eq_x contra
    rw [s_eq_x, Finset.mem_singleton] at z_in_ball
    choose z_eq_x z_zero using z_in_ball
    simp only [ConeIsoMap, Prod.ext_iff, z_zero, eq_self_iff_true, if_true, f_cone, g_cone]
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
    simp [ConeIsoMap, z_one, Nat.one_ne_zero, if_false, Prod.ext_iff, f_cone, g_cone]
    assumption

theorem cone_dim
    [Fintype X.faces]
    (x_nin_X : x ∉ X.vertices)
  : (Cone(X, x) x_nin_X : AbstractSimplicialComplex (E × 𝕜)).dim = X.dim + 1 :=
by
  dsimp only [Cone]
  rw [dim_of_join, negOneBall_dim]
  simp only [zero_add]
