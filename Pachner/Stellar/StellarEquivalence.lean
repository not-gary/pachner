import Pachner.Stellar.StellarCoercion

variable
  {E F 𝕜 : Type _}
  [DecidableEq E] [DecidableEq F]
  [DecidableEq 𝕜] [Ring 𝕜] [Nontrivial 𝕜]
  {X Y Z : AbstractSimplicialComplex E} {s t : Finset E} {x y : E} {f : E → F}

@[simp]
def StellarMove : AbstractSimplicialComplex E → AbstractSimplicialComplex E → Prop :=
  fun X Y : AbstractSimplicialComplex E =>
  (∃ (t : Finset E) (Ht : t ∈ Y.faces) (y : E) (Hy : y ∉ Y.vertices), X ≅ σ(Y, t, y; 𝕜, Ht, Hy)) ∨
    (∃ (s : Finset E) (Hs : s ∈ X.faces) (x : E) (Hx : x ∉ X.vertices), Y ≅ σ(X, s, x; 𝕜, Hs, Hx)) ∨
      X ≅ Y

notation X " ≅ₛₜₘ[" 𝕜 "] " Y : 50 => @StellarMove _ 𝕜 _ _ _ _ X Y

section SynthOrder
set_option synthInstance.checkSynthOrder false

noncomputable instance StellarMove.Weld.Fintype
    (X Y : AbstractSimplicialComplex E) [Fintype X.faces]
    (X_weld_Y : ∃ (t : Finset E) (Ht : t ∈ Y.faces) (y : E) (Hy : y ∉ Y.vertices), X ≅ σ(Y, t, y; 𝕜, Ht, Hy))
  : Fintype Y.faces :=
by
  choose t t_in_Y y y_nin_Y X_weld_Y using X_weld_Y
  apply
    @StellarSubdivision.FintypeConverse _ 𝕜 _ _ _ _ Y t y t_in_Y y_nin_Y
      (IsSimpliciallyIso.Fintype X σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) X_weld_Y)

noncomputable instance StellarMove.Subdiv.Fintype
    (X Y : AbstractSimplicialComplex E)
    [X_fin : Fintype X.faces]
    (X_subdiv_Y : ∃ (s : Finset E) (Hs : s ∈ X.faces) (x : E) (Hx : x ∉ X.vertices), Y ≅ σ(X, s, x; 𝕜, Hs, Hx))
  : Fintype Y.faces :=
by
  choose s s_in_X x x_nin_X X_subdiv_Y using X_subdiv_Y
  rw [simplicialIso_symm] at X_subdiv_Y
  apply
    @IsSimpliciallyIso.Fintype _ _ _ _ σ(X, s, x; 𝕜, s_in_X, x_nin_X)
      (@StellarSubdivision.fintype _ 𝕜 _ _ _ _ X X_fin s x s_in_X x_nin_X) Y X_subdiv_Y

noncomputable instance StellarMove.Fintype
    (X Y : AbstractSimplicialComplex E) [Fintype X.faces]
    (X_move_Y : X ≅ₛₜₘ[𝕜] Y)
  : Fintype Y.faces :=
by
  simp only [StellarMove] at X_move_Y
  by_cases X_weld_Y : ∃ (t : Finset E) (Ht : t ∈ Y.faces) (y : E) (Hy : y ∉ Y.vertices), X ≅ σ(Y, t, y; 𝕜, Ht, Hy)
  apply StellarMove.Weld.Fintype X Y X_weld_Y
  by_cases X_subdiv_Y : ∃ (s : Finset E) (Hs : s ∈ X.faces) (x : E) (Hx : x ∉ X.vertices), Y ≅ σ(X, s, x; 𝕜, Hs, Hx)
  apply StellarMove.Subdiv.Fintype X Y X_subdiv_Y
  by_cases X_iso_Y : X ≅ Y
  apply IsSimpliciallyIso.Fintype X Y X_iso_Y
  have contra : ¬X ≅ₛₜₘ[𝕜] Y :=
    by
    simp only [StellarMove, not_or]
    constructor; assumption
    constructor; assumption
    assumption
  contradiction

end SynthOrder

theorem stellarMove_preserves_dim
    [Fintype X.faces]
    [Fintype Y.faces]
    (X_move_Y : X ≅ₛₜₘ[𝕜] Y)
  : X.dim = Y.dim :=
by
  simp only [StellarMove] at X_move_Y
  cases' X_move_Y with Y_subdiv_X X_move_Y
  choose t t_in_Y y y_nin_Y Y_subdiv_X using Y_subdiv_X
  rw [simplicialIso_preserves_dim Y_subdiv_X]
  symm
  rw [@stellarSubdivision_dim _ 𝕜 _ _ _ _ Y t y _ t_in_Y y_nin_Y]
  rotate_left
  cases' X_move_Y with X_subdiv_Y X_iso_Y
  choose s s_in_X x x_nin_X X_subdiv_Y using X_subdiv_Y
  rw [simplicialIso_preserves_dim X_subdiv_Y]
  rw [@stellarSubdivision_dim _ 𝕜 _ _ _ _ X s x _ s_in_X x_nin_X]
  rotate_left
  rw [simplicialIso_preserves_dim X_iso_Y]
  all_goals
    unfold AbstractSimplicialComplex.dim
    apply le_antisymm <;>
      · apply Finset.max'_le
        intro z z_in_img
        simp only [Finset.mem_image, Set.mem_toFinset, Finset.mem_union] at z_in_img
        cases' z_in_img with z_in_img z_negative

        choose u u_in_K dim_u_z using z_in_img
        apply Finset.le_max'
        simp only [Finset.mem_image, Set.mem_toFinset, Finset.mem_union]
        left
        use u

        apply Finset.le_max'
        simp only [Finset.mem_image, Set.mem_toFinset, Finset.mem_union]
        right
        assumption

def StellarEquiv
    : AbstractSimplicialComplex E → AbstractSimplicialComplex E → Prop :=
  Relation.ReflTransGen (@StellarMove _ 𝕜 _ _ _ _)

notation X " ≅ₛₜ[" 𝕜 "] " Y : 50 => @StellarEquiv _ 𝕜 _ _ _ _ X Y

section SynthOrder
set_option synthInstance.checkSynthOrder false

noncomputable instance StellarEquiv.fintype
    (X Y : AbstractSimplicialComplex E)
    [Fintype X.faces]
    (X_eq_Y : X ≅ₛₜ[𝕜] Y)
  : Fintype Y.faces :=
by
  apply Set.Finite.fintype
  induction' X_eq_Y with K L X_eq_K K_move_L L_dec
  rw [Set.finite_def]
  constructor
  assumption
  rw [Set.finite_def]
  have K_fin : Fintype K.faces := by
    apply Set.Finite.fintype
    assumption
  constructor
  apply @StellarMove.Fintype _ 𝕜 _ _ _ _ K L _ K_move_L

end SynthOrder

theorem stellarEquiv_preserves_dim
    [X_fin : Fintype X.faces]
    (X_eq_Y : X ≅ₛₜ[𝕜] Y)
  : X.dim = @AbstractSimplicialComplex.dim _ Y (@StellarEquiv.fintype _ 𝕜 _ _ _ _ X Y X_fin X_eq_Y) :=
by
  induction' X_eq_Y with K L X_eq_K K_move_L H_ind
  · unfold AbstractSimplicialComplex.dim
    apply le_antisymm <;>
      · rw [Finset.max'_le_iff]
        intro y y_max
        apply Finset.le_max'
        simp only [Finset.mem_image, Set.mem_toFinset, Finset.mem_union] at y_max ⊢
        cases' y_max with y_max y_neg

        left
        choose s s_in_img dim_s_y using y_max
        use s

        right
        assumption
  · let K_fin : Fintype K.faces := by
        apply @StellarEquiv.fintype _ 𝕜 _ _ _ _ X K _ X_eq_K
    trans K.dim
    assumption

    let K_eq_L : K ≅ₛₜ[𝕜] L := by
        unfold StellarEquiv
        apply Relation.ReflTransGen.single
        assumption
    let L_fin : Fintype L.faces := by
        apply @StellarEquiv.fintype _ 𝕜 _ _ _ _ K L K_fin K_eq_L
    apply @stellarMove_preserves_dim _ 𝕜 _ _ _ _ K L K_fin L_fin
    assumption

@[refl]
theorem stellarEquiv_refl : X ≅ₛₜ[𝕜] X := Relation.ReflTransGen.refl

@[symm]
theorem stellarEquiv_symm : X ≅ₛₜ[𝕜] Y ↔ Y ≅ₛₜ[𝕜] X := by
  unfold StellarEquiv
  constructor <;>
    · apply Relation.ReflTransGen.symmetric
      rw [← swap_eq_iff]
      unfold StellarMove Function.swap
      apply funext; intro K
      apply funext; intro L
      simp only [eq_iff_iff]
      constructor
      · intro L_move_K
        cases' L_move_K with K_move_L L_move_K
        · right; left
          choose s Hs Hs_ne x Hx L_subdiv_K using K_move_L
          use s; use Hs; use Hs_ne; use x; use Hx
        · cases' L_move_K with L_move_K L_iso_K
          · left
            choose t Ht Ht_ne y Hy K_subdiv_L using L_move_K
            use t; use Ht; use Ht_ne; use y; use Hy
          · right; right
            rw [simplicialIso_symm]
            assumption
      · intro K_move_L
        cases' K_move_L with L_move_K K_move_L
        · right; left
          choose s Hs Hs_ne x Hx K_subdiv_L using L_move_K
          use s; use Hs; use Hs_ne; use x; use Hx
        · cases' K_move_L with K_move_L K_iso_L
          · left
            choose t Ht Ht_ne y Hy L_subdiv_K using K_move_L
            use t; use Ht; use Ht_ne; use y; use Hy
          · right; right
            rw [simplicialIso_symm]
            assumption

@[trans]
theorem stellarEquiv_trans : X ≅ₛₜ[𝕜] Y → Y ≅ₛₜ[𝕜] Z → X ≅ₛₜ[𝕜] Z := Relation.ReflTransGen.trans

theorem stellarEquiv_neg_trans : X ≅ₛₜ[𝕜] Y → ¬Y ≅ₛₜ[𝕜] Z → ¬X ≅ₛₜ[𝕜] Z := by
  intro X_eq_Y Y_neq_Z
  revert Y_neq_Z
  contrapose
  simp only [Classical.not_not]
  intro X_eq_Z
  rw [stellarEquiv_symm] at X_eq_Y
  revert X_eq_Y X_eq_Z
  apply stellarEquiv_trans

instance StellarEquiv.Trans
  : Trans
      (@StellarEquiv E 𝕜 _ _ _ _)
      (@StellarEquiv E 𝕜 _ _ _ _)
      (@StellarEquiv E 𝕜 _ _ _ _) where
    trans := Relation.ReflTransGen.trans

instance StellarEquiv_StellarMove_left.Trans
  : Trans
      (@StellarMove E 𝕜 _ _ _ _)
      (@StellarEquiv E 𝕜 _ _ _ _)
      (@StellarEquiv E 𝕜 _ _ _ _) where
    trans := Relation.ReflTransGen.head

instance StellarEquiv_StellarMove_right.Trans
  : Trans
      (@StellarEquiv E 𝕜 _ _ _ _)
      (@StellarMove E 𝕜 _ _ _ _)
      (@StellarEquiv E 𝕜 _ _ _ _) where
    trans := Relation.ReflTransGen.tail

instance StellarEquiv_SimplicialIso_left.Trans
  : Trans
      (@IsSimpliciallyIso E E _ _)
      (@StellarEquiv E 𝕜 _ _ _ _)
      (@StellarEquiv E 𝕜 _ _ _ _) where
    trans := (
by
  intro X Y Z X_iso_Y Y_eq_Z
  apply Relation.ReflTransGen.head _ Y_eq_Z
  simp only [StellarMove, X_iso_Y, or_true]
)

instance StellarEquiv_SimplicialIso_right.Trans
  : Trans
      (@StellarEquiv E 𝕜 _ _ _ _)
      (@IsSimpliciallyIso E E _ _)
      (@StellarEquiv E 𝕜 _ _ _ _) where
    trans := (
by
  intro X Y Z X_eq_Y Y_iso_Z
  apply Relation.ReflTransGen.tail X_eq_Y
  simp only [StellarMove, Y_iso_Z, or_true]
)

theorem stellarEquiv_preserves_iso : (X ≅ Y) → X ≅ₛₜ[𝕜] Y := by
  intro X_iso_Y
  calc X
    _ ≅ Y := X_iso_Y
    _ ≅ₛₜ[𝕜] Y := Relation.ReflTransGen.refl

theorem barycenter_injective_image : x ∉ X.vertices → Function.Injective f → f x ∉ (f ''ˢ X).vertices := by
  intro x_nin_X f_inj
  by_contra fx_in_X
  rw [simplicialImage_vertices] at fx_in_X
  have contra : x ∈ X.vertices :=
  by
    apply Set.InjOn.mem_of_mem_image
    apply @Function.Injective.injOn _ _ f _ Set.univ
    assumption
    apply Set.subset_univ
    apply Set.mem_univ
    assumption
  contradiction

theorem stellarSubdivision_injective_image_faces_left
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : (SimplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces ⊆
      σ(SimplicialImage f X, Finset.image f s, f x; 𝕜,
        by
          apply isSimplicialMap_onto_image
          assumption,
        barycenter_injective_image x_nin_X f_inj).faces :=
by
  rw [Set.subset_def]
  intro t t_in_img
  simp only [SimplicialImage, Set.mem_setOf] at t_in_img
  simp only [StellarSubdivision, SimplicialUnion, Set.mem_union] at t_in_img ⊢
  choose u u_in_subdiv fu_t using t_in_img
  cases' u_in_subdiv with u_in_star_comp u_in_join
  left
  simp only [StarComplement, Set.mem_sep_iff] at u_in_star_comp ⊢
  choose u_in_X s_nss_u using u_in_star_comp
  constructor
  simp only [SimplicialImage, Set.mem_setOf]
  use u
  rw [← fu_t]
  revert s_nss_u
  contrapose
  simp only [Classical.not_not, Finset.subset_iff]
  intro fs_ss_fu a a_in_s
  have fa_in_fs : f a ∈ Finset.image f s := by apply Finset.mem_image_of_mem f a_in_s
  specialize fs_ss_fu fa_in_fs
  rw [Function.Injective.mem_finset_image f_inj] at fs_ss_fu
  assumption
  right
  simp only [simplicialJoinProj_mem, Set.mem_union] at u_in_join ⊢
  choose u' u'_in_join u₁ u₁_in_link u_decomp u_ne using u_in_join

  cases' u'_in_join with u'_in_join u'_empty
  choose u₃ u₃_in_barycenter u₂ u₂_in_bd u'_decomp u'_ne using u'_in_join
  subst u'_decomp
  use Finset.image f (u₃ ∪ u₂); constructor

  left
  use Finset.image f u₃; constructor
  simp only [Simplex, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff] at u₃_in_barycenter ⊢
  cases' u₃_in_barycenter with u₃_eq_x u₃_empty

  rotate_left
  right
  rw [Set.mem_singleton_iff] at u₃_empty ⊢
  rw [u₃_empty]
  apply Finset.image_empty

  rotate_right
  choose u₃_eq_x u₃_ne using u₃_eq_x
  cases' u₃_eq_x with contra u₃_eq_x
  rw [Set.mem_singleton_iff] at u₃_ne
  contradiction

  left
  rw [u₃_eq_x]
  constructor; right
  apply Finset.image_singleton
  rw [Set.mem_singleton_iff, Finset.image_eq_empty]
  simp only [Finset.singleton_ne_empty, not_false_eq_true]

  use Finset.image f u₂; constructor
  simp only [FaceBoundary, Set.mem_union, Set.mem_insert_iff, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
    Set.mem_singleton_iff] at u₂_in_bd ⊢
  cases' u₂_in_bd with u₂_in_bd u₂_empty
  left
  choose u₂_ss_s u₂_ne_s using u₂_in_bd
  constructor
  apply Finset.image_subset_image
  assumption
  revert u₂_ne_s
  contrapose
  simp only [Classical.not_not, Finset.ext_iff]
  intro fu₂_eq_fs

  cases' fu₂_eq_fs with fu₂_eq_fs fu₂_empty
  left
  intro a
  specialize fu₂_eq_fs (f a)
  cases' fu₂_eq_fs with fu₂_ss_fs fs_ss_fu₂
  constructor
  intro a_in_u₂
  have fa_in_fu₂ : f a ∈ Finset.image f u₂ := by apply Finset.mem_image_of_mem f a_in_u₂
  specialize fu₂_ss_fs fa_in_fu₂
  rw [Function.Injective.mem_finset_image f_inj] at fu₂_ss_fs
  assumption
  intro a_in_s
  have fa_in_fs : f a ∈ Finset.image f s := by apply Finset.mem_image_of_mem f a_in_s
  specialize fs_ss_fu₂ fa_in_fs
  rw [Function.Injective.mem_finset_image f_inj] at fs_ss_fu₂
  assumption

  right
  intro a
  specialize fu₂_empty (f a)
  cases' fu₂_empty with fu₂_ss_fs fs_ss_fu₂
  constructor
  intro a_in_u₂
  have fa_in_fu₂ : f a ∈ Finset.image f u₂ := by apply Finset.mem_image_of_mem f a_in_u₂
  specialize fu₂_ss_fs fa_in_fu₂
  contradiction
  rw [Function.Injective.mem_finset_image f_inj] at fu₂_ss_fs
  intro a_in_s
  contradiction

  right
  rw [u₂_empty]
  apply Finset.image_empty
  constructor; rw [Finset.image_union]
  rw [ne_eq, Finset.image_eq_empty]
  assumption

  rw [Finset.image_union]
  use Finset.image f u₁; constructor
  simp only [Link, Set.mem_sep_iff] at u₁_in_link ⊢

  cases' u₁_in_link with u₁_in_link u₁_empty
  choose u₁_in_X su₁_in_X su₁_disj using u₁_in_link

  left; constructor
  apply isSimplicialMap_onto_image
  assumption

  constructor
  rw [← Finset.image_union]
  apply isSimplicialMap_onto_image
  assumption
  rw [← Finset.image_inter s u₁ f_inj, Finset.image_eq_empty]
  assumption

  right
  rw [Set.mem_singleton_iff] at u₁_empty ⊢
  rw [u₁_empty]
  apply Finset.image_empty

  rw [← Finset.image_union, ← fu_t, u_decomp]
  constructor
  rw [Finset.image_union]
  rw [ne_eq, Finset.image_eq_empty, Finset.union_eq_empty, not_and_or]
  left; assumption

  rw [Set.mem_singleton_iff] at u'_empty u₁_in_link
  subst u'_empty
  rw [Finset.empty_union] at u_decomp
  subst u_decomp
  use ∅; constructor
  right; apply Set.mem_singleton

  cases' u₁_in_link with u₁_in_link u₁_empty
  use Finset.image f u; constructor; left
  simp only [Link, Set.mem_setOf] at u₁_in_link ⊢
  choose u_in_X su_in_X su_disj using u₁_in_link
  simp only [SimplicialImage, Set.mem_setOf]

  constructor; use u
  constructor; use s ∪ u
  constructor; assumption
  rw [Finset.image_union]
  rw [← Finset.image_inter s u f_inj, Finset.image_eq_empty]
  assumption

  constructor
  rw [Finset.empty_union]
  symm; assumption
  rw [← fu_t, ne_eq, Finset.image_eq_empty]
  assumption

  contradiction

theorem stellarSubdivision_injective_image_faces_right_ac
    [Nonempty E]
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  :
    ∀ t : Finset F,
      (∃ t₁ t₂ t₃ : Finset F,
          t₁ ∈ Lk(SimplicialImage f X, Finset.image f s).faces ∪ {∅} ∧
            t₂ ⊆ Finset.image f s ∧ ¬t₂ = Finset.image f s ∧ ¬t₂ = ∅ ∧
            t₃ = ∅ ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (SimplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces :=
by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_ss_fs t₂_ne_fs t₂_ne t₃_empty t_decomp using t_decomp
  simp only [SimplicialImage, Set.mem_setOf]
  simp only [StellarSubdivision, AbstractSimplicialComplex.instHasUnion, SimplicialUnion, Set.mem_union]
  simp only [Link, Set.mem_union, Set.mem_sep_iff, SimplicialImage, Set.mem_setOf] at t₁_in_link

  cases' t₁_in_link with t₁_in_link t₁_empty
  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  subst t₃_empty

  set u₂ := Finset.image (Function.invFunOn f Set.univ) t₂
  have fu₂_t₂ : Finset.image f u₂ = t₂ :=
  by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro a
    constructor
    intro a_in_img
    choose c c_in_inv fc_a using a_in_img

    rw [Finset.mem_image] at c_in_inv
    choose b b_in_t₂ fb_c using c_in_inv
    rw [← fb_c, @Function.invFunOn_eq _ _ Set.univ f] at fc_a
    rw [← fc_a]
    assumption
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs b_in_t₂
    choose d d_in_s fd_b using t₂_ss_fs
    use d; constructor; apply Set.mem_univ
    assumption
    intro a_in_t₂
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs a_in_t₂
    choose b b_in_s fb_a using t₂_ss_fs
    use b; constructor
    rw [Finset.mem_image]
    use a; constructor; assumption
    rw [← fb_a]
    apply Set.InjOn.leftInvOn_invFunOn
    apply Function.Injective.injOn f_inj
    apply Set.mem_univ
    assumption

  use ∅ ∪ u₂ ∪ u₁; constructor; right
  simp only [simplicialJoinProj_mem]
  use ∅ ∪ u₂; constructor

  simp only [Set.mem_union, simplicialJoinProj_mem]
  by_cases u₂_empty : u₂ = ∅
  right; rw [u₂_empty, Finset.union_empty]
  apply Set.mem_singleton

  left; use ∅; constructor
  right; apply Set.mem_singleton
  use u₂; constructor
  simp only [FaceBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Set.mem_insert_iff, Finset.mem_powerset, not_or]
  left; constructor
  rw [Finset.subset_iff] at t₂_ss_fs ⊢
  intro a a_in_u₂
  have fa_in_t₂ : f a ∈ t₂ :=
  by
    rw [Finset.mem_image] at a_in_u₂
    choose b b_in_t₂ fb_a using a_in_u₂
    rw [← fb_a, @Function.invFunOn_eq _ _ Set.univ f]
    assumption
    specialize t₂_ss_fs b_in_t₂
    rw [Finset.mem_image] at t₂_ss_fs
    choose c c_in_s fc_b using t₂_ss_fs
    use c; constructor; apply Set.mem_univ
    assumption
  specialize t₂_ss_fs fa_in_t₂
  rw [Function.Injective.mem_finset_image f_inj] at t₂_ss_fs
  assumption
  revert t₂_ne_fs
  contrapose
  simp only [not_and_or, Classical.not_not, Finset.ext_iff]

  intro u₂_eq_s b
  constructor
  intro b_in_t₂

  cases' u₂_eq_s with u₂_eq_s u₂_empty
  specialize u₂_eq_s ((Function.invFunOn f Set.univ) b)
  cases' u₂_eq_s with u₂_ss_s s_ss_u₂
  have fb_in_u₂ : (Function.invFunOn f Set.univ) b ∈ u₂ := by
    apply Finset.mem_image_of_mem (Function.invFunOn f Set.univ) b_in_t₂
  specialize u₂_ss_s fb_in_u₂
  rw [Finset.mem_image]
  use(Function.invFunOn f Set.univ) b; constructor
  assumption
  rw [@Function.invFunOn_eq _ _ Set.univ f]
  simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
  specialize t₂_ss_fs b_in_t₂
  choose c c_in_s fc_b using t₂_ss_fs
  use c; constructor; apply Set.mem_univ
  assumption

  rw [← Finset.ext_iff] at u₂_empty
  contradiction

  intro b_in_fs
  rw [Finset.mem_image] at b_in_fs
  choose a a_in_s fa_b using b_in_fs

  cases' u₂_eq_s with u₂_eq_s u₂_empty
  specialize u₂_eq_s a
  cases' u₂_eq_s with u₂_ss_s s_ss_u₂
  specialize s_ss_u₂ a_in_s
  rw [Finset.mem_image] at s_ss_u₂
  choose c c_in_t₂ fc_a using s_ss_u₂
  rw [← fc_a] at fa_b
  rw [@Function.invFunOn_eq _ _ Set.univ f] at fa_b
  rw [← fa_b]
  assumption
  simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
  specialize t₂_ss_fs c_in_t₂
  choose d d_in_s fd_c using t₂_ss_fs
  use d; constructor; apply Set.mem_univ
  assumption

  rw [← Finset.ext_iff] at u₂_empty
  contradiction

  constructor; rfl
  rw [Finset.empty_union]
  assumption

  use u₁; constructor
  simp only [Link, Set.mem_sep_iff, Set.mem_union]
  left; constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ :=
  by
    rw [← Finset.image_union] at fv_fsu₁
    rw [Finset.ext_iff] at fv_fsu₁ ⊢
    intro a
    specialize fv_fsu₁ (f a)
    cases' fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv
    constructor
    intro a_in_v
    specialize fv_ss_fsu₁ (by apply Finset.mem_image_of_mem f a_in_v)
    rw [Function.Injective.mem_finset_image f_inj] at fv_ss_fsu₁
    assumption
    intro a_in_su₁
    specialize fsu₁_ss_fv (by apply Finset.mem_image_of_mem f a_in_su₁)
    rw [Function.Injective.mem_finset_image f_inj] at fsu₁_ss_fv
    assumption
  rw [v_su₁] at v_in_X
  assumption
  rw [← Finset.image_inter s u₁ f_inj, Finset.image_eq_empty] at fst₁_disj
  assumption

  constructor; rfl
  rw [Finset.empty_union, ne_eq, Finset.union_eq_empty, not_and_or]
  right; exact face_nonempty u₁_in_X

  simp only [Finset.image_union, fu₂_t₂, Finset.image_empty]
  symm
  assumption

  set u₂ := Finset.image (Function.invFunOn f Set.univ) t₂
  have fu₂_t₂ : Finset.image f u₂ = t₂ :=
  by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro a
    constructor
    intro a_in_img
    choose c c_in_inv fc_a using a_in_img

    rw [Finset.mem_image] at c_in_inv
    choose b b_in_t₂ fb_c using c_in_inv
    rw [← fb_c, @Function.invFunOn_eq _ _ Set.univ f] at fc_a
    rw [← fc_a]
    assumption
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs b_in_t₂
    choose d d_in_s fd_b using t₂_ss_fs
    use d; constructor; apply Set.mem_univ
    assumption
    intro a_in_t₂
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs a_in_t₂
    choose b b_in_s fb_a using t₂_ss_fs
    use b; constructor
    rw [Finset.mem_image]
    use a; constructor; assumption
    rw [← fb_a]
    apply Set.InjOn.leftInvOn_invFunOn
    apply Function.Injective.injOn f_inj
    apply Set.mem_univ
    assumption

  use u₂; constructor; right
  rw [simplicialJoinProj_mem]
  use u₂; constructor
  simp only [Set.mem_union, simplicialJoinProj_mem]
  left; use ∅; constructor
  right; apply Set.mem_singleton
  use u₂; constructor; left
  rw [faceBoundary_mem_iff_subset, Finset.ssubset_def]
  constructor; constructor

  rw [Finset.subset_iff] at t₂_ss_fs ⊢
  intro a a_in_u₂
  have fa_in_t₂ : f a ∈ t₂ :=
  by
    rw [Finset.mem_image] at a_in_u₂
    choose b b_in_t₂ fb_a using a_in_u₂
    rw [← fb_a, @Function.invFunOn_eq _ _ Set.univ f]
    assumption
    specialize t₂_ss_fs b_in_t₂
    rw [Finset.mem_image] at t₂_ss_fs
    choose c c_in_s fc_b using t₂_ss_fs
    use c; constructor; apply Set.mem_univ
    assumption
  specialize t₂_ss_fs fa_in_t₂
  rw [Function.Injective.mem_finset_image f_inj] at t₂_ss_fs
  assumption
  revert t₂_ss_fs
  contrapose
  simp only [not_and_or, not_not]
  intro s_ss_u₂

  have fs_ss_t₂ : Finset.image f s ⊆ t₂ :=
  by
    rw [← fu₂_t₂]
    apply Finset.image_subset_image s_ss_u₂
  by_contra t₂_ss_fs
  have t₂_eq_fs : t₂ = Finset.image f s :=
  by
    rw [Finset.subset_iff] at fs_ss_t₂ t₂_ss_fs
    rw [Finset.ext_iff]
    intro b
    constructor

    intro b_in_t₂
    specialize t₂_ss_fs b_in_t₂
    assumption

    intro b_in_fs
    specialize fs_ss_t₂ b_in_fs
    assumption
  contradiction

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  constructor
  rw [Finset.empty_union]
  rw [ne_eq, Finset.image_eq_empty]
  assumption

  use ∅; constructor
  rw [Set.mem_union]
  right; apply Set.mem_singleton

  constructor
  rw [Finset.union_empty]
  rw [ne_eq, Finset.image_eq_empty]
  assumption

  rw [Set.mem_singleton_iff] at t₁_empty
  subst t₁_empty t₃_empty t_decomp
  rw [Finset.empty_union, Finset.union_empty]
  assumption

theorem stellarSubdivision_injective_image_faces_right_ad
    [Nonempty E]
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : ∀ t : Finset F,
      (∃ t₁ t₂ t₃ : Finset F,
          t₁ ∈ Lk(SimplicialImage f X, Finset.image f s).faces ∪ {∅} ∧
            t₂ ⊆ Finset.image f s ∧ ¬t₂ = Finset.image f s ∧ ¬t₂ = ∅ ∧
            t₃ = {f x} ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (SimplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces :=
by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_ss_fs t₂_ne_fs t₂_ne t₃_eq_fx t_decomp using t_decomp
  simp only [SimplicialImage, Set.mem_setOf]
  simp only [StellarSubdivision, AbstractSimplicialComplex.instHasUnion, SimplicialUnion, Set.mem_union]
  simp only [Link, Set.mem_union, Set.mem_sep_iff, SimplicialImage, Set.mem_setOf] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  subst t₃_eq_fx

  set u₂ := Finset.image (Function.invFunOn f Set.univ) t₂
  use {x} ∪ u₂ ∪ u₁; constructor; right
  simp only [simplicialJoinProj_mem]
  use {x} ∪ u₂; constructor

  rw [Set.mem_union, simplicialJoinProj_mem]
  left; use {x}; constructor
  simp only [Simplex, Set.mem_union, Set.mem_diff, Finset.mem_coe]
  left; constructor
  apply Finset.mem_powerset_self
  rw [Set.mem_singleton_iff]
  apply Finset.singleton_ne_empty

  use u₂; constructor
  simp only [FaceBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Set.mem_insert_iff, not_or, Finset.mem_powerset]

  by_cases u₂_empty : u₂ = ∅
  right; assumption

  left; constructor
  rw [Finset.subset_iff] at t₂_ss_fs ⊢
  intro a a_in_u₂
  have fa_in_t₂ : f a ∈ t₂ :=
  by
    rw [Finset.mem_image] at a_in_u₂
    choose b b_in_t₂ fb_a using a_in_u₂
    rw [← fb_a, @Function.invFunOn_eq _ _ Set.univ f]
    assumption
    specialize t₂_ss_fs b_in_t₂
    rw [Finset.mem_image] at t₂_ss_fs
    choose c c_in_s fc_b using t₂_ss_fs
    use c; constructor; apply Set.mem_univ
    assumption
  specialize t₂_ss_fs fa_in_t₂
  rw [Function.Injective.mem_finset_image f_inj] at t₂_ss_fs
  assumption

  constructor
  revert t₂_ne_fs
  contrapose
  simp only [Classical.not_not, Finset.ext_iff]
  intro u₂_eq_s b
  constructor
  intro b_in_t₂
  specialize u₂_eq_s ((Function.invFunOn f Set.univ) b)
  cases' u₂_eq_s with u₂_ss_s s_ss_u₂
  have fb_in_u₂ : (Function.invFunOn f Set.univ) b ∈ u₂ := by
    apply Finset.mem_image_of_mem (Function.invFunOn f Set.univ) b_in_t₂
  specialize u₂_ss_s fb_in_u₂
  rw [Finset.mem_image]
  use(Function.invFunOn f Set.univ) b; constructor
  assumption
  rw [@Function.invFunOn_eq _ _ Set.univ f]
  simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
  specialize t₂_ss_fs b_in_t₂
  choose c c_in_s fc_b using t₂_ss_fs
  use c; constructor; apply Set.mem_univ
  assumption
  intro b_in_fs
  rw [Finset.mem_image] at b_in_fs
  choose a a_in_s fa_b using b_in_fs
  specialize u₂_eq_s a
  cases' u₂_eq_s with u₂_ss_s s_ss_u₂
  specialize s_ss_u₂ a_in_s
  rw [Finset.mem_image] at s_ss_u₂
  choose c c_in_t₂ fc_a using s_ss_u₂
  rw [← fc_a] at fa_b
  rw [@Function.invFunOn_eq _ _ Set.univ f] at fa_b
  rw [← fa_b]
  assumption
  simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
  specialize t₂_ss_fs c_in_t₂
  choose d d_in_s fd_c using t₂_ss_fs
  use d; constructor; apply Set.mem_univ
  assumption

  assumption

  constructor; rfl
  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  left; apply Finset.singleton_ne_empty

  use u₁; constructor
  simp only [Link, Set.mem_union, Set.mem_sep_iff]
  left; constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ :=
  by
    rw [← Finset.image_union] at fv_fsu₁
    rw [Finset.ext_iff] at fv_fsu₁ ⊢
    intro a
    specialize fv_fsu₁ (f a)
    cases' fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv
    constructor
    intro a_in_v
    specialize fv_ss_fsu₁ (by apply Finset.mem_image_of_mem f a_in_v)
    rw [Function.Injective.mem_finset_image f_inj] at fv_ss_fsu₁
    assumption
    intro a_in_su₁
    specialize fsu₁_ss_fv (by apply Finset.mem_image_of_mem f a_in_su₁)
    rw [Function.Injective.mem_finset_image f_inj] at fsu₁_ss_fv
    assumption
  rw [v_su₁] at v_in_X
  assumption
  rw [← Finset.image_inter s u₁ f_inj, Finset.image_eq_empty] at fst₁_disj
  assumption

  constructor; rfl
  simp only [ne_eq, Finset.union_eq_empty, not_and_or]
  left; left; apply Finset.singleton_ne_empty

  simp only [Finset.image_union]
  have fu₂_t₂ : Finset.image f u₂ = t₂ :=
  by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro a
    constructor
    intro a_in_img
    choose c c_in_inv fc_a using a_in_img
    rw [Finset.mem_image] at c_in_inv
    choose b b_in_t₂ fb_c using c_in_inv
    rw [← fb_c, @Function.invFunOn_eq _ _ Set.univ f] at fc_a
    rw [← fc_a]
    assumption
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs b_in_t₂
    choose d d_in_s fd_b using t₂_ss_fs
    use d; constructor; apply Set.mem_univ
    assumption
    intro a_in_t₂
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs a_in_t₂
    choose b b_in_s fb_a using t₂_ss_fs
    use b; constructor
    rw [Finset.mem_image]
    use a; constructor; assumption
    rw [← fb_a]
    apply Set.InjOn.leftInvOn_invFunOn
    apply Function.Injective.injOn f_inj
    apply Set.mem_univ
    assumption
  rw [fu₂_t₂, Finset.image_singleton]
  symm
  assumption

  set u₂ := Finset.image (Function.invFunOn f Set.univ) t₂
  have fu₂_t₂ : Finset.image f u₂ = t₂ :=
  by
    simp only [Finset.ext_iff, Finset.mem_image]
    intro a
    constructor
    intro a_in_img
    choose c c_in_inv fc_a using a_in_img
    rw [Finset.mem_image] at c_in_inv
    choose b b_in_t₂ fb_c using c_in_inv
    rw [← fb_c, @Function.invFunOn_eq _ _ Set.univ f] at fc_a
    rw [← fc_a]
    assumption
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs b_in_t₂
    choose d d_in_s fd_b using t₂_ss_fs
    use d; constructor; apply Set.mem_univ
    assumption
    intro a_in_t₂
    simp only [Finset.subset_iff, Finset.mem_image] at t₂_ss_fs
    specialize t₂_ss_fs a_in_t₂
    choose b b_in_s fb_a using t₂_ss_fs
    use b; constructor
    rw [Finset.mem_image]
    use a; constructor; assumption
    rw [← fb_a]
    apply Set.InjOn.leftInvOn_invFunOn
    apply Function.Injective.injOn f_inj
    apply Set.mem_univ
    assumption

  use {x} ∪ u₂; constructor; right
  simp only [simplicialJoinProj_mem, Set.mem_union]
  use {x} ∪ u₂; constructor; left
  use {x}; constructor; left
  simp only [Simplex, Set.mem_diff, Finset.mem_coe]
  constructor; apply Finset.mem_powerset_self
  rw [Set.mem_singleton_iff, ← ne_eq]
  apply Finset.singleton_ne_empty

  use u₂; constructor; left
  rw [faceBoundary_mem_iff_subset, Finset.ssubset_iff_subset_ne]
  constructor; constructor

  rw [Finset.subset_iff] at t₂_ss_fs ⊢
  intro a a_in_u₂
  have fa_in_t₂ : f a ∈ t₂ :=
  by
    rw [Finset.mem_image] at a_in_u₂
    choose b b_in_t₂ fb_a using a_in_u₂
    rw [← fb_a, @Function.invFunOn_eq _ _ Set.univ f]
    assumption
    specialize t₂_ss_fs b_in_t₂
    rw [Finset.mem_image] at t₂_ss_fs
    choose c c_in_s fc_b using t₂_ss_fs
    use c; constructor; apply Set.mem_univ
    assumption
  specialize t₂_ss_fs fa_in_t₂
  rw [Function.Injective.mem_finset_image f_inj] at t₂_ss_fs
  assumption
  revert t₂_ss_fs
  contrapose
  simp only [not_and_or, not_not]
  intro s_ss_u₂

  have fs_ss_t₂ : Finset.image f s ⊆ t₂ :=
  by
    rw [← fu₂_t₂]
    apply Finset.image_subset_image
    apply Finset.subset_of_eq
    symm; assumption
  by_contra t₂_ss_fs
  have t₂_eq_fs : t₂ = Finset.image f s :=
  by
    rw [Finset.subset_iff] at fs_ss_t₂ t₂_ss_fs
    rw [Finset.ext_iff]
    intro b
    constructor

    intro b_in_t₂
    specialize t₂_ss_fs b_in_t₂
    assumption

    intro b_in_fs
    specialize fs_ss_t₂ b_in_fs
    assumption
  contradiction

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  constructor; rfl
  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  left; apply Finset.singleton_ne_empty

  use ∅; constructor
  right; apply Set.mem_singleton
  constructor
  rw [Finset.union_empty]
  rw [ne_eq, Finset.union_eq_empty, not_and_or]
  left; apply Finset.singleton_ne_empty

  rw [Finset.image_union, Finset.image_singleton]
  rw [Set.mem_singleton_iff] at t₁_empty
  subst t₁_empty
  rw [Finset.union_empty] at t_decomp
  rw [← t₃_eq_fx, fu₂_t₂, t_decomp]

theorem stellarSubdivision_injective_image_faces_right_bc
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : ∀ t : Finset F,
      (∃ t₁ t₂ t₃ : Finset F,
          t₁ ∈ Lk(SimplicialImage f X, Finset.image f s).faces ∧
            t₂ = ∅ ∧ t₃ = ∅ ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (SimplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces :=
by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_empty t₃_empty t_decomp using t_decomp
  simp only [SimplicialImage, Set.mem_setOf]
  simp only [StellarSubdivision, SimplicialUnion, Set.mem_union]
  simp only [Link, Set.mem_union, Set.mem_sep_iff, SimplicialImage, Set.mem_setOf] at t₁_in_link

  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  use ∅ ∪ ∅ ∪ u₁; constructor; right
  simp only [simplicialJoinProj_mem]
  use ∅ ∪ ∅; constructor

  simp only [Set.mem_union]
  right; rw [Finset.empty_union]; apply Set.mem_singleton

  use u₁; constructor
  simp only [Link, Set.mem_union, Set.mem_sep_iff]
  left; constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ :=
  by
    rw [← Finset.image_union] at fv_fsu₁
    rw [Finset.ext_iff] at fv_fsu₁ ⊢
    intro a
    specialize fv_fsu₁ (f a)
    cases' fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv
    constructor
    intro a_in_v
    specialize fv_ss_fsu₁ (by apply Finset.mem_image_of_mem f a_in_v)
    rw [Function.Injective.mem_finset_image f_inj] at fv_ss_fsu₁
    assumption
    intro a_in_su₁
    specialize fsu₁_ss_fv (by apply Finset.mem_image_of_mem f a_in_su₁)
    rw [Function.Injective.mem_finset_image f_inj] at fsu₁_ss_fv
    assumption
  rw [v_su₁] at v_in_X
  assumption
  rw [← Finset.image_inter s u₁ f_inj, Finset.image_eq_empty] at fst₁_disj
  assumption

  constructor; rfl
  simp only [Finset.empty_union]
  exact face_nonempty u₁_in_X

  simp only [Finset.image_union, Finset.image_singleton, Finset.image_empty]
  subst t₃_empty
  subst t₂_empty
  symm
  assumption

theorem stellarSubdivision_injective_image_faces_right_bd
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : ∀ t : Finset F,
      (∃ t₁ t₂ t₃ : Finset F,
          t₁ ∈ Lk(SimplicialImage f X, Finset.image f s).faces ∪ {∅} ∧
            t₂ = ∅ ∧ t₃ = {f x} ∧ t = t₃ ∪ t₂ ∪ t₁) →
        t ∈ (SimplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces :=
by
  intro t t_decomp
  choose t₁ t₂ t₃ t₁_in_link t₂_empty t₃_eq_fx t_decomp using t_decomp
  simp only [SimplicialImage, Set.mem_setOf]
  simp only [StellarSubdivision, AbstractSimplicialComplex.instHasUnion, SimplicialUnion, Set.mem_union]
  simp only [Link, Set.mem_union, Set.mem_sep_iff, SimplicialImage, Set.mem_setOf] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  choose t₁_in_fX fst₁_in_fX fst₁_disj using t₁_in_link
  choose u₁ u₁_in_X fu₁_t₁ using t₁_in_fX
  choose v v_in_X fv_fsu₁ using fst₁_in_fX
  subst fu₁_t₁
  use {x} ∪ ∅ ∪ u₁; constructor; right
  simp only [simplicialJoinProj_mem]
  use {x} ∪ ∅; constructor

  simp only [Set.mem_union, simplicialJoinProj_mem]
  left; use {x}; constructor

  simp only [Simplex, Set.mem_diff, Finset.mem_coe]
  left; constructor; apply Finset.mem_powerset_self
  rw [Set.mem_singleton_iff]
  apply Finset.singleton_ne_empty

  use ∅; constructor
  right; apply Set.mem_singleton

  constructor; rfl
  rw [Finset.union_empty]
  apply Finset.singleton_ne_empty

  use u₁; constructor
  simp only [Link, Set.mem_union, Set.mem_sep_iff]
  left; constructor; assumption
  constructor
  have v_su₁ : v = s ∪ u₁ :=
  by
    rw [← Finset.image_union] at fv_fsu₁
    rw [Finset.ext_iff] at fv_fsu₁ ⊢
    intro a
    specialize fv_fsu₁ (f a)
    cases' fv_fsu₁ with fv_ss_fsu₁ fsu₁_ss_fv
    constructor
    intro a_in_v
    specialize fv_ss_fsu₁ (by apply Finset.mem_image_of_mem f a_in_v)
    rw [Function.Injective.mem_finset_image f_inj] at fv_ss_fsu₁
    assumption
    intro a_in_su₁
    specialize fsu₁_ss_fv (by apply Finset.mem_image_of_mem f a_in_su₁)
    rw [Function.Injective.mem_finset_image f_inj] at fsu₁_ss_fv
    assumption
  rw [v_su₁] at v_in_X
  assumption
  rw [← Finset.image_inter s u₁ f_inj, Finset.image_eq_empty] at fst₁_disj
  assumption

  constructor; rfl
  rw [Finset.union_empty, ne_eq, Finset.union_eq_empty, not_and_or]
  left; apply Finset.singleton_ne_empty

  simp only [Finset.image_union, Finset.image_singleton, Finset.image_empty, ← t₃_eq_fx, ← t₂_empty]
  symm
  assumption

  use {x}; constructor; right
  rw [simplicialJoinProj_mem]
  use {x}; constructor
  rw [Set.mem_union, simplicialJoinProj_mem]
  left; use {x}; constructor
  simp only [Set.mem_union, Simplex, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe]
  left; constructor
  apply Finset.mem_powerset_self
  apply Finset.singleton_ne_empty

  use ∅; constructor
  rw [Set.mem_union]
  right; apply Set.mem_singleton

  constructor
  rw [Finset.union_empty]
  apply Finset.singleton_ne_empty

  use ∅; constructor
  rw [Set.mem_union]
  right; apply Set.mem_singleton

  constructor
  rw [Finset.union_empty]
  apply Finset.singleton_ne_empty

  rw [Finset.image_singleton]
  rw [Set.mem_singleton_iff] at t₁_empty
  subst t₁_empty t₂_empty t₃_eq_fx t_decomp
  simp only [Finset.union_empty]

theorem stellarSubdivision_injective_image_faces_right
    [Nonempty E]
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : σ(SimplicialImage f X, Finset.image f s, f x; 𝕜,
        by
          apply isSimplicialMap_onto_image
          assumption,
        barycenter_injective_image x_nin_X f_inj).faces ⊆
      (SimplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)).faces :=
by
  rw [Set.subset_def]
  intro t t_in_subdiv
  simp only [StellarSubdivision, SimplicialUnion, Set.mem_union] at t_in_subdiv
  cases' t_in_subdiv with t_in_star_comp t_in_join
  simp only [StarComplement, Set.mem_sep_iff, SimplicialImage, Set.mem_setOf] at t_in_star_comp
  choose t_in_fX fs_nss_t using t_in_star_comp
  choose u u_in_X fu_t using t_in_fX
  use u; constructor; left
  simp only [StarComplement, Set.mem_sep_iff]
  constructor; assumption
  revert fs_nss_t
  contrapose
  simp only [Classical.not_not, ← fu_t]
  apply Finset.image_subset_image
  assumption
  simp only [simplicialJoinProj_mem] at t_in_join ⊢
  choose t' t'_in_join t₁ t₁_in_link t_decomp t_ne using t_in_join

  rw [Set.mem_union, simplicialJoinProj_mem] at t'_in_join
  cases' t'_in_join with t'_in_join t'_empty

  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp t'_ne using t'_in_join
  subst t'_decomp
  simp only [FaceBoundary, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_powerset] at t₂_in_bd
  simp only [Simplex, Set.mem_union, Set.mem_diff, Finset.mem_coe, Finset.mem_powerset,
    Finset.subset_singleton_iff, Set.mem_singleton_iff] at t₃_in_barycenter
  cases' t₂_in_bd with t₂_in_bd t₂_empty <;>

  -- Cases A, B resp.
  cases' t₃_in_barycenter with t₃_eq_x t₃_empty
  rotate_left

  -- Cases C, D resp.
  choose t₂_ss_fs t₂_ne_fs using t₂_in_bd
  apply stellarSubdivision_injective_image_faces_right_ac
  assumption

  use t₁; use t₂; use t₃
  rw [Set.mem_insert_iff, not_or] at t₂_ne_fs
  choose t₂_ne_fs t₂_ne using t₂_ne_fs
  constructor; assumption
  constructor; assumption
  constructor; assumption
  constructor; assumption
  constructor; assumption
  assumption

  apply stellarSubdivision_injective_image_faces_right_bd
  assumption

  use t₁; use t₂; use t₃
  choose t₃_eq_x t₃_ne using t₃_eq_x
  cases' t₃_eq_x with contra t₃_eq_x
  contradiction
  constructor; assumption
  constructor; assumption
  constructor; assumption
  assumption

  apply stellarSubdivision_injective_image_faces_right_bc
  assumption

  use t₁; use t₂; use t₃
  rw [Set.mem_union] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  constructor; assumption
  constructor; assumption
  constructor; assumption
  assumption

  rw [Set.mem_singleton_iff] at t₁_empty
  subst t₁_empty t₂_empty t₃_empty
  simp only [Finset.union_empty] at t_decomp
  contradiction

  apply stellarSubdivision_injective_image_faces_right_bc
  assumption
  use t₁; use ∅; use ∅
  rw [Set.mem_union] at t₁_in_link
  cases' t₁_in_link with t₁_in_link t₁_empty

  constructor; assumption
  constructor; rfl
  constructor; rfl
  rw [Set.mem_singleton_iff] at t'_empty
  subst t'_empty
  simp only [Finset.empty_union] at t_decomp ⊢
  assumption

  rw [Set.mem_singleton_iff] at t'_empty t₁_empty
  subst t'_empty t₁_empty
  rw [Finset.empty_union] at t_decomp
  contradiction

  apply stellarSubdivision_injective_image_faces_right_ad
  assumption

  use t₁; use t₂; use t₃
  choose t₂_ss_fs t₂_ne_s using t₂_in_bd
  rw [Set.mem_insert_iff, not_or] at t₂_ne_s
  choose t₂_ne_s t₂_ne using t₂_ne_s
  constructor; assumption
  constructor; assumption
  constructor; assumption
  choose t₃_eq_x t₃_ne using t₃_eq_x
  cases' t₃_eq_x with contra t₃_eq_x
  contradiction
  constructor; assumption
  constructor; assumption
  assumption

theorem stellarSubdivision_injective_image
    [Nonempty E]
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (f : E → F)
    (f_inj : Function.Injective f)
  : (SimplicialImage f σ(X, s, x; 𝕜, s_in_X, x_nin_X)) =
      σ(SimplicialImage f X, Finset.image f s, f x; 𝕜,
          by
            apply isSimplicialMap_onto_image
            assumption,
          barycenter_injective_image x_nin_X f_inj) :=
by
  rw [AbstractSimplicialComplex.ext_iff, Set.Subset.antisymm_iff]
  constructor
  apply stellarSubdivision_injective_image_faces_left
  assumption
  apply stellarSubdivision_injective_image_faces_right
  assumption

theorem stellarSsubdivision_exists_iso
    [Nonempty E]
    {Z : AbstractSimplicialComplex F}
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (τ : E → F)
    (τ_inj : Function.Injective τ)
  : (X ≅ Z) → Y ≅ σ(X, s, x; 𝕜, s_in_X, x_nin_X) →
      ∃ W : AbstractSimplicialComplex F, (Y ≅ W) ∧ Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z X_subdiv_Y
  have τ_inj_subdiv : Set.InjOn τ σ(X, s, x; 𝕜, s_in_X, x_nin_X).vertices :=
  by
    apply Set.injOn_of_injective τ_inj
  let τσ := SimplicialCoe.mk τ τ_inj_subdiv
  have τ_inj_X : Set.InjOn τ X.vertices := by apply Set.injOn_of_injective τ_inj
  let τX := SimplicialCoe.mk τ τ_inj_X
  use τσ.coe ''ˢ σ(X, s, x; 𝕜, s_in_X, x_nin_X); constructor
  apply simplicialIso_trans σ(X, s, x; 𝕜, s_in_X, x_nin_X)
  assumption
  apply τσ.simplicialIso_onto_image
  have τX_iso_Z : Z ≅ τX.coe ''ˢ X :=
  by
    apply simplicialIso_trans X
    rw [simplicialIso_symm]
    assumption
    apply τX.simplicialIso_onto_image
  apply @Relation.ReflTransGen.tail _ _ _ (τX.coe ''ˢ X)
  apply Relation.ReflTransGen.single
  right; right
  assumption
  right; left
  use Finset.image τX.coe s
  have τs_in_img : Finset.image τX.coe s ∈ (τX.coe ''ˢ X).faces :=
  by
    apply isSimplicialMap_onto_image X τX.coe
    assumption
  use τs_in_img
  use τX.coe x
  have τx_nin_τX : τX.coe x ∉ (τX.coe ''ˢ X).vertices :=
  by
    by_cases τx_in_X : τX.coe x ∈ (τX.coe ''ˢ X).vertices
    rw [simplicialImage_vertices] at τx_in_X
    have contra : x ∈ X.vertices :=
    by
      rw [Set.mem_image] at τx_in_X
      choose y y_in_X τy_eq_τx using τx_in_X
      rw [Function.Injective.eq_iff τ_inj] at τy_eq_τx
      rw [τy_eq_τx] at y_in_X
      assumption
    contradiction
    assumption
  use τx_nin_τX
  rw [stellarSubdivision_injective_image]
  assumption

theorem stellar_weld_exists_iso
    [Nonempty E]
    {Z : AbstractSimplicialComplex F}
    (t_in_Y : t ∈ Y.faces)
    (y_nin_Y : y ∉ Y.vertices)
  : (X ≅ Z) → X ≅ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) → ∃ W : AbstractSimplicialComplex F, (Y ≅ W) ∧ Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z Y_subdiv_X
  have Z_iso_subdiv : Z ≅ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) :=
  by
    calc Z
      _ ≅ X := by rw [simplicialIso_symm]; exact X_iso_Z
      _ ≅ σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y) := Y_subdiv_X
  let Z_iso_subdiv' := Z_iso_subdiv
  unfold IsSimpliciallyIso at Z_iso_subdiv'
  choose f f_iso using Z_iso_subdiv'
  let f_iso' := f_iso
  unfold IsSimplicialIso at f_iso'
  choose g gf_inv using f_iso'
  let gf_inv' := gf_inv
  unfold IsInverseSimplicialIso at gf_inv'
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id] at gf_inv'
  choose gf_id fg_id using gf_inv'
  have g_iso : IsSimplicialIso g := by apply simplicialIso_inverse_is_simplicialIso f g f_iso gf_inv
  by_cases t_singleton : t.card = 1
  rw [Finset.card_eq_one] at t_singleton
  choose a t_eq_a using t_singleton
  subst t_eq_a
  rw [stellarSubdivision_of_singleton_vertices] at fg_id
  use Z; constructor
  apply simplicialIso_trans σ(Y, {a}, y; 𝕜, t_in_Y, y_nin_Y)
  rw [simplicialIso_symm]
  apply stellarSubdivision_of_singleton_iso_self
  rw [simplicialIso_symm]
  assumption
  apply Relation.ReflTransGen.single
  unfold StellarMove
  right; right
  apply simplicialIso_refl
  have t_nonsingleton : t.card > 1 :=
  by
    have t_ne : t ≠ ∅ := face_nonempty t_in_Y
    rw [ne_eq, ← Finset.card_eq_zero] at t_ne
    omega
  have g_inj : Set.InjOn g.map Y.vertices :=
  by
    apply @Set.InjOn.mono _ _ Y.vertices (Y.vertices ∪ {y})
    apply Set.subset_union_left
    rw [← @stellarSubdivision_vertices _ 𝕜 _ _ _ _ Y t y t_in_Y y_nin_Y t_nonsingleton]
    apply simplicialIso_injective_vertices g g_iso
  let g_coe : SimplicialCoe Y F := SimplicialCoe.mk g.map g_inj
  have gy_nin_gY : g.map y ∉ (g_coe.coe ''ˢ Y).vertices :=
  by
    by_cases gy_in_Y : g.map y ∈ (g_coe.coe ''ˢ Y).vertices
    rw [simplicialImage_vertices] at gy_in_Y
    have contra : y ∈ Y.vertices :=
    by
      apply Set.InjOn.mem_of_mem_image
      apply simplicialIso_injective_vertices g g_iso
      rw [stellarSubdivision_vertices t_in_Y y_nin_Y t_nonsingleton]
      apply Set.subset_union_left
      apply stellarSubdivision_barycenter_mem
      assumption
    contradiction
    assumption
  let φ := @StellarCoeForward _ _ 𝕜 _ _ _ _ _ _ Y g_coe t y (g.map y) t_in_Y y_nin_Y gy_nin_gY
  have φ_inj : Set.InjOn φ.map (Y.vertices ∪ {y}) :=
  by
    rw [← @stellarSubdivision_vertices _ 𝕜 _ _ _ _ Y t y t_in_Y y_nin_Y t_nonsingleton]
    apply
      simplicialIso_injective_vertices φ (stellarCoe_simplicialIso t_in_Y y_nin_Y gy_nin_gY)
  have φy_nin_φY : φ.map y ∉ (SimplicialImage φ.map Y).vertices :=
    by
    by_cases φy_in_Y : φ.map y ∈ (SimplicialImage φ.map Y).vertices
    rw [simplicialImage_vertices] at φy_in_Y
    have contra : y ∈ Y.vertices :=
    by
      apply Set.InjOn.mem_of_mem_image
      apply φ_inj
      apply Set.subset_union_left
      rw [Set.mem_union, Set.mem_singleton_iff]
      right; rfl
      assumption
    contradiction
    assumption
  use SimplicialImage φ.map Y; constructor
  have φY_inj : Set.InjOn φ.map Y.vertices :=
  by
    apply @Set.InjOn.mono _ _ _ (Y.vertices ∪ {y})
    apply Set.subset_union_left
    assumption
  let φY := SimplicialCoe.mk φ.map φY_inj
  apply simplicialIso_trans (φY.coe ''ˢ Y)
  apply φY.simplicialIso_onto_image
  apply simplicialIso_preserves_equiv
  rw [simplicialImage_congr φY.coe φ.map]

  rotate_left
  dsimp only
  apply Relation.ReflTransGen.single
  unfold StellarMove
  left
  use Finset.image φ.map t
  have φt_in_φY : Finset.image φ.map t ∈ (SimplicialImage φ.map Y).faces :=
  by
    apply isSimplicialMap_onto_image Y φ.map
    assumption
  use φt_in_φY
  use φ.map y
  use φy_nin_φY
  apply simplicialIso_trans σ(Y, t, y; 𝕜, t_in_Y, y_nin_Y)
  assumption
  apply
    simplicialIso_trans
      σ(SimplicialImage g_coe.coe Y, Finset.image g_coe.coe t, g.map y; 𝕜, by
        apply isSimplicialMap_onto_image; assumption, gy_nin_gY)
  unfold IsSimpliciallyIso
  use φ
  apply stellarCoe_simplicialIso
  rw [simplicialIso_symm]
  apply stellarCoe_stellarSubdivision <;> assumption

  simp only [Set.EqOn, implies_true, φY]

theorem stellarMove_exists_iso
    [Nonempty E]
    {Z : AbstractSimplicialComplex F}
    (f_inj : Function.Injective f)
  : (X ≅ Z) → X ≅ₛₜₘ[𝕜] Y →
      ∃ W : AbstractSimplicialComplex F, (Y ≅ W) ∧ Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z X_move_Y
  unfold StellarMove at X_move_Y
  cases' X_move_Y with Y_subdiv_X X_move_Y
  choose t t_in_Y y y_nin_Y Y_subdiv_X using Y_subdiv_X
  apply stellar_weld_exists_iso t_in_Y y_nin_Y X_iso_Z Y_subdiv_X
  cases' X_move_Y with X_subdiv_Y X_iso_Y
  choose s s_in_X x x_nin_X X_subdiv_Y using X_subdiv_Y
  apply
    stellarSsubdivision_exists_iso s_in_X x_nin_X f f_inj X_iso_Z X_subdiv_Y
  use Z; constructor
  apply simplicialIso_trans X
  rw [simplicialIso_symm]
  assumption
  assumption
  rfl

theorem stellarEquiv_exists_iso
    [Nonempty E]
    {Z : AbstractSimplicialComplex F}
    (f_inj : Function.Injective f)
  : (X ≅ Z) → X ≅ₛₜ[𝕜] Y →
      ∃ W : AbstractSimplicialComplex F, (Y ≅ W) ∧ Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z X_eq_Y
  induction' X_eq_Y with K Y X_eq_K K_move_Y H_ind
  use Z

  choose L K_iso_L Z_eq_L using H_ind
  have Z_move_W : ∃ W : AbstractSimplicialComplex F, (Y ≅ W) ∧ L ≅ₛₜ[𝕜] W :=
  by
    apply stellarMove_exists_iso
    apply f_inj
    apply K_iso_L
    apply K_move_Y
  choose W Y_iso_W L_move_W using Z_move_W
  use W; constructor
  assumption
  apply stellarEquiv_trans
  assumption
  assumption

theorem stellarMove_iso
    [Nonempty E]
    {Z W : AbstractSimplicialComplex F}
    (f_inj : Function.Injective f)
  : (X ≅ Z) → (Y ≅ W) → X ≅ₛₜₘ[𝕜] Y → Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z Y_iso_W X_move_Y
  have Y_iso_L : ∃ L : AbstractSimplicialComplex F, (Y ≅ L) ∧ Z ≅ₛₜ[𝕜] L :=
  by
    apply stellarMove_exists_iso
    apply f_inj
    apply X_iso_Z
    apply X_move_Y
  choose L Y_iso_L Z_eq_L using Y_iso_L
  apply @Relation.ReflTransGen.tail _ _ _ L
  assumption
  right; right
  apply simplicialIso_trans Y
  rw [simplicialIso_symm]
  assumption
  assumption

theorem stellarEquiv_iso
    [Nonempty E]
    {Z W : AbstractSimplicialComplex F}
    (f_inj : Function.Injective f)
  : (X ≅ Z) → (Y ≅ W) → X ≅ₛₜ[𝕜] Y → Z ≅ₛₜ[𝕜] W :=
by
  intro X_iso_Z Y_iso_W X_eq_Y
  induction' X_eq_Y with K Y X_eq_K K_move_Y H_ind
  rw [simplicialIso_symm] at X_iso_Z
  apply stellarEquiv_preserves_iso
  apply simplicialIso_trans X <;> assumption
  have K_iso_L : ∃ L : AbstractSimplicialComplex F, (K ≅ L) ∧ Z ≅ₛₜ[𝕜] L :=
  by
    apply stellarEquiv_exists_iso
    apply f_inj
    apply X_iso_Z
    apply X_eq_K
  choose L K_iso_L Z_eq_L using K_iso_L
  apply stellarEquiv_trans
  assumption
  apply stellarMove_iso f_inj K_iso_L Y_iso_W K_move_Y
