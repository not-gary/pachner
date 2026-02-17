import Pachner.Stellar.StellarSubdivision

variable {E F 𝕜 : Type _}
variable [DecidableEq E] [DecidableEq F] [DecidableEq 𝕜]
variable [AddCommGroup E] [AddCommGroup F]
variable [Ring 𝕜] [Nontrivial 𝕜]

@[simp]
def stellarCoeMap (f : E → F) (x : E) (y : F) : E → F := fun a : E => if a = x then y else f a

theorem stellar_coe_simplex_image
    (s : Finset E)
    (x : E)
    (y : F)
    (f : E → F)
  : x ∉ s → Finset.image (stellarCoeMap f x y) s = Finset.image f s :=
by
  rw [Finset.ext_iff]
  intro x_nin_s b
  simp only [Finset.mem_image, stellarCoeMap]
  constructor
  · intro b_in_coe
    choose a a_in_s coe_a_b using b_in_coe
    revert coe_a_b
    split_ifs with a_eq_x
    rw [a_eq_x] at a_in_s
    contradiction
    intro fa_b
    use a
  · intro b_in_img
    choose a a_in_s fa_b using b_in_img
    use a; constructor; assumption
    split_ifs with a_eq_x
    rw [a_eq_x] at a_in_s
    contradiction
    assumption

theorem stellar_coe_forward_simplicial
    --[Nonempty E] TODO: keep this or not? seems redundant to [Nonempty s]
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : IsSimplicialMap
      σ(X, s, x; 𝕜, s_in_X, x_nin_X)
      σ(φ.coe ''ˢ X, Finset.image φ.coe s, y; 𝕜, by apply isSimplicialMap_onto_image; assumption, y_nin_coe)
      (stellarCoeMap φ.coe x y) :=
by
  simp only [IsSimplicialMap, stellarSubdivision, SimplicialUnion, Set.mem_union]
  intro t t_in_subdiv
  cases' t_in_subdiv with t_in_star_comp t_in_join

  left
  rw [starComplement_coe_image X s s_in_X φ, stellar_coe_simplex_image]
  apply isSimplicialMap_onto_image
  assumption
  revert x_nin_X
  contrapose
  simp only [Classical.not_not]
  revert x
  simp only [← Finset.mem_coe, ← Set.subset_def]
  apply simplex_subset_vertices
  apply isSubcomplex_face_imp_face
  exact starComplement_subcomplex_simplices X s t t_in_star_comp
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex]
  rfl

  right
  simp only [join_proj_mem, Set.mem_union] at t_in_join ⊢
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join
  cases' t'_in_join with t'_in_join t'_empty

  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join
  choose t'_decomp t'_nonempty using t'_decomp
  subst t'_decomp
  use Finset.image (stellarCoeMap φ.coe x y) (t₃ ∪ t₂)
  constructor

  left
  use Finset.image (stellarCoeMap φ.coe x y) t₃
  constructor

  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff, Set.mem_diff] at t₃_in_barycenter ⊢
  rw [and_or_right, or_comm, Set.mem_singleton_iff, ← or_assoc, or_self_iff] at t₃_in_barycenter
  choose t₃_in_barycenter _ using t₃_in_barycenter
  cases' t₃_in_barycenter with t₃_empty t₃_x


  subst t₃_empty
  right
  apply Finset.image_empty

  left
  constructor

  right
  rw [t₃_x, Finset.image_singleton]
  simp only [stellarCoeMap, eq_self_iff_true, if_true]

  rw [Set.mem_singleton_iff, Finset.image_eq_empty]
  subst t₃_x
  apply Finset.singleton_ne_empty

  use Finset.image (stellarCoeMap φ.coe x y) t₂
  cases' t₂_in_bd with t₂_in_bd t₂_empty

  constructor

  left
  rw [simplexBoundary_coe_image, stellar_coe_simplex_image]
  apply isSimplicialMap_onto_image
  assumption

  revert x_nin_X
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₂_in_X : ↑t₂ ⊆ X.vertices :=
    by
    apply simplex_subset_vertices
    apply isSubcomplex_face_imp_face
    apply t₂_in_bd
    apply simplexBoundary_subcomplex
    assumption
  rw [Set.subset_def] at t₂_in_X
  specialize t₂_in_X x
  assumption

  assumption

  constructor

  apply Finset.image_union

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  subst t₂_empty
  rw [Finset.image_empty]
  rw [Finset.union_empty]
  rw [Finset.union_empty] at t_decomp t'_nonempty ⊢
  constructor

  right
  rfl

  constructor

  rfl

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  choose t_decomp t_nonempty using t_decomp
  use Finset.image (stellarCoeMap φ.coe x y) t₁
  rw [← Finset.image_union]

  constructor

  cases' t₁_in_link with t₁_in_link t₁_empty

  left
  rw [link_coe_image, stellar_coe_simplex_image]
  apply isSimplicialMap_onto_image
  assumption
  revert x_nin_X
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₁_in_X : ↑t₁ ⊆ X.vertices :=
    by
    apply simplex_subset_vertices
    apply isSubcomplex_face_imp_face
    apply t₁_in_link
    apply link_subcomplex
  rw [Set.subset_def] at t₁_in_X
  specialize t₁_in_X x
  assumption
  assumption

  right
  subst t₁_empty
  apply Finset.image_empty

  constructor
  subst t_decomp
  rfl
  rw [ne_eq, Finset.image_eq_empty]
  assumption

  subst t'_empty
  rw [Finset.empty_union] at t_decomp
  choose t_eq_t₁ t_nonempty using t_decomp
  subst t_eq_t₁
  cases' t₁_in_link with t_in_link t_empty

  use ∅
  constructor

  right
  rfl

  use Finset.image (stellarCoeMap φ.coe x y) t
  constructor

  left
  rw [link_coe_image, stellar_coe_simplex_image]
  apply isSimplicialMap_onto_image
  assumption
  revert x_nin_X
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t_in_X : ↑t ⊆ X.vertices :=
    by
    apply simplex_subset_vertices
    apply isSubcomplex_face_imp_face
    apply t_in_link
    apply link_subcomplex
  rw [Set.subset_def] at t_in_X
  specialize t_in_X x
  assumption
  assumption

  constructor

  rw [Finset.empty_union]

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  contradiction

theorem stellar_coe_inverse_simplicial
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E)
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : IsSimplicialMap
      σ(φ.coe ''ˢ X, Finset.image φ.coe s, y; 𝕜, by apply isSimplicialMap_onto_image; assumption, y_nin_coe)
      σ(X, s, x; 𝕜, s_in_X, x_nin_X)
      (stellarCoeMap (φ⁻ᶜ.map) y x) :=
by
  simp only [IsSimplicialMap, stellarSubdivision, SimplicialUnion, Set.mem_union]
  intro t t_in_subdiv
  cases' t_in_subdiv with t_in_star_comp t_in_join

  left
  rw [stellar_coe_simplex_image]
  rw [starComplement_coe_image, simplicialImage_is_lift_image, Set.mem_image] at t_in_star_comp
  choose u u_in_star_comp φu_t using t_in_star_comp
  simp only [SimplicialMapLift] at φu_t
  rw [← φu_t]
  have inv_u : Finset.image (φ⁻ᶜ.map) (Finset.image φ.coe u) = u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.Injective
    apply simplex_subset_vertices
    apply isSubcomplex_face_imp_face
    apply u_in_star_comp
    apply starComplement_subcomplex
  rw [inv_u]
  assumption
  assumption
  revert y_nin_coe
  contrapose
  simp only [Classical.not_not]
  revert y
  simp only [← Finset.mem_coe, ← Set.subset_def]
  apply simplex_subset_vertices
  apply isSubcomplex_face_imp_face
  assumption
  apply starComplement_subcomplex

  right
  simp only [join_proj_mem, Set.mem_union] at t_in_join ⊢
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join
  cases' t'_in_join with t'_in_join t'_empty

  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join
  choose t'_decomp t'_nonempty using t'_decomp
  subst t'_decomp
  use Finset.image (stellarCoeMap (φ⁻ᶜ.map) y x) (t₃ ∪ t₂)
  constructor

  left
  use Finset.image (stellarCoeMap (φ⁻ᶜ.map) y x) t₃
  constructor

  simp only [simplex, Finset.mem_coe, Finset.mem_powerset, Finset.subset_singleton_iff, Set.mem_diff] at t₃_in_barycenter ⊢
  rw [and_or_right, or_comm, Set.mem_singleton_iff, ← or_assoc, or_self_iff] at t₃_in_barycenter
  choose t₃_in_barycenter _ using t₃_in_barycenter
  cases' t₃_in_barycenter with t₃_empty t₃_x

  subst t₃_empty
  rw [Finset.image_empty]
  right
  rfl

  subst t₃_x
  rw [Finset.image_singleton]
  rw [and_or_right, or_comm, Set.mem_singleton_iff, ← or_assoc, or_self_iff]
  simp only [stellarCoeMap, if_true, or_true, Finset.singleton_ne_empty, not_false_eq_true, or_false, and_true]

  use Finset.image (stellarCoeMap (φ⁻ᶜ.map) y x) t₂
  constructor

  cases' t₂_in_bd with t₂_in_bd t₂_empty

  left
  rw [stellar_coe_simplex_image]
  rw [simplexBoundary_coe_image, simplicialImage_is_lift_image, Set.mem_image] at t₂_in_bd
  choose u u_in_bd φu_t₂ using t₂_in_bd
  simp only [SimplicialMapLift] at φu_t₂
  rw [← φu_t₂]
  have inv_u : Finset.image (φ⁻ᶜ.map) (Finset.image φ.coe u) = u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.Injective
    apply simplex_subset_vertices
    apply isSubcomplex_face_imp_face
    apply u_in_bd
    apply simplexBoundary_subcomplex
    assumption
  rw [inv_u]
  assumption
  assumption
  revert y_nin_coe
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₂_in_X : ↑t₂ ⊆ (φ.coe ''ˢ X).vertices :=
    by
    apply simplex_subset_vertices
    apply isSubcomplex_face_imp_face
    apply t₂_in_bd
    apply simplexBoundary_subcomplex
    apply isSimplicialMap_onto_image
    assumption
  rw [Set.subset_def] at t₂_in_X
  specialize t₂_in_X y
  assumption

  right
  subst t₂_empty
  apply Finset.image_empty

  constructor

  rw [Finset.image_union]
  rw [ne_eq, Finset.image_eq_empty]
  assumption

  simp only [ne_eq, Finset.image_eq_empty, t'_nonempty, not_false_eq_true]

  use Finset.image (stellarCoeMap (φ⁻ᶜ.map) y x) t₁
  cases' t₁_in_link with t₁_in_link t₁_empty

  constructor

  rw [stellar_coe_simplex_image]
  rw [link_coe_image, simplicialImage_is_lift_image, Set.mem_image] at t₁_in_link

  left
  choose u u_in_link φu_t₁ using t₁_in_link
  simp only [SimplicialMapLift] at φu_t₁
  rw [← φu_t₁]
  have inv_u : Finset.image (φ⁻ᶜ.map) (Finset.image φ.coe u) = u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.Injective
    apply simplex_subset_vertices
    apply isSubcomplex_face_imp_face
    apply u_in_link
    apply link_subcomplex
  rw [inv_u]
  assumption
  assumption

  revert y_nin_coe
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₁_in_X : ↑t₁ ⊆ (φ.coe ''ˢ X).vertices :=
    by
    apply simplex_subset_vertices
    apply isSubcomplex_face_imp_face
    apply t₁_in_link
    apply link_subcomplex
  rw [Set.subset_def] at t₁_in_X
  specialize t₁_in_X y
  assumption

  choose t_decomp t_nonempty using t_decomp
  constructor

  subst t_decomp
  rw [← Finset.image_union]

  assumption

  subst t₁_empty
  rw [Finset.image_empty]
  constructor

  right
  rfl

  choose t_decomp t_nonempty using t_decomp
  constructor

  rw [Finset.union_empty] at t_decomp ⊢
  subst t_decomp
  rw [Finset.image_union]

  assumption

  subst t'_empty
  rw [Finset.empty_union] at t_decomp
  choose t_eq_t₁ t_nonempty using t_decomp
  subst t_eq_t₁
  cases' t₁_in_link with t_in_link t_empty

  use ∅

  constructor

  right
  rfl

  use Finset.image (stellarCoeMap (φ⁻ᶜ.map) y x) t
  constructor

  left
  rw [stellar_coe_simplex_image]
  rw [link_coe_image, simplicialImage_is_lift_image, Set.mem_image] at t_in_link
  choose u u_in_link φu_t using t_in_link
  simp only [SimplicialMapLift] at φu_t
  rw [← φu_t]
  have inv_u : Finset.image (φ⁻ᶜ.map) (Finset.image φ.coe u) = u :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.Injective
    apply simplex_subset_vertices
    apply isSubcomplex_face_imp_face
    apply u_in_link
    apply link_subcomplex
  rw [inv_u]
  assumption
  assumption

  revert y_nin_coe
  contrapose
  simp only [Classical.not_not, ← Finset.mem_coe]
  have t₁_in_X : ↑t ⊆ (φ.coe ''ˢ X).vertices :=
    by
    apply simplex_subset_vertices
    apply isSubcomplex_face_imp_face
    apply t_in_link
    apply link_subcomplex
  rw [Set.subset_def] at t₁_in_X
  specialize t₁_in_X y
  assumption

  constructor

  rw [Finset.empty_union]

  rw [ne_eq, Finset.image_eq_empty]
  assumption

  contradiction

def stellarCoeForward
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : SimplicialMap
      σ(X, s, x; 𝕜, s_in_X, x_nin_X)
      σ(φ.coe ''ˢ X, Finset.image φ.coe s, y; 𝕜, by apply isSimplicialMap_onto_image; assumption, y_nin_coe) :=
  SimplicialMap.mk (stellarCoeMap φ.coe x y)
    (stellar_coe_forward_simplicial X φ s x y s_in_X x_nin_X y_nin_coe)

noncomputable def stellarCoeInverse
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E)
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : SimplicialMap
      σ(φ.coe ''ˢ X, Finset.image φ.coe s, y; 𝕜, by apply isSimplicialMap_onto_image; assumption, y_nin_coe)
      σ(X, s, x; 𝕜, s_in_X, x_nin_X) :=
  SimplicialMap.mk (stellarCoeMap (φ⁻ᶜ.map) y x)
    (stellar_coe_inverse_simplicial X φ s x y s_in_X x_nin_X y_nin_coe)

theorem stellar_coe_vertices
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E)
    (x : E)
    (y : F)
    (x_nin_X : x ∉ X.vertices)
  : (SimplicialImage (stellarCoeMap φ.coe x y) X).vertices = (φ.coe ''ˢ X).vertices :=
by
  simp only [simplicialImage_vertices, Set.ext_iff, Set.mem_image]
  intro t
  constructor <;>
    · intro t_in_img
      choose u u_in_X coe_u_t using t_in_img
      use u; constructor; assumption
      rw [← coe_u_t]
      have u_ne_x : u ≠ x := by
        by_contra u_eq_x
        rw [u_eq_x] at u_in_X
        contradiction
      simp only [stellarCoeMap, u_ne_x, if_false]

theorem stellar_coe_image
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : σ(SimplicialImage (stellarCoeMap φ.coe x y) X, Finset.image (stellarCoeMap φ.coe x y) s,
        (stellarCoeMap φ.coe x y) x; 𝕜, by apply isSimplicialMap_onto_image; assumption,
        by
          simp only [stellarCoeMap, ↓reduceIte]
          rw [stellar_coe_vertices X φ s x y] <;> assumption)
      ≅ σ(SimplicialImage φ.coe X, Finset.image φ.coe s, y; 𝕜,
          by
            apply isSimplicialMap_onto_image
            assumption,
          y_nin_coe) :=
by
  have x_nin_s : x ∉ s := by
    revert x_nin_X
    contrapose
    simp only [Classical.not_not, ← Finset.mem_coe]
    have s_ss_X : ↑s ⊆ X.vertices := by
      apply simplex_subset_vertices
      assumption
    rw [Set.subset_def] at s_ss_X
    specialize s_ss_X x
    assumption
  simp only [stellar_coe_simplex_image s x y φ.coe x_nin_s]
  simp only [stellarCoeMap, eq_self_iff_true, if_true]
  rw [stellar_subdiv_congr]
  rw [simplicialImage_congr]
  simp only [Set.EqOn]
  intro z z_in_X

  simp only [stellarCoeMap, ite_eq_right_iff]
  intros h
  rw [h] at z_in_X
  contradiction

theorem stellar_coe_inv_iso
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : IsInverseSimplicialIso (stellarCoeForward X φ s x y s_in_X x_nin_X y_nin_coe)
      (@stellarCoeInverse _ _ 𝕜 _ _ _ _ _ _ _ X φ s x y s_in_X x_nin_X y_nin_coe) :=
by
  unfold IsInverseSimplicialIso
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply, id]
  simp only [stellarCoeInverse, stellarCoeForward]
  constructor
  · intro a a_in_subdiv
    have a_in_union : a ∈ X.vertices ∪ {x} :=
    by
      apply Set.mem_of_mem_of_subset a_in_subdiv
      apply stellar_subdiv_subset_vertices
    rw [Set.mem_union, Set.mem_singleton_iff] at a_in_union
    cases' a_in_union with a_in_X a_eq_x
    have a_ne_x : ¬a = x := by
      by_cases a_eq_x : a = x
      rw [a_eq_x] at a_in_X
      contradiction
      assumption
    have φa_ne_y : ¬φ.coe a = y := by
      by_cases φa_eq_y : φ.coe a = y
      have contra : y ∈ (φ.coe ''ˢ X).vertices :=
        by
        rw [simplicialImage_vertices, Set.mem_image]
        use a
      contradiction
      assumption
    simp only [stellarCoeMap, a_ne_x, φa_ne_y, if_false]
    apply Set.InjOn.leftInvOn_invFunOn
    apply φ.Injective
    assumption
    simp only [stellarCoeMap, a_eq_x, eq_self_iff_true, if_true]
  · intro b b_in_coe
    have b_in_union : b ∈ (φ.coe ''ˢ X).vertices ∪ {y} :=
    by
      apply Set.mem_of_mem_of_subset
      apply b_in_coe
      have φs_ne : Nonempty {x // x ∈ Finset.image φ.coe s} :=
      by
        rw [Finset.nonempty_coe_sort, Finset.image_nonempty, ← Finset.nonempty_coe_sort]
        assumption
      apply stellar_subdiv_subset_vertices
    rw [Set.mem_union, Set.mem_singleton_iff] at b_in_union
    cases' b_in_union with b_in_X b_eq_y
    have b_ne_y : ¬b = y := by
      by_cases b_eq_y : b = y
      rw [b_eq_y] at b_in_X
      contradiction
      assumption
    have φb_ne_x : ¬φ⁻ᶜ.map b = x :=
      by
      by_cases φb_eq_x : φ⁻ᶜ.map b = x
      rw [simplicialImage_vertices, Set.mem_image] at b_in_X
      choose a a_in_X φa_b using b_in_X
      rw [← φa_b] at φb_eq_x
      have inv_a : φ⁻ᶜ.map (φ.coe a) = a :=
        by
        simp only [SimplicialCoeInv]
        apply Set.InjOn.leftInvOn_invFunOn
        apply φ.Injective
        assumption
      rw [inv_a] at φb_eq_x
      rw [φb_eq_x] at a_in_X
      contradiction
      assumption
    simp only [stellarCoeMap, b_ne_y, φb_ne_x, if_false]
    simp only [SimplicialCoeInv]
    apply Function.invFunOn_eq
    simp only [simplicialImage_vertices, Set.mem_image] at b_in_X
    assumption
    simp only [stellarCoeMap, b_eq_y, eq_self_iff_true, if_true]

theorem stellar_coe_iso
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (s : Finset E) [s_ne : Nonempty s]
    (x : E)
    (y : F)
    (s_in_X : s ∈ X.faces)
    (x_nin_X : x ∉ X.vertices)
    (y_nin_coe : y ∉ (φ.coe ''ˢ X).vertices)
  : IsSimplicialIso (@stellarCoeForward _ _ 𝕜 _ _ _ _ _ _ _ X φ s _ x y s_in_X x_nin_X y_nin_coe) :=
by
  use stellarCoeInverse X φ s x y s_in_X x_nin_X y_nin_coe
  apply stellar_coe_inv_iso
