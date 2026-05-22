import Pachner.Maps.SimplicialMap

section Isomorphism

variable
  {E F G : Type _}
  [DecidableEq E] [DecidableEq F] [DecidableEq G]
  {X : AbstractSimplicialComplex E} {Y : AbstractSimplicialComplex F} {Z : AbstractSimplicialComplex G}

structure SimplicialIso (X : AbstractSimplicialComplex E) (Y : AbstractSimplicialComplex F) where
  toFun : SimplicialMap X Y -- this naming convention follows (Partial)Equiv, there is also the one from CategoryTheory
  invFun : SimplicialMap Y X -- which would be 'hom' and 'inv'
  left_inv : ∀ {x : E}, x ∈ X.vertices → invFun.map (toFun.map x) = x
  right_inv : ∀ {x : F}, x ∈ Y.vertices → toFun.map (invFun.map x) = x

infixr:50 " ≅' " => SimplicialIso

def SimplicialIso.id' : X ≅' X where
  toFun := idSimplicialMap X
  invFun := idSimplicialMap X
  left_inv := by simp only [idSimplicialMap, _root_.id, imp_true_iff]
  right_inv := by simp only [idSimplicialMap, _root_.id, imp_true_iff]

def SimplicialIso.comp (f : X ≅' Y) (g : Y ≅' Z) : X ≅' Z where
  toFun := f.toFun.comp g.toFun
  invFun := g.invFun.comp f.invFun
  left_inv := by
    intro x x_in_X
    simp only [SimplicialMap.comp, Function.comp_apply]
    rw [g.left_inv (simplicialMap_on_vertices f.toFun x_in_X), f.left_inv x_in_X]
  right_inv := by
    intro x x_in_Z
    simp only [SimplicialMap.comp, Function.comp_apply]
    rw [f.right_inv (simplicialMap_on_vertices g.invFun x_in_Z), g.right_inv x_in_Z]

@[refl]
def SimplicialIso.refl : X ≅' X := id'

@[symm]
def SimplicialIso.symm (f : X ≅' Y) : Y ≅' X where
  toFun := f.invFun
  invFun := f.toFun
  left_inv := f.right_inv
  right_inv := f.left_inv

@[trans]
def SimplicialIso.trans (f : X ≅' Y) (g : Y ≅' Z) : X ≅' Z := f.comp g

instance SimplicialIso.Trans : Trans (@SimplicialIso E F _ _) (@SimplicialIso F G _ _) (@SimplicialIso E G _ _) where
    trans := SimplicialIso.trans

theorem SimplicialIso.EqOn_id_left (f : X ≅' Y) : Set.EqOn (f.invFun.map ∘ f.toFun.map) id X.vertices := by
  intro x x_in_X
  rw [Function.comp_apply, id, f.left_inv x_in_X]

theorem SimplicialIso.EqOn_id_right (f : X ≅' Y) : Set.EqOn (f.toFun.map ∘ f.invFun.map) id Y.vertices := by
  intro y y_in_Y
  rw [Function.comp_apply, id, f.right_inv y_in_Y]

theorem SimplicialIso.injective_vertices (f : X ≅' Y) : Set.InjOn f.toFun.map (X.vertices) := by
  intro x x_in_X y y_in_X fx_eq_fy
  apply_fun f.invFun.map at fx_eq_fy
  rw [f.left_inv x_in_X, f.left_inv y_in_X] at fx_eq_fy
  exact fx_eq_fy

theorem SimplicialIso.surjective_vertices (f : X ≅' Y) : Set.SurjOn f.toFun.map X.vertices Y.vertices := by
  simp only [Set.SurjOn, Set.subset_def, Set.mem_image]
  intro x x_in_Y
  exact ⟨f.invFun.map x, ⟨simplicialMap_on_vertices f.invFun x_in_Y, f.right_inv x_in_Y⟩⟩

theorem SimplicialIso.bijective_vertices (f : X ≅' Y) : Set.BijOn f.toFun.map X.vertices Y.vertices := by
  refine ⟨?_, ⟨f.injective_vertices, f.surjective_vertices⟩⟩
  · intro x x_in_X
    exact simplicialMap_on_vertices f.toFun x_in_X

theorem SimplicialIso.congr_vertices (f : X ≅' Y) : f.toFun.map '' X.vertices = Y.vertices := by
  exact Set.BijOn.image_eq f.bijective_vertices

theorem SimplicialIso.injective_faces (f : X ≅' Y) : ∀ s ∈ X.faces, Set.InjOn f.toFun.map ↑s := by
  intro s s_in_X
  exact Set.InjOn.mono (face_subset_vertices s_in_X) f.injective_vertices

theorem SimplicialIso.simplicialMapLift_bijective (f : X ≅' Y) : Y.faces = (Finset.image f.toFun.map) '' X.faces := by
  rw [Set.ext_iff]
  intro t
  simp only [Set.mem_image]
  constructor
  · intro t_in_Y
    refine ⟨Finset.image f.invFun.map t, ⟨f.invFun.is_simplicial t t_in_Y, ?_⟩⟩
    · simp only [← Finset.coe_inj, Finset.coe_image, ← Set.image_comp,
        Set.EqOn.image_eq (Set.EqOn.mono (face_subset_vertices t_in_Y) f.EqOn_id_right), Set.image_id]
  · intro t_in_image
    rcases t_in_image with ⟨s, s_in_X, fs_eq_t⟩
    subst fs_eq_t
    exact f.toFun.is_simplicial s s_in_X

theorem SimplicialIso.face_mapsTo_face_inv {s : Finset E} {t : Finset F} (f : X ≅' Y) (s_in_X : s ∈ X.faces)
    (fs_eq_t : Finset.image f.toFun.map s = t) : Finset.image f.invFun.map t = s := by
  rw [← fs_eq_t, Finset.ext_iff, Finset.image_image]
  intro x
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · intro x_in_img
    rcases x_in_img with ⟨y, y_in_s, gfy_eq_x⟩
    subst x
    rw [f.left_inv (vertex_if_mem_face s_in_X y_in_s)]
    exact y_in_s
  · intro x_in_s
    exact ⟨x, ⟨x_in_s, f.left_inv (vertex_if_mem_face s_in_X x_in_s)⟩⟩

section SynthOrder
set_option synthInstance.checkSynthOrder false
instance SimplicialIso.fintype (f : X ≅' Y) [Fintype X.faces] : Fintype Y.faces := by
  rw [f.simplicialMapLift_bijective]
  exact Set.fintypeImage X.faces (Finset.image f.toFun.map)
end SynthOrder

theorem SimplicialIso.preserves_face_dim (f : X ≅' Y) : ∀ s ∈ X.faces, face_dim s = face_dim (Finset.image f.toFun.map s) := by
  intro s s_in_X
  unfold face_dim
  apply congr_arg fun z : ℤ => z - 1
  symm
  rw [Nat.cast_inj, Finset.card_image_iff]
  exact f.injective_faces s s_in_X

theorem SimplicialIso.preserves_dim (f : X ≅' Y) [Fintype X.faces] : X.dim = @Y.dim _ (SimplicialIso.fintype f) := by
  have Y_fin : Fintype Y.faces := by exact SimplicialIso.fintype f
  simp only [AbstractSimplicialComplex.dim]
  rw [le_antisymm_iff]
  constructor
  -- dim X ≤ dim Y case.
  · rw [Finset.max'_le_iff]
    intro n n_X_dim
    rw [Finset.mem_union, Finset.mem_image] at n_X_dim
    rcases n_X_dim with ⟨s, s_in_X, s_dim_n⟩ | X_empty
    · rw [Set.mem_toFinset] at s_in_X
      rw [← s_dim_n]
      apply Finset.le_max'
      rw [f.preserves_face_dim s s_in_X, Finset.mem_union, Finset.mem_image]
      refine Or.inl ⟨Finset.image f.toFun.map s, ⟨?_, rfl⟩⟩
      · simp only [Set.mem_toFinset]
        exact f.toFun.is_simplicial s s_in_X
    · apply Finset.le_max'
      rw [Finset.mem_union]
      exact Or.inr X_empty
  -- dim Y ≤ dim X case.
  · rw [Finset.max'_le_iff]
    intro m m_Y_dim
    rw [Finset.mem_union, Finset.mem_image] at m_Y_dim
    rcases m_Y_dim with ⟨t, t_in_Y, t_dim_m⟩ | Y_empty
    · simp only [Set.mem_toFinset] at t_in_Y
      rw [← t_dim_m]
      apply Finset.le_max'
      rw [f.symm.preserves_face_dim t t_in_Y, Finset.mem_union, Finset.mem_image]
      refine Or.inl ⟨Finset.image f.invFun.map t, ⟨?_, rfl⟩⟩
      · rw [Set.mem_toFinset]
        exact f.invFun.is_simplicial t t_in_Y
    · apply Finset.le_max'
      rw [Finset.mem_union]
      exact Or.inr Y_empty

@[simp, deprecated "use individually" (since := "")]
def IsInverseSimplicialIso
    (f : SimplicialMap X Y)
    (g : SimplicialMap Y X)
  : Prop :=
    (X.vertices).restrict (SimplicialMap.comp f g).map = (X.vertices).restrict id ∧
    (Y.vertices).restrict (SimplicialMap.comp g f).map = (Y.vertices).restrict id

@[deprecated "IsInverseSimplicialIso unused" (since := "")]
theorem isInverseSimplicialIso_symm
    (f : SimplicialMap X Y)
    (g : SimplicialMap Y X)
  : IsInverseSimplicialIso f g ↔ IsInverseSimplicialIso g f :=
by
  constructor <;> unfold IsInverseSimplicialIso
  · intro f_inv_g
    cases' f_inv_g with fg_id gf_id
    constructor <;> assumption
  · intro g_inv_f
    cases' g_inv_f with gf_id fg_id
    constructor <;> assumption

@[simp, deprecated SimplicialIso (since := "")]
def IsSimplicialIso (f : SimplicialMap X Y) : Prop :=
    ∃ g : SimplicialMap Y X, IsInverseSimplicialIso f g

@[deprecated SimplicialIso.id' (since := "")]
theorem id_isSimplicialIso : IsSimplicialIso (idSimplicialMap X) := by
  use idSimplicialMap X
  simp only [IsInverseSimplicialIso, Set.restrict_id, and_self]
  tauto

@[deprecated SimplicialIso.symm (since := "")]
theorem simplicialIso_inverse_is_simplicialIso
    (f : SimplicialMap X Y)
    (g : SimplicialMap Y X)
  : IsSimplicialIso f → IsInverseSimplicialIso f g → IsSimplicialIso g :=
by
  intro f_iso g_inv_f
  unfold IsSimplicialIso
  use f
  rw [IsInverseSimplicialIso] at g_inv_f ⊢
  rw [and_comm]
  assumption

@[deprecated SimplicialIso.comp (since := "")]
theorem simplicialIso.comp
    (f : SimplicialMap X Y)
    (g : SimplicialMap Y Z)
  : IsSimplicialIso f → IsSimplicialIso g → IsSimplicialIso (SimplicialMap.comp f g) :=
by
  unfold IsSimplicialIso
  intro f_iso g_iso
  choose f_inv f_iso using f_iso
  choose g_inv g_iso using g_iso
  use g_inv.comp f_inv
  simp only [IsInverseSimplicialIso, SimplicialMap.comp, idSimplicialMap] at *
  cases' f_iso with f_inv_left f_inv_right
  cases' g_iso with g_inv_left g_inv_right
  simp only [Set.restrict_eq_restrict_iff] at *
  unfold Set.EqOn at *
  constructor
  intro x x_vert
  specialize f_inv_left x_vert
  specialize g_inv_left (simplicialMap_on_vertices f x_vert)
  rw [Function.comp_assoc, ← Function.comp_assoc g_inv.map, Function.comp_apply, Function.comp_apply, g_inv_left]
  simp
  assumption
  intro z z_vert
  specialize g_inv_right z_vert
  specialize f_inv_right (simplicialMap_on_vertices g_inv z_vert)
  rw [Function.comp_assoc, ← Function.comp_assoc f.map, Function.comp_apply, Function.comp_apply, f_inv_right]
  simp
  assumption

@[deprecated SimplicialIso.injective_vertices (since := "")]
theorem simplicialIso_injective_vertices
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : Set.InjOn f.map (X.vertices) :=
by
  unfold IsSimplicialIso at f_iso
  choose g g_inv_f using f_iso
  unfold IsInverseSimplicialIso at g_inv_f
  choose fg_id gf_id using g_inv_f
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn] at fg_id
  unfold Set.InjOn
  intro x₁ x₁_in_X x₂ x₂_in_X fx₁_eq_fx₂
  have fgx₁_eq_x₁ : (f.comp g).map x₁ = id x₁ :=
    by
    specialize fg_id x₁_in_X
    assumption
  have fgx₂_eq_x₂ : (f.comp g).map x₂ = id x₂ :=
    by
    specialize fg_id x₂_in_X
    assumption
  simp only [SimplicialMap.comp, Function.comp_apply] at fgx₁_eq_x₁ fgx₂_eq_x₂
  simp only [fx₁_eq_fx₂, fgx₂_eq_x₂] at fgx₁_eq_x₁
  symm
  assumption

@[deprecated SimplicialIso.injective_faces (since := "")]
theorem simplicialIso_injective_faces
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : ∀ s ∈ X.faces, Set.InjOn f.map ↑s :=
by
  intro s s_in_X
  simp only [Set.InjOn]
  intro x₁ x₁_in_s x₂ x₂_in_s fx₁_eq_fx₂
  unfold IsSimplicialIso at f_iso
  choose g gf_inv using f_iso
  unfold IsInverseSimplicialIso at gf_inv
  choose gf_id fg_id using gf_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply] at gf_id
  have x₁_in_X : x₁ ∈ X.vertices := by
    rw [vertex_iff_in_face]
    use s; constructor <;> assumption
  have x₂_in_X : x₂ ∈ X.vertices := by
    rw [vertex_iff_in_face]
    use s; constructor <;> assumption
  have gfx₁_eq_x₁ : g.map (f.map x₁) = x₁ :=
    by
    specialize gf_id x₁_in_X
    assumption
  have gfx₂_eq_x₂ : g.map (f.map x₂) = x₂ :=
    by
    specialize gf_id x₂_in_X
    assumption
  have gfx₁_eq_gfx₂ : g.map (f.map x₁) = g.map (f.map x₂) :=
    by
    apply congr_arg g.map
    assumption
  rw [gfx₁_eq_x₁, gfx₂_eq_x₂] at gfx₁_eq_gfx₂
  assumption

@[deprecated SimplicialIso.surjective_vertices (since := "")]
theorem simplicialIso_surjective_vertices
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : Set.SurjOn f.map (X.vertices) (Y.vertices) :=
by
  unfold IsSimplicialIso at f_iso
  choose g g_inv_f using f_iso
  unfold IsInverseSimplicialIso at g_inv_f
  choose fg_id gf_id using g_inv_f
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn] at gf_id
  simp only [Set.SurjOn, Set.subset_def, Set.mem_image]
  intro x x_in_Y
  specialize gf_id x_in_Y
  simp only [SimplicialMap.comp, Function.comp_apply] at gf_id
  use g.map x; constructor
  rw [vertex_iff_in_face] at x_in_Y ⊢
  choose s s_in_Y x_in_s using x_in_Y
  use Finset.image g.map s; constructor
  apply g.is_simplicial
  assumption
  apply Finset.mem_image_of_mem
  assumption
  assumption

@[simp, deprecated SimplicialIso (since := "")]
def IsSimpliciallyIso
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
  : Prop :=
    ∃ f : SimplicialMap X Y, IsSimplicialIso f

@[deprecated SimplicialIso (since := "")]
infixr:50 " ≅ " => IsSimpliciallyIso

@[deprecated SimplicialIso.simplicialMapLift_bijective (since := "")]
theorem simplicialIso_imp_simplicialMapLift_bijective
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : Y.faces = SimplicialMapLift f '' X.faces :=
by
  unfold IsSimplicialIso at f_iso
  choose g g_inv_f using f_iso
  unfold IsInverseSimplicialIso at g_inv_f
  choose fg_id gf_id using g_inv_f
  rw [Set.ext_iff]
  intro t
  constructor
  intro t_in_Y
  simp only [SimplicialMapLift, Set.mem_image]
  use Finset.image g.map t
  constructor
  apply g.is_simplicial
  assumption
  simp only [← Finset.coe_inj, Finset.coe_image]
  rw [← Set.image_comp]
  conv_rhs => rw [← @Set.image_id F ↑t]
  apply Set.EqOn.image_eq
  simp only [Set.restrict_eq_restrict_iff, SimplicialMap.comp] at gf_id
  have t_in_vert : ↑t ⊆ Y.vertices := by apply face_subset_vertices t_in_Y
  apply Set.EqOn.mono t_in_vert
  assumption
  intro t_in_lift
  simp only [SimplicialMapLift, Set.mem_image] at t_in_lift
  choose s s_in_X fs_eq_t using t_in_lift
  subst fs_eq_t
  apply f.is_simplicial
  assumption

@[deprecated SimplicialIso.congr_vertices (since := "")]
theorem simplicialIso_vertices
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : Y.vertices = f.map '' X.vertices :=
by
  unfold IsSimplicialIso at f_iso
  choose g gf_inv using f_iso
  unfold IsInverseSimplicialIso at gf_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    Set.image_id] at gf_inv
  choose gf_id fg_id using gf_inv
  rw [Set.ext_iff]
  intro x
  constructor
  intro x_in_Y
  specialize fg_id x_in_Y
  rw [Set.mem_image]
  use g.map x; constructor
  rw [AbstractSimplicialComplex.mem_vertices] at x_in_Y ⊢
  rw [← Finset.image_singleton]
  apply g.is_simplicial
  assumption
  assumption
  intro x_in_img
  rw [Set.mem_image] at x_in_img
  choose y y_in_X fy_eq_x using x_in_img
  rw [AbstractSimplicialComplex.mem_vertices] at y_in_X ⊢
  rw [← fy_eq_x, ← Finset.image_singleton]
  apply f.is_simplicial
  assumption

section SynthOrder
set_option synthInstance.checkSynthOrder false
@[deprecated SimplicialIso.fintype (since := "")]
noncomputable instance IsSimpliciallyIso.Fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (Y : AbstractSimplicialComplex F)
    (X_iso_Y : IsSimpliciallyIso X Y)
  : Fintype Y.faces :=
by
  unfold IsSimpliciallyIso at X_iso_Y
  choose f f_iso using X_iso_Y
  rw [simplicialIso_imp_simplicialMapLift_bijective f f_iso]
  apply Set.fintypeImage
end SynthOrder

@[deprecated SimplicialIso.preserves_face_dim (since := "")]
theorem simplicialIso_preserves_face_dim
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f) :
    ∀ s ∈ X.faces, face_dim s = face_dim (Finset.image f.map s) :=
by
  intro s s_in_X
  unfold face_dim
  apply congr_arg fun z : ℤ => z - 1
  symm
  rw [Nat.cast_inj, Finset.card_image_iff]
  apply simplicialIso_injective_faces f f_iso s s_in_X

@[deprecated SimplicialIso.preserves_dim (since := "")]
theorem simplicialIso_preserves_dim
    [Fintype X.faces]
    (X_iso_Y : X ≅ Y) :
    X.dim = @Y.dim _ (IsSimpliciallyIso.Fintype X Y X_iso_Y) :=
by
  have Y_fin : Fintype Y.faces :=
  by
    apply IsSimpliciallyIso.Fintype X Y X_iso_Y

  unfold IsSimpliciallyIso at X_iso_Y
  have X_iso_Y' := X_iso_Y
  choose f f_iso using X_iso_Y'
  simp only [AbstractSimplicialComplex.dim]
  rw [le_antisymm_iff]
  constructor
  -- dim X ≤ dim Y case.
  rw [Finset.max'_le_iff]
  intro n n_X_dim
  rw [Finset.mem_union, Finset.mem_image] at n_X_dim
  cases' n_X_dim with n_X_dim X_empty
  choose s s_in_X s_dim_n using n_X_dim
  rw [Set.mem_toFinset] at s_in_X
  rw [← s_dim_n]
  apply Finset.le_max'
  rw [simplicialIso_preserves_face_dim f f_iso s s_in_X, Finset.mem_union, Finset.mem_image]
  left
  use Finset.image f.map s
  constructor
  simp only [Set.mem_toFinset]
  apply f.is_simplicial
  assumption
  rfl

  apply Finset.le_max'
  rw [Finset.mem_union]
  right
  assumption

  -- dim Y ≤ dim X case.
  rw [Finset.max'_le_iff]
  intro m m_Y_dim
  rw [Finset.mem_union, Finset.mem_image] at m_Y_dim
  cases' m_Y_dim with m_Y_dim Y_empty
  choose t t_in_Y t_dim_m using m_Y_dim
  simp only [Set.mem_toFinset] at t_in_Y
  rw [← t_dim_m]
  let f_iso' := f_iso
  unfold IsSimplicialIso at f_iso'
  choose g gf_inv using f_iso'
  have g_iso : IsSimplicialIso g := by apply simplicialIso_inverse_is_simplicialIso f g f_iso gf_inv
  apply Finset.le_max'
  rw [simplicialIso_preserves_face_dim g g_iso t t_in_Y, Finset.mem_union, Finset.mem_image]
  left
  use Finset.image g.map t
  constructor
  rw [Set.mem_toFinset]
  apply g.is_simplicial
  assumption
  rfl

  apply Finset.le_max'
  rw [Finset.mem_union]
  right
  assumption

-- Being simplicially isomorphic is an equivalence relation.
@[refl, deprecated SimplicialIso.refl (since := "")]
theorem simplicialIso_refl : X ≅ X := by
  unfold IsSimpliciallyIso
  use idSimplicialMap X
  apply id_isSimplicialIso

@[symm, deprecated SimplicialIso.symm (since := "")]
theorem simplicialIso_symm : (X ≅ Y) ↔ (Y ≅ X) := by
  unfold IsSimpliciallyIso
  constructor <;> unfold IsSimplicialIso
  · intro X_iso_Y
    choose f g f_inv_g using X_iso_Y
    use g; use f
    rw [isInverseSimplicialIso_symm]
    assumption
  · intro Y_iso_X
    choose f g f_inv_g using Y_iso_X
    use g; use f
    rw [isInverseSimplicialIso_symm]
    assumption

@[trans, deprecated SimplicialIso.trans (since := "")]
theorem simplicialIso_trans (Y : AbstractSimplicialComplex F) : (X ≅ Y) → Y ≅ Z → X ≅ Z := by
  intro X_iso_Y Y_iso_Z
  unfold IsSimpliciallyIso at *
  choose f f_iso using X_iso_Y
  choose g g_iso using Y_iso_Z
  use f.comp g
  apply simplicialIso.comp <;> assumption

@[deprecated SimplicialIso.Trans (since := "")]
instance IsSimpliciallyIso.Trans
  : Trans (@IsSimpliciallyIso E F _ _) (@IsSimpliciallyIso F G _ _) (@IsSimpliciallyIso E G _ _) where
    trans := simplicialIso_trans _

@[deprecated "should not be a necessary theorem, use rw and SimplicialIso.refl or id" (since := "")]
theorem simplicialIso_preserves_equiv
    {X Y : AbstractSimplicialComplex E}
  : X.faces = Y.faces → X ≅ Y :=
by
  intro H
  have X_eq_Y : X = Y := by rw [AbstractSimplicialComplex.ext_iff, H]
  rw [X_eq_Y]

end Isomorphism
