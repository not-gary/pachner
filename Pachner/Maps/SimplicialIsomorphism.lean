import Pachner.Maps.SimplicialMap

/-
# Simplicial isomorphisms
-/
section Isomorphism

variable {E F G : Type _}
variable [DecidableEq E] [DecidableEq F] [DecidableEq G]

-- A simplicial map is a simplicial isomorphism
-- if it admits an inverse simplicial map.

@[simp]
def IsInverseSimplicialIso
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
    (f : SimplicialMap X Y)
    (g : SimplicialMap Y X)
  : Prop :=
    (X.vertices).restrict (SimplicialMap.comp f g).map = (X.vertices).restrict id ∧
    (Y.vertices).restrict (SimplicialMap.comp g f).map = (Y.vertices).restrict id

theorem IsInverseSimplicialIso_symm
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
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

@[simp]
def IsSimplicialIso
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
    (f : SimplicialMap X Y)
  : Prop :=
    ∃ g : SimplicialMap Y X, IsInverseSimplicialIso f g

--:= set.bij_on (simplicial_map_lift f) X.simplices Y.simplices
-- For example, the identity map is a simplicial isomorphism
-- because it is its own inverse
theorem id_isSimplicialIso
    (X : AbstractSimplicialComplex E)
  : IsSimplicialIso (idSimplicialMap X) :=
by
  use idSimplicialMap X
  simp only [IsInverseSimplicialIso, Set.restrict_id, and_self]
  tauto

theorem iso_inv_is_iso
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
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

-- The composition of two isomorphisms gives an isomorphism.
theorem iso_comp_is_iso
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
    {Z : AbstractSimplicialComplex G}
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
  specialize g_inv_left (simplicialMap_on_vertices X Y f x x_vert)
  rw [Function.comp_assoc, ← Function.comp_assoc g_inv.map, Function.comp_apply, Function.comp_apply, g_inv_left]
  simp
  assumption
  intro z z_vert
  specialize g_inv_right z_vert
  specialize f_inv_right (simplicialMap_on_vertices Z Y g_inv z z_vert)
  rw [Function.comp_assoc, ← Function.comp_assoc f.map, Function.comp_apply, Function.comp_apply, f_inv_right]
  simp
  assumption

theorem iso_is_injective_vertices
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
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

theorem iso_is_injective_simplices
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
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
    rw [vertex_iff_in_simplex]
    use s; constructor <;> assumption
  have x₂_in_X : x₂ ∈ X.vertices := by
    rw [vertex_iff_in_simplex]
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

theorem iso_is_surjective_vertices
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex E}
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
  rw [vertex_iff_in_simplex] at x_in_Y ⊢
  choose s s_in_Y x_in_s using x_in_Y
  use Finset.image g.map s; constructor
  apply g.is_simplicial
  assumption
  apply Finset.mem_image_of_mem
  assumption
  assumption

-- Defining isomorphy between simplicial complexes.
@[simp]
def IsSimpliciallyIso
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
  : Prop :=
    ∃ f : SimplicialMap X Y, IsSimplicialIso f

infixr:50 " ≅ " => IsSimpliciallyIso

theorem simplicial_iso_implies_lift_bij
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (f : SimplicialMap X Y)
  : IsSimplicialIso f → Y.faces = simplicialMapLift f '' X.faces :=
by
  intro f_iso
  unfold IsSimplicialIso at f_iso
  choose g g_inv_f using f_iso
  unfold IsInverseSimplicialIso at g_inv_f
  choose fg_id gf_id using g_inv_f
  rw [Set.ext_iff]
  intro t
  constructor
  intro t_in_Y
  simp only [simplicialMapLift, Set.mem_image]
  use Finset.image g.map t
  constructor
  apply g.is_simplicial
  assumption
  simp only [← Finset.coe_inj, Finset.coe_image]
  rw [← Set.image_comp]
  conv_rhs => rw [← @Set.image_id F ↑t]
  apply Set.EqOn.image_eq
  simp only [Set.restrict_eq_restrict_iff, SimplicialMap.comp] at gf_id
  have t_in_vert : ↑t ⊆ Y.vertices := by apply simplex_subset_vertices t_in_Y
  apply Set.EqOn.mono t_in_vert
  assumption
  intro t_in_lift
  simp only [simplicialMapLift, Set.mem_image] at t_in_lift
  choose s s_in_X fs_eq_t using t_in_lift
  subst fs_eq_t
  apply f.is_simplicial
  assumption

theorem simplicial_iso_vertices
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (f : SimplicialMap X Y)
  : IsSimplicialIso f → Y.vertices = f.map '' X.vertices :=
by
  intro f_iso
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

set_option synthInstance.checkSynthOrder false
noncomputable instance IsSimpliciallyIso.Fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (Y : AbstractSimplicialComplex F)
    (X_iso_Y : IsSimpliciallyIso X Y)
  : Fintype Y.faces :=
by
  unfold IsSimpliciallyIso at X_iso_Y
  choose f f_iso using X_iso_Y
  rw [simplicial_iso_implies_lift_bij X Y f f_iso]
  apply Set.fintypeImage

theorem simplicial_iso_preserves_simplex_dim
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f) :
    ∀ s ∈ X.faces, face_dim s = face_dim (Finset.image f.map s) :=
  by
  intro s s_in_X
  unfold face_dim
  apply congr_arg fun z : ℤ => z - 1
  symm
  rw [Nat.cast_inj, Finset.card_image_iff]
  apply iso_is_injective_simplices f f_iso s s_in_X

theorem simplicial_iso_preserves_dim
    (X : AbstractSimplicialComplex E) [X_fin : Fintype X.faces]
    (Y : AbstractSimplicialComplex F)
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
  rw [simplicial_iso_preserves_simplex_dim f f_iso s s_in_X, Finset.mem_union, Finset.mem_image]
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
  have g_iso : IsSimplicialIso g := by apply iso_inv_is_iso f g f_iso gf_inv
  apply Finset.le_max'
  rw [simplicial_iso_preserves_simplex_dim g g_iso t t_in_Y, Finset.mem_union, Finset.mem_image]
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
@[refl]
theorem simplicial_iso_refl
    (X : AbstractSimplicialComplex E)
  : X ≅ X :=
by
  unfold IsSimpliciallyIso
  use idSimplicialMap X
  apply id_isSimplicialIso

@[symm]
theorem simplicial_iso_symm
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
  : (X ≅ Y) ↔ (Y ≅ X) :=
by
  unfold IsSimpliciallyIso
  constructor <;> unfold IsSimplicialIso
  · intro X_iso_Y
    choose f g f_inv_g using X_iso_Y
    use g; use f
    rw [IsInverseSimplicialIso_symm]
    assumption
  · intro Y_iso_X
    choose f g f_inv_g using Y_iso_X
    use g; use f
    rw [IsInverseSimplicialIso_symm]
    assumption

@[trans]
theorem simplicial_iso_trans
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (Z : AbstractSimplicialComplex G)
  : (X ≅ Y) → Y ≅ Z → X ≅ Z :=
by
  intro X_iso_Y Y_iso_Z
  unfold IsSimpliciallyIso at *
  choose f f_iso using X_iso_Y
  choose g g_iso using Y_iso_Z
  use f.comp g
  apply iso_comp_is_iso <;> assumption

instance IsSimpliciallyIso.Trans
  : Trans (@IsSimpliciallyIso E F _ _) (@IsSimpliciallyIso F G _ _) (@IsSimpliciallyIso E G _ _) where
    trans := simplicial_iso_trans _ _ _

theorem simplicial_iso_preserves_equiv
    (X Y : AbstractSimplicialComplex E)
  : X.faces = Y.faces → X ≅ Y :=
by
  intro H
  have X_eq_Y : X = Y := by rw [AbstractSimplicialComplex.ext_iff, H]
  rw [X_eq_Y]

theorem simplicial_iso_preserves_subcomplex_image
    (X Y Z : AbstractSimplicialComplex E)
    (f : SimplicialMap Y Z)
    (f_iso : IsSimplicialIso f)
  : X ⊆ Y → f.map ''ˢ X ⊆ Z :=
by
  intro X_sub_Y
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex] at X_sub_Y ⊢
  rw [simplicial_iso_implies_lift_bij Y Z f f_iso]
  simp only [simplicialMapLift, Set.image]
  simp only [Set.subset_def] at X_sub_Y ⊢
  intro t t_in_fX
  simp only [Set.mem_setOf] at t_in_fX ⊢
  choose s s_in_X fs_eq_t using t_in_fX
  specialize X_sub_Y s s_in_X
  use s

end Isomorphism
