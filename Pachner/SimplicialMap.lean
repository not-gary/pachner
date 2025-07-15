import Mathlib.Tactic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Pachner.SimplicialComplex
import Mathlib.Logic.Equiv.Defs

variable {𝕜 E F G : Type _}
variable [Ring 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]
variable [AddCommGroup G] [Module 𝕜 G]

set_option autoImplicit false

/-
# Simplicial maps
-/
section SimplicialMap

variable [DecidableEq F]

/- Simplicial maps are maps between the underlying base types
   that map simplices to simplices.
-/
@[simp]
def IsSimplicialMap
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (f : E → F) :=
  ∀ s, s ∈ X.faces → Finset.image f s ∈ Y.faces

structure SimplicialMap
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
  where mk ::
    map : E → F
    is_simplicial : IsSimplicialMap X Y map

theorem simplicialMap_restrict_is_simplicial
    (X Y : Geometry.SimplicialComplex 𝕜 E)
    (Z : Geometry.SimplicialComplex 𝕜 F)
    (f : SimplicialMap X Z)
  : Y ⊆ X → IsSimplicialMap Y Z f.map :=
by
  simp only [IsSimplicialMap, IsSubcomplex]
  intro Y_sub_X s s_in_Y
  simp only [Geometry.SimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def] at Y_sub_X
  specialize Y_sub_X s s_in_Y
  apply f.is_simplicial
  assumption

def SimplicialMap.restrict
    {X Y : Geometry.SimplicialComplex 𝕜 E}
    {Z : Geometry.SimplicialComplex 𝕜 F}
    (f : SimplicialMap X Z)
    (Y_sub_X : Y ⊆ X)
  : SimplicialMap Y Z :=
    SimplicialMap.mk f.map (simplicialMap_restrict_is_simplicial X Y Z f Y_sub_X)

def simplicialMapLift
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
    (f : SimplicialMap X Y)
  : Finset E → Finset F :=
    fun s : Finset E => Finset.image f.map s

def simplicialImage
    (f : E → F)
    (X : Geometry.SimplicialComplex 𝕜 E)
  : Geometry.SimplicialComplex 𝕜 F :=
    Geometry.SimplicialComplex.mk
      {(Finset.image f s) | s ∈ X.faces}
      (by
        simp only [Set.mem_setOf_eq, Finset.image_eq_empty, exists_eq_right]
        apply X.empty_notMem)
      (by
        sorry)
      (by
        intros s t s_in_img t_sset_s t_ne
        simp only [Set.mem_setOf_eq] at ⊢ s_in_img
        choose u Hu u_img using s_in_img
        rw [← u_img, ← Finset.coe_subset, Finset.coe_image, Finset.subset_set_image_iff] at t_sset_s
        choose v v_sset_u v_img using t_sset_s
        use v
        constructor
        apply X.down_closed
        assumption
        assumption
        rw [← v_img, ← Finset.nonempty_iff_ne_empty, Finset.image_nonempty] at t_ne
        rw [← Finset.nonempty_iff_ne_empty]
        assumption
        assumption)
      (by
        sorry)
infixl:80 " ''ˢ " => simplicialImage

theorem simplicialImage_congr
    {X : Geometry.SimplicialComplex 𝕜 E}
    (f g : E → F)
  : Set.EqOn f g X.vertices
      → (f ''ˢ X).faces = (g ''ˢ X).faces :=
  by
  simp only [Set.ext_iff, simplicialImage, Set.mem_setOf]
  intro f_eq_g t
  constructor
  · intro s_in_fX
    choose s s_in_X fs_t using s_in_fX
    use s; constructor; assumption
    simp only [← fs_t, ← Finset.coe_inj, Finset.coe_image]
    apply Set.EqOn.image_eq
    apply Set.EqOn.symm
    apply @Set.EqOn.mono _ _ _ X.vertices
    apply simplex_subset_vertices
    assumption
    assumption
  · intro s_in_fX
    choose s s_in_X fs_t using s_in_fX
    use s; constructor; assumption
    simp only [← fs_t, ← Finset.coe_inj, Finset.coe_image]
    apply Set.EqOn.image_eq
    apply @Set.EqOn.mono _ _ _ X.vertices
    apply simplex_subset_vertices
    assumption
    assumption

theorem map_is_simplicial_onto_image
    (X : Geometry.SimplicialComplex 𝕜 E)
    (f : E → F)
  : IsSimplicialMap X (f ''ˢ X) f :=
by
  unfold IsSimplicialMap
  intro s s_in_X
  simp only [simplicialImage, Set.mem_setOf]
  use s

def SimplicialMap.ontoImage
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Z : Geometry.SimplicialComplex 𝕜 F}
    (f : SimplicialMap X Z)
  : SimplicialMap X (f.map ''ˢ X) :=
    SimplicialMap.mk f.map (map_is_simplicial_onto_image X f.map)

theorem simplicialImage_vertices
    (X : Geometry.SimplicialComplex 𝕜 E)
    (f : E → F)
  : (f ''ˢ X).vertices = f '' X.vertices :=
by
  simp only [vertices_setOf, simplicialImage, Set.image, Set.ext_iff, Set.mem_setOf]
  intro y
  constructor
  intro y_in_vert_img
  choose t t_in_img y_in_t using y_in_vert_img
  choose s s_in_X fs_eq_t using t_in_img
  rw [← fs_eq_t, Finset.mem_image] at y_in_t
  choose x x_in_s fx_eq_y using y_in_t
  use x; constructor
  use s
  assumption
  intro y_in_img_vert
  choose x x_in_X fx_eq_y using y_in_img_vert
  choose s s_in_X x_in_s using x_in_X
  use Finset.image f s; constructor
  use s
  rw [← fx_eq_y]
  apply Finset.mem_image_of_mem
  assumption

notation "⟨" f ", " X "⟩" =>
  @SimplicialMap.mk _ _ _ _ _ _ _ _ _ _ X (f ''ˢ X) f (map_is_simplicial_onto_image X f)

theorem simplicialImage_is_lift_image
    (X : Geometry.SimplicialComplex 𝕜 E)
    (f : E → F)
  : (f ''ˢ X).faces = simplicialMapLift ⟨f, X⟩ '' X.faces :=
by
  simp only [simplicialImage, simplicialMapLift, Set.ext_iff]
  intro s
  constructor
  intro s_in_img
  simp only [Set.mem_setOf] at s_in_img
  choose t t_in_X ft_eq_s using s_in_img
  simp only [Set.mem_image]
  use t
  intro s_in_lift
  simp only [Set.mem_image] at s_in_lift
  choose t t_in_X ft_eq_s using s_in_lift
  simp only [Set.mem_setOf]
  use t

theorem simplicialImage_union [DecidableEq E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
    (f : E → F)
  : (f ''ˢ (X ∪ Y)).faces =
      (f ''ˢ X).faces ∪ (f ''ˢ Y).faces :=
by
  simp only [simplicialImage_is_lift_image, simplicialMapLift, simplicialUnion, Set.image,
    Set.ext_iff, Set.mem_union, Set.mem_setOf]
  intro t
  constructor
  intro t_in_img_union
  choose s s_in_XY fs_eq_t using t_in_img_union
  cases' s_in_XY with s_in_X s_in_Y
  left; use s
  right; use s
  intro t_in_union_img
  cases' t_in_union_img with t_in_left t_in_right
  choose s s_in_X fs_eq_t using t_in_left
  use s; constructor
  left; assumption
  assumption
  choose s s_in_Y fs_eq_t using t_in_right
  use s; constructor
  right; assumption
  assumption

end SimplicialMap

/-
# Simplicial maps on vertices
-/
section vertices

variable [DecidableEq E] [DecidableEq F]

/- In order to prove that simplicial maps
   map vertices to vertices, we first show:
   One can go back and forth between vertices
   and singletons that are simplices.
-/
theorem vertex_to_singleton
    (X : Geometry.SimplicialComplex 𝕜 E)
    (x : E)
    (x_in_X : x ∈ X.vertices)
  : {x} ∈ X.faces :=
by
  simp only [Geometry.SimplicialComplex.vertices_eq] at x_in_X
  rw [Set.mem_iUnion] at x_in_X
  choose s x_in_X using x_in_X
  rw [Set.mem_iUnion] at x_in_X
  choose Hs x_in_s using x_in_X
  -- As x is a vertex, x is contained in a simplex s of X.
  -- Therefore, {x} ⊆ s.
  have x_sub_s : {x} ⊆ s :=
  by
    simp only [Finset.singleton_subset_iff]
    assumption
  -- As the set of simplices of X is closed under subsets,
    -- also {x} is a simplex of X.
  apply X.down_closed
  assumption
  assumption
  apply Finset.singleton_ne_empty

theorem singleton_to_vertex
    (X : Geometry.SimplicialComplex 𝕜 E)
    (x : E)
    (x_in_SX : {x} ∈ X.faces)
  : x ∈ X.vertices :=
by
  -- {x} witnesses that x is contained in a simplex
  -- and thus is a vertex
  simp only [Geometry.SimplicialComplex.vertices_eq, Set.mem_iUnion]
  use {x}
  simp only [Finset.coe_singleton, Set.mem_singleton_iff, exists_prop, and_true]
  assumption

-- Simplicial maps map vertices to vertices.
theorem simplicialMap_on_vertices
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (f : SimplicialMap X Y)
    (x : E)
    (x_in_X : x ∈ X.vertices)
  : f.map x ∈ Y.vertices :=
by
  simp only [Geometry.SimplicialComplex.vertices_eq, Set.mem_iUnion]
  use Finset.image f.map {x}
  constructor
  rw [Finset.mem_coe]
  apply Finset.mem_image_of_mem
  rw [Finset.mem_singleton]
  apply f.is_simplicial
  rw [← Geometry.SimplicialComplex.mem_vertices]
  assumption

theorem simplicial_lift_bij_implies_vertices_bij
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (f : SimplicialMap X Y)
  : Set.BijOn (simplicialMapLift f) X.faces Y.faces
      → Set.BijOn f.map X.vertices Y.vertices :=
by
  simp only [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn, simplicialMapLift, vertices_setOf]
  intro lift_bij
  choose lift_range lift_inj lift_surj using lift_bij
  constructor
  intro x x_in_X
  simp only [Set.mem_setOf] at x_in_X ⊢
  choose s s_in_X x_in_s using x_in_X
  specialize lift_range s_in_X
  use Finset.image f.map s
  constructor; assumption
  apply Finset.mem_image_of_mem
  assumption
  constructor
  intro x₁ x₁_in_X x₂ x₂_in_X fx₁_eq_fx₂
  simp only [Set.mem_setOf] at x₁_in_X x₂_in_X
  rw [← vertex_iff_in_simplex, Geometry.SimplicialComplex.mem_vertices] at x₁_in_X x₂_in_X
  specialize lift_inj x₁_in_X x₂_in_X
  rw [← Finset.singleton_inj, ← Finset.image_singleton, ← Finset.image_singleton] at fx₁_eq_fx₂
  specialize lift_inj fx₁_eq_fx₂
  rw [Finset.singleton_inj] at lift_inj
  assumption
  simp only [Set.subset_def] at lift_surj ⊢
  intro y y_in_Y
  simp only [Set.mem_setOf] at y_in_Y
  choose t t_in_Y y_in_t using y_in_Y
  specialize lift_surj t t_in_Y
  simp only [Set.mem_image] at lift_surj ⊢
  choose s s_in_X fs_eq_t using lift_surj
  rw [← fs_eq_t, Finset.mem_image] at y_in_t
  choose x x_in_s fx_eq_y using y_in_t
  use x; constructor
  simp only [Set.mem_setOf]
  use s
  assumption

theorem vertices_bij_implies_simplicial_lift_mapsTo
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (f : SimplicialMap X Y)
  : Set.BijOn f.map X.vertices Y.vertices
      → Set.MapsTo (simplicialMapLift f) X.faces Y.faces :=
by
  simp only [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn, simplicialMapLift, vertices_setOf]
  intro img_bij
  choose img_range img_inj img_surj using img_bij
  intro s s_in_X
  have s_ne : s ≠ ∅ :=
  by
    revert s_in_X
    contrapose
    rw [not_not]
    intros s_empty
    rw [s_empty]
    apply X.empty_notMem
  simp only [ne_eq, Finset.eq_empty_iff_forall_notMem, not_forall, not_not] at s_ne
  choose x x_in_s using s_ne
  have x_in_X : x ∈ X.vertices :=
    by
    rw [vertices_setOf, Set.mem_setOf]
    use s
  rw [vertices_setOf] at x_in_X
  specialize img_range x_in_X
  simp only [Set.mem_setOf] at img_range
  choose t t_in_Y fx_in_t using img_range
  apply f.is_simplicial
  assumption

theorem vertices_bij_implies_simplicial_lift_inj
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (f : SimplicialMap X Y)
  : Set.BijOn f.map X.vertices Y.vertices
      → Set.InjOn (simplicialMapLift f) X.faces :=
by
  simp only [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn, simplicialMapLift, vertices_setOf]
  intro img_bij
  choose img_range img_inj img_surj using img_bij
  intro s₁ s₁_in_X s₂ s₂_in_X fs₁_eq_fs₂
  simp only [Finset.ext_iff] at fs₁_eq_fs₂ ⊢
  have s₁_ss_vert : ↑s₁ ⊆ X.vertices := by apply simplex_subset_vertices X s₁ s₁_in_X
  have s₂_ss_vert : ↑s₂ ⊆ X.vertices := by apply simplex_subset_vertices X s₂ s₂_in_X
  intro a
  specialize fs₁_eq_fs₂ (f.map a)
  cases' fs₁_eq_fs₂ with fs₁_ss_fs₂ fs₂_ss_fs₁
  constructor
  intro a_in_s₁
  have fa_in_fs₁ : f.map a ∈ Finset.image f.map s₁ := by apply Finset.mem_image_of_mem f.map a_in_s₁
  specialize fs₁_ss_fs₂ fa_in_fs₁
  rw [← Finset.mem_coe, Finset.coe_image, @Set.InjOn.mem_image_iff _ _ X.vertices,
    Finset.mem_coe] at fs₁_ss_fs₂
  assumption
  simp only [vertices_setOf, exists_prop]
  assumption
  assumption
  apply Set.mem_of_subset_of_mem s₁_ss_vert
  rw [Finset.mem_coe]
  assumption
  intro a_in_s₂
  have fa_in_fs₂ : f.map a ∈ Finset.image f.map s₂ := by apply Finset.mem_image_of_mem f.map a_in_s₂
  specialize fs₂_ss_fs₁ fa_in_fs₂
  rw [← Finset.mem_coe, Finset.coe_image, @Set.InjOn.mem_image_iff _ _ X.vertices,
    Finset.mem_coe] at fs₂_ss_fs₁
  assumption
  simp only [vertices_setOf, exists_prop]
  assumption
  assumption
  apply Set.mem_of_subset_of_mem s₂_ss_vert
  rw [Finset.mem_coe]
  assumption

end vertices

/-
# Dimension monotonicity
-/
section Dimension

variable [DecidableEq F]

-- The dimension of simplices does not increase
-- under simplicial maps.
theorem simplicialMap_dim_mono
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (f : SimplicialMap X Y)
    (s : Finset E)
  : face_dim (Finset.image f.map s) ≤ face_dim s :=
by
  calc
    face_dim (Finset.image f.map s) = Finset.card (Finset.image f.map s) - 1 := by simp only [face_dim]
    _ ≤ Finset.card s - 1 := by simp [Finset.card_image_le]
    _ ≤ face_dim s := by simp only [face_dim, le_refl]

end Dimension

/-
# Examples
-/
-- The identity map is simplicial.
theorem id_isSimplicialMap [DecidableEq E]
    (X : Geometry.SimplicialComplex 𝕜 E)
  : IsSimplicialMap X X id :=
by
  simp

def idSimplicialMap [DecidableEq E]
    (X : Geometry.SimplicialComplex 𝕜 E)
  : SimplicialMap X X :=
    SimplicialMap.mk id (id_isSimplicialMap X)

-- Constant maps are simplicial
theorem const_is_simplicial [DecidableEq F]
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (y_0 : F)
    (y0_vertex : y_0 ∈ Y.vertices)
  : IsSimplicialMap X Y (fun x : E => y_0) :=
by
  -- As y_0 is a vertex of Y, the set {y_0} is a simplex of Y
  have y0_in_SY : {y_0} ∈ Y.faces := vertex_to_singleton Y y_0 y0_vertex
  -- Setup for the main argument
  intro (s : Finset E)
  intro (s_in_SX : s ∈ X.faces)
  let f := fun x : E => y_0
  let fs := Finset.image f s
  -- We have f(s) ⊆ {y_0}
  have fs_sub_y0 : fs ⊆ {y_0} :=
  by
    sorry
  -- and thus f(s) is a simplex of Y.
  show fs ∈ Y.faces
  · apply Y.down_closed
    assumption
    assumption
    rw [← Finset.nonempty_iff_ne_empty, Finset.image_nonempty, Finset.nonempty_iff_ne_empty]
    revert s_in_SX
    contrapose
    rw [not_not]
    intros s_empty
    rw [s_empty]
    apply X.empty_notMem

def constSimplicialMap [DecidableEq F]
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (y_0 : F)
    (y0_vertex : y_0 ∈ Y.vertices)
  : SimplicialMap X Y :=
    SimplicialMap.mk (fun _ : E => y_0) (const_is_simplicial X Y y_0 y0_vertex)

-- Compositions of simplicial maps are simplicial
theorem is_simplicial_comp [DecidableEq F] [DecidableEq G]
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
    {Z : Geometry.SimplicialComplex 𝕜 G}
    (f : E → F)
    (f_simpl : IsSimplicialMap X Y f)
    (g : F → G)
    (g_simpl : IsSimplicialMap Y Z g)
  : IsSimplicialMap X Z (g ∘ f) :=
by
  intro (s : Finset E)
  intro (s_in_SX : s ∈ X.faces)
  let t : Finset F := Finset.image f s
  have t_in_SY : t ∈ Y.faces := by apply f_simpl s; apply s_in_SX
  -- or just: tauto},
  have gfs_in_SZ : Finset.image g t ∈ Z.faces := by apply g_simpl t; apply t_in_SY
  show Finset.image (g ∘ f) s ∈ Z.faces
  rw [Finset.image_image.symm]
  assumption

def SimplicialMap.comp [DecidableEq F] [DecidableEq G]
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
    {Z : Geometry.SimplicialComplex 𝕜 G}
    (f : SimplicialMap X Y)
    (g : SimplicialMap Y Z)
  : SimplicialMap X Z :=
    SimplicialMap.mk (g.map ∘ f.map) (is_simplicial_comp f.map f.is_simplicial g.map g.is_simplicial)

/-
# Simplicial isomorphisms
-/
section Isomorphism

variable [DecidableEq E] [DecidableEq F] [DecidableEq G]

-- A simplicial map is a simplicial isomorphism
-- if it admits an inverse simplicial map.

@[simp]
def IsInverseSimplicialIso
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
    (f : SimplicialMap X Y)
    (g : SimplicialMap Y X)
  : Prop :=
    (X.vertices).restrict (SimplicialMap.comp f g).map = (X.vertices).restrict id ∧
    (Y.vertices).restrict (SimplicialMap.comp g f).map = (Y.vertices).restrict id

theorem IsInverseSimplicialIso_symm
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
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
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
    (f : SimplicialMap X Y)
  : Prop :=
    ∃ g : SimplicialMap Y X, IsInverseSimplicialIso f g

--:= set.bij_on (simplicial_map_lift f) X.simplices Y.simplices
-- For example, the identity map is a simplicial isomorphism
-- because it is its own inverse
theorem id_isSimplicialIso
    (X : Geometry.SimplicialComplex 𝕜 E)
  : IsSimplicialIso (idSimplicialMap X) :=
by
  use idSimplicialMap X
  simp only [IsInverseSimplicialIso, Set.restrict_id, and_self]
  tauto

theorem iso_inv_is_iso
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
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
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
    {Z : Geometry.SimplicialComplex 𝕜 G}
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
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
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
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
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
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 E}
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
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
  : Prop :=
    ∃ f : SimplicialMap X Y, IsSimplicialIso f

infixr:50 " ≅ " => IsSimpliciallyIso

theorem simplicial_iso_implies_lift_bij
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
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
  have t_in_vert : ↑t ⊆ Y.vertices := by apply simplex_subset_vertices Y t t_in_Y
  apply Set.EqOn.mono t_in_vert
  assumption
  intro t_in_lift
  simp only [simplicialMapLift, Set.mem_image] at t_in_lift
  choose s s_in_X fs_eq_t using t_in_lift
  subst fs_eq_t
  apply f.is_simplicial
  assumption

theorem simplicial_iso_vertices
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
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
  rw [Geometry.SimplicialComplex.mem_vertices] at x_in_Y ⊢
  rw [← Finset.image_singleton]
  apply g.is_simplicial
  assumption
  assumption
  intro x_in_img
  rw [Set.mem_image] at x_in_img
  choose y y_in_X fy_eq_x using x_in_img
  rw [Geometry.SimplicialComplex.mem_vertices] at y_in_X ⊢
  rw [← fy_eq_x, ← Finset.image_singleton]
  apply f.is_simplicial
  assumption

theorem simplicial_iso_lift_inj
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (f : SimplicialMap X Y)
  : IsSimplicialIso f → Set.InjOn (simplicialMapLift f) X.faces :=
by
  intro f_iso
  have f_iso' := f_iso
  intro s s_in_X t t_in_X fs_eq_ft

  choose g gf_inv using f_iso'
  unfold IsInverseSimplicialIso at gf_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    Set.image_id] at gf_inv
  choose gf_id fg_id using gf_inv

  unfold simplicialMapLift at fs_eq_ft
  simp only [Geometry.SimplicialComplex.mem_vertices] at gf_id fg_id
  rw [Finset.ext_iff] at ⊢ fs_eq_ft
  intro x
  specialize fs_eq_ft (f.map x)
  constructor

  intro x_in_s
  have x_in_X : {x} ∈ X.faces :=
  by
    rw [←Geometry.SimplicialComplex.mem_vertices, vertex_iff_in_simplex]
    use s
  specialize gf_id x_in_X

  -- try shit out
  rw [id_eq] at gf_id
  have fx_in_fs : f.map x ∈ Finset.image f.map s :=
  by
    rw [Finset.mem_image]
    use x
  rw [fs_eq_ft, Finset.mem_image] at fx_in_fs
  choose a a_in_t fa_eq_fs using fx_in_fs
  have fx_in_Y : {f.map x} ∈ Y.faces :=
  by
    rw [← Finset.image_singleton]
    apply f.is_simplicial
    assumption
  specialize fg_id fx_in_Y
  sorry
  sorry

-- what?
noncomputable instance IsSimpliciallyIso.Fintype
    (X : Geometry.SimplicialComplex 𝕜 E) [Fintype X.faces]
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (X_iso_Y : X ≅ Y)
  : Fintype Y.faces :=
by
  unfold IsSimpliciallyIso at X_iso_Y
  choose f f_iso using X_iso_Y
  rw [simplicial_iso_implies_lift_bij X Y f f_iso]
  apply Set.fintypeImage

theorem simplicial_iso_preserves_simplex_dim
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
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
    (X : Geometry.SimplicialComplex 𝕜 E) [X_fin : Fintype X.faces]
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (X_iso_Y : X ≅ Y) :
    X.dim = @Y.dim _ _ _ _ _ _ (IsSimpliciallyIso.Fintype X Y X_iso_Y) :=
by
  have Y_fin : Fintype Y.faces :=
  by
    apply IsSimpliciallyIso.Fintype X Y X_iso_Y

  unfold IsSimpliciallyIso at X_iso_Y
  have X_iso_Y' := X_iso_Y
  choose f f_iso using X_iso_Y'
  simp only [Geometry.SimplicialComplex.dim]
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
    (X : Geometry.SimplicialComplex 𝕜 E)
  : X ≅ X :=
by
  unfold IsSimpliciallyIso
  use idSimplicialMap X
  apply id_isSimplicialIso

@[symm]
theorem simplicial_iso_symm
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
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
    (X : Geometry.SimplicialComplex 𝕜 E)
    (Y : Geometry.SimplicialComplex 𝕜 F)
    (Z : Geometry.SimplicialComplex 𝕜 G)
  : (X ≅ Y) → Y ≅ Z → X ≅ Z :=
by
  intro X_iso_Y Y_iso_Z
  unfold IsSimpliciallyIso at *
  choose f f_iso using X_iso_Y
  choose g g_iso using Y_iso_Z
  use f.comp g
  apply iso_comp_is_iso <;> assumption

theorem simplicial_iso_preserves_equiv
    (X Y : Geometry.SimplicialComplex 𝕜 E)
  : X.faces = Y.faces → X ≅ Y :=
by
  intro H
  unfold IsSimpliciallyIso
  have id_simplicial_X : IsSimplicialMap X Y id :=
    by
    unfold IsSimplicialMap
    intro s Hs
    rw [Finset.image_id, ← H]
    assumption
  have id_simplicial_Y : IsSimplicialMap Y X id :=
    by
    unfold IsSimplicialMap
    intro s Hs
    rw [Finset.image_id, H]
    assumption
  set id_X := SimplicialMap.mk id id_simplicial_X
  use id_X
  unfold IsSimplicialIso
  set id_Y := SimplicialMap.mk id id_simplicial_Y
  use id_Y
  unfold IsInverseSimplicialIso
  constructor <;> simp only [SimplicialMap.comp] <;> rw [Function.id_comp]

theorem simplicial_iso_preserves_subcomplex_image
    (X Y Z : Geometry.SimplicialComplex 𝕜 E)
    (f : SimplicialMap Y Z)
    (f_iso : IsSimplicialIso f)
  : X ⊆ Y → f.map ''ˢ X ⊆ Z :=
by
  intro X_sub_Y
  simp only [Geometry.SimplicialComplex.instHasSubset, IsSubcomplex] at X_sub_Y ⊢
  rw [simplicial_iso_implies_lift_bij Y Z f f_iso]
  simp only [simplicialMapLift, Set.image]
  simp only [Set.subset_def] at X_sub_Y ⊢
  intro t t_in_fX
  simp only [Set.mem_setOf] at t_in_fX ⊢
  choose s s_in_X fs_eq_t using t_in_fX
  specialize X_sub_Y s s_in_X
  use s

end Isomorphism

/-
# Simplicial Coercions
-/
section Coercion

variable [DecidableEq E] [F_dec : DecidableEq F] [DecidableEq G]

-- Define as coercion on types that lifts to simplicial map.
structure SimplicialCoe
    (X : Geometry.SimplicialComplex 𝕜 E)
    (F : Type _)
  where mk ::
    coe : E → F
    Injective : Set.InjOn coe (X.vertices)

def SimplicialCoe.simplicialMap
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
  : SimplicialMap X (φ.coe ''ˢ X) :=
    SimplicialMap.mk φ.coe (map_is_simplicial_onto_image X φ.coe)

instance SimplicialCoe.Fintype
    (X : Geometry.SimplicialComplex 𝕜 E) [Fintype X.faces]
    (φ : SimplicialCoe X F)
  : Fintype (φ.coe ''ˢ X).faces :=
by
  rw [simplicialImage_is_lift_image]
  apply Set.fintypeImage

theorem simplicialCoe_inv_is_simplicial [Nonempty E]
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
  : IsSimplicialMap (φ.coe ''ˢ X) X (Function.invFunOn φ.coe X.vertices) :=
by
  simp only [IsSimplicialMap, simplicialImage]
  intro t t_in_coe
  simp only [Set.mem_setOf] at t_in_coe
  choose s s_in_X coe_s_t using t_in_coe
  rw [← coe_s_t]
  have inv_id : Finset.image (Function.invFunOn φ.coe X.vertices) (Finset.image φ.coe s) = s :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.Injective
    apply simplex_subset_vertices
    assumption
  rw [inv_id]
  assumption

noncomputable def simplicialCoeInv [Nonempty E]
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
  : SimplicialMap (φ.coe ''ˢ X) X :=
    SimplicialMap.mk (Function.invFunOn φ.coe X.vertices) (simplicialCoe_inv_is_simplicial φ)

notation φ "⁻ᶜ" => simplicialCoeInv φ

theorem coe_inv_isInverseSimplicialIso [Nonempty E]
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
  : IsInverseSimplicialIso (SimplicialMap.mk φ.coe (map_is_simplicial_onto_image X φ.coe)) (φ⁻ᶜ) :=
by
  simp only [IsInverseSimplicialIso, SimplicialMap.comp, Set.restrict_eq_restrict_iff]
  constructor
  apply Set.InjOn.leftInvOn_invFunOn
  apply φ.Injective
  simp only [Set.EqOn, id]
  intro y y_in_coe
  apply Function.invFunOn_eq
  rw [simplicialImage_vertices, Set.mem_image] at y_in_coe
  choose x x_in_X coe_x_y using y_in_coe
  use x

theorem coe_is_iso [Nonempty E]
    (X : Geometry.SimplicialComplex 𝕜 E)
    (φ : SimplicialCoe X F)
  : IsSimplicialIso
      (@SimplicialMap.mk 𝕜 E F _ _ _ _ _ _ _ X (φ.coe ''ˢ X) φ.coe (by apply map_is_simplicial_onto_image)) :=
by
  unfold IsSimplicialIso
  use @simplicialCoeInv _ _ _ _ _ _ _ _ _ _ _ _ X φ
  apply coe_inv_isInverseSimplicialIso

theorem simplicialCoeInv_inj [Nonempty E]
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
  : Set.InjOn (φ⁻ᶜ).map (φ.coe ''ˢ X).vertices :=
by
  simp only [Set.InjOn, simplicialImage_vertices, Set.mem_image]
  intro y₁ y₁_in_φX y₂ y₂_in_φX φy₁_eq_φy₂
  choose x₁ x₁_in_X φx₁_y₁ using y₁_in_φX
  choose x₂ x₂_in_X φx₂_y₂ using y₂_in_φX
  have inv_x₁ : φ⁻ᶜ.map (φ.coe x₁) = x₁ :=
    by
    apply Set.InjOn.leftInvOn_invFunOn
    apply φ.Injective
    assumption
  have inv_x₂ : φ⁻ᶜ.map (φ.coe x₂) = x₂ :=
    by
    apply Set.InjOn.leftInvOn_invFunOn
    apply φ.Injective
    assumption
  rw [← φx₁_y₁, ← φx₂_y₂, inv_x₁, inv_x₂] at φy₁_eq_φy₂
  rw [← φy₁_eq_φy₂, φx₁_y₁] at φx₂_y₂
  assumption

theorem SimplicialCoe.iso_onto_image [Nonempty E]
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
  : X ≅ φ.coe ''ˢ X :=
by
  unfold IsSimpliciallyIso
  use φ.simplicialMap
  apply coe_is_iso

theorem coe_preserves_iso [Nonempty E]
    (X Y : Geometry.SimplicialComplex 𝕜 E)
    (φ : SimplicialCoe X F)
    (ψ : SimplicialCoe Y F)
  : (X ≅ Y) → (φ.coe ''ˢ X ≅ ψ.coe ''ˢ Y) :=
by
  intro X_iso_Y
  apply simplicial_iso_trans (φ.coe ''ˢ X) X
  rw [simplicial_iso_symm]
  apply φ.iso_onto_image
  rw [simplicial_iso_symm]
  apply simplicial_iso_trans (ψ.coe ''ˢ Y) Y
  rw [simplicial_iso_symm]
  apply ψ.iso_onto_image
  rw [simplicial_iso_symm]
  assumption

theorem coe_comp_is_injective
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
    (ψ : SimplicialCoe (φ.coe ''ˢ X) G)
  : Set.InjOn (ψ.coe ∘ φ.coe) X.vertices :=
by
  apply Set.InjOn.comp ψ.Injective φ.Injective
  simp only [Set.MapsTo]
  intro x x_vert
  rw [Geometry.SimplicialComplex.vertices_eq]
  dsimp only [simplicialImage, Geometry.SimplicialComplex.faces]
  simp only [Set.mem_iUnion]
  use {φ.coe x}
  constructor
  rw [Finset.mem_coe]
  apply Finset.mem_singleton_self
  simp only [Set.mem_setOf]
  use{x}
  constructor
  assumption
  rw [Finset.image_singleton]

theorem coe_comp_image
    (X : Geometry.SimplicialComplex 𝕜 E)
    (φ : SimplicialCoe X F)
    (ψ : SimplicialCoe (φ.coe ''ˢ X) G)
  : ((ψ.coe ∘ φ.coe) ''ˢ X).faces = (ψ.coe ''ˢ (φ.coe ''ˢ X)).faces :=
  by
  dsimp only [simplicialImage, Geometry.SimplicialComplex.faces]
  rw [Set.ext_iff]
  intro s
  constructor
  · intro s_in_comp
    rw [Set.mem_setOf] at *
    choose t Ht img_eq_s using s_in_comp
    set u : Finset F := Finset.image φ.coe t
    use u
    constructor
    rw [Set.mem_setOf]
    use t
    rw [← Finset.image_image] at img_eq_s
    assumption
  · intro s_in_coe
    rw [Set.mem_setOf] at *
    choose t Ht img_eq_s using s_in_coe
    rw [Set.mem_setOf] at Ht
    choose u u_in_X img_u_eq_t using Ht
    use u; constructor; assumption
    rw [← Finset.image_image, img_u_eq_t]
    assumption

@[simp]
def SimplicialCoe.comp
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
    (ψ : SimplicialCoe (φ.coe ''ˢ X) G)
  : SimplicialCoe X G :=
    SimplicialCoe.mk (ψ.coe ∘ φ.coe) (coe_comp_is_injective φ ψ)

-- Restriction of coe is coe.
theorem coe_restrict_is_injective
    (X Y : Geometry.SimplicialComplex 𝕜 E)
    (φ : SimplicialCoe X F)
    (Y_subcomp_X : Y.vertices ⊆ X.vertices)
  : Set.InjOn φ.coe Y.vertices :=
by
  apply Set.InjOn.mono Y_subcomp_X
  apply φ.Injective

@[simp]
def SimplicialCoe.restrict
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
    (Y : Geometry.SimplicialComplex 𝕜 E)
    (Y_subcomp_X : Y.vertices ⊆ X.vertices)
  : SimplicialCoe Y F :=
    SimplicialCoe.mk φ.coe (coe_restrict_is_injective X Y φ Y_subcomp_X)

notation coe "[" K "; " H "]" => SimplicialCoe.restrict coe K H

def SimplicialCoe.restrictCoe
    {X Y : Geometry.SimplicialComplex 𝕜 E}
    {Y_subcomp_X : Y.vertices ⊆ X.vertices}
  : Coe (SimplicialCoe X F) (SimplicialCoe Y F) :=
    Coe.mk fun φ : SimplicialCoe X F => φ.restrict Y Y_subcomp_X

-- Convert isomorphisms into coercions.
def SimplicialMap.coe
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : SimplicialCoe X F :=
    SimplicialCoe.mk f.map (iso_is_injective_vertices f f_iso)

-- Coercion on images.
--  g[Y] = X → φ[X]
--  ↑     ↗ φ ∘ g
--  Y
def simplicialCoeOnImage
    {X : Geometry.SimplicialComplex 𝕜 E}
    {Y : Geometry.SimplicialComplex 𝕜 F}
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
    (φ : SimplicialCoe Y G)
  : SimplicialCoe X G :=
    SimplicialCoe.mk (φ.coe ∘ f.map)
    (by
      apply Set.InjOn.comp φ.Injective
      apply (f.coe f_iso).Injective
      unfold Set.MapsTo
      intro x x_in_X
      simp only [Geometry.SimplicialComplex.mem_vertices, simplicial_iso_implies_lift_bij X Y f f_iso,
        simplicialMapLift, Set.image, Set.mem_setOf]
      rw [Geometry.SimplicialComplex.vertices, Set.mem_setOf] at x_in_X
      rw [← Finset.image_singleton]
      apply f.is_simplicial
      assumption)

theorem simplicialCoe_union_simplices
    (X Y : Geometry.SimplicialComplex 𝕜 E)
    (φ : SimplicialCoe (X ∪ Y) F)
  : (φ.coe ''ˢ (X ∪ Y)).faces =
      (φ[X; (by apply is_subcomplex_vertices; apply subcomplex_simplicial_union_left)].coe ''ˢ X ∪
          φ[Y; (by apply is_subcomplex_vertices; apply subcomplex_simplicial_union_right)].coe ''ˢ Y).faces :=
by
  apply simplicialImage_union

theorem simplicialCoe_union
    (X Y : Geometry.SimplicialComplex 𝕜 E)
    (φ : SimplicialCoe (X ∪ Y) F)
  : φ.coe ''ˢ (X ∪ Y) ≅
      φ[X; by apply is_subcomplex_vertices; apply subcomplex_simplicial_union_left].coe ''ˢ X ∪
        φ[Y; by apply is_subcomplex_vertices; apply subcomplex_simplicial_union_right].coe ''ˢ Y :=
by
  apply simplicial_iso_preserves_equiv
  apply simplicialCoe_union_simplices

theorem simplicialCoe_injective_vertices
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
  : Set.InjOn φ.coe X.vertices :=
by
  apply φ.Injective

theorem simplicialCoe_surjective_vertices
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
  : Set.SurjOn φ.coe X.vertices (φ.coe ''ˢ X).vertices :=
by
  simp only [Set.SurjOn, simplicialImage_vertices, subset_refl]

theorem simplicialCoe_mapsTo_vertices
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
  : Set.MapsTo φ.coe X.vertices (φ.coe ''ˢ X).vertices :=
by
  simp only [Set.MapsTo, simplicialImage_vertices]
  intro x x_in_X
  apply Set.mem_image_of_mem
  assumption

theorem simplicialCoe_bijective_vertices
    {X : Geometry.SimplicialComplex 𝕜 E}
    (φ : SimplicialCoe X F)
  : Set.BijOn φ.coe X.vertices (φ.coe ''ˢ X).vertices :=
by
  simp only [Set.BijOn]
  constructor
  apply simplicialCoe_mapsTo_vertices
  constructor
  apply simplicialCoe_injective_vertices
  apply simplicialCoe_surjective_vertices

end Coercion

/-
# Simplicial joins
-/
section Join

variable [DecidableEq E] [DecidableEq F]

-- Start with some formalization of disjoint unions.

-- Some stuff to make user notation more convenient.
-- Use 'BinaryDirectSum E F' as the type
-- Use 'BinaryDirectSum.incl_left E F' for the canonical inclusion into the left (and right) factor

section BinaryDirectSum

@[simp]
def BinaryDirectSum.types
    (X : Type _)
    (Y : Type _)
    (i : Fin 2)
  : Type _ :=
    match i with
      | 0 => X
      | 1 => Y

-- Help Lean with some of those instances
instance BinaryDirectSum.types.instAddCommMonoid
    (X : Type _)
    (Y : Type _)
    [x : AddCommGroup X]
    [y : AddCommGroup Y]
    (i : Fin 2)
  : AddCommGroup (BinaryDirectSum.types X Y i) :=
    match i with
      | 0 => x
      | 1 => y

instance BinaryDirectSum.types.instDecidableEq
    (X : Type _)
    (Y : Type _)
    [x : DecidableEq X]
    [y : DecidableEq Y]
    (i : Fin 2)
  : DecidableEq (BinaryDirectSum.types X Y i) :=
    match i with
      | 0 => x
      | 1 => y

-- The actualy type
def BinaryDirectSum
    (X : Type _)
    (Y : Type _)
    [AddCommGroup X]
    [AddCommGroup Y]
  := DirectSum (Fin 2) (BinaryDirectSum.types X Y)

-- The canonical inclusions
@[simp]
def BinaryDirectSum.incl_left
    (X : Type _)
    (Y : Type _)
    [AddCommGroup X]
    [AddCommGroup Y]
  := DirectSum.of (BinaryDirectSum.types X Y) 0

@[simp]
def BinaryDirectSum.incl_right
    (X : Type _)
    (Y : Type _)
    [AddCommGroup X]
    [AddCommGroup Y]
  := DirectSum.of (BinaryDirectSum.types X Y) 1

-- For convenience
@[simp]
def BinaryDirectSum.image_left
    (X : Type _)
    (Y : Type _)
    [AddCommGroup X]
    [AddCommGroup Y]
    [DecidableEq X]
    [DecidableEq Y]
    (s : Finset X)
  := Finset.image (BinaryDirectSum.incl_left X Y) s

@[simp]
def BinaryDirectSum.image_right
    (X : Type _)
    (Y : Type _)
    [AddCommGroup X]
    [AddCommGroup Y]
    [DecidableEq X]
    [DecidableEq Y]
    (t : Finset Y)
  := Finset.image (BinaryDirectSum.incl_right X Y) t

-- Help Lean with some more instances
instance BinaryDirectSum.instAddCommGroup
    (X : Type _)
    (Y : Type _)
    [AddCommGroup X]
    [AddCommGroup Y]
  : AddCommGroup (BinaryDirectSum X Y) :=
    DirectSum.instAddCommGroup (BinaryDirectSum.types X Y)

instance BinaryDirectSum.instDecidableEq
    (X : Type _)
    (Y : Type _)
    [AddCommGroup X]
    [AddCommGroup Y]
    [x : DecidableEq X]
    [y : DecidableEq Y]
  : DecidableEq (BinaryDirectSum X Y) :=
    instDecidableEqDirectSum (Fin 2) (BinaryDirectSum.types X Y)

end BinaryDirectSum

@[simp]
def simplexDisjointUnion
    (s : Finset E)
    (t : Finset F)
  : Finset (BinaryDirectSum E F) :=
    Finset.image (BinaryDirectSum.incl_left E F) s ∪ Finset.image (BinaryDirectSum.incl_right E F) t

infixl:65 " ⊔ₛ " => simplexDisjointUnion

instance SimplexDisjoint.nonempty
    (s : Finset E)
    (t : Finset F)
    (H : Nonempty s ∨ Nonempty t)
  : Nonempty (s ⊔ₛ t) :=
by
  iterate 2 rw [Finset.nonempty_coe_sort, ← Finset.coe_nonempty] at *
  unfold simplexDisjointUnion
  simp
  cases' H with Hs Ht
  · rw [Finset.coe_nonempty] at *
    constructor
    assumption
  · rw [Finset.coe_nonempty] at *
    rw [Or.comm]
    constructor
    assumption

instance SimplexDisjoint.nonempty.left
    (s : Finset E)
    [Nonempty s]
  : Nonempty (s ⊔ₛ (∅ : Finset F)) :=
by
  have : Nonempty ↥s ∨ Nonempty ↥(∅ : Finset F) :=
    by
    left
    assumption
  apply SimplexDisjoint.nonempty s (∅ : Finset F) this

instance SimplexDisjoint.nonempty.right
    (t : Finset F)
    [Nonempty t]
  : Nonempty ((∅ : Finset E) ⊔ₛ t) :=
by
  have : Nonempty ↥(∅ : Finset E) ∨ Nonempty ↥t :=
    by
    right
    assumption
  apply SimplexDisjoint.nonempty (∅ : Finset E) t this

instance SimplexDisjoint.partialOrder
  : PartialOrder (Finset (BinaryDirectSum E F)) :=
    Finset.partialOrder

theorem simplex_disjoint_disjoint (s t : Finset α) :
    @Disjoint _ SimplexDisjoint.partialOrder _ (Finset.product s {(0 : ℕ)})
      (Finset.product t {(1 : ℕ)}) :=
  by
  rw [Finset.disjoint_left]
  intro x x_in_s0
  rw [Finset.mem_product] at *
  cases' x_in_s0 with x_in_s x0
  rw [not_and_or]
  right
  rw [Finset.mem_singleton] at *
  rw [x0]
  simp

theorem simplex_disjoint_mem (s t : Finset α) (x : α × ℕ) :
    x ∈ s ⊔ₛ t ↔ x.fst ∈ s ∧ x.snd = 0 ∨ x.fst ∈ t ∧ x.snd = 1 :=
  by
  simp only [simplexDisjointUnion]
  rw [← Finset.disjUnion_eq_union, Finset.mem_disjUnion]
  constructor
  intro x_in_prod
  cases' x_in_prod with x_in_s0 x_in_t1
  rw [Finset.mem_product] at x_in_s0
  cases' x_in_s0 with x_in_s x0
  left; constructor
  assumption
  rw [Finset.mem_singleton] at x0
  assumption
  rw [Finset.mem_product] at x_in_t1
  cases' x_in_t1 with x_in_t x1
  right; constructor
  assumption
  rw [Finset.mem_singleton] at x1
  assumption
  intro x_in_st
  iterate 2 rw [Finset.mem_product, Finset.mem_singleton]
  assumption
  apply simplex_disjoint_disjoint

theorem simplex_disjoint_mem_left (s t : Finset α) (x : α) : (x, 0) ∈ s ⊔ₛ t ↔ x ∈ s :=
  by
  unfold simplexDisjointUnion
  constructor
  · intro x0_in_st
    rw [Finset.mem_union] at x0_in_st
    cases' x0_in_st with x0_in_s0 x0_in_t1
    rw [Finset.mem_product] at x0_in_s0
    cases' x0_in_s0 with x_in_s zero
    simp at x_in_s
    assumption
    rw [Finset.mem_product] at x0_in_t1
    cases' x0_in_t1 with x_in_t contra
    simp at contra
    contradiction
  · intro x_in_s
    rw [Finset.mem_union]
    left
    rw [Finset.mem_product]
    constructor
    simp; assumption
    simp

theorem simplex_disjoint_mem_right (s t : Finset α) (x : α) : (x, 1) ∈ s ⊔ₛ t ↔ x ∈ t :=
  by
  unfold simplexDisjointUnion
  constructor
  · intro x1_in_st
    rw [Finset.mem_union] at x1_in_st
    cases' x1_in_st with x1_in_s0 x1_in_t1
    rw [Finset.mem_product] at x1_in_s0
    cases' x1_in_s0 with x_in_s contra
    simp at contra
    contradiction
    rw [Finset.mem_product] at x1_in_t1
    cases' x1_in_t1 with x_in_t one
    simp at x_in_t
    assumption
  · intro x_in_t
    rw [Finset.mem_union]
    right
    rw [Finset.mem_product]
    constructor
    simp; assumption
    simp

theorem simplex_disjoint_subset_unique (s t u w : Finset α) : s ⊔ₛ t ⊆ u ⊔ₛ w ↔ s ⊆ u ∧ t ⊆ w :=
  by
  constructor
  intro disj_sset
  rw [Finset.subset_iff] at disj_sset
  constructor <;> rw [Finset.subset_iff] <;> intro x x_in_s
  have Hs_0 : (x, 0) ∈ s ⊔ₛ t := by
    rw [simplex_disjoint_mem_left]
    assumption
  specialize disj_sset Hs_0
  rw [simplex_disjoint_mem_left] at disj_sset
  assumption
  have Ht_1 : (x, 1) ∈ s ⊔ₛ t := by
    rw [simplex_disjoint_mem_right]
    assumption
  specialize disj_sset Ht_1
  rw [simplex_disjoint_mem_right] at disj_sset
  assumption
  intro sset
  cases' sset with s_sset_u t_sset_w
  rw [Finset.subset_iff] at *
  intro x x_in_st
  simp only [simplexDisjointUnion, Finset.mem_union, Finset.mem_product] at *
  cases x_in_st
  left
  cases' x_in_st with x_in_s x0
  constructor
  specialize s_sset_u x_in_s
  assumption
  assumption
  right
  cases' x_in_st with x_in_t x1
  constructor
  specialize t_sset_w x_in_t
  assumption
  assumption

theorem simplex_disjoint_subset_sep (s : Finset (α × ℕ)) (t u : Finset α) :
    s ⊆ t ⊔ₛ u ↔ ∃ z w : Finset α, s = z ⊔ₛ w ∧ z ⊆ t ∧ w ⊆ u :=
  by
  constructor
  intro s_sset_tu
  let z_prod : Finset (α × ℕ) := Finset.filter (fun x : α × ℕ => x.snd = 0) s
  let z : Finset α := Finset.biUnion z_prod fun x => {x.fst}
  let w_prod : Finset (α × ℕ) := Finset.filter (fun x : α × ℕ => x.snd = 1) s
  let w : Finset α := Finset.biUnion w_prod fun x => {x.fst}
  use z; use w
  have s_eq_zw : s = z ⊔ₛ w := by
    rw [Finset.ext_iff]
    intro x
    constructor
    rw [Finset.subset_iff] at s_sset_tu
    simp_rw [simplex_disjoint_mem] at s_sset_tu
    intro x_in_s
    specialize s_sset_tu x_in_s
    rw [simplex_disjoint_mem]
    simp only [z, z_prod, w, w_prod]
    iterate 2 rw [Finset.mem_biUnion]
    cases s_sset_tu
    left
    cases' s_sset_tu with x_in_t x0
    use x
    rw [Finset.mem_filter]
    constructor; constructor; assumption
    assumption
    rw [Finset.mem_singleton]
    assumption
    right
    cases' s_sset_tu with x_in_u x1
    constructor
    use x
    rw [Finset.mem_filter]
    constructor; constructor; assumption
    assumption
    rw [Finset.mem_singleton]
    assumption
    intro x_in_zw
    rw [simplex_disjoint_mem] at x_in_zw
    cases x_in_zw <;>
      · cases' x_in_zw with x_in_filter xn
        simp only [z, z_prod, w, w_prod] at x_in_filter
        rw [Finset.mem_biUnion] at x_in_filter
        choose y y_in_prod x_eq_y using x_in_filter
        rw [Finset.mem_filter] at y_in_prod
        cases' y_in_prod with y_in_s yn
        rw [Finset.mem_singleton] at x_eq_y
        have : x = y := by
          rw [Prod.eq_iff_fst_eq_snd_eq]
          constructor
          assumption
          rw [xn, yn]
        rw [this]
        assumption
  constructor
  apply s_eq_zw
  rw [← simplex_disjoint_subset_unique, ← s_eq_zw]
  assumption
  intro s_eq_zw
  choose z w s_eq_zw using s_eq_zw
  choose s_eq_zw z_sset_t w_sset_u using s_eq_zw
  rw [Finset.subset_iff]
  intro x x_in_s
  rw [s_eq_zw] at x_in_s
  rw [simplex_disjoint_mem] at *
  cases x_in_s
  left
  cases' x_in_s with x_in_t x0
  constructor
  rw [Finset.subset_iff] at z_sset_t
  specialize z_sset_t x_in_t
  assumption
  assumption
  right
  cases' x_in_s with x_in_u x1
  constructor
  rw [Finset.subset_iff] at w_sset_u
  specialize w_sset_u x_in_u
  assumption
  assumption

theorem simplex_disjoint_eq_unique (s t u w : Finset α) : s ⊔ₛ t = u ⊔ₛ w ↔ s = u ∧ t = w :=
  by
  constructor
  · intro H
    repeat' rw [Finset.Subset.antisymm_iff] at *
    cases' H with st_sset_uw uw_sset_st
    rw [simplex_disjoint_subset_unique] at *
    tauto
  · intro H
    repeat' rw [Finset.Subset.antisymm_iff] at *
    repeat' rw [simplex_disjoint_subset_unique]
    tauto

theorem simplex_disjoint_empty (s t : Finset α) : s ⊔ₛ t = ∅ ↔ s = ∅ ∧ t = ∅ :=
  by
  have H : (∅ : Finset (α × ℕ)) = (∅ : Finset α) ⊔ₛ (∅ : Finset α) :=
    by
    simp
    repeat' rw [Finset.map_empty]
  rw [H]
  apply simplex_disjoint_eq_unique

theorem simplex_disjoint_distr_union (s t u w : Finset α) : s ⊔ₛ t ∪ (u ⊔ₛ w) = s ∪ u ⊔ₛ (t ∪ w) :=
  by
  unfold simplexDisjointUnion
  rw [← Finset.union_assoc]
  rw [Finset.union_assoc _ (Finset.product t {1}) (Finset.product u {0})]
  rw [Finset.union_comm (Finset.product t {1}) (Finset.product u {0})]
  rw [← Finset.union_assoc]
  rw [Finset.union_assoc _ (Finset.product t {1}) (Finset.product w {1})]
  repeat' rw [Finset.union_product]

theorem simplex_disjoint_distr_inter (s t u w : Finset α) : (s ⊔ₛ t) ∩ (u ⊔ₛ w) = s ∩ u ⊔ₛ t ∩ w :=
  by
  unfold simplexDisjointUnion
  repeat' rw [Finset.inter_union_distrib_left]
  repeat' rw [Finset.union_inter_distrib_right]
  have H_tu_empty :
    (Finset.product t {1} : Finset (α × ℕ)) ∩ (Finset.product u {0} : Finset (α × ℕ)) = ∅ :=
    by
    rw [← Finset.disjoint_iff_inter_eq_empty]
    rw [Finset.disjoint_product]
    right
    rw [Finset.disjoint_iff_inter_eq_empty]
    tauto
  have H_sw_empty :
    (Finset.product s {0} : Finset (α × ℕ)) ∩ (Finset.product w {1} : Finset (α × ℕ)) = ∅ :=
    by
    rw [← Finset.disjoint_iff_inter_eq_empty]
    rw [Finset.disjoint_product]
    right
    rw [Finset.disjoint_iff_inter_eq_empty]
    tauto
  rw [H_tu_empty, H_sw_empty]
  repeat' rw [Finset.union_empty, Finset.empty_union]
  repeat' rw [Finset.inter_product]

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem simplex_disjoint_card (s t : Finset α) : (s ⊔ₛ t).card = s.card + t.card :=
  by
  simp only [simplexDisjointUnion]
  set s₀ : Finset (α × ℕ) := s ×ˢ {0}
  set t₁ : Finset (α × ℕ) := t ×ˢ {1}
  have card_disj : (s₀ ∪ t₁).card = s₀.card + t₁.card :=
    by
    apply Finset.card_union_of_disjoint
    simp only [s₀, t₁, Finset.disjoint_product, Finset.disjoint_singleton]
    right
    apply Nat.zero_ne_one
  simp only [card_disj, s₀, t₁, Finset.card_product, Finset.card_singleton, mul_one]

/- ././././Mathport/Syntax/Translate/Expr.lean:373:4: unsupported set replacement {(«expr ⊔ₛ »(s, t)) | (s «expr ∈ » X.simplices) (t «expr ∈ » Y.simplices)} -/
-- Define simplicial join.
@[simp]
def simplicialJoin (X Y : SimplicialComplex α) : SimplicialComplex (α × ℕ) :=
  SimplicialComplex.mk
    "././././Mathport/Syntax/Translate/Expr.lean:373:4: unsupported set replacement {(«expr ⊔ₛ »(s, t)) | (s «expr ∈ » X.simplices) (t «expr ∈ » Y.simplices)}"
    (by
      rw [Set.nonempty_coe_sort, Set.nonempty_def]
      use∅
      rw [Set.mem_setOf]
      use∅; constructor; apply simplicialComplex_empty_simplex
      use∅; constructor; apply simplicialComplex_empty_simplex
      tauto)
    (by
      unfold IsSubsetClosed
      intro s s_in_XY t t_sset_s
      rw [Set.mem_setOf] at *
      choose u Hu v Hv uv_eq_s using s_in_XY
      rw [← uv_eq_s, simplex_disjoint_subset_sep] at t_sset_s
      choose z w t_eq_zw using t_sset_s
      choose t_eq_zw z_sset_u w_sset_v using t_eq_zw
      use z; constructor
      apply X.subset_closed u <;> assumption
      use w; constructor
      apply Y.subset_closed v <;> assumption
      symm; assumption)

infixl:70 " ⋆ " => simplicialJoin

theorem simplicialJoin_as_union (X Y : SimplicialComplex α) :
    (X ⋆ Y).simplices = ⋃ s ∈ X.simplices, ⋃ t ∈ Y.simplices, {s ⊔ₛ t} :=
  by
  simp only [simplicialJoin, Set.ext_iff, Set.mem_iUnion, Set.mem_setOf, Set.mem_singleton_iff]
  intro x
  constructor
  intro x_in_join
  choose s s_in_X t t_in_Y st_eq_x using x_in_join
  use s; constructor; assumption
  use t; constructor; assumption
  symm; assumption
  intro x_in_union
  choose s s_in_X t t_in_Y st_eq_x using x_in_union
  use s; constructor; assumption
  use t; constructor; assumption
  symm; assumption

-- Establish basic algebraic properties about joins.
instance simplicialJoin.fintype (X : SimplicialComplex α) [Fintype X.simplices]
    (Y : SimplicialComplex α) [Fintype Y.simplices] : Fintype (X ⋆ Y).simplices :=
  by
  rw [simplicialJoin_as_union]
  apply Set.fintypeBiUnion
  intro s s_in_X
  apply Set.fintypeBiUnion
  intro t t_in_Y
  apply Unique.fintype

theorem simplicialJoin_sep (X Y : SimplicialComplex α) (s t : Finset α) :
    s ⊔ₛ t ∈ (X ⋆ Y).simplices ↔ s ∈ X.simplices ∧ t ∈ Y.simplices :=
  by
  unfold simplicialJoin
  simp only [SimplicialComplex.simplices]
  rw [Set.mem_setOf]
  constructor
  · intro st_in_XY
    choose u Hu w Hw uw_eq_st using st_in_XY
    rw [simplex_disjoint_eq_unique] at uw_eq_st
    cases' uw_eq_st with u_eq_s w_eq_t
    constructor
    rw [u_eq_s] at Hu
    assumption
    rw [w_eq_t] at Hw
    assumption
  · intro st_in_XY
    cases' st_in_XY with s_in_X t_in_Y
    use s; constructor; assumption
    use t; constructor; assumption
    rfl

theorem simplicialJoin_mem (X Y : SimplicialComplex α) (s : Finset (α × ℕ)) :
    s ∈ (X ⋆ Y).simplices ↔ ∃ t ∈ X.simplices, ∃ u ∈ Y.simplices, s = t ⊔ₛ u :=
  by
  unfold simplicialJoin
  simp only [SimplicialComplex.simplices]
  rw [Set.mem_setOf]
  constructor
  · intro s_in_XY
    choose t Ht u Hu s_eq_tu using s_in_XY
    use t; constructor; assumption
    use u; constructor; assumption
    symm
    assumption
  · intro s_eq_tu
    choose t Ht u Hu s_eq_tu using s_eq_tu
    use t; constructor; assumption
    use u; constructor; assumption
    symm
    assumption

theorem simplicialJoin_incl_left (X Y : SimplicialComplex α) (s : Finset α) :
    s ∈ X.simplices → s ⊔ₛ ∅ ∈ (X ⋆ Y).simplices :=
  by
  intro s_in_X
  unfold simplicialJoin
  simp only [SimplicialComplex.simplices]
  rw [Set.mem_setOf]
  use s; constructor; assumption
  use∅; constructor; apply simplicialComplex_empty_simplex
  rfl

theorem simplicialJoin_incl_right (X Y : SimplicialComplex α) (t : Finset α) :
    t ∈ Y.simplices → ∅ ⊔ₛ t ∈ (X ⋆ Y).simplices :=
  by
  intro t_in_Y
  unfold simplicialJoin
  simp only [SimplicialComplex.simplices]
  rw [Set.mem_setOf]
  use∅; constructor; apply simplicialComplex_empty_simplex
  use t; constructor; assumption
  rfl

theorem simplicialJoin_vertices_mem_left (X Y : SimplicialComplex α) (x : α) :
    (x, 0) ∈ vertices (X ⋆ Y) ↔ x ∈ vertices X :=
  by
  dsimp only [vertices, simplicialJoin, SimplicialComplex.simplices]
  repeat' rw [Set.mem_iUnion]
  constructor
  · intro x0_in_XY
    choose s s_lift Hs x0_in_s using x0_in_XY
    rw [Set.mem_setOf, Set.mem_range] at Hs
    choose Hs s_lifts using Hs
    choose t Ht u Hu tu_eq_s using Hs
    use t
    rw [Set.mem_iUnion]
    use Ht
    have Hx_0 : (x, 0) ∈ s := by
      rw [← Finset.mem_coe, s_lifts]
      assumption
    rw [Finset.mem_coe]
    rw [← tu_eq_s, simplex_disjoint_mem_left] at Hx_0
    assumption
  · intro x_in_s
    choose s s_lift Hs x_in_s using x_in_s
    rw [Set.mem_range] at Hs
    choose Hs s_lifts using Hs
    use s ⊔ₛ ∅
    rw [Set.mem_setOf, Set.mem_iUnion]
    have H_ex :
      ∃ (z : Finset α) (Hz : z ∈ X.simplices) (w : Finset α) (Hw : w ∈ Y.simplices),
        z ⊔ₛ w = s ⊔ₛ ∅ :=
      by
      use s; constructor; assumption
      use∅; constructor; apply simplicialComplex_empty_simplex
      rfl
    use H_ex
    rw [Finset.mem_coe, simplex_disjoint_mem_left]
    have Hx : x ∈ s := by
      rw [← Finset.mem_coe, s_lifts]
      assumption
    assumption

theorem simplicialJoin_vertices_mem_right (X Y : SimplicialComplex α) (x : α) :
    (x, 1) ∈ vertices (X ⋆ Y) ↔ x ∈ vertices Y :=
  by
  dsimp only [vertices, simplicialJoin, SimplicialComplex.simplices]
  repeat' rw [Set.mem_iUnion]
  constructor
  · intro x1_in_XY
    choose s s_lift Hs x1_in_s using x1_in_XY
    rw [Set.mem_setOf, Set.mem_range] at Hs
    choose Hs s_lifts using Hs
    choose t Ht u Hu tu_eq_s using Hs
    use u
    rw [Set.mem_iUnion]
    use Hu
    have Hx_1 : (x, 1) ∈ s := by
      rw [← Finset.mem_coe, s_lifts]
      assumption
    rw [Finset.mem_coe]
    rw [← tu_eq_s, simplex_disjoint_mem_right] at Hx_1
    assumption
  · intro x_in_s
    choose s s_lift Hs x_in_s using x_in_s
    rw [Set.mem_range] at Hs
    choose Hs s_lifts using Hs
    use∅ ⊔ₛ s
    rw [Set.mem_setOf, Set.mem_iUnion]
    have H_ex :
      ∃ (z : Finset α) (Hz : z ∈ X.simplices) (w : Finset α) (Hw : w ∈ Y.simplices),
        z ⊔ₛ w = ∅ ⊔ₛ s :=
      by
      use∅; constructor; apply simplicialComplex_empty_simplex
      use s; constructor; assumption
      rfl
    use H_ex
    rw [Finset.mem_coe, simplex_disjoint_mem_right]
    have Hx : x ∈ s := by
      rw [← Finset.mem_coe, s_lifts]
      assumption
    assumption

theorem simplicialJoin_mem_vertices (X Y : SimplicialComplex α) (x : α × ℕ) :
    x ∈ vertices (X ⋆ Y) ↔ x.fst ∈ vertices X ∧ x.snd = 0 ∨ x.fst ∈ vertices Y ∧ x.snd = 1 :=
  by
  constructor
  · intro x_in_XY
    simp only [vertices, simplicialJoin] at x_in_XY
    rw [Set.mem_iUnion] at x_in_XY
    choose y x_in_XY using x_in_XY
    rw [Set.mem_iUnion] at x_in_XY
    choose Hy x_in_y using x_in_XY
    rw [Set.mem_setOf] at Hy
    choose s Hy using Hy
    cases' Hy with Hs Hy
    choose t Hy using Hy
    cases' Hy with Ht st_eq_y
    rw [Finset.ext_iff] at st_eq_y
    specialize st_eq_y x
    cases' st_eq_y with st_imp_y y_imp_st
    rw [Finset.mem_coe] at x_in_y
    specialize y_imp_st x_in_y
    rw [simplex_disjoint_mem] at y_imp_st
    cases' y_imp_st with x_in_s x_in_t
    left
    cases' x_in_s with x_in_s x0
    constructor
    simp only [vertices]
    rw [Set.mem_iUnion]
    use s
    rw [Set.mem_iUnion]
    use Hs
    rw [Finset.mem_coe]
    assumption
    assumption
    right
    cases' x_in_t with x_in_t x1
    constructor
    simp only [vertices]
    rw [Set.mem_iUnion]
    use t
    rw [Set.mem_iUnion]
    use Ht
    rw [Finset.mem_coe]
    assumption
    assumption
  · intro x_in_X_or_Y
    cases' x_in_X_or_Y with x_in_X x_in_Y
    cases' x_in_X with x_in_X x0
    simp only [vertices] at *
    rw [Set.mem_iUnion] at *
    choose s x_in_X using x_in_X
    use s ⊔ₛ ∅
    rw [Set.mem_iUnion] at *
    choose Hs x_in_s using x_in_X
    have Hs_incl : s ⊔ₛ ∅ ∈ (X ⋆ Y).simplices :=
      by
      apply simplicialJoin_incl_left
      assumption
    use Hs_incl
    rw [Finset.mem_coe, simplex_disjoint_mem]
    left
    rw [Finset.mem_coe] at x_in_s
    constructor <;> assumption
    cases' x_in_Y with x_in_Y x1
    simp only [vertices] at *
    rw [Set.mem_iUnion] at *
    choose t x_in_Y using x_in_Y
    use∅ ⊔ₛ t
    rw [Set.mem_iUnion] at *
    choose Ht x_in_t using x_in_Y
    have Ht_incl : ∅ ⊔ₛ t ∈ (X ⋆ Y).simplices :=
      by
      apply simplicialJoin_incl_right
      assumption
    use Ht_incl
    rw [Finset.mem_coe, simplex_disjoint_mem]
    right
    rw [Finset.mem_coe] at x_in_t
    constructor <;> assumption

def simplicialJoinIsoMap (f g : α → β) : α × ℕ → β × ℕ := fun x : α × ℕ =>
  if x.snd = 0 then (f x.fst, x.snd) else (g x.fst, x.snd)

theorem simplicialJoin_iso_simplicial (X Y : SimplicialComplex α) (Z W : SimplicialComplex β)
    (f : SimplicialMap X Z) (g : SimplicialMap Y W) :
    IsSimplicialMap (X ⋆ Y) (Z ⋆ W) (simplicialJoinIsoMap f.map g.map) :=
  by
  unfold IsSimplicialMap
  intro s s_in_XY
  rw [simplicialJoin_mem] at *
  choose t Ht u Hu s_eq_tu using s_in_XY
  use Finset.image f.map t; constructor
  apply f.is_simplicial
  assumption
  use Finset.image g.map u; constructor
  apply g.is_simplicial
  assumption
  rw [s_eq_tu]
  simp only [simplexDisjointUnion]
  rw [Finset.image_union]
  rw [Finset.ext_iff]
  intro x
  constructor
  · intro x_in_f
    rw [Finset.mem_union] at *
    cases x_in_f
    left
    rw [Finset.mem_product]
    rw [Finset.mem_image] at *
    choose y y_in_t0 using x_in_f
    cases' y_in_t0 with y_in_t0 fy_x
    use y.fst
    rw [Finset.mem_product] at y_in_t0
    cases' y_in_t0 with y_in_t0 y_0
    constructor
    assumption
    simp only [simplicialJoinIsoMap] at fy_x
    revert fy_x
    split_ifs
    intro y0_x
    rw [← y0_x]
    rw [Finset.mem_singleton] at y_0
    contradiction
    simp only [simplicialJoinIsoMap] at fy_x
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
    finish
    simp only [Finset.mem_image, simplicialJoinIsoMap] at x_in_f
    choose y y_in_u fy_eq_x using x_in_f
    revert fy_eq_x
    split_ifs
    rw [Finset.mem_product, Finset.mem_singleton] at y_in_u
    choose y_in_u y_one using y_in_u
    have contra : y.snd ≠ 0 := by omega
    contradiction
    intro gy_eq_x
    simp only [Prod.ext_iff, Prod.fst, Prod.snd] at gy_eq_x
    choose gy_eq_x x_one using gy_eq_x
    rw [Finset.mem_product, Finset.mem_singleton] at y_in_u
    choose y_in_u y_one using y_in_u
    right
    rw [Finset.mem_product, Finset.mem_image]
    constructor
    use y.fst; constructor
    assumption
    assumption
    rw [Finset.mem_singleton, ← x_one]
    assumption
  · intro x_in_f_prod
    rw [Finset.mem_union] at *
    cases x_in_f_prod
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
    simp only [simplicialJoinIsoMap]
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
    simp only [simplicialJoinIsoMap]
    split_ifs
    finish
    rw [Prod.eq_iff_fst_eq_snd_eq]
    constructor
    assumption
    rw [x1]

def simplicialJoinIsoInverseMap (f g : β → α) : β × ℕ → α × ℕ := fun x : β × ℕ =>
  if x.snd = 0 then (f x.fst, x.snd) else (g x.fst, x.snd)

theorem simplicialJoin_iso (X Y : SimplicialComplex α) (Z W : SimplicialComplex β) :
    X ≅ Z → Y ≅ W → X ⋆ Y ≅ Z ⋆ W := by
  unfold IsSimpliciallyIso
  unfold IsSimplicialIso
  unfold IsInverseSimplicialIso
  simp only [SimplicialMap.comp, SimplicialMap.map]
  intro X_iso_Z Y_iso_W
  choose f_xz g_zx fxz_inv_gzx using X_iso_Z
  choose f_yw g_wy fyw_inv_gwy using Y_iso_W
  cases' fxz_inv_gzx with gzx_fxz_id fxz_gzx_id
  cases' fyw_inv_gwy with gwy_fyw_id fyw_gwy_id
  let fs : SimplicialMap (X ⋆ Y) (Z ⋆ W) :=
    SimplicialMap.mk (simplicialJoinIsoMap f_xz.map f_yw.map)
      (simplicialJoin_iso_simplicial X Y Z W f_xz f_yw)
  let gs : SimplicialMap (Z ⋆ W) (X ⋆ Y) :=
    SimplicialMap.mk (simplicialJoinIsoMap g_zx.map g_wy.map)
      (simplicialJoin_iso_simplicial Z W X Y g_zx g_wy)
  use fs
  use gs
  simp only [SimplicialMap.map]
  constructor <;> rw [Function.funext_iff]
  · intro x
    simp only [id, Function.comp, simplicialJoinIsoMap]
    simp at *
    split_ifs <;> rw [Prod.eq_iff_fst_eq_snd_eq]
    constructor
    simp
    rw [← Function.comp_apply g_zx.map f_xz.map, gzx_fxz_id]
    simp
    rw [← simplicialJoin_vertices_mem_left _ Y]
    have x_in_XY : ↑x ∈ vertices (X ⋆ Y) := by apply Subtype.coe_prop
    rw [← h]
    simp only [Prod.mk.eta]
    assumption
    constructor
    simp
    rw [← Function.comp_apply g_wy.map f_yw.map, gwy_fyw_id]
    simp
    rw [← simplicialJoin_vertices_mem_right X]
    have x_in_XY : ↑x ∈ vertices (X ⋆ Y) := by apply Subtype.coe_prop
    rw [simplicialJoin_mem_vertices] at x_in_XY
    cases x_in_XY
    cases' x_in_XY with x_in_X x0
    contradiction
    cases' x_in_XY with x_in_Y x1
    rw [← x1]
    simp only [Prod.mk.eta]
    rw [simplicialJoin_mem_vertices]
    right
    constructor <;> assumption
  · intro x
    simp only [id, Function.comp, simplicialJoinIsoMap]
    simp at *
    split_ifs <;> rw [Prod.eq_iff_fst_eq_snd_eq]
    constructor
    simp
    rw [← Function.comp_apply f_xz.map g_zx.map, fxz_gzx_id]
    simp
    rw [← simplicialJoin_vertices_mem_left _ W]
    have x_in_XY : ↑x ∈ vertices (Z ⋆ W) := by apply Subtype.coe_prop
    rw [← h]
    simp only [Prod.mk.eta]
    assumption
    constructor
    simp
    rw [← Function.comp_apply f_yw.map g_wy.map, fyw_gwy_id]
    simp
    rw [← simplicialJoin_vertices_mem_right Z]
    have x_in_XY : ↑x ∈ vertices (Z ⋆ W) := by apply Subtype.coe_prop
    rw [simplicialJoin_mem_vertices] at x_in_XY
    cases x_in_XY
    cases' x_in_XY with x_in_X x0
    contradiction
    cases' x_in_XY with x_in_Y x1
    rw [← x1]
    simp only [Prod.mk.eta]
    rw [simplicialJoin_mem_vertices]
    right
    constructor <;> assumption

theorem simplicialJoin_iso_left (X Y Z : SimplicialComplex α) : X ≅ Y → X ⋆ Z ≅ Y ⋆ Z :=
  by
  intro X_iso_Y
  apply simplicialJoin_iso
  assumption
  rfl

theorem simplicialJoin_iso_right (X Y Z : SimplicialComplex α) : X ≅ Y → Z ⋆ X ≅ Z ⋆ Y :=
  by
  intro X_iso_Y
  apply simplicialJoin_iso
  rfl
  assumption

def simplicialJoinAssocForwardAux (X Y Z : SimplicialComplex α) (ψ : SimplicialCoe (Y ⋆ Z) α) :
    α × ℕ → α × ℕ := fun x : α × ℕ => if x.snd = 0 then x else (ψ.coe (x.fst, 0), x.snd)

def simplicialJoinAssocForwardMap (X Y Z : SimplicialComplex α) (φ : SimplicialCoe (X ⋆ Y) α)
    (ψ : SimplicialCoe (Y ⋆ Z) α) (f : SimplicialMap (φ[X ⋆ Y]) (X ⋆ Y)) : α × ℕ → α × ℕ :=
  fun x : α × ℕ =>
  if x.snd = 0 then (simplicialJoinAssocForwardAux X Y Z ψ) (f.map x.fst) else (ψ.coe x, x.snd)

theorem simplicialJoin_assoc_forward_simplicial_left (X Y Z : SimplicialComplex α)
    (φ : SimplicialCoe (X ⋆ Y) α) (ψ : SimplicialCoe (Y ⋆ Z) α)
    (f : SimplicialMap (φ[X ⋆ Y]) (X ⋆ Y)) (f_inv : IsInverseSimplicialIso φ.SimplicialMap f)
    (a b t : Finset α) (a_in_X : a ∈ X.simplices) (b_in_Y : b ∈ Y.simplices)
    (t_in_Z : t ∈ Z.simplices) :
    Finset.image (simplicialJoinAssocForwardMap X Y Z φ ψ f) (Finset.image φ.coe (a ⊔ₛ b) ⊔ₛ t) ⊆
      a ⊔ₛ Finset.image ψ.coe (b ⊔ₛ t) :=
  by
  simp only [simplicialJoinAssocForwardMap, Finset.subset_iff]
  intro x x_in_img
  rw [Finset.mem_image] at x_in_img
  choose y y_in_u img_y_x using x_in_img
  unfold IsInverseSimplicialIso at f_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def] at f_inv
  choose fφ_id φf_id using f_inv
  simp only [simplexDisjointUnion, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_singleton]
  revert img_y_x
  split_ifs
  simp only [simplicialJoinAssocForwardAux]
  have y_rw : y = (y.fst, 0) := by
    simp only [Prod.ext_iff]
    constructor; rfl; assumption
  rw [y_rw, simplex_disjoint_mem_left, Finset.mem_image] at y_in_u
  choose z z_in_ab coe_z_y using y_in_u
  have z_in_join : z ∈ vertices (X ⋆ Y) :=
    by
    rw [vertex_iff_in_simplex]
    use a ⊔ₛ b; constructor
    rw [simplicialJoin_mem]
    use a; constructor; assumption
    use b; constructor; assumption
    rfl
    assumption
  specialize fφ_id z_in_join
  have coe_rw : φ.simplicial_map.map = φ.coe := by rfl
  rw [coe_rw] at fφ_id
  split_ifs
  intro fy_x
  left
  rw [← coe_z_y, fφ_id] at fy_x h_1
  subst fy_x
  rw [simplex_disjoint_mem] at z_in_ab
  cases' z_in_ab with z_in_a contra
  assumption
  choose z_in_b contra using contra
  have H : z.snd ≠ 0 := by omega
  contradiction
  intro ψfy_x
  right
  rw [← coe_z_y, fφ_id] at ψfy_x h_1
  subst ψfy_x
  simp only [Prod.fst, Prod.snd]
  rw [simplex_disjoint_mem] at z_in_ab
  cases' z_in_ab with contra z_in_b
  choose z_in_a contra using contra
  contradiction
  choose z_in_b z_one using z_in_b
  constructor
  use(z.fst, 0); constructor; left
  simp only [Prod.fst, Prod.snd]
  constructor; assumption; rfl
  apply congr_arg; rfl
  assumption
  intro ψy_x
  right
  rw [simplex_disjoint_mem] at y_in_u
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

theorem simplicialJoin_assoc_forward_simplicial_right (X Y Z : SimplicialComplex α)
    (φ : SimplicialCoe (X ⋆ Y) α) (ψ : SimplicialCoe (Y ⋆ Z) α)
    (f : SimplicialMap (φ[X ⋆ Y]) (X ⋆ Y)) (f_inv : IsInverseSimplicialIso φ.SimplicialMap f)
    (a b t : Finset α) (a_in_X : a ∈ X.simplices) (b_in_Y : b ∈ Y.simplices)
    (t_in_Z : t ∈ Z.simplices) :
    a ⊔ₛ Finset.image ψ.coe (b ⊔ₛ t) ⊆
      Finset.image (simplicialJoinAssocForwardMap X Y Z φ ψ f) (Finset.image φ.coe (a ⊔ₛ b) ⊔ₛ t) :=
  by
  simp only [simplicialJoinAssocForwardMap, Finset.subset_iff]
  intro x x_in_join
  unfold IsInverseSimplicialIso at f_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def] at f_inv
  choose fφ_id φf_id using f_inv
  simp only [simplex_disjoint_mem, Finset.mem_image] at x_in_join
  simp only [Finset.mem_image, simplicialJoinAssocForwardAux]
  cases' x_in_join with x_in_a x_in_ψ
  have x_in_XY : x ∈ vertices (X ⋆ Y) :=
    by
    rw [vertex_iff_in_simplex]
    use a ⊔ₛ b; constructor
    rw [simplicialJoin_mem]
    use a; constructor; assumption
    use b; constructor; assumption
    rfl
    rw [simplex_disjoint_mem]
    left; assumption
  specialize fφ_id x_in_XY
  have coe_rw : φ.simplicial_map.map = φ.coe := by rfl
  rw [coe_rw] at fφ_id
  use(φ.coe x, 0); constructor
  rw [simplex_disjoint_mem_left]
  apply Finset.mem_image_of_mem
  rw [simplex_disjoint_mem]
  left; assumption
  choose x_in_a x_zero using x_in_a
  simp only [fφ_id, x_zero, eq_self_iff_true, if_true]
  choose x_in_ψ x_one using x_in_ψ
  choose y y_in_bt ψy_x using x_in_ψ
  cases' y_in_bt with y_in_b y_in_t
  choose y_in_b y_zero using y_in_b
  use(φ.coe (y.fst, 1), 0); constructor
  rw [simplex_disjoint_mem_left]
  apply Finset.mem_image_of_mem
  rw [simplex_disjoint_mem]
  right
  simp only [Prod.fst, Prod.snd]
  constructor; assumption; rfl
  have y_in_XY : (y.fst, 1) ∈ vertices (X ⋆ Y) :=
    by
    rw [vertex_iff_in_simplex]
    use a ⊔ₛ b; constructor
    rw [simplicialJoin_mem]
    use a; constructor; assumption
    use b; constructor; assumption
    rfl
    rw [simplex_disjoint_mem]
    simp only [Prod.fst, Prod.snd]
    right
    constructor; assumption; rfl
  specialize fφ_id y_in_XY
  have coe_rw : φ.simplicial_map.map = φ.coe := by rfl
  rw [coe_rw] at fφ_id
  simp only [fφ_id, y_zero, eq_self_iff_true, if_true, Nat.one_ne_zero, if_false]
  have y_rw : y = (y.fst, y.snd) := by
    simp only [Prod.ext_iff]
    constructor <;> rfl
  rw [y_rw] at ψy_x
  rw [← y_zero, ← x_one, ψy_x]
  simp only [Prod.ext_iff]
  constructor <;> rfl
  use y; constructor
  rw [simplex_disjoint_mem]
  right; assumption
  choose y_in_t y_one using y_in_t
  simp only [y_one, Nat.one_ne_zero, if_false, Prod.ext_iff]
  rw [@comm _ Eq] at x_one
  constructor; assumption; assumption

theorem simplicialJoin_assoc_forward_simplicial (X Y Z : SimplicialComplex α)
    (φ : SimplicialCoe (X ⋆ Y) α) (ψ : SimplicialCoe (Y ⋆ Z) α)
    (f : SimplicialMap (φ[X ⋆ Y]) (X ⋆ Y)) (f_inv : IsInverseSimplicialIso φ.SimplicialMap f) :
    IsSimplicialMap (φ[X ⋆ Y] ⋆ Z) (X ⋆ ψ[Y ⋆ Z]) (simplicialJoinAssocForwardMap X Y Z φ ψ f) :=
  by
  simp only [IsSimplicialMap]
  intro u u_in_join
  rw [simplicialJoin_mem] at u_in_join ⊢
  choose s s_in_coe t t_in_z u_eq_st using u_in_join
  simp only [simplicialImage, simplicialJoin, Set.mem_setOf] at s_in_coe
  choose v v_in_join coe_v_s using s_in_coe
  choose a a_in_X b b_in_Y ab_eq_v using v_in_join
  subst ab_eq_v
  subst coe_v_s
  subst u_eq_st
  use a; constructor; assumption
  use Finset.image ψ.coe (b ⊔ₛ t); constructor
  simp only [simplicialImage, Set.mem_setOf, simplicialJoin_mem]
  use b ⊔ₛ t; constructor
  use b; constructor; assumption
  use t; constructor; assumption
  rfl; rfl
  simp only [simplicialJoinAssocForwardMap, Finset.ext_iff]
  intro x
  constructor
  apply simplicialJoin_assoc_forward_simplicial_left <;> assumption
  apply simplicialJoin_assoc_forward_simplicial_right <;> assumption

def simplicialJoinAssocInvAux (X Y Z : SimplicialComplex α) (φ : SimplicialCoe (X ⋆ Y) α) :
    α × ℕ → α × ℕ := fun x : α × ℕ => if x.snd = 0 then (φ.coe (x.fst, 1), 0) else x

def simplicialJoinAssocInvMap (X Y Z : SimplicialComplex α) (φ : SimplicialCoe (X ⋆ Y) α)
    (ψ : SimplicialCoe (Y ⋆ Z) α) (g : SimplicialMap (ψ[Y ⋆ Z]) (Y ⋆ Z)) : α × ℕ → α × ℕ :=
  fun x : α × ℕ =>
  if x.snd = 0 then (φ.coe x, 0) else (simplicialJoinAssocInvAux X Y Z φ) (g.map x.fst)

theorem simplicialJoin_assoc_inv_simplicial_left (X Y Z : SimplicialComplex α)
    (φ : SimplicialCoe (X ⋆ Y) α) (ψ : SimplicialCoe (Y ⋆ Z) α)
    (g : SimplicialMap (ψ[Y ⋆ Z]) (Y ⋆ Z)) (g_inv : IsInverseSimplicialIso ψ.SimplicialMap g)
    (s a b : Finset α) (s_in_X : s ∈ X.simplices) (a_in_Y : a ∈ Y.simplices)
    (b_in_Z : b ∈ Z.simplices) :
    Finset.image (simplicialJoinAssocInvMap X Y Z φ ψ g) (s ⊔ₛ Finset.image ψ.coe (a ⊔ₛ b)) ⊆
      Finset.image φ.coe (s ⊔ₛ a) ⊔ₛ b :=
  by
  simp only [simplicialJoinAssocInvMap, Finset.subset_iff]
  intro x x_in_img
  unfold IsInverseSimplicialIso at g_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def] at g_inv
  choose gψ_id ψg_id using g_inv
  simp only [Finset.mem_image, simplex_disjoint_mem, simplicialJoinAssocInvMap] at x_in_img
  choose y y_in_join img_y_x using x_in_img
  simp only [simplexDisjointUnion, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_singleton]
  revert img_y_x
  split_ifs
  cases' y_in_join with y_in_s contra
  intro φy_x
  left
  simp only [Prod.ext_iff] at φy_x
  choose φy_x x_zero using φy_x
  rw [@comm _ Eq] at x_zero
  use y; constructor
  left; assumption
  assumption
  assumption
  choose y_in_coe contra using contra
  have H : y.snd ≠ 0 := by omega
  contradiction
  cases' y_in_join with contra y_in_coe
  choose y_in_s contra using contra
  contradiction
  choose y_in_coe y_one using y_in_coe
  choose z z_in_join ψz_y using y_in_coe
  simp only [simplicialJoinAssocInvAux]
  intro img_y_x
  have z_in_YZ : z ∈ vertices (Y ⋆ Z) :=
    by
    rw [vertex_iff_in_simplex]
    use a ⊔ₛ b; constructor
    rw [simplicialJoin_mem]
    use a; constructor; assumption
    use b; constructor; assumption
    rfl
    rw [simplex_disjoint_mem]
    assumption
  specialize gψ_id z_in_YZ
  have coe_rw : ψ.simplicial_map.map = ψ.coe := by rfl
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
  constructor; assumption; rfl
  assumption
  assumption
  right
  choose z_in_b z_one using z_in_b
  simp only [← ψz_y, gψ_id, Prod.ext_iff, z_one, Nat.one_ne_zero, if_false] at img_y_x
  choose z_eq_x x_one using img_y_x
  rw [z_eq_x] at z_in_b
  rw [@comm _ Eq] at x_one
  constructor <;> assumption

theorem simplicialJoin_assoc_inv_simplicial_right (X Y Z : SimplicialComplex α)
    (φ : SimplicialCoe (X ⋆ Y) α) (ψ : SimplicialCoe (Y ⋆ Z) α)
    (g : SimplicialMap (ψ[Y ⋆ Z]) (Y ⋆ Z)) (g_inv : IsInverseSimplicialIso ψ.SimplicialMap g)
    (s a b : Finset α) (s_in_X : s ∈ X.simplices) (a_in_Y : a ∈ Y.simplices)
    (b_in_Z : b ∈ Z.simplices) :
    Finset.image φ.coe (s ⊔ₛ a) ⊔ₛ b ⊆
      Finset.image (simplicialJoinAssocInvMap X Y Z φ ψ g) (s ⊔ₛ Finset.image ψ.coe (a ⊔ₛ b)) :=
  by
  simp only [simplicialJoinAssocInvMap, Finset.subset_iff]
  intro x x_in_join
  unfold IsInverseSimplicialIso at g_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def] at g_inv
  choose gψ_id ψg_id using g_inv
  simp only [simplex_disjoint_mem, Finset.mem_image] at x_in_join
  simp only [Finset.mem_image, simplicialJoinAssocInvMap]
  cases' x_in_join with x_in_coe x_in_b
  choose x_in_coe x_zero using x_in_coe
  choose y y_in_join φy_x using x_in_coe
  simp only [simplicialJoinAssocInvAux]
  cases' y_in_join with y_in_s y_in_a
  use y; constructor
  rw [simplex_disjoint_mem]
  left; assumption
  choose y_in_s y_zero using y_in_s
  rw [@comm _ Eq] at x_zero
  simp only [y_zero, eq_self_iff_true, if_true, Prod.ext_iff]
  constructor <;> assumption
  choose y_in_a y_one using y_in_a
  use(ψ.coe (y.fst, 0), 1); constructor
  rw [simplex_disjoint_mem_right]
  apply Finset.mem_image_of_mem
  rw [simplex_disjoint_mem_left]
  assumption
  have y_in_YZ : (y.fst, 0) ∈ vertices (Y ⋆ Z) :=
    by
    rw [vertex_iff_in_simplex]
    use a ⊔ₛ b; constructor
    rw [simplicialJoin_mem]
    use a; constructor; assumption
    use b; constructor; assumption
    rfl
    rw [simplex_disjoint_mem_left]
    assumption
  specialize gψ_id y_in_YZ
  have coe_rw : ψ.simplicial_map.map = ψ.coe := by rfl
  rw [coe_rw] at gψ_id
  simp only [y_one, gψ_id, Nat.one_ne_zero, if_false, eq_self_iff_true, if_true]
  have y_rw : y = (y.fst, y.snd) := by
    simp only [Prod.ext_iff]
    constructor <;> rfl
  rw [y_rw] at φy_x
  rw [← y_one, ← x_zero, φy_x]
  simp only [Prod.ext_iff]
  constructor <;> rfl
  use(ψ.coe x, 1); constructor
  rw [simplex_disjoint_mem_right]
  apply Finset.mem_image_of_mem
  rw [simplex_disjoint_mem]
  right; assumption
  have x_in_YZ : x ∈ vertices (Y ⋆ Z) :=
    by
    rw [vertex_iff_in_simplex]
    use a ⊔ₛ b; constructor
    rw [simplicialJoin_mem]
    use a; constructor; assumption
    use b; constructor; assumption
    rfl
    rw [simplex_disjoint_mem]
    right; assumption
  specialize gψ_id x_in_YZ
  have coe_rw : ψ.simplicial_map.map = ψ.coe := by rfl
  rw [coe_rw] at gψ_id
  choose x_in_b x_one using x_in_b
  simp only [simplicialJoinAssocInvAux]
  simp only [Prod.snd, x_one, gψ_id, Nat.one_ne_zero, if_false]

theorem simplicialJoin_assoc_inv_simplicial (X Y Z : SimplicialComplex α)
    (φ : SimplicialCoe (X ⋆ Y) α) (ψ : SimplicialCoe (Y ⋆ Z) α)
    (g : SimplicialMap (ψ[Y ⋆ Z]) (Y ⋆ Z)) (g_inv : IsInverseSimplicialIso ψ.SimplicialMap g) :
    IsSimplicialMap (X ⋆ ψ[Y ⋆ Z]) (φ[X ⋆ Y] ⋆ Z) (simplicialJoinAssocInvMap X Y Z φ ψ g) :=
  by
  simp only [IsSimplicialMap]
  intro u u_in_join
  rw [simplicialJoin_mem] at u_in_join ⊢
  choose s s_in_X t t_in_coe u_eq_st using u_in_join
  simp only [simplicialImage, simplicialJoin, Set.mem_setOf] at t_in_coe
  choose v v_in_join coe_v_s using t_in_coe
  choose a a_in_Y b b_in_Z ab_eq_v using v_in_join
  subst ab_eq_v
  subst coe_v_s
  subst u_eq_st
  use Finset.image φ.coe (s ⊔ₛ a); constructor
  simp only [simplicialImage, Set.mem_setOf, simplicialJoin_mem]
  use s ⊔ₛ a; constructor
  use s; constructor; assumption
  use a; constructor; assumption
  rfl; rfl
  use b; constructor; assumption
  simp only [simplicialJoinAssocForwardMap, Finset.ext_iff]
  intro x
  constructor
  apply simplicialJoin_assoc_inv_simplicial_left <;> assumption
  apply simplicialJoin_assoc_inv_simplicial_right <;> assumption

theorem simplicialJoin_assoc [Nonempty α] (X Y Z : SimplicialComplex α)
    (φ : SimplicialCoe (X ⋆ Y) α) (ψ : SimplicialCoe (Y ⋆ Z) α) : φ[X ⋆ Y] ⋆ Z ≅ X ⋆ ψ[Y ⋆ Z] :=
  by
  have φ_iso : IsSimplicialIso φ.simplicial_map := by apply coe_is_iso
  have ψ_iso : IsSimplicialIso ψ.simplicial_map := by apply coe_is_iso
  unfold IsSimplicialIso at φ_iso ψ_iso
  choose gXY gφ_inv using φ_iso
  choose gYZ gψ_inv using ψ_iso
  let f_assoc : SimplicialMap (φ[X ⋆ Y] ⋆ Z) (X ⋆ ψ[Y ⋆ Z]) :=
    SimplicialMap.mk (simplicialJoinAssocForwardMap X Y Z φ ψ gXY)
      (simplicialJoin_assoc_forward_simplicial X Y Z φ ψ gXY gφ_inv)
  let g_assoc : SimplicialMap (X ⋆ ψ[Y ⋆ Z]) (φ[X ⋆ Y] ⋆ Z) :=
    SimplicialMap.mk (simplicialJoinAssocInvMap X Y Z φ ψ gYZ)
      (simplicialJoin_assoc_inv_simplicial X Y Z φ ψ gYZ gψ_inv)
  unfold IsInverseSimplicialIso at gφ_inv gψ_inv
  simp only [Set.restrict_eq_restrict_iff, Set.EqOn, SimplicialMap.comp, Function.comp_apply,
    id.def] at gφ_inv gψ_inv
  have φ_rw : φ.simplicial_map.map = φ.coe := by rfl
  have ψ_rw : ψ.simplicial_map.map = ψ.coe := by rfl
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
    id.def]
  simp only [simplicialJoinAssocForwardMap, simplicialJoinAssocInvMap]
  constructor
  · intro x x_in_join
    rw [vertex_iff_in_simplex] at x_in_join
    choose u u_in_join x_in_u using x_in_join
    simp only [simplicialJoin_mem, simplicialImage, Set.mem_setOf] at u_in_join
    choose s s_in_coe t t_in_Z u_eq_st using u_in_join
    choose v v_in_join coe_v_s using s_in_coe
    choose a a_in_X b b_in_Y v_eq_ab using v_in_join
    subst v_eq_ab
    subst coe_v_s
    subst u_eq_st
    simp only [Finset.mem_image, simplex_disjoint_mem] at x_in_u
    cases' x_in_u with x_in_coe x_in_t
    choose x_in_coe x_zero using x_in_coe
    choose y y_in_join φy_x using x_in_coe
    simp only [← φy_x, x_zero, eq_self_iff_true, if_true]
    simp only [simplicialJoinAssocForwardAux, simplicialJoinAssocInvAux]
    have y_in_XY : y ∈ vertices (X ⋆ Y) :=
      by
      rw [vertex_iff_in_simplex]
      use a ⊔ₛ b; constructor
      rw [simplicialJoin_mem]
      use a; constructor; assumption
      use b; constructor; assumption
      rfl
      rw [simplex_disjoint_mem]
      assumption
    specialize gφ_id y_in_XY
    simp only [gφ_id]
    cases' y_in_join with y_in_a y_in_b
    choose y_in_a y_zero using y_in_a
    simp only [y_zero, eq_self_iff_true, if_true, Prod.snd, Prod.ext_iff]
    rw [@comm _ Eq] at x_zero
    constructor <;> assumption
    choose y_in_b y_one using y_in_b
    have y_in_YZ : (y.fst, 0) ∈ vertices (Y ⋆ Z) :=
      by
      rw [simplicialJoin_vertices_mem_left, vertex_iff_in_simplex]
      use b; constructor <;> assumption
    specialize gψ_id y_in_YZ
    simp only [gψ_id, y_one, eq_self_iff_true, if_true, Nat.one_ne_zero, if_false, Prod.snd,
      Prod.ext_iff]
    have y_rw : y = (y.fst, y.snd) := by
      simp only [Prod.ext_iff]
      constructor <;> rfl
    rw [@comm _ Eq] at x_zero
    rw [← y_one, ← y_rw]
    constructor <;> assumption
    have x_in_YZ : x ∈ vertices (Y ⋆ Z) :=
      by
      rw [vertex_iff_in_simplex]
      use b ⊔ₛ t; constructor
      rw [simplicialJoin_mem]
      use b; constructor; assumption
      use t; constructor; assumption
      rfl
      rw [simplex_disjoint_mem]
      right; assumption
    choose x_in_t x_one using x_in_t
    specialize gψ_id x_in_YZ
    simp only [simplicialJoinAssocInvAux]
    simp only [gψ_id, x_one, Nat.one_ne_zero, if_false]
  · intro x x_in_join
    rw [vertex_iff_in_simplex] at x_in_join
    choose u u_in_join x_in_u using x_in_join
    simp only [simplicialJoin_mem, simplicialImage, Set.mem_setOf] at u_in_join
    choose s s_in_X t t_in_coe u_eq_st using u_in_join
    choose v v_in_join coe_v_t using t_in_coe
    choose a a_in_X b b_in_Y v_eq_ab using v_in_join
    subst v_eq_ab
    subst coe_v_t
    subst u_eq_st
    simp only [Finset.mem_image, simplex_disjoint_mem] at x_in_u
    cases' x_in_u with x_in_s x_in_coe
    have x_in_XY : x ∈ vertices (X ⋆ Y) :=
      by
      rw [vertex_iff_in_simplex]
      use s ⊔ₛ a; constructor
      rw [simplicialJoin_mem]
      use s; constructor; assumption
      use a; constructor; assumption
      rfl
      rw [simplex_disjoint_mem]
      left; assumption
    choose x_in_s x_one using x_in_s
    specialize gφ_id x_in_XY
    simp only [simplicialJoinAssocForwardAux]
    simp only [gφ_id, x_one, eq_self_iff_true, if_true]
    choose x_in_coe x_one using x_in_coe
    choose y y_in_join ψy_x using x_in_coe
    cases' y_in_join with y_in_a y_in_b
    have y_in_YZ : y ∈ vertices (Y ⋆ Z) :=
      by
      rw [vertex_iff_in_simplex]
      use a ⊔ₛ b; constructor
      rw [simplicialJoin_mem]
      use a; constructor; assumption
      use b; constructor; assumption
      rfl
      rw [simplex_disjoint_mem]
      left; assumption
    choose y_in_a y_zero using y_in_a
    specialize gψ_id y_in_YZ
    have y_in_XY : (y.fst, 1) ∈ vertices (X ⋆ Y) :=
      by
      rw [simplicialJoin_vertices_mem_right, vertex_iff_in_simplex]
      use a; constructor <;> assumption
    specialize gφ_id y_in_XY
    simp only [simplicialJoinAssocForwardAux, simplicialJoinAssocInvAux]
    simp only [← ψy_x, gψ_id, gφ_id, y_zero, x_one, eq_self_iff_true, if_true, Nat.one_ne_zero,
      if_false, Prod.snd]
    have y_rw : y = (y.fst, y.snd) := by
      simp only [Prod.ext_iff]
      constructor <;> rfl
    rw [← y_zero, ← y_rw]
    rw [@comm _ Eq] at x_one
    simp only [Prod.ext_iff]
    constructor <;> assumption
    have y_in_YZ : y ∈ vertices (Y ⋆ Z) :=
      by
      rw [vertex_iff_in_simplex]
      use a ⊔ₛ b; constructor
      rw [simplicialJoin_mem]
      use a; constructor; assumption
      use b; constructor; assumption
      rfl
      rw [simplex_disjoint_mem]
      right; assumption
    choose y_in_b y_one using y_in_b
    specialize gψ_id y_in_YZ
    simp only [simplicialJoinAssocForwardAux, simplicialJoinAssocInvAux]
    simp only [← ψy_x, gψ_id, y_one, x_one, Nat.one_ne_zero, if_false, Prod.ext_iff]
    constructor <;> rfl

def simplicialJoinCommMap : α × ℕ → α × ℕ := fun x : α × ℕ =>
  if x.snd = 0 then (x.fst, 1) else (x.fst, 0)

theorem simplicialJoin_comm_simplicial (X Y : SimplicialComplex α) :
    IsSimplicialMap (X ⋆ Y) (Y ⋆ X) simplicialJoinCommMap :=
  by
  simp only [IsSimplicialMap, simplicialJoin, Set.mem_setOf]
  intro u u_in_XY
  choose s s_in_X t t_in_Y st_eq_u using u_in_XY
  use t; constructor; assumption
  use s; constructor; assumption
  simp only [simplicialJoinCommMap, Finset.ext_iff]
  intro x; constructor
  · intro x_in_ts
    rw [simplex_disjoint_mem] at x_in_ts
    rw [Finset.mem_image]
    cases' x_in_ts with x_in_t x_in_s
    choose x_in_t x_zero using x_in_t
    use(x.fst, 1); constructor
    rw [← st_eq_u, simplex_disjoint_mem_right]
    assumption
    simp only [Nat.one_ne_zero, if_false]
    simp only [← x_zero, Prod.ext_iff]
    constructor <;> rfl
    choose x_in_s x_one using x_in_s
    use(x.fst, 0); constructor
    rw [← st_eq_u, simplex_disjoint_mem_left]
    assumption
    simp only [eq_self_iff_true, if_true]
    simp only [← x_one, Prod.ext_iff]
    constructor <;> rfl
  · intro x_in_img
    rw [Finset.mem_image] at x_in_img
    rw [simplex_disjoint_mem]
    choose y y_in_u fy_eq_x using x_in_img
    revert fy_eq_x
    split_ifs
    intro y_one_x
    simp only [Prod.ext_iff, Prod.fst, Prod.snd] at y_one_x
    choose y_eq_x x_one using y_one_x
    rw [@comm _ Eq] at x_one
    rw [← st_eq_u, simplex_disjoint_mem] at y_in_u
    cases' y_in_u with y_in_s contra
    choose y_in_s y_zero using y_in_s
    rw [y_eq_x] at y_in_s
    right; constructor <;> assumption
    choose y_in_t contra using contra
    have H : y.snd ≠ 0 := by omega
    contradiction
    intro y_zero_x
    simp only [Prod.ext_iff, Prod.fst, Prod.snd] at y_zero_x
    choose y_eq_x x_zero using y_zero_x
    rw [@comm _ Eq] at x_zero
    rw [← st_eq_u, simplex_disjoint_mem] at y_in_u
    cases' y_in_u with contra y_in_t
    choose y_in_s contra using contra
    contradiction
    choose y_in_t y_one using y_in_t
    rw [y_eq_x] at y_in_t
    left; constructor <;> assumption

theorem simplicialJoin_comm (X Y : SimplicialComplex α) : X ⋆ Y ≅ Y ⋆ X :=
  by
  let f : SimplicialMap (X ⋆ Y) (Y ⋆ X) :=
    SimplicialMap.mk simplicialJoinCommMap (simplicialJoin_comm_simplicial X Y)
  let g : SimplicialMap (Y ⋆ X) (X ⋆ Y) :=
    SimplicialMap.mk simplicialJoinCommMap (simplicialJoin_comm_simplicial Y X)
  unfold IsSimpliciallyIso
  use f
  unfold IsSimplicialIso
  use g
  unfold IsInverseSimplicialIso
  constructor <;>
    · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
      intro x x_in_XY
      rw [simplicialJoin_mem_vertices] at x_in_XY
      simp only [f, g, SimplicialMap.comp, simplicialJoinCommMap, id.def, Function.comp_apply]
      cases' x_in_XY with x_in_X x_in_Y
      choose x_in_X x_zero using x_in_X
      simp only [x_zero, eq_self_iff_true, if_true, Nat.one_ne_zero, if_false]
      simp only [← x_zero, Prod.ext_iff, Prod.fst, Prod.snd]
      constructor <;> rfl
      choose x_in_Y x_one using x_in_Y
      simp only [x_one, eq_self_iff_true, if_true, Nat.one_ne_zero, if_false]
      simp only [← x_one, Prod.ext_iff, Prod.fst, Prod.snd]
      constructor <;> rfl

-- Make sense of natural projections, inclusions, etc.
def simplicialJoinIdForwardMap : α × ℕ → α := fun x : α × ℕ => x.fst

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem simplicialJoin_id_left_forward_simplicial (X : SimplicialComplex α) :
    IsSimplicialMap (X ⋆ emptySc) X simplicialJoinIdForwardMap :=
  by
  simp only [IsSimplicialMap, simplicialJoinIdForwardMap, emptySc]
  intro u u_in_X_empty
  rw [simplicialJoin_mem] at u_in_X_empty
  choose s s_in_X t t_in_empty st_eq_u using u_in_X_empty
  rw [Set.mem_singleton_iff] at t_in_empty
  simp only [t_in_empty, simplexDisjointUnion, Finset.empty_product, Finset.union_empty] at st_eq_u
  simp only [st_eq_u]
  have s_img : Finset.image Prod.fst (s ×ˢ {0}) = s :=
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
    simp only [Prod.fst]
  rw [s_img]
  assumption

def simplicialJoinIdLeftInverseMap : α → α × ℕ := fun x : α => (x, 0)

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem simplicialJoin_id_left_inverse_simplicial (X : SimplicialComplex α) :
    IsSimplicialMap X (X ⋆ emptySc) simplicialJoinIdLeftInverseMap :=
  by
  simp only [IsSimplicialMap]
  intro u u_in_X
  simp only [simplicialJoin, emptySc, Set.mem_setOf]
  use u; constructor; assumption
  use∅; constructor; apply simplicialComplex_empty_simplex
  have u_img : Finset.image simplicialJoinIdLeftInverseMap u = u ×ˢ {0} :=
    by
    simp only [simplicialJoinIdLeftInverseMap, Finset.ext_iff, Finset.mem_image, Finset.mem_product]
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
    constructor; rfl; assumption
  simp only [u_img, simplexDisjointUnion, Finset.empty_product, Finset.union_empty]

theorem simplicialJoin_id_left (X : SimplicialComplex α) : X ⋆ emptySc ≅ X :=
  by
  let f : SimplicialMap (X ⋆ emptySc) X :=
    SimplicialMap.mk simplicialJoinIdForwardMap (simplicialJoin_id_left_forward_simplicial X)
  let g : SimplicialMap X (X ⋆ emptySc) :=
    SimplicialMap.mk simplicialJoinIdLeftInverseMap (simplicialJoin_id_left_inverse_simplicial X)
  unfold IsSimpliciallyIso
  use f
  unfold IsSimplicialIso
  use g
  unfold IsInverseSimplicialIso
  constructor
  · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
    intro x x_in_X_empty
    rw [simplicialJoin_mem_vertices] at x_in_X_empty
    simp only [f, g, simplicialJoinIdForwardMap, simplicialJoinIdLeftInverseMap]
    simp only [SimplicialMap.comp, Function.comp_apply, id.def, Prod.ext_iff, Prod.fst, Prod.snd]
    cases' x_in_X_empty with x_in_X contra
    choose x_in_X x_zero using x_in_X
    rw [@comm _ Eq] at x_zero
    constructor
    rfl
    assumption
    choose contra x_one using contra
    rw [emptySc_vertices] at contra
    have H : x.fst ∉ ∅ := by apply Set.not_mem_empty x.fst
    contradiction
  · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
    intro x x_in_X
    simp only [f, g, simplicialJoinIdForwardMap, simplicialJoinIdLeftInverseMap]
    simp only [SimplicialMap.comp, Function.comp_apply, id.def]

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem simplicialJoin_id_right_forward_simplicial (X : SimplicialComplex α) :
    IsSimplicialMap (emptySc ⋆ X) X simplicialJoinIdForwardMap :=
  by
  simp only [IsSimplicialMap, simplicialJoinIdForwardMap, emptySc]
  intro u u_in_empty_X
  rw [simplicialJoin_mem] at u_in_empty_X
  choose s s_in_empty t t_in_X st_eq_u using u_in_empty_X
  rw [Set.mem_singleton_iff] at s_in_empty
  simp only [s_in_empty, simplexDisjointUnion, Finset.empty_product, Finset.empty_union] at st_eq_u
  simp only [st_eq_u]
  have t_img : Finset.image Prod.fst (t ×ˢ {1}) = t :=
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
    simp only [Prod.fst]
  rw [t_img]
  assumption

def simplicialJoinIdRightInverseMap : α → α × ℕ := fun x : α => (x, 1)

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem simplicialJoin_id_right_inverse_simplicial (X : SimplicialComplex α) :
    IsSimplicialMap X (emptySc ⋆ X) simplicialJoinIdRightInverseMap :=
  by
  simp only [IsSimplicialMap]
  intro u u_in_X
  simp only [simplicialJoin, emptySc, Set.mem_setOf]
  use∅; constructor; apply simplicialComplex_empty_simplex
  use u; constructor; assumption
  have u_img : Finset.image simplicialJoinIdRightInverseMap u = u ×ˢ {1} :=
    by
    simp only [simplicialJoinIdRightInverseMap, Finset.ext_iff, Finset.mem_image,
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
    constructor; rfl; assumption
  simp only [u_img, simplexDisjointUnion, Finset.empty_product, Finset.empty_union]

theorem simplicialJoin_id_right (X : SimplicialComplex α) : emptySc ⋆ X ≅ X :=
  by
  let f : SimplicialMap (emptySc ⋆ X) X :=
    SimplicialMap.mk simplicialJoinIdForwardMap (simplicialJoin_id_right_forward_simplicial X)
  let g : SimplicialMap X (emptySc ⋆ X) :=
    SimplicialMap.mk simplicialJoinIdRightInverseMap (simplicialJoin_id_right_inverse_simplicial X)
  unfold IsSimpliciallyIso
  use f
  unfold IsSimplicialIso
  use g
  unfold IsInverseSimplicialIso
  constructor
  · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
    intro x x_in_empty_X
    rw [simplicialJoin_mem_vertices] at x_in_empty_X
    simp only [f, g, simplicialJoinIdForwardMap, simplicialJoinIdRightInverseMap]
    simp only [SimplicialMap.comp, Function.comp_apply, id.def, Prod.ext_iff, Prod.fst, Prod.snd]
    cases' x_in_empty_X with contra x_in_X
    choose contra x_one using contra
    rw [emptySc_vertices] at contra
    have H : x.fst ∉ ∅ := by apply Set.not_mem_empty x.fst
    contradiction
    choose x_in_X x_zero using x_in_X
    rw [@comm _ Eq] at x_zero
    constructor
    rfl
    assumption
  · simp only [Set.restrict_eq_restrict_iff, Set.EqOn]
    intro x x_in_X
    simp only [f, g, simplicialJoinIdForwardMap, simplicialJoinIdRightInverseMap]
    simp only [SimplicialMap.comp, Function.comp_apply, id.def]

theorem simplicialJoin_natural_incl_left (X Y : SimplicialComplex α) (t : Finset α) :
    t ∈ Y.simplices ↔ X ⋆ simplex t ⊆ X ⋆ Y :=
  by
  simp only [simplicialJoin, IsSubcomplex, Set.subset_def, Set.mem_setOf]
  constructor
  -- t ∈ Y case.
  intro t_in_Y u u_in_join
  choose s s_in_X v v_in_Y sv_eq_u using u_in_join
  use s; constructor; assumption
  use v; constructor
  apply simplex_if_in_subcomplex (simplex t)
  assumption
  rw [← simplex_iff_subcomplex_mem]
  assumption
  assumption
  -- X ⋆ t ⊆ X ⋆ Y case.
  intro X_sub_Y
  specialize X_sub_Y (∅ ⊔ₛ t)
  have X_mem :
    ∃ (s : Finset α) (H : s ∈ X.simplices) (v : Finset α) (H : v ∈ (simplex t).simplices),
      s ⊔ₛ v = ∅ ⊔ₛ t :=
    by
    use∅; constructor; apply simplicialComplex_empty_simplex
    use t; constructor
    simp only [simplex, Finset.mem_coe]
    apply Finset.mem_powerset_self
    rfl
  specialize X_sub_Y X_mem
  choose s s_in_X v v_in_Y sv_eq_t using X_sub_Y
  rw [simplex_disjoint_eq_unique] at sv_eq_t
  choose s_empty v_eq_t using sv_eq_t
  subst v_eq_t
  assumption

theorem simplicialJoin_natural_incl_right (X Y : SimplicialComplex α) (s : Finset α) :
    s ∈ X.simplices ↔ simplex s ⋆ Y ⊆ X ⋆ Y :=
  by
  simp only [simplicialJoin, IsSubcomplex, Set.subset_def, Set.mem_setOf]
  constructor
  -- s ∈ X case.
  intro s_in_X u u_in_join
  choose t t_in_X v v_in_Y tv_eq_u using u_in_join
  use t; constructor
  apply simplex_if_in_subcomplex (simplex s)
  assumption
  rw [← simplex_iff_subcomplex_mem]
  assumption
  use v; constructor
  assumption
  assumption
  -- X ⋆ t ⊆ X ⋆ Y case.
  intro X_sub_Y
  specialize X_sub_Y (s ⊔ₛ ∅)
  have Y_mem :
    ∃ (t : Finset α) (H : t ∈ (simplex s).simplices) (v : Finset α) (H : v ∈ Y.simplices),
      t ⊔ₛ v = s ⊔ₛ ∅ :=
    by
    use s; constructor
    simp only [simplex, Finset.mem_coe]
    apply Finset.mem_powerset_self
    use∅; constructor; apply simplicialComplex_empty_simplex
    rfl
  specialize X_sub_Y Y_mem
  choose t t_in_X v v_in_Y tv_eq_s using X_sub_Y
  rw [simplex_disjoint_eq_unique] at tv_eq_s
  choose s_eq_t v_empty using tv_eq_s
  subst s_eq_t
  assumption

theorem simplicialJoin_subcomplex (X Y Z W : SimplicialComplex α) (X_subcomp_Z : X ⊆ Z)
    (Y_subcomp_W : Y ⊆ W) : X ⋆ Y ⊆ Z ⋆ W :=
  by
  simp only [SimplicialComplex.hasSubset, IsSubcomplex] at *
  simp only [simplicialJoin, SimplicialComplex.simplices]
  simp only [Set.subset_def] at *
  intro s s_in_XY
  simp only [Set.mem_setOf] at *
  choose t Ht u Hu tu_eq_s using s_in_XY
  specialize X_subcomp_Z t Ht
  specialize Y_subcomp_W u Hu
  use t; constructor; apply X_subcomp_Z
  use u; constructor; apply Y_subcomp_W
  apply tu_eq_s

theorem simplicialJoin_distr_union_left (X Y Z : SimplicialComplex α) :
    (X ⋆ (Y ∪ Z)).simplices = (X ⋆ Y ∪ X ⋆ Z).simplices :=
  by
  simp only [simplicialJoin, simplicialUnion, Set.ext_iff, Set.mem_union, Set.mem_setOf]
  intro u
  constructor
  · intro u_in_join
    choose s s_in_X t t_in_YZ st_eq_u using u_in_join
    cases' t_in_YZ with t_in_Y t_in_Z
    left
    use s; constructor; assumption
    use t; constructor; assumption
    assumption
    right
    use s; constructor; assumption
    use t; constructor; assumption
    assumption
  · intro u_in_union
    cases' u_in_union with u_in_XY u_in_XZ
    choose s s_in_X t t_in_Y st_eq_u using u_in_XY
    use s; constructor; assumption
    use t; constructor
    left; assumption
    assumption
    choose s s_in_X t t_in_Z st_eq_u using u_in_XZ
    use s; constructor; assumption
    use t; constructor
    right; assumption
    assumption

theorem simplicialJoin_distr_union_left_iso (X Y Z : SimplicialComplex α) :
    X ⋆ (Y ∪ Z) ≅ X ⋆ Y ∪ X ⋆ Z :=
  by
  apply simplicial_iso_preserves_equiv
  apply simplicialJoin_distr_union_left

theorem simplicialJoin_distr_union_right (X Y Z : SimplicialComplex α) :
    ((Y ∪ Z) ⋆ X).simplices = (Y ⋆ X ∪ Z ⋆ X).simplices :=
  by
  simp only [simplicialJoin, simplicialUnion, Set.ext_iff, Set.mem_union, Set.mem_setOf]
  intro u
  constructor
  · intro u_in_join
    choose s s_in_YZ t t_in_X st_eq_u using u_in_join
    cases' s_in_YZ with s_in_Y s_in_Z
    left
    use s; constructor; assumption
    use t; constructor; assumption
    assumption
    right
    use s; constructor; assumption
    use t; constructor; assumption
    assumption
  · intro u_in_union
    cases' u_in_union with u_in_XY u_in_XZ
    choose s s_in_X t t_in_Y st_eq_u using u_in_XY
    use s; constructor
    left; assumption
    use t; constructor; assumption
    assumption
    choose s s_in_X t t_in_Z st_eq_u using u_in_XZ
    use s; constructor
    right; assumption
    use t; constructor; assumption
    assumption

theorem simplicialJoin_distr_union_right_iso (X Y Z : SimplicialComplex α) :
    (Y ∪ Z) ⋆ X ≅ Y ⋆ X ∪ Z ⋆ X :=
  by
  apply simplicial_iso_preserves_equiv
  apply simplicialJoin_distr_union_right

-- Lemma 2.1, p.5
theorem dim_of_join (X Y : SimplicialComplex α) [Fintype X.simplices] [Fintype Y.simplices] :
    dimOfComplex (X ⋆ Y) = dimOfComplex X + dimOfComplex Y + 1 :=
  by
  intros
  set k := dimOfComplex (X ⋆ Y)
  set n := dimOfComplex X
  set m := dimOfComplex Y
  rw [le_antisymm_iff]
  constructor
  · have k_dim : k ∈ Finset.image dim (X ⋆ Y).simplices.toFinset := by apply Finset.max'_mem
    simp only [Finset.mem_image, Set.mem_toFinset] at k_dim
    choose u u_in_XY dim_u_k using k_dim
    rw [simplicialJoin_mem] at u_in_XY
    choose s s_in_X t t_in_Y u_eq_st using u_in_XY
    rw [← dim_u_k, dim, u_eq_st, simplex_disjoint_card]
    have st_dim : ↑(s.card + t.card) - 1 = dim s + dim t + 1 := by simp; linarith
    rw [st_dim]
    have s_le_dim : dim s ≤ dimOfComplex X :=
      by
      apply Finset.le_max'
      simp only [Finset.mem_image, Set.mem_toFinset]
      use s; constructor; assumption
      rfl
    have t_le_dim : dim t ≤ dimOfComplex Y :=
      by
      apply Finset.le_max'
      simp only [Finset.mem_image, Set.mem_toFinset]
      use t; constructor; assumption
      rfl
    linarith
  · have n_dim : n ∈ Finset.image dim X.simplices.to_finset := by apply Finset.max'_mem
    have m_dim : m ∈ Finset.image dim Y.simplices.to_finset := by apply Finset.max'_mem
    simp only [Finset.mem_image, Set.mem_toFinset] at n_dim m_dim
    choose s s_in_X dim_s_n using n_dim
    choose t t_in_Y dim_t_m using m_dim
    have st_dim : ↑(s.card + t.card) - 1 = dim s + dim t + 1 := by simp; linarith
    simp only [← dim_s_n, ← dim_t_m, ← st_dim, ← simplex_disjoint_card]
    apply Finset.le_max'
    simp only [Finset.mem_image, Set.mem_toFinset]
    use s ⊔ₛ t; constructor
    rw [simplicialJoin_mem]
    use s; constructor; assumption
    use t; constructor; assumption
    rfl
    unfold dim

-- Show that, for disjoint complexes, projection to the first coordinate is a coercion.
theorem join_fst_proj_is_coe (X Y : SimplicialComplex α) :
    Disjoint (vertices X) (vertices Y) → Set.InjOn Prod.fst (vertices (X ⋆ Y)) :=
  by
  intro X_disj_Y
  simp only [Set.InjOn, vertices_setOf, simplicialJoin, Set.mem_setOf]
  simp only [vertices_setOf, Set.disjoint_iff_forall_ne, Set.mem_setOf] at X_disj_Y
  intro x₁ x₁_in_lhs x₂ x₂_in_rhs
  choose s₁ s₁_in_join x₁_in_s₁ using x₁_in_lhs
  choose u₁ u₁_in_X v₁ v₁_in_Y uv₁_eq_s₁ using s₁_in_join
  rw [← uv₁_eq_s₁, simplex_disjoint_mem] at x₁_in_s₁
  choose s₂ s₂_in_join x₂_in_s₂ using x₂_in_rhs
  choose u₂ u₂_in_X v₂ v₂_in_Y uv₂_eq_s₂ using s₂_in_join
  rw [← uv₂_eq_s₂, simplex_disjoint_mem] at x₂_in_s₂
  cases' x₁_in_s₁ with x₁_in_X x₁_in_Y <;> cases' x₂_in_s₂ with x₂_in_X x₂_in_Y
  -- x₁, x₂ ∈ X case.
  intro x₁_eq_x₂
  choose x₁_in_u₁ x₁_zero using x₁_in_X
  choose x₂_in_u₂ x₂_zero using x₂_in_X
  rw [← x₂_zero] at x₁_zero
  rw [Prod.ext_iff]
  constructor <;> assumption
  -- x₁ ∈ X, x₂ ∈ Y case.
  contrapose
  intro x₁_neq_x₂
  choose x₁_in_u₁ x₁_zero using x₁_in_X
  choose x₂_in_v₂ x₂_one using x₂_in_Y
  have H₁ : ∃ (s : Finset α) (H : s ∈ X.simplices), x₁.fst ∈ s := by use u₁;
    constructor <;> assumption
  specialize X_disj_Y x₁.fst H₁
  have H₂ : ∃ (s : Finset α) (H : s ∈ Y.simplices), x₂.fst ∈ s := by use v₂;
    constructor <;> assumption
  specialize X_disj_Y x₂.fst H₂
  assumption
  -- x₁ ∈ Y, x₂ ∈ X case.
  contrapose
  intro x₁_neq_x₂
  choose x₁_in_v₁ x₁_one using x₁_in_Y
  choose x₂_in_u₂ x₂_zero using x₂_in_X
  have H₂ : ∃ (s : Finset α) (H : s ∈ X.simplices), x₂.fst ∈ s := by use u₂;
    constructor <;> assumption
  specialize X_disj_Y x₂.fst H₂
  have H₁ : ∃ (s : Finset α) (H : s ∈ Y.simplices), x₁.fst ∈ s := by use v₁;
    constructor <;> assumption
  specialize X_disj_Y x₁.fst H₁
  rw [← Ne.def, ne_comm]
  assumption
  -- x₁, x₂ ∈ Y case.
  intro x₁_eq_x₂
  choose x₁_in_v₁ x₁_one using x₁_in_Y
  choose x₂_in_v₂ x₂_one using x₂_in_Y
  rw [← x₂_one] at x₁_one
  rw [Prod.ext_iff]
  constructor <;> assumption

def joinFst {X Y : SimplicialComplex α} (H : Disjoint (vertices X) (vertices Y)) :
    SimplicialCoe (X ⋆ Y) α :=
  SimplicialCoe.mk Prod.fst (join_fst_proj_is_coe X Y H)

notation "π₁" => joinFst

theorem join_proj_vertices_mem (X Y : SimplicialComplex α) (x : α)
    (H : Disjoint (vertices X) (vertices Y)) :
    x ∈ vertices (π₁ H[X ⋆ Y]) ↔ x ∈ vertices X ∨ x ∈ vertices Y :=
  by
  simp only [vertices_setOf, simplicialImage, simplicialJoin, Set.mem_setOf, joinFst]
  constructor
  -- x ∈ X ⋆ Y case.
  intro x_in_join
  choose u u_in_img x_in_u using x_in_join
  choose v v_in_join proj_v_u using u_in_img
  choose s s_in_X t t_in_Y st_eq_v using v_in_join
  rw [← proj_v_u, Finset.mem_image] at x_in_u
  choose y y_in_v proj_y_x using x_in_u
  rw [← st_eq_v, simplex_disjoint_mem] at y_in_v
  cases' y_in_v with y_in_X y_in_Y
  left
  choose y_in_s y_zero using y_in_X
  subst proj_y_x
  use s; constructor <;> assumption
  right
  choose y_in_t y_one using y_in_Y
  subst proj_y_x
  use t; constructor <;> assumption
  -- x ∈ X ∪ Y case.
  intro x_in_union
  cases' x_in_union with x_in_X x_in_Y
  -- x ∈ X subcase.
  choose s s_in_X x_in_s using x_in_X
  use s; constructor
  use s ⊔ₛ ∅; constructor
  use s; constructor; assumption
  use∅; constructor; apply simplicialComplex_empty_simplex
  rfl
  simp only [simplexDisjointUnion, Finset.image_union, Finset.empty_product, Finset.image_empty,
    Finset.union_empty]
  simp only [Finset.ext_iff, Finset.mem_image]
  intro a
  constructor
  intro a_in_img
  choose b b_in_prod proj_b_a using a_in_img
  simp only [Finset.mem_product] at b_in_prod
  choose b_in_s b_zero using b_in_prod
  subst proj_b_a
  assumption
  intro a_in_s
  use(a, 0); constructor
  simp only [Finset.mem_product, Prod.fst, Prod.snd, Finset.mem_singleton]
  constructor; assumption; rfl
  simp only [Prod.fst]
  assumption
  -- x ∈ Y subcase.
  choose t t_in_Y x_in_t using x_in_Y
  use t; constructor
  use∅ ⊔ₛ t; constructor
  use∅; constructor; apply simplicialComplex_empty_simplex
  use t; constructor; assumption
  rfl
  simp only [simplexDisjointUnion, Finset.image_union, Finset.empty_product, Finset.image_empty,
    Finset.empty_union]
  simp only [Finset.ext_iff, Finset.mem_image]
  intro a
  constructor
  intro a_in_img
  choose b b_in_prod proj_b_a using a_in_img
  simp only [Finset.mem_product] at b_in_prod
  choose b_in_s b_one using b_in_prod
  subst proj_b_a
  assumption
  intro a_in_s
  use(a, 1); constructor
  simp only [Finset.mem_product, Prod.fst, Prod.snd, Finset.mem_singleton]
  constructor; assumption; rfl
  simp only [Prod.fst]
  assumption

theorem simplexDisjointUnion_prod_fst (s t : Finset α) : Finset.image Prod.fst (s ⊔ₛ t) = s ∪ t :=
  by
  simp only [simplexDisjointUnion, Finset.image_union, Finset.ext_iff, Finset.mem_image,
    Finset.mem_union]
  intro x
  constructor
  intro x_in_img
  cases' x_in_img with x_in_s x_in_t
  left
  choose y y_in_prod proj_y_x using x_in_s
  simp only [Finset.mem_product] at y_in_prod
  choose y_in_s y_zero using y_in_prod
  subst proj_y_x
  assumption
  right
  choose y y_in_prod proj_y_x using x_in_t
  simp only [Finset.mem_product] at y_in_prod
  choose y_in_t y_one using y_in_prod
  subst proj_y_x
  assumption
  intro x_in_st
  cases' x_in_st with x_in_s x_in_t
  left
  use(x, 0); constructor
  simp only [Finset.mem_product]
  constructor
  assumption
  apply Finset.mem_singleton_self
  simp only [Prod.fst]
  right
  use(x, 1); constructor
  simp only [Finset.mem_product]
  constructor
  assumption
  apply Finset.mem_singleton_self
  simp only [Prod.fst]

theorem join_proj_mem (X Y : SimplicialComplex α) (s : Finset α)
    (H : Disjoint (vertices X) (vertices Y)) :
    s ∈ π₁ H[X ⋆ Y].simplices ↔ ∃ t ∈ X.simplices, ∃ u ∈ Y.simplices, s = t ∪ u :=
  by
  simp only [simplicialImage, simplicialJoin, joinFst, Set.mem_setOf]
  constructor
  -- s ∈ X ⋆ Y case.
  intro s_in_join
  choose v v_in_join proj_v_s using s_in_join
  choose t t_in_X u u_in_Y tu_eq_v using v_in_join
  rw [← tu_eq_v, simplexDisjointUnion_prod_fst] at proj_v_s
  use t; constructor; assumption
  use u; constructor; assumption
  symm
  assumption
  -- s X ∪ Y case.
  intro x_decomp
  choose t t_in_X u u_in_Y s_eq_tu using x_decomp
  rw [← simplexDisjointUnion_prod_fst] at s_eq_tu
  use t ⊔ₛ u; constructor
  use t; constructor; assumption
  use u; constructor; assumption
  rfl
  symm
  assumption

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (s₁ t₁ «expr ∈ » X.simplices) -/
/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (s₂ t₂ «expr ∈ » Y.simplices) -/
theorem join_proj_disj_union_mem (X Y : SimplicialComplex α) (s t : Finset α)
    (H : Disjoint (vertices X) (vertices Y)) :
    s ∪ t ∈ π₁ H[X ⋆ Y].simplices ↔
      ∃ (s₁ : _) (_ : s₁ ∈ X.simplices) (t₁ : _) (_ : t₁ ∈ X.simplices) (s₂ : _) (_ :
        s₂ ∈ Y.simplices) (t₂ : _) (_ : t₂ ∈ Y.simplices),
        s = s₁ ∪ s₂ ∧ t = t₁ ∪ t₂ ∧ s₁ ∪ t₁ ∈ X.simplices ∧ s₂ ∪ t₂ ∈ Y.simplices :=
  by
  rw [join_proj_mem]
  constructor
  -- s ∪ t ∈ X ⋆ Y case.
  intro st_in_join
  choose u u_in_X v v_in_X st_eq_uv using st_in_join
  use s ∩ u; constructor
  apply X.subset_closed u
  assumption
  apply Finset.inter_subset_right
  use t ∩ u; constructor
  apply X.subset_closed u
  assumption
  apply Finset.inter_subset_right
  use s ∩ v; constructor
  apply Y.subset_closed v
  assumption
  apply Finset.inter_subset_right
  use t ∩ v; constructor
  apply Y.subset_closed v
  assumption
  apply Finset.inter_subset_right
  constructor
  rw [← Finset.inter_union_distrib_left, ← st_eq_uv, Finset.union_comm, Finset.inter_union_self]
  constructor
  rw [← Finset.inter_union_distrib_left, ← st_eq_uv, Finset.inter_union_self]
  constructor
  rw [← Finset.union_inter_distrib_right, st_eq_uv, Finset.inter_comm, Finset.union_comm,
    Finset.inter_union_self]
  assumption
  rw [← Finset.union_inter_distrib_right, st_eq_uv, Finset.inter_comm, Finset.inter_union_self]
  assumption
  -- s ∪ t decomp case.
  intro st_decomp
  choose s₁ s₁_in_X t₁ t₁_in_X s₂ s₂_in_Y t₂ t₂_in_Y st_decomp using st_decomp
  choose s_decomp t_decomp st₁_in_X st₂_in_Y using st_decomp
  use s₁ ∪ t₁; constructor; assumption
  use s₂ ∪ t₂; constructor; assumption
  rw [Finset.union_comm s₂, Finset.union_assoc, ← Finset.union_assoc t₁,
    Finset.union_comm (t₁ ∪ t₂), ← Finset.union_assoc]
  rw [← s_decomp, ← t_decomp]

-- General result on existence of coercion for complexes over ℕ
@[simp]
def finiteNatComplexBound (X : SimplicialComplex ℕ) [Fintype X.simplices] : ℕ :=
  (vertices X ∪ {(0 : ℕ)}).toFinset.max'
    (by
      rw [Set.toFinset_nonempty, Set.union_nonempty]
      right
      apply Set.singleton_nonempty)

theorem finiteNatComplexBound_ne (X : SimplicialComplex ℕ) [Fintype X.simplices]
    [X_ne : (vertices X).toFinset.Nonempty] :
    finiteNatComplexBound X = (vertices X).toFinset.max' X_ne :=
  by
  simp only [finiteNatComplexBound, le_antisymm_iff]
  constructor
  rw [Finset.max'_le_iff]
  intro y y_in_X
  rw [Set.mem_toFinset, Set.mem_union, Set.mem_singleton_iff, ← Set.mem_toFinset] at y_in_X
  cases' y_in_X with y_in_X y_zero
  apply Finset.le_max'
  assumption
  rw [y_zero]
  apply zero_le
  rw [Finset.max'_le_iff]
  intro y y_in_X
  apply Finset.le_max'
  rw [Set.mem_toFinset, Set.mem_union, Set.mem_singleton_iff, ← Set.mem_toFinset]
  left; assumption

def joinNatProjMap (X Y : SimplicialComplex ℕ) [Fintype X.simplices] : ℕ × ℕ → ℕ := fun x : ℕ × ℕ =>
  if x.snd = 0 then x.fst else x.fst + finiteNatComplexBound X + 1

theorem join_nat_proj_is_coe (X Y : SimplicialComplex ℕ) [Fintype X.simplices] :
    Set.InjOn (joinNatProjMap X Y) (vertices (X ⋆ Y)) :=
  by
  simp only [Set.InjOn, simplicialJoin_mem_vertices, joinNatProjMap]
  simp only [Set.mem_setOf, simplicialJoin_mem, ite_eq_iff]
  intro x₁ x₁_in_join x₂ x₂_in_join x₁_eq_x₂
  cases' x₁_in_join with x₁_in_X x₁_in_Y <;> cases' x₂_in_join with x₂_in_X x₂_in_Y
  -- x₁, x₂ ∈ X case.
  choose x₁_in_X x₁_zero using x₁_in_X
  choose x₂_in_X x₂_zero using x₂_in_X
  cases' x₁_eq_x₂ with x₁_eq_x₂ contra
  choose x₁_zero x₁_eq_x₂ using x₁_eq_x₂
  rw [@comm _ Eq, ite_eq_iff] at x₁_eq_x₂
  cases' x₁_eq_x₂ with x₁_eq_x₂ contra
  choose x₂_zero x₁_eq_x₂ using x₁_eq_x₂
  rw [Prod.ext_iff]
  constructor
  symm
  assumption
  rw [← x₂_zero] at x₁_zero
  assumption
  choose contra H using contra
  contradiction
  choose contra H using contra
  contradiction
  -- x₁ ∈ X, x₂ ∈ Y case.
  choose x₁_in_X x₁_zero using x₁_in_X
  choose x₂_in_Y x₂_one using x₂_in_Y
  cases' x₁_eq_x₂ with x₁_eq_x₂ contra
  choose x₁_zero x₁_eq_x₂ using x₁_eq_x₂
  rw [@comm _ Eq, ite_eq_iff] at x₁_eq_x₂
  cases' x₁_eq_x₂ with contra x₁_eq_x₂
  choose contra H using contra
  have x₂_nonzero : x₂.snd ≠ 0 := by omega
  contradiction
  choose x₂_nonzero x₁_eq_x₂ using x₁_eq_x₂
  have x₁_le_bound : x₁.fst ≤ finiteNatComplexBound X :=
    by
    by_cases X_ne : vertices X = ∅
    rw [X_ne] at x₁_in_X
    have contra : x₁.fst ∉ ∅ := by apply Set.not_mem_empty
    contradiction
    rw [← Ne.def, ← Set.nonempty_iff_ne_empty, ← Set.toFinset_nonempty] at X_ne
    rw [@finiteNatComplexBound_ne X _ X_ne]
    apply Finset.le_max'
    rw [Set.mem_toFinset]
    assumption
  have x₁_lt_x₂_bound : x₁.fst < x₂.fst + finiteNatComplexBound X + 1 := by omega
  have contra : x₂.fst + finiteNatComplexBound X + 1 ≠ x₁.fst := ne_of_gt x₁_lt_x₂_bound
  contradiction
  choose contra H using contra
  contradiction
  -- x₁ ∈ Y, x₂ ∈ X case.
  choose x₁_in_Y x₁_one using x₁_in_Y
  choose x₂_in_X x₂_zero using x₂_in_X
  cases' x₁_eq_x₂ with contra x₁_eq_x₂
  choose contra H using contra
  have x₁_nonzero : x₁.snd ≠ 0 := by omega
  contradiction
  choose x₁_zero x₁_eq_x₂ using x₁_eq_x₂
  rw [@comm _ Eq, ite_eq_iff] at x₁_eq_x₂
  cases' x₁_eq_x₂ with x₁_eq_x₂ contra
  choose x₂_nonzero x₁_eq_x₂ using x₁_eq_x₂
  have x₂_le_bound : x₂.fst ≤ finiteNatComplexBound X :=
    by
    simp only [finiteNatComplexBound]
    apply Finset.le_max'
    rw [Set.mem_toFinset, Set.mem_union]
    left; assumption
  have x₂_lt_x₁_bound : x₂.fst < x₁.fst + finiteNatComplexBound X + 1 := by omega
  have contra : x₂.fst ≠ x₁.fst + finiteNatComplexBound X + 1 := ne_of_lt x₂_lt_x₁_bound
  contradiction
  choose contra H using contra
  have x₂_nonzero : x₂.snd ≠ 0 := by omega
  contradiction
  -- x₁, x₂ ∈ Y case.
  choose x₁_in_Y x₁_one using x₁_in_Y
  choose x₂_in_Y x₂_one using x₂_in_Y
  cases' x₁_eq_x₂ with contra x₁_eq_x₂
  choose contra H using contra
  have x₁_nonzero : x₁.snd ≠ 0 := by omega
  contradiction
  choose x₁_nonzero x₁_eq_x₂ using x₁_eq_x₂
  rw [@comm _ Eq, ite_eq_iff] at x₁_eq_x₂
  cases' x₁_eq_x₂ with contra x₁_eq_x₂
  choose contra H using contra
  have x₂_nonzero : x₂.snd ≠ 0 := by omega
  contradiction
  choose x₂_nonzero x₁_eq_x₂ using x₁_eq_x₂
  have x₁_fst_eq_x₂_fst : x₁.fst = x₂.fst :=
    by
    rw [Nat.add_assoc, Nat.add_assoc] at x₁_eq_x₂
    symm
    apply Nat.add_right_cancel x₁_eq_x₂
  rw [← x₂_one] at x₁_one
  rw [Prod.ext_iff]
  constructor <;> assumption

def joinNatProj (X Y : SimplicialComplex ℕ) [Fintype X.simplices] : SimplicialCoe (X ⋆ Y) ℕ :=
  SimplicialCoe.mk (joinNatProjMap X Y) (join_nat_proj_is_coe X Y)

notation "ν⟨" X ", " Y "⟩" => joinNatProj X Y

end Join
