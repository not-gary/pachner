import Pachner.Basic.AbstractSimplicialComplex
import Pachner.Subcomplex.Union

variable
  {E F G : Type _}
  [DecidableEq F] [DecidableEq G]
  {X : AbstractSimplicialComplex E} {Y : AbstractSimplicialComplex F} {Z : AbstractSimplicialComplex G}

section SimplicialMap

variable
  {Y : AbstractSimplicialComplex E} {Z : AbstractSimplicialComplex F}
  {f : E → F}

@[simp]
def IsSimplicialMap
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (f : E → F) :=
  ∀ s, s ∈ X.faces → Finset.image f s ∈ Y.faces

structure SimplicialMap
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
  where mk ::
    map : E → F
    is_simplicial : IsSimplicialMap X Y map

theorem simplicialMap_restrict_is_simplicial
    (X Y : AbstractSimplicialComplex E)
    (Z : AbstractSimplicialComplex F)
    (f : SimplicialMap X Z)
  : Y ⊆ X → IsSimplicialMap Y Z f.map :=
by
  simp only [IsSimplicialMap, IsSubcomplex]
  intro Y_sub_X s s_in_Y
  simp only [AbstractSimplicialComplex.instHasSubset, IsSubcomplex, Set.subset_def] at Y_sub_X
  specialize Y_sub_X s s_in_Y
  apply f.is_simplicial
  assumption

def SimplicialMap.restrict
    (f : SimplicialMap X Z)
    (Y_sub_X : Y ⊆ X)
  : SimplicialMap Y Z :=
    SimplicialMap.mk f.map (simplicialMap_restrict_is_simplicial X Y Z f Y_sub_X)

def SimplicialMapLift
    (f : SimplicialMap X Z)
  : Finset E → Finset F :=
    fun s : Finset E => Finset.image f.map s

def SimplicialImage
    (f : E → F)
    (X : AbstractSimplicialComplex E)
  : AbstractSimplicialComplex F :=
    AbstractSimplicialComplex.mk
      ((Finset.image f) '' X.faces)
      (by
        simp only [Set.mem_image, X.empty_notMem]
        simp only [Finset.image_eq_empty, not_exists, not_and, ← ne_eq]
        intro s
        exact face_nonempty
        )
      (by
        intros s t s_in_img t_sset_s t_ne
        simp only [Set.mem_image] at ⊢ s_in_img
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
infixl:80 " ''ˢ " => SimplicialImage

theorem simplicialImage_congr (f g : E → F) : Set.EqOn f g X.vertices → (f ''ˢ X) = (g ''ˢ X) := by
  simp only [AbstractSimplicialComplex.ext_iff, Set.ext_iff, SimplicialImage, Set.mem_setOf]
  intro f_eq_g t
  constructor
  · intro s_in_fX
    choose s s_in_X fs_t using s_in_fX
    use s; constructor; assumption
    simp only [← fs_t, ← Finset.coe_inj, Finset.coe_image]
    apply Set.EqOn.image_eq
    apply Set.EqOn.symm
    apply @Set.EqOn.mono _ _ _ X.vertices
    apply face_subset_vertices
    assumption
    assumption
  · intro s_in_fX
    choose s s_in_X fs_t using s_in_fX
    use s; constructor; assumption
    simp only [← fs_t, ← Finset.coe_inj, Finset.coe_image]
    apply Set.EqOn.image_eq
    apply @Set.EqOn.mono _ _ _ X.vertices
    apply face_subset_vertices
    assumption
    assumption

theorem simplicialImage_comp
    (f : E → F)
    (g : F → G)
  : (g ∘ f) ''ˢ X = g ''ˢ (f ''ˢ X) :=
by
  simp only [AbstractSimplicialComplex.ext_iff, SimplicialImage, Set.ext_iff]
  intro z
  simp only [Set.mem_setOf, ← Finset.image_image]
  constructor
  · intro H
    choose s s_in_X z_eq_gfs using H
    use Finset.image f s
    exact ⟨by use s; , z_eq_gfs⟩ --TODO: weird syntax?
  · intro H
    choose s s_in_f gs_eq_z using H
    choose t t_in_X ft_eq_s using s_in_f
    use t
    simp only [ft_eq_s, gs_eq_z, eq_self, and_true, t_in_X]

theorem isSimplicialMap_onto_image
    (X : AbstractSimplicialComplex E)
    (f : E → F)
  : IsSimplicialMap X (f ''ˢ X) f :=
by
  unfold IsSimplicialMap
  intro s s_in_X
  simp only [SimplicialImage, Set.mem_setOf]
  use s

def SimplicialMap.ontoImage
    (f : SimplicialMap X Z)
  : SimplicialMap X (f.map ''ˢ X) :=
    SimplicialMap.mk f.map (isSimplicialMap_onto_image X f.map)

theorem simplicialImage_vertices : (f ''ˢ X).vertices = f '' X.vertices := by
  simp only [vertices_setOf, SimplicialImage, Set.image, Set.ext_iff, Set.mem_setOf]
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
  SimplicialMap.mk f (isSimplicialMap_onto_image X f)

theorem simplicialImage_is_lift_image : (f ''ˢ X).faces = SimplicialMapLift ⟨f, X⟩ '' X.faces := by
  simp only [SimplicialImage, SimplicialMapLift, Set.ext_iff, Set.mem_setOf, Set.mem_image,
    forall_true_iff]

theorem simplicialImage_union : (f ''ˢ (X ∪ Y)) = (f ''ˢ X) ∪ (f ''ˢ Y) := by
  simp only [AbstractSimplicialComplex.ext_iff, AbstractSimplicialComplex.instHasUnion, SimplicialUnion,
  simplicialImage_is_lift_image, SimplicialMapLift, Set.image_union]

end SimplicialMap

section SimplicialMap.vertices

variable {x : E} {f : SimplicialMap X Y}

theorem simplicialMap_on_vertices
    (f : SimplicialMap X Y)
    (x_in_X : x ∈ X.vertices)
  : f.map x ∈ Y.vertices :=
by
  rw [AbstractSimplicialComplex.mem_vertices, ← Finset.image_singleton]
  apply f.is_simplicial
  simp only [← AbstractSimplicialComplex.mem_vertices, x_in_X]

theorem simplicialMapLift_bij_imp_vertices_bij
  : Set.BijOn (SimplicialMapLift f) X.faces Y.faces → Set.BijOn f.map X.vertices Y.vertices :=
by
  simp only [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn, SimplicialMapLift, vertices_setOf]
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
  rw [← vertex_iff_in_face, AbstractSimplicialComplex.mem_vertices] at x₁_in_X x₂_in_X
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

theorem vertices_bij_imp_simplicialMapLift_mapsTo
  : Set.BijOn f.map X.vertices Y.vertices → Set.MapsTo (SimplicialMapLift f) X.faces Y.faces :=
by
  simp only [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn, SimplicialMapLift, vertices_setOf]
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

theorem vertices_bij_imp_simplicialMapLift_inj
  : Set.BijOn f.map X.vertices Y.vertices → Set.InjOn (SimplicialMapLift f) X.faces :=
by
  simp only [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn, SimplicialMapLift, vertices_setOf]
  intro img_bij
  choose img_range img_inj img_surj using img_bij
  intro s₁ s₁_in_X s₂ s₂_in_X fs₁_eq_fs₂
  simp only [Finset.ext_iff] at fs₁_eq_fs₂ ⊢
  have s₁_ss_vert : ↑s₁ ⊆ X.vertices := by apply face_subset_vertices s₁_in_X
  have s₂_ss_vert : ↑s₂ ⊆ X.vertices := by apply face_subset_vertices s₂_in_X
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

section SimplicialMap.Dimension

theorem simplicialMap_dim_mono
    (f : SimplicialMap X Y)
    (s : Finset E)
  : face_dim (Finset.image f.map s) ≤ face_dim s :=
by
  calc
    face_dim (Finset.image f.map s) = Finset.card (Finset.image f.map s) - 1 := by simp only [face_dim]
    _ ≤ Finset.card s - 1 := by simp [Finset.card_image_le]
    _ ≤ face_dim s := by simp only [face_dim, le_refl]

end SimplicialMap.Dimension

section SimplicialMap.Examples

theorem id_isSimplicialMap [DecidableEq E]
  : IsSimplicialMap X X id :=
by
  simp only [IsSimplicialMap, Finset.image_id, imp_self, implies_true]

def idSimplicialMap [DecidableEq E]
    (X : AbstractSimplicialComplex E)
  : SimplicialMap X X :=
    SimplicialMap.mk id (id_isSimplicialMap)

theorem const_is_simplicial
    (y_0 : F)
    (y0_vertex : y_0 ∈ Y.vertices)
  : IsSimplicialMap X Y (fun _ : E => y_0) :=
by
  intro s s_in_X
  rw [Finset.image_const, ← AbstractSimplicialComplex.mem_vertices]
  exact y0_vertex
  rw [Finset.nonempty_iff_ne_empty]
  exact face_nonempty s_in_X

def constSimplicialMap
    (X : AbstractSimplicialComplex E)
    (Y : AbstractSimplicialComplex F)
    (y_0 : F)
    (y0_vertex : y_0 ∈ Y.vertices)
  : SimplicialMap X Y :=
    SimplicialMap.mk (fun _ : E => y_0) (const_is_simplicial y_0 y0_vertex)

theorem isSimplicial_comp
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
  have gfs_in_SZ : Finset.image g t ∈ Z.faces := by apply g_simpl t; apply t_in_SY
  show Finset.image (g ∘ f) s ∈ Z.faces
  rw [Finset.image_image.symm]
  assumption

def SimplicialMap.comp
    (f : SimplicialMap X Y)
    (g : SimplicialMap Y Z)
  : SimplicialMap X Z :=
    SimplicialMap.mk (g.map ∘ f.map) (isSimplicial_comp f.map f.is_simplicial g.map g.is_simplicial)

end SimplicialMap.Examples
