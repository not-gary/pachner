import Pachner.Maps.SimplicialIsomorphism

/-
# Simplicial Coercions
-/
section Coercion

variable {E F G : Type _}
variable [DecidableEq E] [F_dec : DecidableEq F] [DecidableEq G]

-- Define as coercion on types that lifts to simplicial map.
structure SimplicialCoe
    (X : AbstractSimplicialComplex E)
    (F : Type _)
  where mk ::
    coe : E → F
    Injective : Set.InjOn coe (X.vertices)

def SimplicialCoe.simplicialMap
    {X : AbstractSimplicialComplex E}
    (φ : SimplicialCoe X F)
  : SimplicialMap X (φ.coe ''ˢ X) :=
    SimplicialMap.mk φ.coe (map_is_simplicial_onto_image X φ.coe)

instance SimplicialCoe.Fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (φ : SimplicialCoe X F)
  : Fintype (φ.coe ''ˢ X).faces :=
by
  rw [simplicialImage_is_lift_image]
  apply Set.fintypeImage

theorem simplicialCoe_inv_is_simplicial [Nonempty E]
    {X : AbstractSimplicialComplex E}
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
    {X : AbstractSimplicialComplex E}
    (φ : SimplicialCoe X F)
  : SimplicialMap (φ.coe ''ˢ X) X :=
    SimplicialMap.mk (Function.invFunOn φ.coe X.vertices) (simplicialCoe_inv_is_simplicial φ)

notation φ "⁻ᶜ" => simplicialCoeInv φ

theorem coe_inv_isInverseSimplicialIso [Nonempty E]
    {X : AbstractSimplicialComplex E}
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
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
  : IsSimplicialIso
      (@SimplicialMap.mk E F _ X (φ.coe ''ˢ X) φ.coe (by apply map_is_simplicial_onto_image)) :=
by
  unfold IsSimplicialIso
  use @simplicialCoeInv _ _ _ _ _ X φ
  apply coe_inv_isInverseSimplicialIso

theorem simplicialCoeInv_inj [Nonempty E]
    {X : AbstractSimplicialComplex E}
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
    {X : AbstractSimplicialComplex E}
    (φ : SimplicialCoe X F)
  : X ≅ φ.coe ''ˢ X :=
by
  unfold IsSimpliciallyIso
  use φ.simplicialMap
  apply coe_is_iso

theorem coe_preserves_iso [Nonempty E]
    (X Y : AbstractSimplicialComplex E)
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
    {X : AbstractSimplicialComplex E}
    (φ : SimplicialCoe X F)
    (ψ : SimplicialCoe (φ.coe ''ˢ X) G)
  : Set.InjOn (ψ.coe ∘ φ.coe) X.vertices :=
by
  apply Set.InjOn.comp ψ.Injective φ.Injective
  simp only [Set.MapsTo]
  intro x x_vert
  rw [AbstractSimplicialComplex.vertices_eq]
  simp only [simplicialImage, Set.mem_iUnion]
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
    (X : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (ψ : SimplicialCoe (φ.coe ''ˢ X) G)
  : ((ψ.coe ∘ φ.coe) ''ˢ X).faces = (ψ.coe ''ˢ (φ.coe ''ˢ X)).faces :=
  by
  simp only [simplicialImage, Set.ext_iff]
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
    {X : AbstractSimplicialComplex E}
    (φ : SimplicialCoe X F)
    (ψ : SimplicialCoe (φ.coe ''ˢ X) G)
  : SimplicialCoe X G :=
    SimplicialCoe.mk (ψ.coe ∘ φ.coe) (coe_comp_is_injective φ ψ)

-- Restriction of coe is coe.
theorem coe_restrict_is_injective
    (X Y : AbstractSimplicialComplex E)
    (φ : SimplicialCoe X F)
    (Y_subcomp_X : Y.vertices ⊆ X.vertices)
  : Set.InjOn φ.coe Y.vertices :=
by
  apply Set.InjOn.mono Y_subcomp_X
  apply φ.Injective

@[simp]
def SimplicialCoe.restrict
    {X : AbstractSimplicialComplex E}
    (φ : SimplicialCoe X F)
    (Y : AbstractSimplicialComplex E)
    (Y_subcomp_X : Y.vertices ⊆ X.vertices)
  : SimplicialCoe Y F :=
    SimplicialCoe.mk φ.coe (coe_restrict_is_injective X Y φ Y_subcomp_X)

notation coe "[" K "; " H "]" => SimplicialCoe.restrict coe K H

def SimplicialCoe.restrictCoe
    {X Y : AbstractSimplicialComplex E}
    {Y_subcomp_X : Y.vertices ⊆ X.vertices}
  : Coe (SimplicialCoe X F) (SimplicialCoe Y F) :=
    Coe.mk fun φ : SimplicialCoe X F => φ.restrict Y Y_subcomp_X

-- Convert isomorphisms into coercions.
def SimplicialMap.coe
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : SimplicialCoe X F :=
    SimplicialCoe.mk f.map (iso_is_injective_vertices f f_iso)

-- Coercion on images.
--  g[Y] = X → φ[X]
--  ↑     ↗ φ ∘ g
--  Y
def simplicialCoeOnImage
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
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
      simp only [AbstractSimplicialComplex.mem_vertices, simplicial_iso_implies_lift_bij X Y f f_iso,
        simplicialMapLift, Set.image, Set.mem_setOf]
      rw [AbstractSimplicialComplex.vertices, Set.mem_setOf] at x_in_X
      rw [← Finset.image_singleton]
      apply f.is_simplicial
      assumption)

theorem simplicialCoe_union_simplices
    (X Y : AbstractSimplicialComplex E)
    (φ : SimplicialCoe (X ∪ Y) F)
  : (φ.coe ''ˢ (X ∪ Y)).faces =
      (φ[X; (by apply is_subcomplex_vertices; apply subcomplex_simplicial_union_left)].coe ''ˢ X ∪
          φ[Y; (by apply is_subcomplex_vertices; apply subcomplex_simplicial_union_right)].coe ''ˢ Y).faces :=
by
  apply simplicialImage_union

theorem simplicialCoe_union
    (X Y : AbstractSimplicialComplex E)
    (φ : SimplicialCoe (X ∪ Y) F)
  : φ.coe ''ˢ (X ∪ Y) ≅
      φ[X; by apply is_subcomplex_vertices; apply subcomplex_simplicial_union_left].coe ''ˢ X ∪
        φ[Y; by apply is_subcomplex_vertices; apply subcomplex_simplicial_union_right].coe ''ˢ Y :=
by
  apply simplicial_iso_preserves_equiv
  apply simplicialCoe_union_simplices

theorem simplicialCoe_injective_vertices
    {X : AbstractSimplicialComplex E}
    (φ : SimplicialCoe X F)
  : Set.InjOn φ.coe X.vertices :=
by
  apply φ.Injective

theorem simplicialCoe_surjective_vertices
    {X : AbstractSimplicialComplex E}
    (φ : SimplicialCoe X F)
  : Set.SurjOn φ.coe X.vertices (φ.coe ''ˢ X).vertices :=
by
  simp only [Set.SurjOn, simplicialImage_vertices, subset_refl]

theorem simplicialCoe_mapsTo_vertices
    {X : AbstractSimplicialComplex E}
    (φ : SimplicialCoe X F)
  : Set.MapsTo φ.coe X.vertices (φ.coe ''ˢ X).vertices :=
by
  simp only [Set.MapsTo, simplicialImage_vertices]
  intro x x_in_X
  apply Set.mem_image_of_mem
  assumption

theorem simplicialCoe_bijective_vertices
    {X : AbstractSimplicialComplex E}
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
