import Pachner.Maps.SimplicialIsomorphism

section Coercion

variable
  {E F G : Type _}
  [DecidableEq F]
  {X Y : AbstractSimplicialComplex E}

-- Define as coercion on types that lifts to simplicial map.
structure SimplicialCoe
    (X : AbstractSimplicialComplex E)
    (F : Type _)
  where mk ::
    coe : E → F
    Injective : Set.InjOn coe (X.vertices)

def SimplicialCoe.simplicialMap
    (φ : SimplicialCoe X F)
  : SimplicialMap X (φ.coe ''ˢ X) :=
    SimplicialMap.mk φ.coe (isSimplicialMap_onto_image X φ.coe)

instance SimplicialCoe.Fintype
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (φ : SimplicialCoe X F)
  : Fintype (φ.coe ''ˢ X).faces :=
by
  rw [simplicialImage_is_lift_image]
  apply Set.fintypeImage

theorem simplicialCoe_inv_isSimplicialMap [Nonempty E] [DecidableEq E]
    (φ : SimplicialCoe X F)
  : IsSimplicialMap (φ.coe ''ˢ X) X (Function.invFunOn φ.coe X.vertices) :=
by
  simp only [IsSimplicialMap, SimplicialImage]
  intro t t_in_coe
  choose s s_in_X coe_s_t using t_in_coe
  rw [← coe_s_t]
  have inv_id : Finset.image (Function.invFunOn φ.coe X.vertices) (Finset.image φ.coe s) = s :=
    by
    simp only [← Finset.coe_inj, Finset.coe_image]
    apply Set.InjOn.invFunOn_image
    apply φ.Injective
    apply face_subset_vertices
    assumption
  rw [inv_id]
  assumption

noncomputable def SimplicialCoeInv [Nonempty E] [DecidableEq E]
    {X : AbstractSimplicialComplex E}
    (φ : SimplicialCoe X F)
  : SimplicialMap (φ.coe ''ˢ X) X :=
    SimplicialMap.mk (Function.invFunOn φ.coe X.vertices) (simplicialCoe_inv_isSimplicialMap φ)

notation φ "⁻ᶜ" => SimplicialCoeInv φ

theorem simplicialCoe_inverse_isInverseSimplicialIso [Nonempty E] [DecidableEq E]
    (φ : SimplicialCoe X F)
  : IsInverseSimplicialIso (SimplicialMap.mk φ.coe (isSimplicialMap_onto_image X φ.coe)) (φ⁻ᶜ) :=
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

theorem simplicialCoe_is_simplicialIso [Nonempty E] [DecidableEq E]
    (φ : SimplicialCoe X F)
  : IsSimplicialIso
      (@SimplicialMap.mk _ _ _ X (φ.coe ''ˢ X) φ.coe (by apply isSimplicialMap_onto_image)) :=
by
  unfold IsSimplicialIso
  use SimplicialCoeInv φ
  apply simplicialCoe_inverse_isInverseSimplicialIso

theorem simplicialCoeInv_injective [Nonempty E] [DecidableEq E]
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

theorem SimplicialCoe.simplicialIso_onto_image [Nonempty E] [DecidableEq E]
    (φ : SimplicialCoe X F)
  : X ≅ φ.coe ''ˢ X :=
by
  unfold IsSimpliciallyIso
  use φ.simplicialMap
  apply simplicialCoe_is_simplicialIso

theorem simplicialCoe_preserves_simplicialIso [Nonempty E] [DecidableEq E]
    (φ : SimplicialCoe X F)
    (ψ : SimplicialCoe Y F)
  : (X ≅ Y) → (φ.coe ''ˢ X ≅ ψ.coe ''ˢ Y) :=
by
  intro X_iso_Y
  calc φ.coe ''ˢ X
    _ ≅ X := by rw [simplicialIso_symm]; exact φ.simplicialIso_onto_image
    _ ≅ Y := X_iso_Y
    _ ≅ ψ.coe ''ˢ Y := ψ.simplicialIso_onto_image

theorem simplicialCoe_comp_injective
    (φ : SimplicialCoe X F)
    (ψ : SimplicialCoe (φ.coe ''ˢ X) G)
  : Set.InjOn (ψ.coe ∘ φ.coe) X.vertices :=
by
  simp only [Set.InjOn.comp ψ.Injective φ.Injective, simplicialImage_vertices, Set.mapsTo_image]

theorem simplicialCoe_comp_image
    [DecidableEq G]
    (φ : SimplicialCoe X F)
    (ψ : SimplicialCoe (φ.coe ''ˢ X) G)
  : ((ψ.coe ∘ φ.coe) ''ˢ X) = (ψ.coe ''ˢ (φ.coe ''ˢ X)) :=
by
  exact simplicialImage_comp φ.coe ψ.coe

@[simp]
def SimplicialCoe.comp
    (φ : SimplicialCoe X F)
    (ψ : SimplicialCoe (φ.coe ''ˢ X) G)
  : SimplicialCoe X G :=
    SimplicialCoe.mk (ψ.coe ∘ φ.coe) (simplicialCoe_comp_injective φ ψ)

-- Restriction of coe is coe.
theorem simplicialCoe_restrict_is_injective
    (φ : SimplicialCoe X F)
    (Y_subcomp_X : Y.vertices ⊆ X.vertices)
  : Set.InjOn φ.coe Y.vertices :=
by
  apply Set.InjOn.mono Y_subcomp_X
  apply φ.Injective

@[simp]
def SimplicialCoe.restrict
    (φ : SimplicialCoe X F)
    (Y : AbstractSimplicialComplex E)
    (Y_subcomp_X : Y.vertices ⊆ X.vertices)
  : SimplicialCoe Y F :=
    SimplicialCoe.mk φ.coe (simplicialCoe_restrict_is_injective φ Y_subcomp_X)

notation coe "[" K "; " H "]" => SimplicialCoe.restrict coe K H

def SimplicialCoe.restrictCoe
    {X Y : AbstractSimplicialComplex E}
    {Y_subcomp_X : Y.vertices ⊆ X.vertices}
  : Coe (SimplicialCoe X F) (SimplicialCoe Y F) :=
    Coe.mk fun φ : SimplicialCoe X F => φ.restrict Y Y_subcomp_X

-- Convert isomorphisms into coercions.
def SimplicialMap.coe [DecidableEq E]
    {X : AbstractSimplicialComplex E}
    {Y : AbstractSimplicialComplex F}
    (f : SimplicialMap X Y)
    (f_iso : IsSimplicialIso f)
  : SimplicialCoe X F :=
    SimplicialCoe.mk f.map (simplicialIso_injective_vertices f f_iso)

-- Coercion on images.
--  g[Y] = X → φ[X]
--  ↑     ↗ φ ∘ g
--  Y
def SimplicialCoeOnImage [DecidableEq E]
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
      simp only [AbstractSimplicialComplex.mem_vertices, simplicialIso_imp_simplicialMapLift_bijective f f_iso,
        SimplicialMapLift, Set.image, Set.mem_setOf]
      rw [AbstractSimplicialComplex.vertices, Set.mem_setOf] at x_in_X
      rw [← Finset.image_singleton]
      apply f.is_simplicial
      assumption)

theorem simplicialCoe_union
    (φ : SimplicialCoe (X ∪ Y) F)
  : φ.coe ''ˢ (X ∪ Y) =
      φ[X; by apply isSubcomplex_vertices; apply simplicialUnion_subcomplex_left].coe ''ˢ X ∪
        φ[Y; by apply isSubcomplex_vertices; apply simplicialUnion_subcomplex_right].coe ''ˢ Y :=
by
  exact simplicialImage_union

theorem simplicialCoe_injective_vertices
    (φ : SimplicialCoe X F)
  : Set.InjOn φ.coe X.vertices :=
by
  exact φ.Injective

theorem simplicialCoe_surjective_vertices
    (φ : SimplicialCoe X F)
  : Set.SurjOn φ.coe X.vertices (φ.coe ''ˢ X).vertices :=
by
  simp only [Set.SurjOn, simplicialImage_vertices, subset_refl]

theorem simplicialCoe_mapsTo_vertices
    (φ : SimplicialCoe X F)
  : Set.MapsTo φ.coe X.vertices (φ.coe ''ˢ X).vertices :=
by
  simp only [simplicialImage_vertices, Set.mapsTo_image]

theorem simplicialCoe_bijective_vertices
    (φ : SimplicialCoe X F)
  : Set.BijOn φ.coe X.vertices (φ.coe ''ˢ X).vertices :=
by
  simp only [Set.BijOn, simplicialCoe_mapsTo_vertices, simplicialCoe_injective_vertices,
      simplicialCoe_surjective_vertices, and_true]

end Coercion
