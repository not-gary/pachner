import Pachner.Basic.AbstractSimplicialComplex

section Disjoint
variable {E : Type _}

def DisjointComplexes
    (X Y : AbstractSimplicialComplex E) : Prop :=
  Disjoint (X.vertices) (Y.vertices)

theorem disjoint_simplices_iff_disj_vertices [DecidableEq E]
    (X Y : AbstractSimplicialComplex E)
    (s t : Finset E)
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces)
  : DisjointComplexes X Y → Disjoint s t :=
by
  simp only [DisjointComplexes, AbstractSimplicialComplex.vertices_eq]
  intro XY_disj
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.subset_empty_iff] at XY_disj
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.subset_empty, ← Finset.coe_subset,
    Finset.coe_empty, Finset.coe_inter]
  apply
    @Set.Subset.trans _ _
      ((⋃ (s : Finset E) (H : s ∈ X.faces), ↑s) ∩ ⋃ (s : Finset E) (H : s ∈ Y.faces), ↑s)
  apply Set.inter_subset_inter <;> apply Set.subset_biUnion_of_mem <;> assumption
  simp only [Set.subset_empty_iff] at ⊢ XY_disj
  assumption

theorem disjoint_singleton
    (X : AbstractSimplicialComplex E)
    (x : E)
  : x ∉ X.vertices → DisjointComplexes X (simplex {x}) :=
by
  simp only [DisjointComplexes, simplex_vertices {x}]
  intro x_nin_X
  rw [Set.disjoint_iff_inter_eq_empty, Finset.coe_singleton, Set.inter_singleton_eq_empty]
  assumption

theorem disjoint_complexes_disjoint_simplices
    (X Y : AbstractSimplicialComplex E)
    (s t : Finset E)
    (s_in_X : s ∈ X.faces)
    (t_in_Y : t ∈ Y.faces)
    (XY_disj : Disjoint (X.vertices) (Y.vertices))
  : Disjoint s t :=
by
  rw [← Finset.disjoint_coe]
  apply @Set.disjoint_of_subset _ _ (X.vertices) _ (Y.vertices)
  apply simplex_subset_vertices
  assumption
  apply simplex_subset_vertices
  assumption
  assumption

end Disjoint


section DisjointUnion
variable {E 𝕜 : Type _}
variable [DecidableEq E] [DecidableEq 𝕜] [Ring 𝕜] [Nontrivial 𝕜]

@[simp]
def simplexDisjointUnion (s t : Finset E) : Finset (E × 𝕜) :=
  s ×ˢ {0} ∪ t ×ˢ {1}

infixl:65 " ⊔ₛ " => simplexDisjointUnion

instance SimplexDisjoint.nonempty
    (s t : Finset E)
    (H : Nonempty s ∨ Nonempty t) :
    Nonempty (s ⊔ₛ t : Finset (E × 𝕜)) :=
by
  iterate 2 rw [Finset.nonempty_coe_sort, ← Finset.coe_nonempty] at *
  unfold simplexDisjointUnion
  rw [Finset.coe_union, Set.union_nonempty]
  cases' H with Hs Ht
  left
  rw [Finset.coe_nonempty] at *
  rw [Finset.nonempty_product]
  constructor
  assumption
  simp
  right
  rw [Finset.coe_nonempty] at *
  rw [Finset.nonempty_product]
  constructor
  assumption
  simp

instance SimplexDisjoint.nonempty.left
    (s : Finset E) [Nonempty s]
  : Nonempty (s ⊔ₛ ∅ : Finset (E × 𝕜)) :=
by
  have : Nonempty ↥s ∨ Nonempty ↥(∅ : Finset E) := by left; assumption
  apply @SimplexDisjoint.nonempty _ _ _ _ _ s (∅ : Finset E) this

instance SimplexDisjoint.nonempty.right
    (t : Finset E) [Nonempty t]
  : Nonempty (∅ ⊔ₛ t : Finset (E × 𝕜)) :=
by
  have : Nonempty ↥(∅ : Finset E) ∨ Nonempty ↥t := by right; assumption
  apply @SimplexDisjoint.nonempty _ _ _ _ _ (∅ : Finset E) t this

instance SimplexDisjoint.partialOrder : PartialOrder (Finset (E × 𝕜)) :=
  Finset.partialOrder

theorem simplex_disjoint_disjoint
    (s t : Finset E)
  : @Disjoint _ SimplexDisjoint.partialOrder _ (Finset.product s {(0 : 𝕜)}) (Finset.product t {(1 : 𝕜)}) :=
by
  rw [Finset.disjoint_left]
  intro x x_in_s0
  rw [Finset.product_eq_sprod, Finset.mem_product] at *
  cases' x_in_s0 with x_in_s x0
  rw [not_and_or]
  right
  rw [Finset.mem_singleton] at *
  rw [x0]
  simp

theorem simplex_disjoint_mem
    (s t : Finset E)
    (x : E × 𝕜)
  : x ∈ s ⊔ₛ t ↔ x.fst ∈ s ∧ x.snd = 0 ∨ x.fst ∈ t ∧ x.snd = 1 :=
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

theorem simplex_disjoint_mem_left
    (s t : Finset E)
    (x : E)
  : (x, 0) ∈ (s ⊔ₛ t : Finset (E × 𝕜)) ↔ x ∈ s :=
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
  · intro x_in_s
    rw [Finset.mem_union]
    left
    rw [Finset.mem_product]
    constructor
    simp; assumption
    simp

theorem simplex_disjoint_mem_right
    (s t : Finset E)
    (x : E)
  : (x, 1) ∈ (s ⊔ₛ t : Finset (E × 𝕜)) ↔ x ∈ t :=
by
  unfold simplexDisjointUnion
  constructor
  · intro x1_in_st
    rw [Finset.mem_union] at x1_in_st
    cases' x1_in_st with x1_in_s0 x1_in_t1
    rw [Finset.mem_product] at x1_in_s0
    cases' x1_in_s0 with x_in_s contra
    simp at contra
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

theorem simplex_disjoint_subset_unique
    (s t u w : Finset E)
  : s ⊔ₛ t ⊆ (u ⊔ₛ w : Finset (E × 𝕜)) ↔ s ⊆ u ∧ t ⊆ w :=
by
  constructor
  intro disj_sset
  rw [Finset.subset_iff] at disj_sset
  constructor <;> rw [Finset.subset_iff] <;> intro x x_in_s
  have Hs_0 : (x, 0) ∈ (s ⊔ₛ t : Finset (E × 𝕜)) := by
    rw [simplex_disjoint_mem_left]
    assumption
  specialize disj_sset Hs_0
  rw [simplex_disjoint_mem_left] at disj_sset
  assumption
  have Ht_1 : (x, 1) ∈ (s ⊔ₛ t : Finset (E × 𝕜)) := by
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
  cases' x_in_st with x_in_st x_in_st
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

theorem simplex_disjoint_subset_sep
    (s : Finset (E × 𝕜))
    (t u : Finset E)
  : s ⊆ t ⊔ₛ u ↔ ∃ z w : Finset E, s = z ⊔ₛ w ∧ z ⊆ t ∧ w ⊆ u :=
by
  constructor
  intro s_sset_tu
  let z_prod : Finset (E × 𝕜) := Finset.filter (fun x : E × 𝕜 => x.snd = 0) s
  let z : Finset E := Finset.biUnion z_prod fun x => {x.fst}
  let w_prod : Finset (E × 𝕜) := Finset.filter (fun x : E × 𝕜 => x.snd = 1) s
  let w : Finset E := Finset.biUnion w_prod fun x => {x.fst}
  use z; use w
  have s_eq_zw : s = z ⊔ₛ w :=
  by
    rw [Finset.ext_iff]
    intro x
    constructor
    rw [Finset.subset_iff] at s_sset_tu
    intro x_in_s
    specialize s_sset_tu x_in_s
    simp_rw [simplex_disjoint_mem] at s_sset_tu
    rw [simplex_disjoint_mem]
    simp only [z, z_prod, w, w_prod]
    iterate 2 rw [Finset.mem_biUnion]
    cases' s_sset_tu with s_sset_tu s_sset_tu
    left
    cases' s_sset_tu with x_in_t x0
    constructor
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
    cases' x_in_zw with x_in_zw x_in_zw  <;>
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
  rw [← @simplex_disjoint_subset_unique E 𝕜, ← s_eq_zw]
  assumption
  intro s_eq_zw
  choose z w s_eq_zw using s_eq_zw
  choose s_eq_zw z_sset_t w_sset_u using s_eq_zw
  rw [Finset.subset_iff]
  intro x x_in_s
  rw [s_eq_zw] at x_in_s
  rw [simplex_disjoint_mem] at *
  cases' x_in_s with x_in_s x_in_s
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

theorem simplex_disjoint_eq_unique
    (s t u w : Finset E)
  : s ⊔ₛ t = (u ⊔ₛ w : Finset (E × 𝕜)) ↔ s = u ∧ t = w :=
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

theorem simplex_disjoint_empty
    (s t : Finset E)
  : (s ⊔ₛ t : Finset (E × 𝕜)) = ∅ ↔ s = ∅ ∧ t = ∅ :=
by
  have H : (∅ : Finset (E × 𝕜)) = (∅ : Finset E) ⊔ₛ (∅ : Finset E) := by simp
  rw [H]
  apply simplex_disjoint_eq_unique

theorem simplex_disjoint_distr_union
    (s t u w : Finset E)
  : s ⊔ₛ t ∪ (u ⊔ₛ w : Finset (E × 𝕜)) = s ∪ u ⊔ₛ (t ∪ w) :=
by
  unfold simplexDisjointUnion
  rw [← Finset.union_assoc]
  rw [Finset.union_assoc _ (t ×ˢ {1}) (u ×ˢ {0})]
  rw [Finset.union_comm (t ×ˢ {1}) (u ×ˢ {0})]
  rw [← Finset.union_assoc]
  rw [Finset.union_assoc _ (t ×ˢ {1}) (w ×ˢ {1})]
  repeat' rw [Finset.union_product]

theorem simplex_disjoint_distr_inter
    (s t u w : Finset E)
  : (s ⊔ₛ t : Finset (E × 𝕜)) ∩ (u ⊔ₛ w) = s ∩ u ⊔ₛ t ∩ w :=
by
  unfold simplexDisjointUnion
  repeat' rw [Finset.inter_union_distrib_left]
  repeat' rw [Finset.union_inter_distrib_right]
  have H_tu_empty :
    (t ×ˢ {1} : Finset (E × 𝕜)) ∩ (u ×ˢ {0} : Finset (E × 𝕜)) = ∅ :=
  by
    rw [← Finset.disjoint_iff_inter_eq_empty]
    rw [Finset.disjoint_product]
    right
    rw [Finset.disjoint_iff_inter_eq_empty]
    simp only [Finset.mem_singleton, zero_ne_one, not_false_eq_true,
      Finset.inter_singleton_of_notMem]
  have H_sw_empty :
    (s ×ˢ {0} : Finset (E × 𝕜)) ∩ (w ×ˢ {1} : Finset (E × 𝕜)) = ∅ :=
  by
    rw [← Finset.disjoint_iff_inter_eq_empty]
    rw [Finset.disjoint_product]
    right
    rw [Finset.disjoint_iff_inter_eq_empty]
    simp only [Finset.mem_singleton, one_ne_zero, not_false_eq_true,
      Finset.inter_singleton_of_notMem]
  rw [H_tu_empty, H_sw_empty]
  repeat' rw [Finset.union_empty, Finset.empty_union]
  repeat' rw [Finset.inter_product]

theorem simplex_disjoint_card
    (s t : Finset E)
  : (s ⊔ₛ t : Finset (E × 𝕜)).card = s.card + t.card :=
by
  simp only [simplexDisjointUnion]
  set s₀ : Finset (E × 𝕜) := s ×ˢ {0}
  set t₁ : Finset (E × 𝕜) := t ×ˢ {1}
  have card_disj : (s₀ ∪ t₁).card = s₀.card + t₁.card :=
  by
    apply Finset.card_union_of_disjoint
    simp only [s₀, t₁, Finset.disjoint_product, Finset.disjoint_singleton]
    right; simp only [ne_eq, zero_ne_one, not_false_eq_true, t₁, s₀]
  simp only [card_disj, s₀, t₁, Finset.card_product, Finset.card_singleton, mul_one]

end DisjointUnion
