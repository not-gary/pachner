import tactic          -- standard proof tactics
import data.set        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset     -- type-level finite sets
import .simplicial_complex
import .simplicial_subcomplex
import .stellar

variables {α : Type*} [decidable_eq α]

def stellar_n_sphere
    (n : ℤ)
  : simplicial_complex ℕ
:= match n with
   | int.of_nat m :=
      simplicial_complex.mk
        (finset.powerset (finset.range (m + 2)) \ {finset.range (m + 2)})
        (begin
          rw [set.nonempty_coe_sort, set.nonempty_def],
          use ∅,
          rw [set.mem_diff],
          split,

          rw [finset.mem_coe],
          apply finset.empty_mem_powerset,

          rw [set.mem_singleton_iff],
          apply ne.symm,
          apply finset.nonempty.ne_empty,
          rw [finset.nonempty_range_iff],
          tauto,
        end)
        (begin
          simp only[is_subset_closed],
          intros s s_sphere t t_sset_s,

          rw [set.mem_diff, finset.mem_coe, finset.mem_powerset, set.mem_singleton_iff] at *,
          cases s_sphere with s_in_power s_ne_range,
          split,

          apply @subset_trans _ _ _ t s (finset.range(m + 2));
          assumption,

          have Hs : s ⊂ finset.range (m + 2), from
          begin
            apply ssubset_of_ne_of_subset;
            assumption,
          end,
          apply ne_of_ssubset,
          apply @ssubset_of_subset_of_ssubset _ _ _ _ t s (finset.range(m + 2));
          assumption,
        end)
   | int.neg_succ_of_nat n := empty_sc
   end
notation `S(` n `)` := stellar_n_sphere n

lemma stellar_sphere_vertices
    (n : ℕ)
  : vertices S(n) = finset.range (n + 2)
:= begin
  have Hn : ↑n = int.of_nat n, by tauto,
  rw [Hn],

  simp only[vertices, stellar_n_sphere],
  rw [set.ext_iff],
  intro x,
  split,

  { intro x_in_vert,
    rw [set.mem_Union] at x_in_vert,
    choose s x_in_vert using x_in_vert,
    rw [set.mem_Union] at x_in_vert,
    choose Hs x_in_s using x_in_vert,
    simp only[simplicial_complex.simplices] at Hs,
    
    rw [set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset] at Hs,
    cases Hs with s_sset_range s_ne_range,
    
    rw [finset.mem_coe] at *,
    rw [finset.subset_iff] at s_sset_range,
    specialize s_sset_range x_in_s,
    rw [finset.mem_range] at *,
    assumption, },

  { intro x_in_range,
    rw [set.mem_Union],
    use {x},
    rw [set.mem_Union],
    dsimp only[simplicial_complex.simplices],
    
    have Hx : {x} ∈ ↑(finset.powerset (finset.range (n + 2))) \ {finset.range (n + 2)}, from
    begin
      rw [set.mem_diff, set.mem_singleton_iff, finset.mem_coe, finset.mem_powerset, ←finset.ssubset_iff_subset_ne, finset.ssubset_iff],
      destruct x,

      intro x_zero,
      use x.succ,
      split,

      rw [finset.mem_singleton],
      simp,

      rw [finset.subset_iff],
      intros y y_eq_x,
      rw [finset.mem_coe, finset.mem_range] at *,
      rw [finset.mem_insert, finset.mem_singleton] at y_eq_x,
      cases y_eq_x;
      subst y;
      rw [finset.mem_range],
      omega,
      assumption,

      intros x_pred x_nonzero,
      use x_pred,
      split,

      rw [finset.mem_singleton],
      subst x,
      omega,

      rw [finset.subset_iff],
      intros y y_eq_x,
      rw [finset.mem_coe, finset.mem_range] at x_in_range,
      rw [finset.mem_range],
      rw [finset.mem_insert, finset.mem_singleton] at y_eq_x,
      cases y_eq_x;
      subst y,
      omega,
      assumption,
    end,
    use Hx,
    rw [finset.mem_coe, finset.mem_singleton], }
end

lemma stellar_sphere_range
    (n m : ℕ)
  : m ≤ n → finset.range m ∈ S(n).simplices
:= sorry

lemma stellar_sphere_star_complement
    (n : ℕ)
    (n_nonzero : n > 0)
  : @star_complement ℕ _
      S(↑n) (finset.range n)
      (by { simp, omega, })
      (by { apply stellar_sphere_range, simp, })
    ≅ (simplex {n + 1}) ⋆ ∂(finset.range n)
:= sorry

lemma stellar_sphere_empty_link
    (n : ℕ)
  : Lk(S(↑n), finset.range n) (by { apply stellar_sphere_range, simp, })
      ≅ @empty_sc ℕ
:= sorry

lemma stellar_zero_sphere_iso
    (n m : ℕ)
  : n ≠ m → simplex {n} ∪ @simplex ℕ {m} ≅ S(0)
:= sorry

lemma range_boundary_is_stellar_sphere
    (n : ℕ)
    (n_nonzero : n > 0)
  : ∂(finset.range n) ≅ S(n - 1)
:= sorry

lemma stellar_sphere_inductive
    (n : ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
  : S(n) ≅ₛₜ φ[S(0) ⋆ S(n - 1)]
:= begin
  apply @stellar_equiv_iso _ _ _ _ (S(↑n) ⋆ empty_sc) (S(↑0) ⋆ S(↑n - 1)),
  apply simplicial_join_id_left,
  apply φ.iso_onto_image,

  have Hn : ↑n = int.of_nat n, by tauto,
  induction n,

  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_trans (S(↑0) ⋆ empty_sc) S(↑0),
  apply simplicial_join_id_left,

  have H_empty : S(↑0 - 1) = empty_sc, from
  begin
    have H_neg : -1 = int.neg_succ_of_nat 0, by tauto,

    simp,
    rw [H_neg],
    unfold stellar_n_sphere,
  end,

  rw [simplicial_iso_symm, H_empty],
  apply simplicial_join_id_left,

  set n := n_n,
  apply @relation.refl_trans_gen.head _ _ _ (S(↑0) ⋆ S(↑n.succ - 1)),
  rotate, refl,

  unfold stellar_move,
  intro ψ,
  right, left,
  use (finset.range (n.succ) ⊔ₛ ∅),

  have Hs : finset.range (n.succ) ⊔ₛ ∅ ∈ (S(↑n.succ) ⋆ empty_sc).simplices, from
  begin
    rw [simplicial_join_sep],
    split,
    
    rw [Hn],
    simp only[stellar_n_sphere, simplicial_complex.simplices],
    rw [set.mem_diff],
    split,

    rw [finset.mem_coe, finset.mem_powerset, finset.range_subset],
    simp,

    simp,
    rw [finset.ext_iff],
    simp,
    use (n.succ + 1),
    simp,

    apply simplicial_complex_empty_simplex,
  end,
  use Hs,

  have H_range_ne : nonempty (finset.range n.succ), from
  begin
    rw [finset.nonempty_coe_sort, finset.nonempty_range_iff],
    simp,
  end,
  have Hs_ne : nonempty ↥(finset.range n.succ ⊔ₛ ∅), from
  begin
    apply @simplex_disjoint.nonempty.left _ _ (finset.range n.succ) H_range_ne,
  end,
  use Hs_ne,

  use (n.succ + 2, 0),
  have Hx : (n.succ + 2, 0) ∉ vertices (S(↑(n.succ)) ⋆ empty_sc), from
  begin
    rw [simplicial_join_vertices_mem_left, stellar_sphere_vertices],
    rw [finset.mem_coe, finset.mem_range],
    simp,
  end,
  use Hx,

  rw [simplicial_iso_symm],
  set s : finset ℕ := finset.range n.succ,
  apply simplicial_iso_trans
    (@stellar_subdivision _ _ (S(n.succ) ⋆ empty_sc)
      (s ⊔ₛ ∅) Hs_ne
      (n.succ + 2, 0)
      Hs Hx ψ)
    ((@stellar_subdivision _ _ S(n.succ)
      s H_range_ne
      (n.succ + 2)
      (by { sorry })
      (by { sorry })
      φ) ⋆ empty_sc),

  rw [simplicial_iso_symm],
  apply @stellar_subdiv_distr_join_left ℕ _ S(n.succ) empty_sc s H_range_ne,
  { sorry },
  { sorry },

  apply simplicial_iso_trans
    ((@stellar_subdivision _ _ S(n.succ)
      s H_range_ne
      (n.succ + 2)
      (by { sorry })
      (by { sorry })
      φ) ⋆ empty_sc)
    (@stellar_subdivision _ _ S(n.succ)
      s H_range_ne
      (n.succ + 2)
      (by { sorry })
      (by { sorry })
      φ),
  apply simplicial_join_id_left,

  apply simplicial_iso_trans
    (@stellar_subdivision _ _ S(n.succ)
      s H_range_ne
      (n.succ + 2)
      (by { sorry })
      (by { sorry })
      φ)
    (((simplex {n.succ + 1}) ⋆ ∂s) ∪ ((simplex {n.succ + 2}) ⋆ ∂s)),


  unfold stellar_subdivision,
  apply simplicial_union_iso,

  apply stellar_sphere_star_complement,
  simp,

  apply simplicial_iso_trans
    (φ[φ[(simplex {n.succ + 2}) ⋆ ∂s] ⋆ Lk(S(n.succ), s) sorry])
    (φ[(simplex {n.succ + 2}) ⋆ ∂s] ⋆ Lk(S(n.succ), s) sorry),
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,

  apply simplicial_iso_trans
    (φ[(simplex {n.succ + 2}) ⋆ ∂s] ⋆ Lk(S(n.succ), s) sorry)
    (φ[(simplex {n.succ + 2}) ⋆ ∂s] ⋆ empty_sc),
  apply simplicial_join_iso,
  apply simplicial_iso_refl,
  apply stellar_sphere_empty_link,

  apply simplicial_iso_trans
    (φ[(simplex {n.succ + 2}) ⋆ ∂s] ⋆ empty_sc)
    (φ[(simplex {n.succ + 2}) ⋆ ∂s]),
  apply simplicial_join_id_left,
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,

  apply simplicial_iso_trans
    (simplex {n.succ + 1} ⋆ ∂s ∪ simplex {n.succ + 2} ⋆ ∂s)
    ((simplex {n.succ + 1} ∪ simplex {n.succ + 2}) ⋆ ∂s),
  rw [simplicial_iso_symm],
  apply simplicial_join_distr_union_right,
  apply simplicial_join_iso,

  apply stellar_zero_sphere_iso,
  simp,

  apply range_boundary_is_stellar_sphere,
  simp,
end

lemma join_stellar_sphere
    (m n : ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
  : φ[S(m) ⋆ S(n)] ≅ₛₜ S(m + n + 1)
:= begin
  rw [stellar_equiv_symm],
  apply stellar_equiv_trans
    S(m + n + 1)
    (φ[S(0) ⋆ S(m + n + 1 - 1)]),
  apply stellar_sphere_inductive,

  apply stellar_equiv_iso
    (S(0) ⋆ S(m + n + 1 - 1))
    (S(m) ⋆ S(n))
    (φ[S(0) ⋆ S(m + n + 1 - 1)])
    (φ[S(m) ⋆ S(n)]),
  rotate, apply φ.iso_onto_image,
  rotate, apply φ.iso_onto_image,

  have Hn : ↑n = int.of_nat n, by tauto,
  have Hm : ↑m = int.of_nat m, by tauto,
  rw [Hn, Hm],

  induction m;
  induction n,

  -- m, n = 0
  simp,

  -- m = 0, n ≠ 0
  have Hnn : ↑n_n = int.of_nat n_n, by tauto,
  specialize n_ih Hnn,
  simp only [zero_add, int.of_nat_eq_coe, nat.cast_zero, add_tsub_cancel_right],
  
  -- m ≠ 0, n = 0
  have Hmn : ↑m_n = int.of_nat m_n, by tauto,
  specialize m_ih Hmn,
  simp only [add_zero, int.of_nat_eq_coe, nat.cast_zero, add_tsub_cancel_right],
  apply stellar_equiv_preserves_iso,
  apply simplicial_join_comm,

  -- m, n ≠ 0
  have Hnn : ↑n_n = int.of_nat n_n, by tauto,
  have Hmn : ↑m_n = int.of_nat m_n, by tauto,
  specialize n_ih Hnn,
  specialize m_ih Hmn,
  simp only [add_zero, int.of_nat_eq_coe, nat.cast_zero, add_tsub_cancel_right] at *,

  have H : S(m_n.succ + n_n.succ) ≅ₛₜ φ[S(m_n) ⋆ S(n_n.succ)], from
  begin
    rw [stellar_equiv_symm],
    apply stellar_equiv_trans
      (φ[S(m_n) ⋆ S(n_n.succ)])
      (φ[S(0) ⋆ S(m_n + n_n.succ)]),

    apply stellar_equiv_iso
      (S(m_n) ⋆ S(n_n.succ))
      (S(0) ⋆ S(m_n + n_n.succ))
      (φ[S(m_n) ⋆ S(n_n.succ)])
      (φ[S(0) ⋆ S(m_n + n_n.succ)]),
    apply φ.iso_onto_image,
    apply φ.iso_onto_image,
    rw [stellar_equiv_symm],
    assumption,

    rw [stellar_equiv_symm],
    have H_rw : ↑m_n + ↑(n_n.succ) = ↑(m_n.succ) + ↑(n_n.succ) - 1, by simp,
    have HS_rw : S(↑m_n + ↑(n_n.succ)) = S(↑(m_n.succ) + ↑(n_n.succ) - 1), from
    begin
      apply congr_arg,
      sorry, --stupid
    end,
    rw [HS_rw],
    apply stellar_sphere_inductive,
  end,

  apply stellar_equiv_trans
    (S(0) ⋆ S(m_n.succ + n_n.succ))
    (S(0) ⋆ φ[S(m_n) ⋆ S(n_n.succ)]),
  apply simplicial_join_stellar_equiv_right,
  assumption,

  apply stellar_equiv_trans
    (S(0) ⋆ φ[S(m_n) ⋆ S(n_n.succ)])
    (S(0) ⋆ φ[S(m_n) ⋆ φ[S(0) ⋆ S(n_n)]]),
  apply simplicial_join_stellar_equiv_right,
  apply stellar_equiv_iso
    (S(m_n) ⋆ S(n_n.succ))
    (S(m_n) ⋆ φ[S(0) ⋆ S(n_n)])
    (φ[S(m_n) ⋆ S(n_n.succ)])
    (φ[S(m_n) ⋆ φ[S(0) ⋆ S(n_n)]]),
  apply φ.iso_onto_image,
  apply φ.iso_onto_image,
  apply simplicial_join_stellar_equiv_right,
  have Hn_pred : ↑n_n = ↑(n_n.succ) - 1, by simp,
  have HSn_rw : S(↑n_n) = S(↑(n_n.succ) - 1), from
  begin
    conv_rhs { congr, simp },
  end,
  rw [HSn_rw],
  apply stellar_sphere_inductive,

  apply stellar_equiv_trans
    (S(0) ⋆ φ[S(m_n) ⋆ φ[S(0) ⋆ S(n_n)]])
    (φ[S(0) ⋆ S(m_n)] ⋆ φ[S(0) ⋆ S(n_n)]),
  apply stellar_equiv_preserves_iso,
  rw [simplicial_iso_symm],
  apply simplicial_join_assoc,

  apply simplicial_join_stellar_equiv,
  
  rw [stellar_equiv_symm],
  have Hm_pred : ↑m_n = ↑(m_n.succ) - 1, by simp,
  have HSm_rw : S(↑m_n) = S(↑(m_n.succ) - 1), from
  begin
    conv_rhs { congr, simp },
  end,
  rw [HSm_rw],
  apply stellar_sphere_inductive,

  rw [stellar_equiv_symm],
  have Hn_pred : ↑n_n = ↑(n_n.succ) - 1, by simp,
  have HSn_rw : S(↑n_n) = S(↑(n_n.succ) - 1), from
  begin
    conv_rhs { congr, simp },
  end,
  rw [HSn_rw],
  apply stellar_sphere_inductive,
end

@[simp]
def stellar_n_disk
    (n : ℤ)
  : simplicial_complex ℕ
:= match n with
   | int.of_nat m :=
        simplicial_complex.mk
          (finset.powerset (finset.range (m + 1)))
          (begin
            rw [set.nonempty_coe_sort, set.nonempty_def],
            use ∅,
            rw [finset.mem_coe],
            apply finset.empty_mem_powerset,
          end)
          (by { simp, tauto })
   | _ := empty_sc
   end
notation `D(` n `)` := stellar_n_disk n

lemma stellar_disk_range
    (m n : ℕ)
  : m ≤ n + 1 → finset.range m ∈ D(n).simplices
:= sorry

lemma disk_is_sphere_iff_empty
    (m n : ℤ)
  : D(m) ≅ₛₜ S(n) ↔ m < 0 ∧ n < 0
:= sorry

-- TODO: Prove maps are simplicial.
--       Reprove for m, n ≥ -1. Cascade to later proofs.
lemma join_stellar_disk
    (m n : ℤ)
  : D(m) ⋆ D(n) ≅ D(m + n + 1)
:= begin
  sorry,

  -- m, n ∈ ℕ case.
  let f : ℕ × ℕ → ℕ := λ x : ℕ × ℕ, if (x.snd = 0) then x.fst else (m + x.fst + 1),
  have f_simpl : is_simplicial_map (D(m) ⋆ D(n)) D(m + n + 1) f, from
  begin
    sorry,
  end,

  let g : ℕ → ℕ × ℕ := λ x : ℕ, if (x ≤ m) then (x, 0) else ((x - m - 1), 1),
  have g_simpl : is_simplicial_map D(m + n + 1) (D(m) ⋆ D(n)) g,
  begin
    sorry,
  end,

  let fs : simplicial_map (D(m) ⋆ D(n)) D(m + n + 1) := simplicial_map.mk f f_simpl,
  let gs : simplicial_map D(m + n + 1) (D(m) ⋆ D(n)) := simplicial_map.mk g g_simpl,

  unfold is_simplicially_iso,
  use fs,
  unfold is_simplicial_iso,
  use gs,
  unfold is_inverse_simplicial_iso,

  have Hm : ↑m = int.of_nat m, by tauto,
  have Hn : ↑n = int.of_nat n, by tauto,

  simp only[simplicial_map.comp, simplicial_map.map, set.restrict_eq_restrict_iff],
  unfold set.eq_on,
  split,

  { intros x x_in_vert_join,
    
    dsimp only[vertices, simplicial_join, stellar_n_disk, simplicial_complex.simplices] at x_in_vert_join,
    rw [set.mem_Union] at x_in_vert_join,
    choose s x_in_vert_join using x_in_vert_join,
    rw [set.mem_Union] at x_in_vert_join,
    choose Hs x_in_s using x_in_vert_join,
    
    rw [set.mem_set_of] at Hs,
    choose t Ht u Hu tu_eq_s using Hs,
    
    simp_rw [Hm, Hn] at Ht Hu,
    unfold stellar_n_disk._match_1 at Ht Hu,
    simp only[simplicial_complex.simplices] at Ht Hu,
    rw [finset.mem_coe] at *,
    rw [finset.mem_powerset, finset.subset_iff] at Ht Hu,
    
    rw [←tu_eq_s, simplex_disjoint_mem] at x_in_s,
    rw [function.comp_apply],
    simp only[f, g],
    cases x_in_s with x_in_t x_in_u,
    
    cases x_in_t with x_in_t x0,
    split_ifs,
    
    rw [←x0],
    simp,
    
    specialize Ht x_in_t,
    rw [finset.mem_range] at Ht,
    have : x.fst ≤ m, by omega,
    contradiction,
    
    cases x_in_u with x_in_u x1,
    split_ifs,
    
    have : ¬x.snd = 0, by omega,
    contradiction,
    
    have : ¬x.snd = 0, by omega,
    contradiction,
    
    have : ¬m ≤ m + 1, by omega,
    have : m ≤ m + 1, by omega,
    contradiction,
    
    iterate 2 { rw [nat.add_comm, ←nat.add_assoc] },
    iterate 2 {rw [nat.add_sub_assoc, nat.sub_self, nat.add_zero] },
    rw [←x1],
    simp,
    
    simp, },

  { intros x x_in_vert_disk,
  
    dsimp only[vertices, stellar_n_disk, simplicial_complex.simplices] at x_in_vert_disk,
    rw [set.mem_Union] at x_in_vert_disk,
    choose s x_in_vert_disk using x_in_vert_disk,
    rw [set.mem_Union] at x_in_vert_disk,
    choose Hs x_in_s using x_in_vert_disk,
    
    have H_sum : int.of_nat m + int.of_nat n + 1 = int.of_nat (m + n + 1), by tauto,
    simp_rw [Hm, Hn, H_sum] at Hs,
    unfold stellar_n_disk._match_1 at Hs,
    simp only[simplicial_complex.simplices] at Hs,
    rw [finset.mem_coe] at *,
    rw [finset.mem_powerset, finset.subset_iff] at Hs,
    specialize Hs x_in_s,
    rw [finset.mem_range] at Hs,
    
    rw [function.comp_apply],
    simp only[f, g],
    split_ifs,
    
    simp,
    
    have : x ≤ m, by omega,
    contradiction,
    
    iterate 2 { rw [←nat.add_sub_assoc] },
    rw [nat.sub_add_cancel],
    rw [nat.add_comm, nat.add_sub_assoc, nat.sub_self, nat.add_zero],
    simp,
    
    have : 1 ≤ x, by omega,
    rw [nat.add_comm, nat.add_sub_assoc, nat.sub_self, nat.add_zero],
    assumption,
    
    simp,
    omega,
    omega, },
end

@[simp]
def is_stellar_sphere
    (X : simplicial_complex ℕ)
  : Prop
:= ∃ (n : ℤ) (H : -1 ≤ n), X ≅ₛₜ S(n)

@[simp]
def is_stellar_n_sphere
    (X : simplicial_complex ℕ)
    (n : ℤ)
  : Prop
:= X ≅ₛₜ S(n)

@[simp]
def is_stellar_ball
    (X : simplicial_complex ℕ)
  : Prop
:= ∃ (n : ℤ) (H : -1 ≤ n), X ≅ₛₜ D(n)

@[simp]
def is_stellar_n_ball
    (X : simplicial_complex ℕ)
    (n : ℤ)
  : Prop
:= X ≅ₛₜ D(n)

lemma stellar_equiv_preserves_stellar_n_sphere
    (X Y : simplicial_complex ℕ)
    (n : ℤ)
  : is_stellar_n_sphere X n → X ≅ₛₜ Y → is_stellar_n_sphere Y n
:= sorry

lemma stellar_equiv_preserves_not_stellar_n_sphere
    (X Y : simplicial_complex ℕ)
    (n : ℤ)
  : ¬is_stellar_n_sphere X n → X ≅ₛₜ Y → ¬is_stellar_n_sphere Y n
:= sorry

lemma stellar_equiv_preserves_stellar_sphere
    (X Y : simplicial_complex ℕ)
  : is_stellar_sphere X → X ≅ₛₜ Y → is_stellar_sphere Y
:= sorry

lemma stellar_equiv_preserves_not_stellar_sphere
    (X Y : simplicial_complex ℕ)
  : ¬is_stellar_sphere X → X ≅ₛₜ Y → ¬is_stellar_sphere Y
:= sorry

lemma stellar_equiv_preserves_stellar_n_ball
    (X Y : simplicial_complex ℕ)
    (n : ℤ)
  : is_stellar_n_ball X n → X ≅ₛₜ Y → is_stellar_n_ball Y n
:= sorry

lemma stellar_equiv_preserves_not_stellar_n_ball
    (X Y : simplicial_complex ℕ)
    (n : ℤ)
  : ¬is_stellar_n_ball X n → X ≅ₛₜ Y → ¬is_stellar_n_ball Y n
:= sorry

lemma stellar_equiv_preserves_stellar_ball
    (X Y : simplicial_complex ℕ)
  : is_stellar_ball X → X ≅ₛₜ Y → is_stellar_ball Y
:= sorry

lemma stellar_equiv_preserves_not_stellar_ball
    (X Y : simplicial_complex ℕ)
  : ¬is_stellar_ball X → X ≅ₛₜ Y → ¬is_stellar_ball Y
:= sorry

@[simp]
def is_stellar_n_manifold
    (X : simplicial_complex ℕ)
    (n : ℕ)
  : Prop
:= ∀ x : ℕ,
    ({x} ∈ X.simplices) →
      is_stellar_n_sphere (Lk(X, {x}) (by assumption)) (n - 1) ∨
      is_stellar_n_ball (Lk(X, {x}) (by assumption)) (n - 1)

structure stellar_manifold
:= mk :: (complex : simplicial_complex ℕ)
         (dim : ℕ)
         (is_manifold : is_stellar_n_manifold complex dim)

lemma simplicial_iso_preserves_stellar_mfd
    (X Y : simplicial_complex ℕ)
    (n : ℕ)
  : is_stellar_n_manifold X n → X ≅ Y → is_stellar_n_manifold Y n
:= sorry

lemma simplex_dim_le_manifold_dim
    (X : stellar_manifold)
    (s : finset ℕ)
    (s_in_X : s ∈ X.complex.simplices)
  : dim s ≤ X.dim
:= sorry

lemma manifold_dim_sub_simplex
    (X : stellar_manifold)
    (s : finset ℕ)
    (s_in_X : s ∈ X.complex.simplices)
  : -1 ≤ ↑(X.dim) - dim s - 1
:= begin
  have H := simplex_dim_le_manifold_dim X s s_in_X,
  omega,
end

/-
# Boundary of a Stellar Manifold
-/

-- Boundary of a complex is the simplices whose
-- link is not a sphere.
-- noncomputable
def simplicial_complex_boundary
    (X : simplicial_complex ℕ)
  : simplicial_complex ℕ
:= simplicial_complex.mk
    ({s ∈ X.simplices \ {∅} | s ∈ X.simplices → ¬is_stellar_sphere (Lk(X, s) (by { assumption, }))} ∪ {∅})
    (begin
      rw [set.nonempty_coe_sort, set.nonempty_def],
      use ∅,
      rw [set.mem_union, set.mem_sep_iff],
      right,
      simp,
    end)
    (sorry)

-- Computability requires proof that is_stellar_sphere is decidable.
-- So, we assume the noncomputable finite instance on X.
noncomputable
instance simplicial_complex_boundary.fintype
    (X : simplicial_complex ℕ) [finite X.simplices]
  : fintype (simplicial_complex_boundary X).simplices
:= begin
  simp only[simplicial_complex_boundary, simplicial_complex.simplices],

  have : {s ∈ X.simplices \ {∅} | s ∈ X.simplices → ¬is_stellar_sphere (Lk(X, s) (by { assumption }))}.finite, from
  begin
    apply set.finite.sep,
    apply set.finite.diff,
    rw [←set.finite_coe_iff],
    assumption,
  end,

  apply set.finite.fintype,
  apply set.finite.union,
  assumption,

  simp,
end

lemma simplicial_complex_boundary_iso
    (X Y : simplicial_complex ℕ)
  : X ≅ Y → simplicial_complex_boundary X ≅ simplicial_complex_boundary Y
:= sorry

lemma simplicial_complex_boundary_subcomplex
    (X : simplicial_complex ℕ)
    (s : finset ℕ)
    (s_in_bd_X : s ∈ (simplicial_complex_boundary X).simplices)
  : s ∈ X.simplices
:= sorry

lemma simplicial_complex_boundary_subcomplex_vertices
    (X : simplicial_complex ℕ)
    (x : ℕ)
    (x_in_X_bd : x ∈ vertices (simplicial_complex_boundary X))
  : x ∈ vertices X
:= sorry

lemma boundary_subcomplex_simplicial_complex_vertices
    (X : simplicial_complex ℕ)
    (x : ℕ)
    (x_nin_X : x ∉ vertices X)
  : x ∉ vertices (simplicial_complex_boundary X)
:= begin
  revert x_nin_X,
  contrapose,
  simp,
  apply simplicial_complex_boundary_subcomplex_vertices,
end

/-
# Closed Stellar Manifolds
-/

def stellar_manifold.closed
    (M : stellar_manifold)
  : Prop
:= ∀ s : finset ℕ, (s ∈ M.complex.simplices) → is_stellar_sphere (Lk(M.complex, s) (by assumption))

/-
# Properties of Stellar Balls/Spheres
-/

lemma link_zero_disk_empty
    (x : ℕ)
    (x_in_disk : {x} ∈ D(0).simplices)
  : Lk(D(0), {x}) x_in_disk ≅ @empty_sc ℕ
:= begin
  apply simplicial_iso_preserves_equiv,
  simp only[link, stellar_n_disk, empty_sc, simplicial_complex.simplices],
  simp only[stellar_n_disk] at x_in_disk,

  have H : 0 = int.of_nat 0, by tauto,
  rw [H] at *,
  dsimp only [stellar_n_disk] at *,

  rw [set.ext_iff],
  intro s,
  split,

  intro s_in_link,
  rw [set.mem_sep_iff] at s_in_link,
  choose s_in_power xs_in_power xs_empty using s_in_link,
  rw [finset.mem_coe] at *,
  rw [finset.mem_powerset] at *,
  have H_range : finset.range (0 + 1) = {0}, by tauto,
  rw [H_range] at *,
  have Hx_0 : {x} = {0}, by finish,
  rw [finset.singleton_inj] at Hx_0,
  rw [Hx_0] at *,
  have : s = ∅ ∨ s = {0}, by finish,
  have Hs_empty : s = ∅, by finish,
  rw [set.mem_singleton_iff],
  assumption,

  intro s_empty,
  rw [set.mem_singleton_iff] at s_empty,
  rw [set.mem_sep_iff],
  rw [finset.mem_coe, finset.mem_powerset] at x_in_disk,
  have H_range : finset.range (0 + 1) = {0}, by tauto,
  rw [H_range, finset.singleton_subset_iff, finset.mem_singleton] at x_in_disk,
  split,

  rw [finset.mem_coe, s_empty],
  apply finset.empty_mem_powerset,
  split,

  rw [finset.mem_coe, s_empty, x_in_disk, finset.union_empty, H_range],
  apply finset.mem_powerset_self,

  rw [s_empty, x_in_disk, finset.inter_empty],
end

lemma link_disk_iso_disk
    (n x : ℕ)
    (x_in_disk : {x} ∈ D(n + 1).simplices)
  : Lk(D(n + 1), {x}) x_in_disk ≅ D(n)
:= begin
  unfold is_simplicially_iso,
  set m := ↑n + 1,

  have Hn_cast : ↑n = int.of_nat n, by tauto,
  have Hm_cast : ↑m = int.of_nat m, by tauto,

  let f : ℕ → ℕ := λ i : ℕ, if (i < x) then i else (i - 1),
  have f_simpl : is_simplicial_map (Lk(D(m), {x}) x_in_disk) D(n) f, from
  begin
    sorry
    -- unfold is_simplicial_map,
    -- intros s s_in_link,
    -- simp only[link, stellar_n_disk, simplicial_complex.simplices] at x_in_disk s_in_link ⊢,
    -- rw [set.mem_sep_iff] at s_in_link,
    -- choose s_in_power xs_in_power xs_empty using s_in_link,
    -- -- TODO: simplify match
    -- rw [finset.mem_coe, finset.mem_powerset, finset.subset_iff] at *,
    -- intros y y_in_img,
    -- rw [finset.mem_image] at y_in_img,
    -- choose b Hb fb_eq_y using y_in_img,
    -- specialize s_in_power Hb,
    -- have Hbs : b ∈ {x} ∪ s, by { apply finset.mem_union_right, assumption },
    -- specialize xs_in_power Hbs,
    -- have Hx : x ∈ {x}, by { rw [finset.mem_singleton], },
    -- specialize x_in_disk Hx, 
    -- simp only[f] at fb_eq_y,
    -- revert fb_eq_y,
    -- split_ifs,

    -- intro b_eq_y,
    -- rw [finset.mem_range] at *,
    -- subst b,
    -- have Hmn : n + 1 = m, by tauto,
    -- rw [Hmn] at *,
    -- omega,

    -- intro b_pred_eq_y,
    -- rw [finset.mem_range] at *,
    -- subst y,
    -- have Hmn : n + 1 = m, by tauto,
    -- rw [Hmn] at *,
    -- omega,
  end,

  let g : ℕ → ℕ := λ i : ℕ, if (i < x) then i else i + 1,
  have g_simpl : is_simplicial_map D(n) (Lk(D(m), {x}) x_in_disk) g, from
  begin
    sorry
    -- unfold is_simplicial_map,
    -- intros s s_in_disk,
    -- simp only[link, stellar_n_disk, simplicial_complex.simplices] at x_in_disk s_in_disk ⊢,
    -- rw [set.mem_sep_iff],
    -- repeat { rw [finset.mem_coe, finset.mem_powerset, finset.subset_iff] at *, },
    -- split,

    -- intros y y_in_img,
    -- rw [finset.mem_image] at y_in_img,
    -- choose a Ha ga_eq_x using y_in_img,
    -- specialize s_in_disk Ha,
    -- have Hx : x ∈ {x}, by { rw [finset.mem_singleton] },
    -- specialize x_in_disk Hx,
    -- rw [finset.mem_range] at *,
    -- revert ga_eq_x,
    -- simp only[g],
    -- split_ifs,

    -- intro a_eq_y,
    -- subst y,
    -- omega,

    -- intro a_succ_eq_y,
    -- subst y,
    -- have Hmn : n + 1 = m, by tauto,
    -- rw [Hmn] at *,
    -- omega,

    -- split,
    -- intros y y_in_ximg,
    -- rw [finset.mem_union] at y_in_ximg,
    -- cases y_in_ximg,

    -- specialize x_in_disk y_in_ximg,
    -- assumption,

    -- rw [finset.mem_image] at y_in_ximg,
    -- choose a Ha ga_eq_y using y_in_ximg,
    -- specialize s_in_disk Ha,
    -- rw [finset.mem_range] at *,
    -- simp only[g] at ga_eq_y,
    -- revert ga_eq_y,
    -- split_ifs,

    -- intro a_eq_y,
    -- subst y,
    -- have Hmn : n + 1 = m, by tauto,
    -- rw [Hmn] at *,
    -- omega,

    -- intro a_succ_eq_y,
    -- subst y,
    -- have Hmn : n + 1 = m, by tauto,
    -- rw [Hmn] at *,
    -- omega,

    -- apply finset.singleton_inter_of_not_mem,
    -- rw [finset.mem_image],
    -- simp,
    -- intros y y_in_s,
    -- simp only[g],
    -- split_ifs;
    -- omega,
  end,

  let fs : simplicial_map (Lk(D(m), {x}) x_in_disk) D(n) := simplicial_map.mk f f_simpl,
  let gs : simplicial_map D(n) (Lk(D(m), {x}) x_in_disk) := simplicial_map.mk g g_simpl,

  use fs,
  unfold is_simplicial_iso,
  use gs,
  unfold is_inverse_simplicial_iso,
  split,

  { simp only[simplicial_map.comp, simplicial_map.map],
    simp,
    unfold set.eq_on,
    intros y y_in_vert_link,
    simp only[vertices] at y_in_vert_link,
    rw [set.mem_Union] at y_in_vert_link,
    choose s y_in_vert_link using y_in_vert_link,
    rw [set.mem_Union] at y_in_vert_link,
    choose Hs y_in_s using y_in_vert_link,
    
    simp only[simplicial_complex.simplices] at Hs,
    rw [set.mem_inter_iff] at Hs,
    cases Hs with Hs_union Hs_inter,
    rw [set.mem_sep_iff] at Hs_union Hs_inter,
    cases Hs_union with s_in_disk xs_in_disk,
    cases Hs_inter with s_in_disk xs_empty,
    rw [finset.mem_coe] at *,

    have y_nin_xs : y ∉ {x} ∩ s, from
    begin
      rw [xs_empty],
      tauto,
    end,
    rw [finset.mem_inter] at y_nin_xs,
    simp at y_nin_xs,
    have y_ne_x : y ≠ x, from
    begin
      revert y_in_s,
      contrapose,
      tauto,
    end,

    rw [function.comp_apply],
    simp only[f, g],
    split_ifs,
    
    simp,
    
    have : y = x, by omega,
    contradiction,
    
    have : 1 ≤ y, by omega,
    rw [nat.sub_add_cancel],
    simp,
    assumption, },

  { simp only[simplicial_map.comp, simplicial_map.map],
    simp,
    unfold set.eq_on,
    intros y y_in_vert_disk,
    simp only[vertices] at y_in_vert_disk,
    rw [set.mem_Union] at y_in_vert_disk,
    choose s y_in_vert_disk using y_in_vert_disk,
    rw [set.mem_Union] at y_in_vert_disk,
    choose Hs y_in_s using y_in_vert_disk,
    
    simp only [Hn_cast] at Hs,
    simp only[stellar_n_disk, simplicial_complex.simplices] at Hs,
    rw [finset.mem_coe] at *,
    rw [finset.mem_powerset, finset.subset_iff] at Hs,
    specialize Hs y_in_s,
    rw [finset.mem_range] at Hs,
    
    rw [function.comp_apply],
    simp only[f, g],
    split_ifs,
    
    simp,
    
    have : y < x, by omega,
    contradiction,
    
    simp, }
end

-- Lemma 3.2 (1), p.10
lemma stellar_n_ball_is_stellar_mfd
  : ∀ (n : ℕ), is_stellar_n_manifold D(n) n
:= begin
  intro n,
  induction n,

  dsimp only[is_stellar_n_manifold, is_stellar_sphere, is_stellar_ball],
  intros x x_in_disk,
  right,

  apply stellar_equiv_preserves_iso,
  apply link_zero_disk_empty,

  dsimp only[is_stellar_n_manifold, is_stellar_sphere, is_stellar_ball],
  intros x x_in_disk,
  right,

  apply stellar_equiv_preserves_iso,
  have H : D(↑(n_n.succ) - 1) = D(↑n_n), by simp,
  rw [H],
  apply link_disk_iso_disk n_n x x_in_disk,
end

-- TODO: Finish lemma.
lemma link_zero_sphere_empty
    (x : ℕ)
    (x_in_sphere : {x} ∈ S(0).simplices)
  : Lk(S(0), {x}) x_in_sphere ≅ @empty_sc ℕ
:= begin
  apply simplicial_iso_preserves_equiv,
  simp only[link, stellar_n_sphere, empty_sc, simplicial_complex.simplices],
  simp only[stellar_n_sphere, simplicial_complex.simplices] at x_in_sphere,
  rw [set.ext_iff],
  intro s,
  split,

  { intro s_in_link,
    rw [set.mem_sep_iff] at s_in_link,
    choose s_in_power xs_in_power xs_empty using s_in_link,
    have H : 0 = int.of_nat 0, by tauto,
    simp only [H, stellar_n_sphere] at *,
    rw [set.mem_diff] at *,
    
    cases s_in_power with s_in_power s_nin_int,
    cases xs_in_power with xs_in_power xs_nin_int,
    cases x_in_sphere with x_in_power x_nin_int,
    
    rw [finset.mem_coe, finset.mem_powerset] at *,
    rw [set.mem_singleton_iff] at *,
    have H_range : finset.range (0 + 2) = {0, 1}, by tauto,
    rw [H_range] at *,
    have Hx : x ∈ {x}, by { rw [finset.mem_singleton], },
    rw [finset.subset_iff] at x_in_power,
    specialize x_in_power Hx,
    simp at x_in_power,
    cases x_in_power,
    
    subst x,
    have s_sset : s ⊂ {0, 1}, from
    begin
      rw [finset.ssubset_iff_subset_ne],
      split; assumption,
    end,
    have s0_sset : {0} ∪ s ⊂ {0, 1}, from
    begin
      rw [finset.ssubset_iff_subset_ne],
      split; assumption,
    end,
    rw [finset.ssubset_iff_subset_ne] at s0_sset,
    cases s0_sset with s0_subset s0_ne,
    have s0_diff_sset : ({0} ∪ s) \ {0} ⊂ {0, 1} \ {0}, from
    begin
      rw [finset.union_sdiff_left],
      rw [finset.ssubset_iff_subset_ne],
      split,

      apply finset.sdiff_subset_sdiff; tauto,

      simp,
      rw [finset.ext_iff],
      simp, use 1,
      split; simp,

      sorry,
    end,
    all_goals {sorry}, },

  { sorry, }
end

lemma link_sphere_iso_sphere
    (n x : ℕ)
    (x_in_sphere : {x} ∈ S(n + 1).simplices)
  : Lk(S(n + 1), {x}) x_in_sphere ≅ S(n)
:= begin
  unfold is_simplicially_iso,
  set m := ↑n + 1,

  have Hn_cast : ↑n = int.of_nat n, by tauto,
  have Hn_succ_cast : ↑n + 1 = int.of_nat (n + 1), by tauto,

  let f : ℕ → ℕ := λ i : ℕ, if (i < x) then i else (i - 1),
  have f_simpl : is_simplicial_map (Lk(S(m), {x}) x_in_sphere) S(n) f, by sorry,

  let g : ℕ → ℕ := λ i : ℕ, if (i < x) then i else (i + 1),
  have g_simpl : is_simplicial_map S(n) (Lk(S(m), {x}) x_in_sphere) g, by sorry,

  let fs : simplicial_map (Lk(S(m), {x}) x_in_sphere) S(n) := simplicial_map.mk f f_simpl,
  let gs : simplicial_map S(n) (Lk(S(m), {x}) x_in_sphere) := simplicial_map.mk g g_simpl,

  use fs,
  unfold is_simplicial_iso,
  use gs,
  unfold is_inverse_simplicial_iso,
  split,

  { simp only[simplicial_map.comp, simplicial_map.map],
    simp,
    unfold set.eq_on,
    intros y y_in_vert,

    simp only[vertices] at y_in_vert,
    rw [set.mem_Union] at y_in_vert,
    choose s y_in_vert using y_in_vert,
    rw [set.mem_Union] at y_in_vert,
    choose s_in_link y_in_s using y_in_vert,
    
    simp only[simplicial_complex.simplices] at s_in_link,
    rw [set.mem_inter_iff] at s_in_link,
    cases s_in_link with s_in_union s_in_inter,
    rw [set.mem_sep_iff] at s_in_union s_in_inter,
    cases s_in_union with s_in_sphere xs_in_sphere,
    cases s_in_inter with s_in_sphere xs_empty,
    
    simp only [Hn_succ_cast, stellar_n_sphere] at *,
    simp only [Hn_cast, stellar_n_sphere] at *,
    rw [set.mem_diff] at *,
    cases s_in_sphere with s_in_power s_nin_int,
    cases xs_in_sphere with xs_in_power xs_nin_int,
    cases x_in_sphere with x_in_power x_nin_int,
    rw [finset.mem_coe] at *,
    
    rw [finset.mem_powerset, finset.subset_iff] at *,
    specialize s_in_power y_in_s,
    have Hx : x ∈ {x}, by { rw [finset.mem_singleton] },
    specialize x_in_power Hx,
    have Hxs : x ∈ {x} ∪ s, by { rw [finset.mem_union], left, apply Hx },
    specialize xs_in_power Hxs,
    rw [finset.mem_range] at *,

    have y_nin_xs : y ∉ {x} ∩ s, from
    begin
      rw [xs_empty],
      tauto,
    end,
    rw [finset.mem_inter] at y_nin_xs,
    simp at y_nin_xs,
    have y_ne_x : y ≠ x, from
    begin
      revert y_in_s,
      contrapose,
      tauto,
    end,
    
    rw [function.comp_apply],
    simp only[f, g],
    split_ifs,
    
    simp,
    
    have : y = x, by omega,
    contradiction,
    
    have : 1 ≤ y, by omega,
    rw [nat.sub_add_cancel],
    simp,
    assumption, },

  { simp only[simplicial_map.comp, simplicial_map.map],
    simp,
    unfold set.eq_on,
    intros y y_in_vert,

    simp only[vertices] at y_in_vert,
    rw [set.mem_Union] at y_in_vert,
    choose s y_in_vert using y_in_vert,
    rw [set.mem_Union] at y_in_vert,
    choose s_in_sphere y_in_s using y_in_vert,
    
    simp only [Hn_succ_cast] at x_in_sphere,
    simp only [Hn_cast] at s_in_sphere,
    simp only [stellar_n_sphere, simplicial_complex.simplices] at s_in_sphere x_in_sphere,
    rw [set.mem_diff] at s_in_sphere x_in_sphere,
    cases s_in_sphere with s_in_power s_nin_int,
    cases x_in_sphere with x_in_power x_nin_int,
    rw [finset.mem_coe] at *,
    
    rw [finset.mem_powerset, finset.subset_iff] at *,
    specialize s_in_power y_in_s,
    have Hx : x ∈ {x}, by { rw [finset.mem_singleton] },
    specialize x_in_power Hx,
    rw [finset.mem_range] at *,

    rw [function.comp_apply],
    simp only[f, g],
    split_ifs,

    simp,

    have : y < x, by omega,
    contradiction,

    simp, },
end

-- Lemma 3.2 (2), p.10
-- TODO: Prove maps are simplicial. Should be almost identical to disk.
lemma stellar_n_sphere_is_stellar_mfd
  : ∀ (n : ℕ), is_stellar_n_manifold S(n) n
:= begin
  intro n,
  induction n;
  unfold is_stellar_n_manifold;
  intros x x_in_sphere;
  left,

  unfold is_stellar_n_sphere,
  have H_neg_one : S(-1) = empty_sc, from
  begin
    have H1_cast : -1 = int.neg_succ_of_nat 0, by tauto,
    simp only [H1_cast, stellar_n_sphere],
  end,
  have HS_0 : S(↑0 - 1) = S(-1), by simp,
  rw [HS_0, H_neg_one],
  apply stellar_equiv_preserves_iso,
  apply link_zero_sphere_empty,

  unfold is_stellar_n_sphere,

  apply stellar_equiv_preserves_iso,
  have HS_n : S(↑(n_n.succ) - 1) = S(n_n), by simp,
  rw [HS_n],
  apply link_sphere_iso_sphere,
end

-- Lemma 3.3 (1), p.12
lemma join_stellar_balls
    (X Y : simplicial_complex ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
    (m n : ℤ)
  : -1 ≤ m → -1 ≤ n →
      is_stellar_n_ball X m →
        is_stellar_n_ball Y n →
          is_stellar_n_ball (φ[X ⋆ Y]) (m + n + 1)
:= begin
  intros m_geq_neg_one n_geq_neg_one X_stellar_ball Y_stellar_ball,
  unfold is_stellar_n_ball at *,

  apply stellar_equiv_trans (φ[X ⋆ Y]) (φ[D(m) ⋆ D(n)]),
  apply stellar_equiv_iso (X ⋆ Y) (D(m) ⋆ D(n)),
  apply φ.iso_onto_image,
  apply φ.iso_onto_image,
  apply @join_comm_stellar_equiv _ _ _ _ _ _ φ;
  assumption,

  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_trans (φ[D(m) ⋆ D(n)]) (D(m) ⋆ D(n)),
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,
  apply join_stellar_disk,
end

-- Lemma 3.3 (2), p.12
lemma join_stellar_spheres
    (X Y : simplicial_complex ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
    (m n : ℕ)
  : is_stellar_n_sphere X m → is_stellar_n_sphere Y n → is_stellar_n_sphere (φ[X ⋆ Y]) (m + n + 1)
:= begin
  intros X_stellar_sphere Y_stellar_sphere,
  unfold is_stellar_n_sphere at *,

  apply stellar_equiv_trans (φ[X ⋆ Y]) (φ[S(m) ⋆ S(n)]),
  apply stellar_equiv_iso (X ⋆ Y) (S(m) ⋆ S(n)),
  apply φ.iso_onto_image,
  apply φ.iso_onto_image,
  apply @join_comm_stellar_equiv _ _ _ _ _ _ φ;
  assumption,

  apply join_stellar_sphere,
end

lemma join_stellar_spheres_gen
    (X Y : simplicial_complex ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
  : is_stellar_sphere X → is_stellar_sphere Y → is_stellar_sphere (φ[X ⋆ Y])
:= begin
  intros X_sphere Y_sphere,
  unfold is_stellar_sphere at *,
  choose m m_bound X_m_sphere using X_sphere,
  choose n n_bound Y_n_sphere using Y_sphere,

  induction m;
  induction n,

  -- m, n ≥ 0
  use (m + n + 1), split,
  apply @int.le_trans _ (m + n),
  apply @int.le_trans _ m,
  tauto, simp, simp,
  apply join_stellar_spheres;
  assumption,

  -- m ≥ 0, n < 0
  use m, split, tauto,
  simp only [stellar_n_sphere] at Y_n_sphere,
  apply stellar_equiv_trans (φ[X ⋆ Y]) (φ[X ⋆ empty_sc]),

  apply stellar_equiv_iso (X ⋆ Y) (X ⋆ empty_sc),
  apply φ.iso_onto_image,
  apply φ.iso_onto_image,
  apply simplicial_join_stellar_equiv_right,
  assumption,

  apply stellar_equiv_trans (φ[X ⋆ empty_sc]) X,
  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_trans (φ[X ⋆ empty_sc]) (X ⋆ empty_sc),
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,
  apply simplicial_iso_trans (X ⋆ empty_sc) X,
  apply simplicial_join_id_left,
  apply simplicial_iso_refl,
  assumption,

  -- m < 0, n ≥ 0
  use n, split, tauto,
  simp only [stellar_n_sphere] at X_m_sphere,
  apply stellar_equiv_trans (φ[X ⋆ Y]) (φ[empty_sc ⋆ Y]),

  apply stellar_equiv_iso (X ⋆ Y) (empty_sc ⋆ Y),
  apply φ.iso_onto_image,
  apply φ.iso_onto_image,
  apply simplicial_join_stellar_equiv_left,
  assumption,

  apply stellar_equiv_trans (φ[empty_sc ⋆ Y]) Y,
  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_trans (φ[empty_sc ⋆ Y]) (empty_sc ⋆ Y),
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,
  apply simplicial_iso_trans (empty_sc ⋆ Y) Y,
  apply simplicial_join_id_right,
  apply simplicial_iso_refl,
  assumption,

  -- m, n < 0
  use (-[1+ 0]), split, tauto,
  simp only [stellar_n_sphere] at *,
  apply stellar_equiv_trans (φ[X ⋆ Y]) (φ[empty_sc ⋆ empty_sc]),

  apply stellar_equiv_iso (X ⋆ Y) (empty_sc ⋆ empty_sc),
  apply φ.iso_onto_image,
  apply φ.iso_onto_image,
  apply simplicial_join_stellar_equiv;
  assumption,

  apply stellar_equiv_iso empty_sc empty_sc,

  apply simplicial_iso_trans empty_sc (empty_sc ⋆ empty_sc),
  rw [simplicial_iso_symm],
  apply simplicial_join_id_left,
  apply φ.iso_onto_image,
  apply simplicial_iso_refl,

  refl,
end

lemma stellar_subdiv_disk
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
    (n x : ℕ)
    (x_nin_disk : x ∉ vertices D(n + 1))
  : σ(D(n + 1), finset.range(n + 2); x, φ; sorry, sorry, x_nin_disk) ≅ D(0) ⋆ S(n)
:= sorry

-- Lemma 3.3 (3), p.12
lemma join_stellar_ball_and_sphere
    (X Y : simplicial_complex ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
    (m n : ℤ)
  : 0 ≤ m → -1 ≤ n →
      is_stellar_n_ball X m →
        is_stellar_n_sphere Y n →
          is_stellar_n_ball (φ[X ⋆ Y]) (m + n + 1)
:= begin
  intros m_geq_zero n_geq_neg_one X_stellar_ball Y_stellar_sphere,
  unfold is_stellar_n_sphere at Y_stellar_sphere,
  unfold is_stellar_n_ball at *,

  induction m;
  induction n,

  -- m, n ≥ 0
  apply stellar_equiv_trans (φ[X ⋆ Y]) (φ[D(m) ⋆ S(n)]),
  apply stellar_equiv_iso (X ⋆ Y) (D(m) ⋆ S(n)),
  apply φ.iso_onto_image,
  apply φ.iso_onto_image,
  apply @join_comm_stellar_equiv _ _ _ _ _ _ φ;
  assumption,

  apply stellar_equiv_trans (φ[D(m) ⋆ S(n)]) (φ[φ[D(↑m - 1) ⋆ D(0)] ⋆ S(n)]),
  apply stellar_equiv_iso (D(m) ⋆ S(n)) (φ[D(↑m - 1) ⋆ D(0)] ⋆ S(n)),
  apply φ.iso_onto_image,
  apply φ.iso_onto_image,
  apply stellar_equiv_preserves_iso,
  apply simplicial_join_iso_left,
  rw [simplicial_iso_symm],
  apply simplicial_iso_trans (φ[D(↑m - 1) ⋆ D(0)]) (D(↑m - 1) ⋆ D(0)),
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,

  have H1 : D(↑m - 1) ⋆ D(0) ≅ D(↑m - 1 + 0 + 1), by { apply join_stellar_disk },
  have H2 : D(↑m - 1 + 0 + 1) ≅ D(↑m), from
  begin
    apply simplicial_iso_preserves_equiv,
    simp,
  end,
  apply simplicial_iso_trans (D(↑m - 1) ⋆ D(0)) D(↑m - 1 + 0 + 1);
  assumption,

  apply stellar_equiv_trans (φ[φ[D(↑m - 1) ⋆ D(0)] ⋆ S(n)]) (φ[D(↑m - 1) ⋆ φ[D(0) ⋆ S(n)]]),
  apply stellar_equiv_iso (φ[D(↑m - 1) ⋆ D(0)] ⋆ S(n)) (D(↑m - 1) ⋆ φ[D(0) ⋆ S(n)]),
  apply φ.iso_onto_image,
  apply φ.iso_onto_image,
  apply stellar_equiv_preserves_iso,
  apply simplicial_join_assoc,

  apply stellar_equiv_trans (φ[D(↑m - 1) ⋆ φ[D(0) ⋆ S(n)]]) (φ[D(↑m - 1) ⋆ D(n + 1)]),
  apply stellar_equiv_iso (D(↑m - 1) ⋆ φ[D(0) ⋆ S(n)]) (D(↑m - 1) ⋆ D(n + 1)),
  apply φ.iso_onto_image,
  apply φ.iso_onto_image,
  apply simplicial_join_stellar_equiv_right,
  apply relation.refl_trans_gen.single,

  unfold stellar_move,
  intro ψ,
  left,

  use (finset.range (n + 2)),
  have Ht : finset.range (n + 2) ∈ D(n + 1).simplices, from
  begin
    apply stellar_disk_range,
    simp,
  end,
  use Ht,
  
  have Ht_ne : nonempty ↥(finset.range (n + 2)), from
  begin
    rw [finset.nonempty_coe_sort, finset.nonempty_range_iff],
    simp,
  end,
  use Ht_ne,

  use (n + 2),
  have Hy : n + 2 ∉ vertices D(n + 1), from
  begin
    unfold vertices,
    simp only [set.mem_Union, not_exists],
    intros x x_in_disk,
    have Hn : ↑n + 1 = int.of_nat (n + 1), by tauto,
    simp only [Hn, stellar_n_disk] at x_in_disk,

    rw [finset.mem_coe] at *,
    rw [finset.mem_powerset] at x_in_disk,

    revert x_in_disk,
    contrapose,
    intro n_in_x,
    simp at n_in_x,
    simp only [finset.subset_iff, not_forall],
    use (n + 2), split, assumption,
    rw [finset.mem_range],
    simp,
  end,
  use Hy,

  apply simplicial_iso_trans (φ[D(0) ⋆ S(n)]) (D(0) ⋆ S(n)),
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,
  rw [simplicial_iso_symm],
  apply stellar_subdiv_disk,

  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_trans (φ[D(↑m - 1) ⋆ D(↑n + 1)]) (D(↑m - 1) ⋆ D(n + 1)),
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,

  apply simplicial_iso_trans (D(↑m - 1) ⋆ D(n + 1)) D(↑m - 1 + (n + 1) + 1),
  apply join_stellar_disk,

  apply simplicial_iso_trans D(↑m - 1 + (n + 1) + 1) D(↑m + n + 1),
  apply simplicial_iso_preserves_equiv,
  simp,
  refl,

  -- m ≥ 0, n < 0
  have n_neg_one : -1 = -[1+ n], from
  begin
    rw [le_iff_eq_or_lt] at n_geq_neg_one,
    cases n_geq_neg_one,
    assumption,
    rw [int.lt_iff_add_one_le] at n_geq_neg_one,
    simp only [add_left_neg, int.neg_succ_not_nonneg] at n_geq_neg_one,
    contradiction,
  end,
  rw [←n_neg_one] at Y_stellar_sphere ⊢,

  have H_rw : int.of_nat m + -1 + 1 = m, by simp,
  rw [H_rw],

  apply stellar_equiv_trans (φ[X ⋆ Y]) (φ[D(m) ⋆ S(-1)]),
  apply stellar_equiv_iso (X ⋆ Y) (D(m) ⋆ S(-1)),
  apply φ.iso_onto_image,
  apply φ.iso_onto_image,
  apply simplicial_join_stellar_equiv,
  assumption,
  assumption,

  have H_rw_neg_one : -1 = -[1+ 0], by tauto,
  simp only [H_rw_neg_one, stellar_n_sphere],
  apply stellar_equiv_preserves_iso,
  rw [simplicial_iso_symm],
  apply simplicial_iso_trans D(m) (D(m) ⋆ empty_sc),
  rw [simplicial_iso_symm],
  apply simplicial_join_id_left,
  apply φ.iso_onto_image,

  -- m < 0, n ≥ 0
  have H_contra := int.neg_succ_lt_zero m,
  rw [←not_lt] at m_geq_zero,
  contradiction,

  -- m, n < 0
  have H_contra := int.neg_succ_lt_zero m,
  rw [←not_lt] at m_geq_zero,
  contradiction,
end

-- Proposition 3.4 (1), p.13
lemma stellar_link_is_stellar_ball_or_sphere
    (X : stellar_manifold)
    (s : finset ℕ)
    (s_in_X : s ∈ X.complex.simplices)
  : 0 ≤ dim s →
      is_stellar_n_sphere (Lk(X.complex, s) s_in_X) (X.dim - (dim s) - 1)
        ∨ is_stellar_n_ball (Lk(X.complex, s) s_in_X) (X.dim - (dim s) - 1)
:= begin
  intro s_nontriv,
  induction X_dim : X.dim generalizing X s,

  -- 0-dim case
  rw [←X_dim],
  have Hk : dim s = 0, from
  begin
    sorry,
  end,
  rw [Hk],

  have Hs : ∃ x : ℕ, s = {x}, by { rw [←dim_zero_iff_vertex], assumption },
  choose x s_vertex using Hs,
  simp only [s_vertex],
  rw [s_vertex] at s_in_X,
  apply X.is_manifold x s_in_X,

  -- n-dim case, n > 0
  by_cases (dim s = 0),
  
  -- s is vertex
  rw [←X_dim],
  have Hs : ∃ x : ℕ, s = {x}, by { rw [←dim_zero_iff_vertex], assumption },
  choose x s_vertex using Hs,
  simp only [h, tsub_zero],
  simp only [s_vertex] at s_in_X ⊢,
  apply X.is_manifold x s_in_X,

  -- s is larger simplex, i.e. face or edge
  rw [←X_dim],
  have Hs_nonzero : 0 < dim s, by omega,
  have Hx : ∃ (x ∈ s) (t : finset ℕ), t = s \ {x}, by { apply simplex_decomp, assumption },
  choose x x_in_s t t_decomp_s using Hx,

  let x_in_L : {x} ∈ X.complex.simplices := by { apply X.complex.subset_closed s, assumption, rw [finset.singleton_subset_iff], assumption, },
  let L := Lk(X.complex, {x}) x_in_L,

  let sx_in_L : s \ {x} ∈ L.simplices := by { apply face_in_link_of_complement },
  let K := Lk(L, s \ {x}) sx_in_L,

  suffices : is_stellar_n_sphere K (↑(X.dim) - dim s - 1)
              ∨ is_stellar_n_ball K (↑(X.dim) - dim s - 1), from
  begin
    cases this,

    left,
    apply stellar_equiv_preserves_stellar_n_sphere K,
    assumption,
    apply stellar_equiv_preserves_iso,
    rw [simplicial_iso_symm],
    apply link_of_face_complement,

    right,
    apply stellar_equiv_preserves_stellar_n_ball K,
    assumption,
    apply stellar_equiv_preserves_iso,
    rw [simplicial_iso_symm],
    apply link_of_face_complement,
  end,

  have L_mfd : is_stellar_n_manifold L (↑(X.dim) - 1), from
  begin
    sorry,
  end,
  let Lm := stellar_manifold.mk L (↑(X.dim) - 1) L_mfd,
  have Lm_dim : Lm.dim = n, by { simp [X_dim], },

  specialize ih Lm,
  specialize ih (s \ {x}),
  have HL : Lm.complex = L, by simp,
  rw [HL] at ih,
  specialize ih sx_in_L,
  specialize ih (by { apply simplex_decomp_dim; assumption, }),
  specialize ih Lm_dim,

  have Hn : ↑(X.dim) - dim s - 1 = ↑n - dim (s \ {x}) - 1, from
  begin
    simp only [@simplex_decomp_dim_eq _ _ s x x_in_s Hs_nonzero, X_dim],
    simp only [dim, nat.cast_succ],
    ring,
  end,
  simp only [K, Hn],
  assumption,
end

lemma stellar_sphere_and_ball_iff_empty
    (X : simplicial_complex ℕ)
  : is_stellar_sphere X ∧ is_stellar_ball X ↔ X ≅ @empty_sc ℕ
:= sorry

lemma not_stellar_sphere_imp_nonempty
    (X : simplicial_complex ℕ)
  : ¬is_stellar_sphere X → ¬X ≅ @empty_sc ℕ
:= begin
  intro X_not_sphere,
  have H_contra : ¬is_stellar_sphere X ∨ ¬is_stellar_ball X, from
  begin
    left, assumption,
  end,
  contrapose H_contra,
  revert H_contra,
  simp only [not_or_distrib, not_not],

  have H := stellar_sphere_and_ball_iff_empty X,
  cases H with H_oif H_if,
  assumption,
end

lemma not_stellar_ball_imp_nonempty
    (X : simplicial_complex ℕ)
  : ¬is_stellar_ball X → ¬X ≅ @empty_sc ℕ
:= begin
  intro X_not_ball,
  have H_contra : ¬is_stellar_sphere X ∨ ¬is_stellar_ball X, from
  begin
    right, assumption,
  end,
  contrapose H_contra,
  revert H_contra,
  simp only [not_or_distrib, not_not],

  have H := stellar_sphere_and_ball_iff_empty X,
  cases H with H_oif H_if,
  assumption,
end

lemma link_not_n_sphere_iff_n_ball
    (X : stellar_manifold)
    (s : finset ℕ)
    (s_in_X : s ∈ X.complex.simplices)
    (s_ne : 0 ≤ dim s)
    (link_ne : ¬Lk(X.complex, s) s_in_X ≅ @empty_sc ℕ)
  : ¬is_stellar_n_sphere (Lk(X.complex, s) s_in_X) (X.dim - (dim s) - 1)
      ↔ is_stellar_n_ball (Lk(X.complex, s) s_in_X) (X.dim - (dim s) - 1)
:= begin
  split,

  { intro not_n_sphere,
    have H_cases := stellar_link_is_stellar_ball_or_sphere X s s_in_X s_ne,
    cases H_cases with H_sphere H_ball,
    
    contradiction,
    assumption, },

  { intro n_ball,
    have H_cases := stellar_link_is_stellar_ball_or_sphere X s s_in_X s_ne,
    cases H_cases with H_sphere H_ball,
    
    have H_contra : is_stellar_sphere (Lk(X.complex, s) s_in_X) ∧ is_stellar_ball (Lk(X.complex, s) s_in_X), from
    begin
      split,

      unfold is_stellar_sphere,
      unfold is_stellar_n_sphere at H_sphere,
      use (↑(X.dim) - dim s - 1),
      assumption,

      unfold is_stellar_ball,
      unfold is_stellar_n_ball at n_ball,
      use (↑(X.dim) - dim s - 1),
      assumption,
    end,
    rw [stellar_sphere_and_ball_iff_empty] at H_contra,
    contradiction,
    
    by_cases (is_stellar_n_sphere (Lk(X.complex, s) s_in_X) (↑(X.dim) - dim s - 1)),
    have H_contra : is_stellar_sphere (Lk(X.complex, s) s_in_X) ∧ is_stellar_ball (Lk(X.complex, s) s_in_X), from
    begin
      split,

      unfold is_stellar_sphere,
      unfold is_stellar_n_sphere at h,
      use (↑(X.dim) - dim s - 1),
      assumption,

      unfold is_stellar_ball,
      unfold is_stellar_n_ball at n_ball,
      use (↑(X.dim) - dim s - 1),
      assumption,
    end,
    rw [stellar_sphere_and_ball_iff_empty] at H_contra,
    contradiction,
    
    contradiction, },
end

lemma link_not_sphere_iff_ball
    (X : stellar_manifold)
    (s : finset ℕ)
    (s_in_X : s ∈ X.complex.simplices)
    (s_ne : 0 ≤ dim s)
    (link_ne : ¬Lk(X.complex, s) s_in_X ≅ @empty_sc ℕ)
  : ¬is_stellar_sphere (Lk(X.complex, s) s_in_X) ↔ is_stellar_ball (Lk(X.complex, s) s_in_X)
:= begin
  split,

  { intro not_sphere,
    simp only [is_stellar_sphere, not_exists] at not_sphere,
    specialize not_sphere (↑(X.dim) - dim s - 1),
    
    unfold is_stellar_ball,
    use (↑(X.dim) - dim s - 1),
    
    have H_cases := link_not_n_sphere_iff_n_ball X s s_in_X s_ne link_ne,
    cases H_cases with H_ball H_sphere,
    simp only [is_stellar_n_sphere, is_stellar_n_ball] at H_ball,

    have H_dim := simplex_dim_le_manifold_dim X s s_in_X,
    have H_sphere_dim : -1 ≤ ↑(X.dim) - dim s - 1, by omega,
    specialize not_sphere H_sphere_dim,
    specialize H_ball not_sphere,
    split; assumption, },

  { intro is_ball,
    unfold is_stellar_ball at is_ball,
    choose n n_bound n_ball using is_ball,
    
    apply stellar_equiv_preserves_not_stellar_sphere D(n),
    rotate,
    rw [stellar_equiv_symm],
    assumption,
    
    simp only [is_stellar_sphere, not_exists],
    intro m,
    sorry, },
end

lemma stellar_subdiv_zero_dim_ident
    (X : stellar_manifold)
    (s : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
    (s_in_X : s ∈ X.complex.simplices)
    (x_nin_X : x ∉ vertices X.complex)
  : X.dim = 0 →
      σ(X.complex, s; x, φ; s_ne, s_in_X, x_nin_X) ≅ X.complex
:= sorry

-- Proposition 3.4 (2), p.13
lemma stellar_eq_preserves_stellar_mfd
    (X Y : simplicial_complex ℕ)
    (n : ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
  : is_stellar_n_manifold X n → X ≅ₛₜ Y → is_stellar_n_manifold Y n
:= begin
  intros X_mfd X_eq_Y,
  induction n,

  -- 0-dim case
  unfold is_stellar_n_manifold at *,
  induction X_eq_Y with K L X_eq_K K_move_L,
  assumption,

  intros l l_in_L,
  unfold stellar_move at K_move_L,
  specialize K_move_L φ,
  cases K_move_L with K_subdiv_L K_move_L,

  choose t Ht Ht_ne y Hy K_subdiv_L using K_subdiv_L,
  unfold is_simplicially_iso at K_subdiv_L,
  choose f f_iso using K_subdiv_L,
  unfold is_simplicial_iso at f_iso,
  choose g fg_inv using f_iso,

  have k_in_K : finset.image g.map {l} ∈ K.simplices, from
  begin
    apply g.is_simplicial,
  end,
end

lemma link_not_stellar_sphere_imp_stellar_ball
    (X : stellar_manifold)
    (s : finset ℕ)
    (s_in_X : s ∈ X.complex.simplices)
  : 0 ≤ dim s →
      ¬is_stellar_sphere (Lk(X.complex, s) s_in_X)
        → is_stellar_ball (Lk(X.complex, s) s_in_X)
:= begin
  intros s_nontriv link_not_sphere,

  have X_mfd : is_stellar_n_sphere (Lk(X.complex, s) s_in_X) (X.dim - (dim s) - 1)
                ∨ is_stellar_n_ball (Lk(X.complex, s) s_in_X) (X.dim - (dim s) - 1), from
  begin
    apply stellar_link_is_stellar_ball_or_sphere,
    assumption,
  end,

  cases X_mfd,
  simp only [is_stellar_sphere, not_exists] at link_not_sphere,
  specialize link_not_sphere (↑(X.dim) - dim s - 1),
  specialize link_not_sphere (manifold_dim_sub_simplex X s s_in_X),
  contradiction,

  simp only [is_stellar_ball],
  use (↑(X.dim) - dim s - 1), split,
  apply manifold_dim_sub_simplex X s s_in_X,
  simp only [is_stellar_n_ball] at X_mfd,
  assumption,
end

-- Lemma 3.6, p.16
-- TODO: Unclear why Lk(K, u) ≅ₛₜ D(n). New proof?
lemma boundary_link_comm
    (X : stellar_manifold)
    (s : finset ℕ)
    (s_in_bd_X : s ∈ (simplicial_complex_boundary X.complex).simplices)
  : 0 ≤ dim s → simplicial_complex_boundary (Lk(X.complex, s) (simplicial_complex_boundary_subcomplex X.complex s s_in_bd_X)) ≅ Lk(simplicial_complex_boundary X.complex, s) s_in_bd_X
:= sorry
-- := begin
--   intro s_nontriv,
--   apply simplicial_iso_preserves_equiv,
--   dsimp only [simplicial_complex_boundary, simplicial_complex.simplices],
--   rw [set.ext_iff],
--   intro u,
--   split,

--   { intro s_in_bd,
--     simp only [set.mem_union, set.mem_sep_iff] at s_in_bd,
--     cases s_in_bd with u_in_link u_empty,
--     cases u_in_link with u_in_link_ne link_not_sphere,
--     have u_in_link := u_in_link_ne,
--     cases u_in_link with u_in_link u_ne,
--     specialize link_not_sphere u_in_link,
    
--     simp only [link, simplicial_complex.simplices],
--     simp only [set.mem_sep_iff, set.mem_union],
--     split, left,
    
--     split,
--     rw [set.mem_diff],
--     split,
--     apply link_subcomplex X.complex s u,
--     apply u_in_link,
--     assumption,
    
--     intro u_in_X,
--     simp only [link, set.mem_sep_iff] at u_in_link,
--     choose u_in_X us_in_X us_empty using u_in_link,

--     have s_in_X : s ∈ X.complex.simplices := (boundary_simplex_in_complex X.complex s s_in_bd_X),

--     have X_mfd_u : is_stellar_sphere (Lk(X.complex, u) u_in_X) ∨ is_stellar_ball (Lk(X.complex, u) u_in_X), from
--     begin
--       simp only [is_stellar_sphere, is_stellar_ball],
--       rw [←exists_or_distrib],
--       use (X.dim - dim u - 1),
--       apply stellar_link_is_stellar_ball_or_sphere,
--       simp,
--       change (0 < u.card),
--       rw [finset.card_pos, finset.nonempty_iff_ne_empty],
--       rw [set.mem_singleton_iff] at u_ne,
--       assumption,
--     end,

--     have su_rw : u = (s ∪ u) \ s, from
--     begin
--       symmetry,
--       rw [finset.union_sdiff_left, finset.sdiff_eq_self_iff_disjoint, disjoint.comm, finset.disjoint_iff_inter_eq_empty],
--       assumption,
--     end,

--     have link_rw : Lk(Lk(X.complex, s) s_in_X, u) u_in_link
--                     ≅ Lk(Lk(X.complex, s) s_in_X, (s ∪ u) \ s) (by { rw [←su_rw], assumption }), from
--     begin
--       apply simplicial_iso_preserves_equiv,
--       conv_lhs {
--         congr, congr, skip, rw [su_rw],
--       },
--     end,
    
--     have sphere_rw : Lk(X.complex, s ∪ u) us_in_X ≅ₛₜ Lk(Lk(X.complex, s) s_in_X, u) u_in_link, from
--     begin
--       apply stellar_equiv_preserves_iso,
--       rw [simplicial_iso_symm],
--       apply simplicial_iso_trans
--         (Lk(Lk(X.complex, s) s_in_X, u) u_in_link)
--         (Lk(Lk(X.complex, s) s_in_X, (s ∪ u) \ s) (by { rw [←su_rw], assumption })),
--       assumption,
--       rw [simplicial_iso_symm],
--       apply link_of_face_complement X.complex (s ∪ u) s,
--       apply finset.subset_union_left,
--     end,
    
--     apply stellar_equiv_preserves_not_stellar_sphere (Lk(Lk(X.complex, s) s_in_X, u) u_in_link),
--     assumption,
--     apply stellar_equiv_trans
--       (Lk(Lk(X.complex, s) s_in_X, u) u_in_link)
--       (Lk(X.complex, s ∪ u) us_in_X),
--     rw [stellar_equiv_symm],
--     assumption,
    
--      },

--   {}
-- end

-- Lemma 3.8, p.17
-- TODO: Julian's proof uses a link wrt subcomplex, not simplex.
--       Need to rework either the proof or def.
lemma stellar_ball_boundary_ident
    (X : simplicial_complex ℕ)
    (s : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : is_stellar_ball X →
      s ∉ (simplicial_complex_boundary X).simplices →
        simplicial_complex_boundary (@stellar_subdivision _ _ X s s_ne x s_in_X x_nin_X φ)
          ≅ simplicial_complex_boundary X
:= begin
  intros X_stellar_ball s_nin_bd,
  have s_link_sphere : is_stellar_sphere (Lk(X, s) s_in_X), from
  begin
    simp only [simplicial_complex_boundary] at s_nin_bd,
    simp only [set.mem_union, set.mem_sep_iff] at s_nin_bd,
    finish,
  end,
  sorry,
end

lemma stellar_ball_boundary_comm
    (X : simplicial_complex ℕ)
    (s : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (s_in_bd : s ∈ (simplicial_complex_boundary X).simplices)
  : is_stellar_ball X →
      simplicial_complex_boundary (σ(X, s; x, φ; s_ne, s_in_X, x_nin_X))
        ≅ σ(simplicial_complex_boundary X, s; x, φ; s_ne, s_in_bd, sorry)
:= sorry

lemma disk_boundary_is_sphere
    (n : ℤ)
  : simplicial_complex_boundary D(n + 1) ≅ S(n)
:= sorry

-- TODO: Fill in proofs for boundary non-membership.
--       cf. proof of Cor. 3.12
lemma stellar_equiv_factors_stellar_ball_boundary
    (X Y : simplicial_complex ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
  : is_stellar_ball X → X ≅ₛₜ Y → simplicial_complex_boundary X ≅ₛₜ simplicial_complex_boundary Y
:= begin
  intros X_ball X_eq_Y,
  induction X_eq_Y with K L X_eq_K K_move_L,
  refl,

  have K_ball : is_stellar_ball K, from
  begin
    apply stellar_equiv_preserves_stellar_ball X;
    assumption,
  end,

  have L_ball : is_stellar_ball L, from
  begin
    apply stellar_equiv_preserves_stellar_ball K,
    assumption,
    apply relation.refl_trans_gen.single,
    assumption,
  end,

  apply stellar_equiv_trans
    (simplicial_complex_boundary X)
    (simplicial_complex_boundary K),
  assumption,

  unfold stellar_move at K_move_L,
  specialize K_move_L φ,
  cases K_move_L with L_subdiv_K K_subdiv_L,

  choose t Ht Ht_ne y Hy L_subdiv_K using L_subdiv_K,
  apply stellar_equiv_trans
    (simplicial_complex_boundary K)
    (simplicial_complex_boundary (σ(L, t; y, φ; Ht_ne, Ht, Hy))),
  apply stellar_equiv_preserves_iso,
  apply simplicial_complex_boundary_iso,
  assumption,

  by_cases (t ∈ (simplicial_complex_boundary L).simplices),

  -- t ∈ ∂L case
  rw [stellar_equiv_symm],
  apply stellar_equiv_trans
    (simplicial_complex_boundary L)
    (σ(simplicial_complex_boundary L, t; y, φ; Ht_ne, h, sorry)),
  apply relation.refl_trans_gen.single,
  unfold stellar_move,
  intro ψ,
  right, left,
  use t, use Ht,
  rw [set.mem_singleton_iff],
  change (t ≠ ∅),
  rw [←@finset.nonempty_iff_ne_empty _ t, ←finset.nonempty_coe_sort],
  assumption,

  simp only [simplicial_complex_boundary, simplicial_complex.simplices] at h,
  simp only [set.mem_union, set.mem_sep_iff] at h,
  cases h,

  cases h with t_in_L t_in_bd,
  assumption,

  rw [set.mem_singleton_iff] at h,
  rw [finset.nonempty_coe_sort, finset.nonempty_iff_ne_empty] at Ht_ne,
  contradiction,

  use Ht_ne, use y,
  use sorry,

  rw [stellar_equiv_symm],
  apply stellar_equiv_preserves_iso,
  apply stellar_ball_boundary_comm,
  assumption,

  -- t ∉ ∂L case
  apply stellar_equiv_preserves_iso,
  apply stellar_ball_boundary_ident;
  assumption,

  cases K_subdiv_L with K_subdiv_L K_iso_L,
  choose s Hs Hs_ne x Hx K_subdiv_L using K_subdiv_L,
  rw [stellar_equiv_symm],
  apply stellar_equiv_trans
    (simplicial_complex_boundary L)
    (simplicial_complex_boundary (σ(K, s; x, φ; Hs_ne, Hs, Hx))),
  apply stellar_equiv_preserves_iso,
  apply simplicial_complex_boundary_iso,
  assumption,

  by_cases (s ∈ (simplicial_complex_boundary K).simplices),

  -- s ∈ ∂K case
  rw [stellar_equiv_symm],
  apply stellar_equiv_trans
    (simplicial_complex_boundary K)
    (σ(simplicial_complex_boundary K, s; x, φ; Hs_ne, h, sorry)),
  apply relation.refl_trans_gen.single,
  unfold stellar_move,
  intro ψ,
  right, left,
  use s, use Hs,
  rw [set.mem_singleton_iff],
  change (s ≠ ∅),
  rw [←@finset.nonempty_iff_ne_empty _ s, ←finset.nonempty_coe_sort],
  assumption,

  simp only [simplicial_complex_boundary, simplicial_complex.simplices] at h,
  simp only [set.mem_union, set.mem_sep_iff] at h,
  cases h,

  cases h with s_in_K s_in_bd,
  assumption,

  rw [set.mem_singleton_iff] at h,
  rw [finset.nonempty_coe_sort, finset.nonempty_iff_ne_empty] at Hs_ne,
  contradiction,

  use Hs_ne, use x,
  use sorry,

  rw [stellar_equiv_symm],
  apply stellar_equiv_preserves_iso,
  apply stellar_ball_boundary_comm,
  assumption,

  -- s ∉ ∂K case
  apply stellar_equiv_preserves_iso,
  apply stellar_ball_boundary_ident;
  assumption,

  apply stellar_equiv_preserves_iso,
  apply simplicial_complex_boundary_iso,
  assumption,
end

-- Corollary 3.9, p.17
lemma boundary_of_ball_is_sphere
    (X : simplicial_complex ℕ)
    (n : ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
  : is_stellar_n_ball X (n + 1) → is_stellar_n_sphere (simplicial_complex_boundary X) n
:= begin
  intro X_n_ball,
  unfold is_stellar_n_ball at X_n_ball,
  unfold is_stellar_n_sphere,
  rw [stellar_equiv_symm] at X_n_ball,

  have X_n_ball_ind := X_n_ball,
  induction X_n_ball_ind with K L disk_eq_K K_move_L disk_ih,
  apply stellar_equiv_preserves_iso,
  apply disk_boundary_is_sphere,

  specialize disk_ih disk_eq_K,
  rw [stellar_equiv_symm],
  apply stellar_equiv_trans S(n) (simplicial_complex_boundary K),
  rw [stellar_equiv_symm],
  assumption,
  
  apply stellar_equiv_factors_stellar_ball_boundary,
  apply φ,

  rw [stellar_equiv_symm] at X_n_ball,
  apply stellar_equiv_preserves_stellar_ball L,
  unfold is_stellar_ball,
  use (n + 1), split, sorry,
  assumption,
  rw [stellar_equiv_symm],
  apply relation.refl_trans_gen.single,
  assumption,

  apply relation.refl_trans_gen.single,
  assumption,
end

-- Corollary 3.10, p.17
lemma closed_mfd_empty_boundary
    (X : stellar_manifold)
    (X_closed : X.closed)
  : simplicial_complex_boundary X.complex ≅ @empty_sc ℕ
:= begin
  apply simplicial_iso_preserves_equiv,
  simp only [simplicial_complex_boundary, empty_sc, simplicial_complex.simplices],
  apply set.union_eq_self_of_subset_left,
  rw [set.subset_singleton_iff],

  intros s s_in_bd,
  rw [set.mem_sep_iff, set.mem_diff] at s_in_bd,
  cases s_in_bd with s_in_X s_in_bd,
  cases s_in_X with s_in_X s_ne,
  specialize s_in_bd s_in_X,

  unfold stellar_manifold.closed at X_closed,
  specialize X_closed s,
  specialize X_closed s_in_X,
  contradiction,
end

-- Proposition 3.11 (1), p.18
lemma stellar_ball_boundary_distr_join_union
    (X Y : stellar_manifold)
    (m n : ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
  : is_stellar_n_ball X.complex m →
      is_stellar_n_ball Y.complex n →
        simplicial_complex_boundary (φ[X.complex ⋆ Y.complex]) ≅ (X.complex ⋆ (simplicial_complex_boundary Y.complex)) ∪ ((simplicial_complex_boundary X.complex) ⋆ Y.complex)
:= begin
  intros X_ball Y_ball,
  unfold is_stellar_n_ball at *,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans
    (X.complex ⋆ simplicial_complex_boundary Y.complex ∪ simplicial_complex_boundary X.complex ⋆ Y.complex)
    (φ[X.complex ⋆ simplicial_complex_boundary Y.complex ∪ simplicial_complex_boundary X.complex ⋆ Y.complex]),
  apply φ.iso_onto_image,
  rw [simplicial_iso_symm],

  apply simplicial_iso_preserves_equiv,
  rw [set.ext_iff],
  intro s,
  split,

  { intro s_in_bd,
    simp only [simplicial_complex_boundary, simplicial_complex.simplices] at s_in_bd,
    simp only [set.mem_union, set.mem_sep_iff] at s_in_bd,
    cases s_in_bd,
    
    rotate,
    rw [set.mem_singleton_iff] at s_in_bd,
    rw [s_in_bd],
    apply simplicial_complex_empty_simplex,
    
    cases s_in_bd with s_in_XY s_not_sphere,
    rw [set.mem_diff] at s_in_XY,
    cases s_in_XY with s_in_XY s_ne,
    specialize s_not_sphere s_in_XY,

    simp only [simplicial_image, simplicial_complex.simplices] at s_in_XY,
    simp only [set.mem_set_of] at s_in_XY,
    choose s' s'_in_XY s'_eq_s using s_in_XY,
    
    dsimp only [simplicial_image, simplicial_complex_boundary, simplicial_join, simplicial_union, simplicial_complex.simplices],
    simp only [set.mem_set_of],
    use s', split, rotate, assumption,
    
    simp only [set.mem_union, set.mem_set_of],
    have tu_in_XY := s'_in_XY,
    rw [simplicial_join_mem] at s'_in_XY,
    choose t t_in_X u u_in_Y s'_eq_tu using s'_in_XY,
    rw [s'_eq_tu] at tu_in_XY,
    
    by_cases Ht : t = ∅;
    by_cases Hu : u = ∅,
    
    rw [Ht, Hu] at s'_eq_tu,
    rw [s'_eq_tu] at s'_eq_s,
    simp at s'_eq_s,
    rw [set.mem_singleton_iff] at s_ne,
    finish,
    
    right,
    use t,
    split,
    right,
    rw [set.mem_singleton_iff],
    assumption,
    use u, split, assumption,
    symmetry,
    assumption,
    
    left,
    use t, split, assumption,
    use u,
    split,
    right,
    rw [set.mem_singleton_iff],
    assumption,
    symmetry,
    assumption,
    
    have H_link_sep : ¬is_stellar_sphere (φ[Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y]), from
    begin
      apply stellar_equiv_preserves_not_stellar_sphere (Lk(φ[X.complex ⋆ Y.complex], s) s_in_XY),
      assumption,

      apply stellar_equiv_preserves_iso,
      apply simplicial_iso_trans
        (Lk(φ[X.complex ⋆ Y.complex], s) s_in_XY)
        (Lk(X.complex ⋆ Y.complex, t ⊔ₛ u) tu_in_XY),
      rw [simplicial_iso_symm],
      apply link_iso _ _ _ _ (@simplicial_map.mk _ _ _ (X.complex ⋆ Y.complex) (φ[X.complex ⋆ Y.complex]) φ.coe (by { apply map_is_simplicial_onto_image, })),

      apply coe_is_iso,
      simp only [simplicial_coe.coe],
      rw [←s'_eq_tu],
      assumption,

      apply simplicial_iso_trans
        (Lk(X.complex ⋆ Y.complex, t ⊔ₛ u) tu_in_XY)
        (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y),
      apply join_fact_link,

      apply φ.iso_onto_image,
    end,

    have H_bd_sep : ¬is_stellar_sphere (Lk(X.complex, t) t_in_X) ∨ ¬is_stellar_sphere (Lk(Y.complex, u) u_in_Y), from
    begin
      revert H_link_sep,
      contrapose,

      simp only [not_not, not_or_distrib],
      intros X_and_Y_spheres,
      cases X_and_Y_spheres with X_sphere Y_sphere,
      apply join_stellar_spheres_gen;
      assumption,
    end,
    cases H_bd_sep,
    
    right,
    use t,
    split,
    left,
    rw [set.mem_sep_iff],
    split,
    rw [set.mem_diff],
    split,
    assumption,
    rw [set.mem_singleton_iff],
    assumption,
    intro t_in_X,
    assumption,
    
    use u, split, assumption,
    symmetry,
    assumption,
    
    left,
    use t, split, assumption,
    
    use u,
    split,
    left,
    rw [set.mem_sep_iff],
    split,
    rw [set.mem_diff],
    split,
    assumption,
    rw [set.mem_singleton_iff],
    assumption,
    intro u_in_Y,
    assumption,
    
    symmetry,
    assumption, },

  { intro s_in_union,
    dsimp only [simplicial_complex_boundary, simplicial_image, simplicial_complex.simplices],
    simp only [set.mem_union, set.mem_sep_iff, set.mem_diff, set.mem_set_of],
    
    simp only [simplicial_image, simplicial_complex.simplices] at s_in_union,
    simp only [set.mem_set_of] at s_in_union,
    choose s' s'_in_union s'_eq_s using s_in_union,
    dsimp only [simplicial_union, simplicial_complex_boundary, simplicial_join, simplicial_complex.simplices] at s'_in_union,
    simp only [set.mem_union, set.mem_set_of] at s'_in_union,
    cases s'_in_union with s'_in_bd s'_in_bd,
    
    all_goals {
      choose t t_in_X u u_in_Y tu_eq_s' using s'_in_bd,
      try {
        simp only [set.mem_sep_iff, set.mem_diff] at u_in_Y,
        cases u_in_Y with α_in_bd α_empty,
      },
      try {
        simp only [set.mem_sep_iff, set.mem_diff] at t_in_X,
        cases t_in_X with α_in_bd α_empty,
      },

      -- u ∈ ∂K
      cases α_in_bd with α_in_bd α_not_sphere,
      cases α_in_bd with α_in_K α_ne,
      specialize α_not_sphere α_in_K,
      
      left, split, split,
      use s', split,
      rw [←tu_eq_s', simplicial_join_sep],
      split; assumption,
      assumption,
      rw [set.mem_singleton_iff] at α_ne ⊢,
      rw [←s'_eq_s, ←tu_eq_s', finset.image_eq_empty, simplex_disjoint_empty],
      simp only [not_and_distrib],
      tauto,
      
      -- Lk(φ[X ⋆ Y], s) is not stellar sphere
      intro s''_in_XY_img,
      choose s'' s''_in_XY s''_eq_s using s''_in_XY_img,
      
      try {
        apply stellar_equiv_preserves_not_stellar_sphere
          (φ[Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) α_in_K]),
        have link_K_ne : ¬Lk(Y.complex, u) α_in_K ≅ @empty_sc ℕ, from
        begin
          apply not_stellar_sphere_imp_nonempty,
          assumption,
        end,
        have α_dim : 0 ≤ dim u, by sorry,
      },
      try {
        apply stellar_equiv_preserves_not_stellar_sphere
          (φ[Lk(X.complex, t) α_in_K ⋆ Lk(Y.complex, u) u_in_Y]),
        have link_K_ne : ¬Lk(X.complex, t) α_in_K ≅ @empty_sc ℕ, from
        begin
          apply not_stellar_sphere_imp_nonempty,
          assumption,
        end,
        have α_dim : 0 ≤ dim t, by sorry,
      },
      rw [link_not_sphere_iff_ball _ _ _ α_dim link_K_ne] at α_not_sphere,
      unfold is_stellar_ball at α_not_sphere,
      choose z z_bound link_K_z_ball using α_not_sphere,

      have Hz : 0 ≤ z, from
      begin
        sorry,
      end,
    },

    any_goals {
      apply stellar_equiv_preserves_not_stellar_sphere
        (φ[Lk(X.complex, t) t_in_X ⋆ D(z)])
        (φ[Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) α_in_K]),
      have H_cases := stellar_link_is_stellar_ball_or_sphere X t t_in_X,
    },

    any_goals {
      apply stellar_equiv_preserves_not_stellar_sphere
        (φ[D(z) ⋆ Lk(Y.complex, u) u_in_Y])
        (φ[Lk(X.complex, t) α_in_K ⋆ Lk(Y.complex, u) u_in_Y]),
      have H_cases := stellar_link_is_stellar_ball_or_sphere Y u u_in_Y,
    },
      
    -- s' ∈ X ⋆ ∂Y
    { by_cases (t = ∅),
      
      -- t = ∅
      { apply stellar_equiv_preserves_not_stellar_sphere
          (φ[X.complex ⋆ D(z)]),
        apply stellar_equiv_preserves_not_stellar_sphere
          (φ[D(m) ⋆ D(z)]),
        
        apply stellar_equiv_preserves_not_stellar_sphere
          (D(m + z + 1)),
        simp only [is_stellar_sphere, not_exists],
        intros x x_bound,
        rw [disk_is_sphere_iff_empty],
        simp only [not_and_distrib],
        left,
        simp only [not_lt],
        apply @int.le_trans _ (m + z),
        apply @int.le_trans _ z,
        assumption,
        simp only [le_add_iff_nonneg_left, nat.cast_nonneg],
        simp only [le_add_iff_nonneg_right, zero_le_one],
        
        apply stellar_equiv_preserves_iso,
        rw [simplicial_iso_symm],
        apply simplicial_iso_trans (φ[D(m) ⋆ D(z)]) (D(m) ⋆ D(z)),
        rw [simplicial_iso_symm],
        apply φ.iso_onto_image,
        apply join_stellar_disk,
        
        apply stellar_equiv_iso
          (D(m) ⋆ D(z))
          (X.complex ⋆ D(z)),
        apply φ.iso_onto_image,
        apply φ.iso_onto_image,
        apply simplicial_join_stellar_equiv_left,
        rw [stellar_equiv_symm],
        assumption,
        
        apply stellar_equiv_iso
          (X.complex ⋆ D(z))
          (Lk(X.complex, t) t_in_X ⋆ D(z)),
        apply φ.iso_onto_image,
        apply φ.iso_onto_image,
        apply stellar_equiv_preserves_iso,
        apply simplicial_join_iso_left,
        simp only [h],
        rw [simplicial_iso_symm],
        apply link_ident, },
      
      -- t ≠ ∅ ↔ 0 ≤ dim t
      { have t_dim : 0 ≤ dim t, by sorry,
        -- TODO: Turn into more general lemma.
        have HXt : dim t ≤ X.dim, by sorry,
        specialize H_cases t_dim,
        cases H_cases with link_X_sphere link_X_ball,
        
        -- X ≅ₛₜ S(n)
        apply stellar_equiv_preserves_not_stellar_sphere
          (φ[D(z) ⋆ S(↑(X.dim) - dim t - 1)]),
        apply stellar_equiv_preserves_not_stellar_sphere
          (D(z + (↑(X.dim) - dim t - 1) + 1)),
        simp only [is_stellar_sphere, not_exists],
        intros x x_bound,
        rw [disk_is_sphere_iff_empty],
        simp only [not_and_distrib],
        left,
        simp only [not_lt],
        omega,
        
        have H_join_ball := join_stellar_ball_and_sphere
          D(z) S(↑(X.dim) - dim t - 1) φ
          z (↑(X.dim) - dim t - 1)
          Hz (by {sorry})
          (by {sorry})
          (by {sorry}),
        unfold is_stellar_n_ball at H_join_ball,
        rw [stellar_equiv_symm],
        assumption,
        
        apply stellar_equiv_iso
          (S(↑(X.dim) - dim t - 1) ⋆ D(z))
          (Lk(X.complex, t) t_in_X ⋆ D(z)),
        apply simplicial_iso_trans
          (S(↑(X.dim) - dim t - 1) ⋆ D(z))
          (D(z) ⋆ S(↑(X.dim) - dim t - 1)),
        apply simplicial_join_comm,
        apply φ.iso_onto_image,
        apply φ.iso_onto_image,
        
        apply simplicial_join_stellar_equiv_left,
        unfold is_stellar_n_sphere at link_X_sphere,
        rw [stellar_equiv_symm],
        assumption,
        
        -- X ≅ₛₜ D(n)
        apply stellar_equiv_preserves_not_stellar_sphere
          (φ[D(z) ⋆ D(↑(X.dim) - dim t - 1)]),
        apply stellar_equiv_preserves_not_stellar_sphere
          (D(z + (↑(X.dim) - dim t - 1) + 1)),
        simp only [is_stellar_sphere, not_exists],
        intros x x_bound,
        rw [disk_is_sphere_iff_empty],
        simp only [not_and_distrib],
        left,
        simp only [not_lt],
        omega,
        
        have Hz_neg_one : -1 ≤ z, by omega,
        have H_join_ball := join_stellar_balls
          D(z) D(↑(X.dim) - dim t - 1) φ
          z (↑(X.dim) - dim t - 1)
          Hz_neg_one (by {sorry})
          (by {sorry})
          (by {sorry}),
        unfold is_stellar_n_ball at H_join_ball,
        rw [stellar_equiv_symm],
        assumption,
        
        apply stellar_equiv_iso
          (D(↑(X.dim) - dim t - 1) ⋆ D(z))
          (Lk(X.complex, t) t_in_X ⋆ D(z)),
        apply simplicial_iso_trans
          (D(↑(X.dim) - dim t - 1) ⋆ D(z))
          (D(z) ⋆ D(↑(X.dim) - dim t - 1)),
        apply simplicial_join_comm,
        apply φ.iso_onto_image,
        apply φ.iso_onto_image,
        
        apply simplicial_join_stellar_equiv_left,
        unfold is_stellar_n_ball at link_X_ball,
        rw [stellar_equiv_symm],
        assumption, }, },
      
    { apply stellar_equiv_iso
        (Lk(X.complex, t) t_in_X ⋆ D(z))
        (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) α_in_K),
      apply φ.iso_onto_image,
      apply φ.iso_onto_image,
      
      apply simplicial_join_stellar_equiv_right,
      rw [stellar_equiv_symm],
      assumption, },
      
    { have s'_in_XY : s' ∈ (X.complex ⋆ Y.complex).simplices, from
      begin
        rw [simplicial_join_mem],
        use t, split, assumption,
        use u, split, assumption,
        symmetry,
        assumption,
      end,
      apply stellar_equiv_iso
        (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) α_in_K)
        (Lk(X.complex ⋆ Y.complex, s') s'_in_XY),
      apply φ.iso_onto_image,
      let φs := simplicial_map.mk φ.coe (map_is_simplicial_onto_image (X.complex ⋆ Y.complex) φ.coe φ.injective),
      apply link_iso _ _ _ _ _ _ _ (coe_is_iso _ φ) s'_eq_s,
      
      rw [stellar_equiv_symm],
      apply stellar_equiv_preserves_iso,
      simp only [←tu_eq_s'],
      apply join_fact_link, },
      
      -- u = ∅
    { by_cases (t = ∅),
      
      -- t = ∅
      rw [set.mem_singleton_iff] at α_empty,
      have s'_empty : s' = ∅, from
      begin
        rw [←tu_eq_s', simplex_disjoint_empty],
        split; assumption,
      end,
      rw [s'_empty, finset.image_empty] at s'_eq_s,
      right,
      rw [set.mem_singleton_iff],
      symmetry,
      assumption,
      
      -- t ≠ ∅
      left, split, split,
      use s', split,
      rw [←tu_eq_s', simplicial_join_sep],
      split, assumption,
      rw [set.mem_singleton_iff] at α_empty,
      rw [α_empty],
      apply simplicial_complex_empty_simplex,
      assumption,
      rw [set.mem_singleton_iff],
      rw [←s'_eq_s, ←tu_eq_s', finset.image_eq_empty, simplex_disjoint_empty],
      simp only [not_and_distrib],
      left, assumption,

      intro s''_in_XY,

      have t_dim : 0 ≤ dim t, by sorry,
      -- TODO: Turn into more general lemma.
      have HXt : dim t ≤ X.dim, by sorry,
      have HX_cases := stellar_link_is_stellar_ball_or_sphere X t t_in_X,

      specialize HX_cases t_dim,
      cases HX_cases with link_X_sphere link_X_ball,
      
      -- X ≅ₛₜ S(n)
      apply stellar_equiv_preserves_not_stellar_sphere
        (φ[D(n) ⋆ S(↑(X.dim) - dim t - 1)]),
      apply stellar_equiv_preserves_not_stellar_sphere
        (D(n + (↑(X.dim) - dim t - 1) + 1)),
      simp only [is_stellar_sphere, not_exists],
      intros x x_bound,
      rw [disk_is_sphere_iff_empty],
      simp only [not_and_distrib],
      left,
      simp only [not_lt],
      apply @int.le_trans _ n,
      apply int.coe_zero_le,
      omega,

      have H_join_ball := join_stellar_ball_and_sphere
        D(n) S(↑(X.dim) - dim t - 1) φ
        n (↑(X.dim) - dim t - 1)
        (by {sorry})
        (by {sorry})
        (by {sorry})
        (by {sorry}),
      unfold is_stellar_n_ball at H_join_ball,
      rw [stellar_equiv_symm],
      assumption,
      
      have u_in_Y : u ∈ Y.complex.simplices, from
      begin
        rw [set.mem_singleton_iff] at α_empty,
        rw [α_empty],
        apply simplicial_complex_empty_simplex,
      end,
      apply stellar_equiv_iso
        (S(↑(X.dim) - dim t - 1) ⋆ D(n))
        (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y),
      apply simplicial_iso_trans
        (S(↑(X.dim) - dim t - 1) ⋆ D(n))
        (D(n) ⋆ S(↑(X.dim) - dim t - 1)),
      apply simplicial_join_comm,
      apply φ.iso_onto_image,

      have s'_in_XY : s' ∈ (X.complex ⋆ Y.complex).simplices, from
      begin
        rw [simplicial_join_mem],
        use t, split, assumption,
        use u, split, assumption,
        symmetry,
        assumption,
      end,
      rw [simplicial_iso_symm],
      apply simplicial_iso_trans
        (Lk(φ[X.complex ⋆ Y.complex], s) _)
        (Lk(X.complex ⋆ Y.complex, s') s'_in_XY),
      let φs := simplicial_map.mk φ.coe (map_is_simplicial_onto_image (X.complex ⋆ Y.complex) φ.coe φ.injective),
      rw [simplicial_iso_symm],
      apply link_iso _ _ _ _ _ _ _ (coe_is_iso _ φ) s'_eq_s,

      simp only [←tu_eq_s'],
      apply join_fact_link,

      apply stellar_equiv_trans
        (S(↑(X.dim) - dim t - 1) ⋆ D(n))
        (S(↑(X.dim) - dim t - 1) ⋆ Lk(Y.complex, u) u_in_Y),
      apply simplicial_join_stellar_equiv_right,
      rw [stellar_equiv_symm],
      apply stellar_equiv_trans (Lk(Y.complex, u) u_in_Y) Y.complex,
      rw [set.mem_singleton_iff] at α_empty,
      simp only [α_empty],
      apply stellar_equiv_preserves_iso,
      apply link_ident,
      assumption,
      
      apply simplicial_join_stellar_equiv_left,
      unfold is_stellar_n_sphere at link_X_sphere,
      rw [stellar_equiv_symm],
      assumption,
      
      -- X ≅ₛₜ D(n)
      apply stellar_equiv_preserves_not_stellar_sphere
        (φ[D(n) ⋆ D(↑(X.dim) - dim t - 1)]),
      apply stellar_equiv_preserves_not_stellar_sphere
        (D(n + (↑(X.dim) - dim t - 1) + 1)),
      simp only [is_stellar_sphere, not_exists],
      intros x x_bound,
      rw [disk_is_sphere_iff_empty],
      simp only [not_and_distrib],
      left,
      simp only [not_lt],
      apply @int.le_trans _ n,
      apply int.coe_zero_le,
      omega,
      
      have H_join_ball := join_stellar_balls
        D(n) D(↑(X.dim) - dim t - 1) φ
        n (↑(X.dim) - dim t - 1)
        (by {sorry})
        (by {sorry})
        (by {sorry})
        (by {sorry}),
      unfold is_stellar_n_ball at H_join_ball,
      rw [stellar_equiv_symm],
      assumption,
      
      have u_in_Y : u ∈ Y.complex.simplices, from
      begin
        rw [set.mem_singleton_iff] at α_empty,
        rw [α_empty],
        apply simplicial_complex_empty_simplex,
      end,
      apply stellar_equiv_iso
        (D(↑(X.dim) - dim t - 1) ⋆ D(n))
        (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y),
      apply simplicial_iso_trans
        (D(↑(X.dim) - dim t - 1) ⋆ D(n))
        (D(n) ⋆ D(↑(X.dim) - dim t - 1)),
      apply simplicial_join_comm,
      apply φ.iso_onto_image,

      have s'_in_XY : s' ∈ (X.complex ⋆ Y.complex).simplices, from
      begin
        rw [simplicial_join_mem],
        use t, split, assumption,
        use u, split, assumption,
        symmetry,
        assumption,
      end,
      rw [simplicial_iso_symm],
      apply simplicial_iso_trans
        (Lk(φ[X.complex ⋆ Y.complex], s) _)
        (Lk(X.complex ⋆ Y.complex, s') s'_in_XY),
      let φs := simplicial_map.mk φ.coe (map_is_simplicial_onto_image (X.complex ⋆ Y.complex) φ.coe φ.injective),
      rw [simplicial_iso_symm],
      apply link_iso _ _ _ _ _ _ _ (coe_is_iso _ φ) s'_eq_s,

      simp only [←tu_eq_s'],
      apply join_fact_link,

      apply stellar_equiv_trans
        (D(↑(X.dim) - dim t - 1) ⋆ D(n))
        (D(↑(X.dim) - dim t - 1) ⋆ Lk(Y.complex, u) u_in_Y),
      apply simplicial_join_stellar_equiv_right,
      rw [stellar_equiv_symm],
      apply stellar_equiv_trans (Lk(Y.complex, u) u_in_Y) Y.complex,
      rw [set.mem_singleton_iff] at α_empty,
      simp only [α_empty],
      apply stellar_equiv_preserves_iso,
      apply link_ident,
      assumption,
      
      apply simplicial_join_stellar_equiv_left,
      unfold is_stellar_n_ball at link_X_ball,
      rw [stellar_equiv_symm],
      assumption, },
      
    -- s' ∈ ∂X ⋆ Y
    { by_cases (u = ∅),
      
      -- u = ∅
      { apply stellar_equiv_preserves_not_stellar_sphere
          (φ[D(z) ⋆ Y.complex]),
        apply stellar_equiv_preserves_not_stellar_sphere
          (φ[D(z) ⋆ D(n)]),
        
        apply stellar_equiv_preserves_not_stellar_sphere
          (D(z + n + 1)),
        simp only [is_stellar_sphere, not_exists],
        intros x x_bound,
        rw [disk_is_sphere_iff_empty],
        simp only [not_and_distrib],
        left,
        simp only [not_lt],
        apply @int.le_trans _ (z + n),
        apply @int.le_trans _ z,
        assumption,
        simp only [le_add_iff_nonneg_right, nat.cast_nonneg],
        simp,
        
        apply stellar_equiv_preserves_iso,
        rw [simplicial_iso_symm],
        apply simplicial_iso_trans (φ[D(z) ⋆ D(n)]) (D(z) ⋆ D(n)),
        rw [simplicial_iso_symm],
        apply φ.iso_onto_image,
        apply join_stellar_disk,
        
        apply stellar_equiv_iso
          (D(z) ⋆ D(n))
          (D(z) ⋆ Y.complex),
        apply φ.iso_onto_image,
        apply φ.iso_onto_image,
        apply simplicial_join_stellar_equiv_right,
        rw [stellar_equiv_symm],
        assumption,
        
        apply stellar_equiv_iso
          (D(z) ⋆ Y.complex)
          (D(z) ⋆ Lk(Y.complex, u) u_in_Y),
        apply φ.iso_onto_image,
        apply φ.iso_onto_image,
        apply stellar_equiv_preserves_iso,
        apply simplicial_join_iso_right,
        simp only [h],
        rw [simplicial_iso_symm],
        apply link_ident, },
      
      -- u ≠ ∅ ↔ 0 ≤ dim u
      { have u_dim : 0 ≤ dim u, by sorry,
        -- TODO: Turn into more general lemma.
        have HYu : dim u ≤ Y.dim, by sorry,
        specialize H_cases u_dim,
        cases H_cases with link_Y_sphere link_Y_ball,
        
        -- Y ≅ₛₜ S(n)
        apply stellar_equiv_preserves_not_stellar_sphere
          (φ[D(z) ⋆ S(↑(Y.dim) - dim u - 1)]),
        apply stellar_equiv_preserves_not_stellar_sphere
          (D(z + (↑(Y.dim) - dim u - 1) + 1)),
        simp only [is_stellar_sphere, not_exists],
        intros x x_bound,
        rw [disk_is_sphere_iff_empty],
        simp only [not_and_distrib],
        left,
        simp only [not_lt],
        omega,
        
        have H_join_ball := join_stellar_ball_and_sphere
          D(z) S(↑(Y.dim) - dim u - 1) φ
          z (↑(Y.dim) - dim u - 1)
          Hz (by {sorry})
          (by {sorry})
          (by {sorry}),
        unfold is_stellar_n_ball at H_join_ball,
        rw [stellar_equiv_symm],
        assumption,
        
        apply stellar_equiv_iso
          (D(z) ⋆ S(↑(Y.dim) - dim u - 1))
          (D(z) ⋆ Lk(Y.complex, u) u_in_Y),
        apply φ.iso_onto_image,
        apply φ.iso_onto_image,
        
        apply simplicial_join_stellar_equiv_right,
        unfold is_stellar_n_sphere at link_Y_sphere,
        rw [stellar_equiv_symm],
        assumption,
        
        -- Y ≅ₛₜ D(n)
        apply stellar_equiv_preserves_not_stellar_sphere
          (φ[D(z) ⋆ D(↑(Y.dim) - dim u - 1)]),
        apply stellar_equiv_preserves_not_stellar_sphere
          (D(z + (↑(Y.dim) - dim u - 1) + 1)),
        simp only [is_stellar_sphere, not_exists],
        intros x x_bound,
        rw [disk_is_sphere_iff_empty],
        simp only [not_and_distrib],
        left,
        simp only [not_lt],
        omega,
        
        have Hz_neg_one : -1 ≤ z, by omega,
        have H_join_ball := join_stellar_balls
          D(z) D(↑(Y.dim) - dim u - 1) φ
          z (↑(Y.dim) - dim u - 1)
          Hz_neg_one (by {sorry})
          (by {sorry})
          (by {sorry}),
        unfold is_stellar_n_ball at H_join_ball,
        rw [stellar_equiv_symm],
        assumption,
        
        apply stellar_equiv_iso
          (D(z) ⋆ D(↑(Y.dim) - dim u - 1))
          (D(z) ⋆ Lk(Y.complex, u) u_in_Y),
        apply φ.iso_onto_image,
        apply φ.iso_onto_image,
        
        apply simplicial_join_stellar_equiv_right,
        unfold is_stellar_n_ball at link_Y_ball,
        rw [stellar_equiv_symm],
        assumption, }, },
        
    { apply stellar_equiv_iso
        (D(z) ⋆ Lk(Y.complex, u) u_in_Y)
        (Lk(X.complex, t) α_in_K ⋆ Lk(Y.complex, u) u_in_Y),
      apply φ.iso_onto_image,
      apply φ.iso_onto_image,
      
      apply simplicial_join_stellar_equiv_left,
      rw [stellar_equiv_symm],
      assumption, },
      
    { have s'_in_XY : s' ∈ (X.complex ⋆ Y.complex).simplices, from
      begin
        rw [simplicial_join_mem],
        use t, split, assumption,
        use u, split, assumption,
        symmetry,
        assumption,
      end,
      apply stellar_equiv_iso
        (Lk(X.complex, t) α_in_K ⋆ Lk(Y.complex, u) u_in_Y)
        (Lk(X.complex ⋆ Y.complex, s') s'_in_XY),
      apply φ.iso_onto_image,
      let φs := simplicial_map.mk φ.coe (map_is_simplicial_onto_image (X.complex ⋆ Y.complex) φ.coe φ.injective),
      apply link_iso _ _ _ _ _ _ _ (coe_is_iso _ φ) s'_eq_s,
      
      rw [stellar_equiv_symm],
      apply stellar_equiv_preserves_iso,
      simp only [←tu_eq_s'],
      apply join_fact_link, },
      
      -- t = ∅
    { by_cases (u = ∅),
      
      -- u = ∅
      rw [set.mem_singleton_iff] at α_empty,
      have s'_empty : s' = ∅, from
      begin
        rw [←tu_eq_s', simplex_disjoint_empty],
        split; assumption,
      end,
      rw [s'_empty, finset.image_empty] at s'_eq_s,
      right,
      rw [set.mem_singleton_iff],
      symmetry,
      assumption,
      
      -- u ≠ ∅
      left, split, split,
      use s', split,
      rw [←tu_eq_s', simplicial_join_sep],
      split,
      rw [set.mem_singleton_iff] at α_empty,
      rw [α_empty],
      apply simplicial_complex_empty_simplex,
      assumption,
      assumption,
      rw [set.mem_singleton_iff],
      rw [←s'_eq_s, ←tu_eq_s', finset.image_eq_empty, simplex_disjoint_empty],
      simp only [not_and_distrib],
      right, assumption,

      intro s''_in_XY,

      have u_dim : 0 ≤ dim u, by sorry,
      -- TODO: Turn into more general lemma.
      have HYu : dim u ≤ Y.dim, by sorry,
      have H_cases := stellar_link_is_stellar_ball_or_sphere Y u u_in_Y,

      specialize H_cases u_dim,
      cases H_cases with link_Y_sphere link_Y_ball,
      
      -- Y ≅ₛₜ S(n)
      apply stellar_equiv_preserves_not_stellar_sphere
        (φ[D(m) ⋆ S(↑(Y.dim) - dim u - 1)]),
      apply stellar_equiv_preserves_not_stellar_sphere
        (D(m + (↑(Y.dim) - dim u - 1) + 1)),
      simp only [is_stellar_sphere, not_exists],
      intros x x_bound,
      rw [disk_is_sphere_iff_empty],
      simp only [not_and_distrib],
      left,
      simp only [not_lt],
      apply @int.le_trans _ m,
      apply int.coe_zero_le,
      omega,

      have H_join_ball := join_stellar_ball_and_sphere
        D(m) S(↑(Y.dim) - dim u - 1) φ
        m (↑(Y.dim) - dim u - 1)
        (by {sorry})
        (by {sorry})
        (by {sorry})
        (by {sorry}),
      unfold is_stellar_n_ball at H_join_ball,
      rw [stellar_equiv_symm],
      assumption,
      
      have t_in_X : t ∈ X.complex.simplices, from
      begin
        rw [set.mem_singleton_iff] at α_empty,
        rw [α_empty],
        apply simplicial_complex_empty_simplex,
      end,
      apply stellar_equiv_iso
        (D(m) ⋆ S(↑(Y.dim) - dim u - 1))
        (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y),
      apply φ.iso_onto_image,

      have s'_in_XY : s' ∈ (X.complex ⋆ Y.complex).simplices, from
      begin
        rw [simplicial_join_mem],
        use t, split, assumption,
        use u, split, assumption,
        symmetry,
        assumption,
      end,
      rw [simplicial_iso_symm],
      apply simplicial_iso_trans
        (Lk(φ[X.complex ⋆ Y.complex], s) _)
        (Lk(X.complex ⋆ Y.complex, s') s'_in_XY),
      let φs := simplicial_map.mk φ.coe (map_is_simplicial_onto_image (X.complex ⋆ Y.complex) φ.coe φ.injective),
      rw [simplicial_iso_symm],
      apply link_iso _ _ _ _ _ _ _ (coe_is_iso _ φ) s'_eq_s,

      simp only [←tu_eq_s'],
      apply join_fact_link,

      apply stellar_equiv_trans
        (D(m) ⋆ S(↑(Y.dim) - dim u - 1))
        (Lk(X.complex, t) t_in_X ⋆ S(↑(Y.dim) - dim u - 1)),
      apply simplicial_join_stellar_equiv_left,
      rw [stellar_equiv_symm],
      apply stellar_equiv_trans (Lk(X.complex, t) t_in_X) X.complex,
      rw [set.mem_singleton_iff] at α_empty,
      simp only [α_empty],
      apply stellar_equiv_preserves_iso,
      apply link_ident,
      assumption,
      
      apply simplicial_join_stellar_equiv_right,
      unfold is_stellar_n_sphere at link_Y_sphere,
      rw [stellar_equiv_symm],
      assumption,
      
      -- Y ≅ₛₜ D(n)
      apply stellar_equiv_preserves_not_stellar_sphere
        (φ[D(m) ⋆ D(↑(Y.dim) - dim u - 1)]),
      apply stellar_equiv_preserves_not_stellar_sphere
        (D(m + (↑(Y.dim) - dim u - 1) + 1)),
      simp only [is_stellar_sphere, not_exists],
      intros x x_bound,
      rw [disk_is_sphere_iff_empty],
      simp only [not_and_distrib],
      left,
      simp only [not_lt],
      apply @int.le_trans _ m,
      apply int.coe_zero_le,
      omega,
      
      have H_join_ball := join_stellar_balls
        D(m) D(↑(Y.dim) - dim u - 1) φ
        m (↑(Y.dim) - dim u - 1)
        (by {sorry})
        (by {sorry})
        (by {sorry})
        (by {sorry}),
      unfold is_stellar_n_ball at H_join_ball,
      rw [stellar_equiv_symm],
      assumption,
      
      have t_in_X : t ∈ X.complex.simplices, from
      begin
        rw [set.mem_singleton_iff] at α_empty,
        rw [α_empty],
        apply simplicial_complex_empty_simplex,
      end,
      apply stellar_equiv_iso
        (D(m) ⋆ D(↑(Y.dim) - dim u - 1))
        (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y),
      apply φ.iso_onto_image,

      have s'_in_XY : s' ∈ (X.complex ⋆ Y.complex).simplices, from
      begin
        rw [simplicial_join_mem],
        use t, split, assumption,
        use u, split, assumption,
        symmetry,
        assumption,
      end,
      rw [simplicial_iso_symm],
      apply simplicial_iso_trans
        (Lk(φ[X.complex ⋆ Y.complex], s) _)
        (Lk(X.complex ⋆ Y.complex, s') s'_in_XY),
      let φs := simplicial_map.mk φ.coe (map_is_simplicial_onto_image (X.complex ⋆ Y.complex) φ.coe φ.injective),
      rw [simplicial_iso_symm],
      apply link_iso _ _ _ _ _ _ _ (coe_is_iso _ φ) s'_eq_s,

      simp only [←tu_eq_s'],
      apply join_fact_link,

      apply stellar_equiv_trans
        (D(m) ⋆ D(↑(Y.dim) - dim u - 1))
        (Lk(X.complex, t) t_in_X ⋆ D(↑(Y.dim) - dim u - 1)),
      apply simplicial_join_stellar_equiv_left,
      rw [stellar_equiv_symm],
      apply stellar_equiv_trans (Lk(X.complex, t) t_in_X) X.complex,
      rw [set.mem_singleton_iff] at α_empty,
      simp only [α_empty],
      apply stellar_equiv_preserves_iso,
      apply link_ident,
      assumption,
      
      apply simplicial_join_stellar_equiv_right,
      unfold is_stellar_n_ball at link_Y_ball,
      rw [stellar_equiv_symm],
      assumption, }, },
end

-- Proposition 3.11 (2), p.18
lemma stellar_sphere_ball_boundary_distr_join_left
    (X Y : simplicial_complex ℕ)
    (m n : ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
  : is_stellar_n_sphere X m →
      is_stellar_n_ball Y n →
        simplicial_complex_boundary (φ[X ⋆ Y]) ≅ X ⋆ (simplicial_complex_boundary Y)
:= sorry

lemma neg_one_ball_is_zero_disk {α : Type*} [decidable_eq α]
    (X : simplicial_complex α)
    (x : α)
    (x_nin_X : x ∉ vertices X)
  : neg_one_ball x x_nin_X ≅ D(0)
:= begin
  have H_zero : 0 = int.of_nat 0, by tauto,
  rw [H_zero],
  simp only [stellar_n_disk, neg_one_ball],

  let f : α → ℕ := λ a, 0,
  let g : ℕ → α := λ n, x,

  set B := neg_one_ball x x_nin_X,

  -- TODO: Prove simplicial.
  have f_simp : is_simplicial_map B D(0) f, by sorry,
  have g_simp : is_simplicial_map D(0) B g, by sorry,

  let fs := simplicial_map.mk f f_simp,
  let gs := simplicial_map.mk g g_simp,

  unfold is_simplicially_iso,
  use fs,
  unfold is_simplicial_iso,
  use gs,
  unfold is_inverse_simplicial_iso,
  split,

  -- TODO: Prove mutual inverses.
  sorry,
  sorry,
end

lemma cone_is_zero_disk_join_boundary
    (X : simplicial_complex ℕ)
    (x : ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
    (x_nin_X : x ∉ vertices X)
  : Cone(X, x) x_nin_X ≅ D(0) ⋆ X
:= begin
  unfold cone,
  apply simplicial_join_iso_left,
  apply neg_one_ball_is_zero_disk,
end

-- Corollary 3.12, p.20
lemma stellar_ball_boundary_comm_cone_union
    (X : simplicial_complex ℕ)
    (x : ℕ)
    (φ : simplicial_coe (ℕ × ℕ) ℕ)
    (x_nin_X : x ∉ vertices X)
    (X_ball : is_stellar_ball X)
  : simplicial_complex_boundary (φ[Cone(X, x) x_nin_X]) ≅ φ[(Cone((simplicial_complex_boundary X), x) (boundary_subcomplex_simplicial_complex_vertices X x x_nin_X))] ∪ X
:= begin
  set x_nin_X_bd := boundary_subcomplex_simplicial_complex_vertices X x x_nin_X,

  apply simplicial_iso_trans
    (simplicial_complex_boundary (φ[Cone(X, x) x_nin_X]))
    (simplicial_complex_boundary (φ[D(0) ⋆ X])),
  apply simplicial_complex_boundary_iso,
  
  apply simplicial_iso_trans (φ[Cone(X, x) x_nin_X]) (Cone(X, x) x_nin_X),
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans (φ[D(0) ⋆ X]) (D(0) ⋆ X),
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,
  
  rw [simplicial_iso_symm],
  apply cone_is_zero_disk_join_boundary,
  apply φ,

  apply simplicial_iso_trans
    (simplicial_complex_boundary (φ[D(0) ⋆ X]))
    ((D(0) ⋆ simplicial_complex_boundary X) ∪ (simplicial_complex_boundary D(0) ⋆ X)),
  sorry,  -- apply stellar_ball_boundary_distr_join_union,
          -- unfold is_stellar_ball,
          -- use 0,
          -- assumption,
  -- TODO: 3.11 (1) is too slow, causes timeout.

  apply simplicial_iso_trans
    ((D(0) ⋆ simplicial_complex_boundary X) ∪ (simplicial_complex_boundary D(0) ⋆ X))
    ((D(0) ⋆ simplicial_complex_boundary X) ∪ (empty_sc ⋆ X)),
  apply simplicial_union_iso_right,
  apply simplicial_join_iso_left,
  apply simplicial_iso_trans (simplicial_complex_boundary D(0)) S(-1),
  apply disk_boundary_is_sphere (-1),
  have H_neg_one : -1 = -[1+ 0], by tauto,
  rw [H_neg_one],
  simp only [stellar_n_sphere],

  apply simplicial_union_iso,

  rotate,
  apply simplicial_join_id_right,

  apply simplicial_iso_trans
    (D(0) ⋆ simplicial_complex_boundary X)
    (Cone(simplicial_complex_boundary X, x) x_nin_X_bd),
  rw [simplicial_iso_symm],
  apply cone_is_zero_disk_join_boundary,
  apply φ,
  apply φ.iso_onto_image,
end

