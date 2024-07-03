import tactic          -- standard proof tactics
import data.set.basic        -- basics on sets
import data.set.finite -- basics on finite sets
import data.finset.basic     -- type-level finite sets
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

instance stellar_n_sphere.fintype
    (n : ℤ)
  : fintype (S(n)).simplices
:= sorry

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

-- Special coercion on spheres.
def join_proj_spheres_map
    (m : ℕ) (n : ℤ)
  : ℕ × ℕ → ℕ
:= λ x : ℕ × ℕ, if (x.snd = 0) then x.fst else x.fst + m + 2

lemma join_proj_spheres_is_coe
    (m : ℕ) (n : ℤ)
  : set.inj_on (join_proj_spheres_map m n) (vertices (S(m) ⋆ S(n)))
:= begin
  simp only [set.inj_on],
  intros x x_in_join y y_in_join px_eq_py,
  simp only [join_proj_spheres_map, ite_eq_iff] at px_eq_py,
  cases px_eq_py,
  all_goals {
    cases px_eq_py with x_snd x_eq_py,
    symmetry' at x_eq_py,
    simp only [ite_eq_iff] at x_eq_py,
    cases x_eq_py;
    cases x_eq_py with y_snd x_eq_y,
  },

  -- x, y in LHS.
  simp only [prod.eq_iff_fst_eq_snd_eq],
  split,

  symmetry,
  apply x_eq_y,

  rw [←y_snd] at x_snd,
  apply x_snd,

  -- x in LHS, y in RHS. Contradiction.
  have H := simplicial_join_vertices_mem_left S(m) S(n) x.fst,
  cases H with px_in_Sm x_in_Sm_Sn,
  rw [←@prod.mk.eta ℕ ℕ x, x_snd] at x_in_join,
  specialize px_in_Sm x_in_join,
  rw [stellar_sphere_vertices, finset.mem_coe, finset.mem_range] at px_in_Sm,
  have H_contra : ¬x.fst < m + 2, by omega,
  contradiction,

  -- x in RHS, y in LHS. Contradiction.
  have H := simplicial_join_vertices_mem_left S(m) S(n) y.fst,
  cases H with py_in_Sm y_in_Sm_Sn,
  rw [←@prod.mk.eta ℕ ℕ y, y_snd] at y_in_join,
  specialize py_in_Sm y_in_join,
  rw [stellar_sphere_vertices, finset.mem_coe, finset.mem_range] at py_in_Sm,
  have H_contra : ¬y.fst < m + 2, by omega,
  contradiction,

  -- x, y in RHS.
  simp only [prod.eq_iff_fst_eq_snd_eq],
  split,

  simp only [add_left_inj] at x_eq_y,
  symmetry' at x_eq_y,
  apply x_eq_y,

  rw [simplicial_join_mem_vertices] at x_in_join y_in_join,
  cases x_in_join with x_contra x_in_rhs,
  cases x_contra, contradiction,

  cases y_in_join with y_contra y_in_rhs,
  cases y_contra, contradiction,

  cases x_in_rhs with x_in_Sn x_snd,
  cases y_in_rhs with y_in_Sn y_snd,
  rw [←y_snd] at x_snd,
  apply x_snd,
end

def join_proj_spheres
    (m : ℕ) (n : ℤ)
  : simplicial_coe (S(m) ⋆ S(n)) ℕ
:= simplicial_coe.mk (join_proj_spheres_map m n) (join_proj_spheres_is_coe m n)
notation `φˢ⟨` m `, ` n `⟩` := join_proj_spheres m n

lemma stellar_sphere_inductive
    (n : ℕ)
  : S(n) ≅ₛₜ (φˢ⟨0, n - 1⟩[S(0) ⋆ S(n - 1)])
:= begin
  apply @stellar_equiv_iso _ _ _ _ (S(↑n) ⋆ empty_sc) (S(↑0) ⋆ S(↑n - 1)),
  apply simplicial_join_id_left,
  apply (φˢ⟨0, n - 1⟩).iso_onto_image,

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
      Hs Hx)
    ((@stellar_subdivision _ _ S(n.succ)
      s H_range_ne
      (n.succ + 2)
      (by { sorry })
      (by { sorry })) ⋆ empty_sc),

  rw [simplicial_iso_symm],
  apply @stellar_subdiv_distr_join_left ℕ _ S(n.succ) empty_sc s H_range_ne,
  { sorry },
  { sorry },

  apply simplicial_iso_trans
    ((@stellar_subdivision _ _ S(n.succ)
      s H_range_ne
      (n.succ + 2)
      (by { sorry })
      (by { sorry })) ⋆ empty_sc)
    (@stellar_subdivision _ _ S(n.succ)
      s H_range_ne
      (n.succ + 2)
      (by { sorry })
      (by { sorry })),
  apply simplicial_join_id_left,

  apply simplicial_iso_trans
    (@stellar_subdivision _ _ S(n.succ)
      s H_range_ne
      (n.succ + 2)
      (by { sorry })
      (by { sorry }))
    (((simplex {n.succ + 1}) ⋆ ∂s) ∪ ((simplex {n.succ + 2}) ⋆ ∂s)),


  unfold stellar_subdivision,
  apply simplicial_union_iso,

  apply stellar_sphere_star_complement,
  simp,

  apply simplicial_iso_trans
    ((π₁ _)[(π₁ _)[(simplex {n.succ + 2}) ⋆ ∂s] ⋆ Lk(S(n.succ), s) sorry])
    ((π₁ _)[(simplex {n.succ + 2}) ⋆ ∂s] ⋆ Lk(S(n.succ), s) sorry),
  rw [simplicial_iso_symm],
  apply (π₁ _).iso_onto_image,

  apply simplicial_iso_trans
    ((π₁ _)[(simplex {n.succ + 2}) ⋆ ∂s] ⋆ Lk(S(n.succ), s) sorry)
    ((π₁ _)[(simplex {n.succ + 2}) ⋆ ∂s] ⋆ empty_sc),
  apply simplicial_join_iso,
  apply simplicial_iso_refl,
  apply stellar_sphere_empty_link,

  apply simplicial_iso_trans
    ((π₁ _)[(simplex {n.succ + 2}) ⋆ ∂s] ⋆ empty_sc)
    ((π₁ _)[(simplex {n.succ + 2}) ⋆ ∂s]),
  apply simplicial_join_id_left,
  rw [simplicial_iso_symm],
  apply (π₁ _).iso_onto_image,

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
  : φˢ⟨m, n⟩[S(m) ⋆ S(n)] ≅ₛₜ S(m + n + 1)
:= begin
  rw [stellar_equiv_symm],
  apply stellar_equiv_trans
    S(m + n + 1)
    (φˢ⟨0, m + n + 1 - 1⟩[S(0) ⋆ S(m + n + 1 - 1)]),
  apply stellar_sphere_inductive,

  apply stellar_equiv_iso
    (S(0) ⋆ S(m + n + 1 - 1))
    (S(m) ⋆ S(n))
    (φˢ⟨0, m + n + 1 - 1⟩[S(0) ⋆ S(m + n + 1 - 1)])
    (φˢ⟨m, n⟩[S(m) ⋆ S(n)]),
  rotate, apply φˢ⟨m, n⟩.iso_onto_image,
  rotate, apply φˢ⟨0, m + n + 1 - 1⟩.iso_onto_image,

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

  have H : S(m_n.succ + n_n.succ) ≅ₛₜ φˢ⟨m_n, n_n.succ⟩[S(m_n) ⋆ S(n_n.succ)], from
  begin
    rw [stellar_equiv_symm],
    apply stellar_equiv_trans
      (φˢ⟨m_n, n_n.succ⟩[S(m_n) ⋆ S(n_n.succ)])
      (φˢ⟨0, m_n + n_n.succ⟩[S(0) ⋆ S(m_n + n_n.succ)]),

    apply stellar_equiv_iso
      (S(m_n) ⋆ S(n_n.succ))
      (S(0) ⋆ S(m_n + n_n.succ))
      (φˢ⟨m_n, n_n.succ⟩[S(m_n) ⋆ S(n_n.succ)])
      (φˢ⟨0, m_n + n_n.succ⟩[S(0) ⋆ S(m_n + n_n.succ)]),
    apply φˢ⟨m_n, n_n.succ⟩.iso_onto_image,
    apply φˢ⟨0, m_n + n_n.succ⟩.iso_onto_image,
    rw [stellar_equiv_symm],
    assumption,

    rw [stellar_equiv_symm],
    have H_rw : ↑m_n + ↑(n_n.succ) = ↑(m_n.succ) + ↑(n_n.succ) - 1, by simp,
    have HS_rw : S(↑m_n + ↑(n_n.succ)) = S(↑(m_n.succ) + ↑(n_n.succ) - 1), from
    begin
      apply congr_arg,
      sorry, --stupid
    end,
    simp_rw [HS_rw],
    apply stellar_sphere_inductive,
  end,

  apply stellar_equiv_trans
    (S(0) ⋆ S(m_n.succ + n_n.succ))
    (S(0) ⋆ φˢ⟨m_n, n_n.succ⟩[S(m_n) ⋆ S(n_n.succ)]),
  apply simplicial_join_stellar_equiv_right,
  assumption,

  apply stellar_equiv_trans
    (S(0) ⋆ φˢ⟨m_n, n_n.succ⟩[S(m_n) ⋆ S(n_n.succ)])
    (φˢ⟨0, m_n⟩[S(0) ⋆ S(m_n)] ⋆ S(n_n.succ)),
  apply stellar_equiv_preserves_iso,
  rw [simplicial_iso_symm],
  apply simplicial_join_assoc,

  apply simplicial_join_stellar_equiv_left,
  have H_rw : S(m_n) = S(m_n.succ - 1), by simp,
  simp_rw [stellar_equiv_symm, H_rw],
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

instance stellar_n_disk.fintype
    (n : ℤ)
  : fintype (D(n)).simplices
:= sorry

lemma stellar_disk_range
    (m n : ℕ)
  : m ≤ n + 1 → finset.range m ∈ D(n).simplices
:= sorry

lemma disk_is_sphere_iff_empty
    (m n : ℤ)
  : D(m) ≅ₛₜ S(n) ↔ m < 0 ∧ n < 0
:= sorry

-- Special coercion on disks.
def join_proj_disks_map
    (m : ℕ) (n : ℤ)
  : ℕ × ℕ → ℕ
:= λ x : ℕ × ℕ, if (x.snd = 0) then x.fst else x.fst + m + 1

lemma join_proj_disks_is_coe
    (m : ℕ) (n : ℤ)
  : set.inj_on (join_proj_disks_map m n) (vertices (D(m) ⋆ D(n)))
:= by { admit, }

def join_proj_disks
    (m : ℕ) (n : ℤ)
  : simplicial_coe (D(m) ⋆ D(n)) ℕ
:= simplicial_coe.mk (join_proj_disks_map m n) (join_proj_disks_is_coe m n)
notation `φᵈ⟨` m `, ` n `⟩` := join_proj_disks m n

-- Special coercion on disks and spheres.
def join_proj_disk_sphere_map
    (m : ℕ) (n : ℤ)
  : ℕ × ℕ → ℕ
:= λ x : ℕ × ℕ, if (x.snd = 0) then x.fst else x.fst + m + 2

lemma join_proj_disk_sphere_is_coe
    (m : ℕ) (n : ℤ)
  : set.inj_on (join_proj_disk_sphere_map m n) (vertices (D(m) ⋆ S(n)))
:= by { admit, }

lemma join_proj_disk_sphere_is_coe_swap
    (m : ℕ) (n : ℤ)
  : set.inj_on (join_proj_disk_sphere_map m n) (vertices (S(m) ⋆ D(n)))
:= by { admit, }

def join_proj_disk_sphere
    (m : ℕ) (n : ℤ)
  : simplicial_coe (D(m) ⋆ S(n)) ℕ
:= simplicial_coe.mk (join_proj_disk_sphere_map m n) (join_proj_disk_sphere_is_coe m n)
notation `φᵈˢ⟨` m `, ` n `⟩` := join_proj_disk_sphere m n

def join_proj_sphere_disk
    (m : ℕ) (n : ℤ)
  : simplicial_coe (S(m) ⋆ D(n)) ℕ
:= simplicial_coe.mk (join_proj_disk_sphere_map m n) (join_proj_disk_sphere_is_coe_swap m n)
notation `φˢᵈ⟨` m `, ` n `⟩` := join_proj_sphere_disk m n

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

instance stellar_manifold.fintype
    (X : stellar_manifold)
  : fintype X.complex.simplices
:= sorry

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

lemma manifold_dim_is_complex_dim
    (X : stellar_manifold)
  : ↑X.dim = dim_of_complex X.complex
:= sorry

lemma simplex_boundary_is_sphere
    (s : finset ℕ)
  : ∂s ≅ S(dim s)
:= sorry

lemma manifold_dim_mono
    (X Y : stellar_manifold)
    (Y_submfd_X : Y.complex ⊆ X.complex)
  : Y.dim ≤ X.dim
:= sorry

lemma star_complement_is_mfd
    (X : stellar_manifold)
    (s : finset ℕ) [s_ne : nonempty s]
    (s_in_X : s ∈ X.complex.simplices)
  : is_stellar_n_manifold (star_complement X.complex s s_in_X) X.dim
:= sorry

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

lemma simplicial_complex_boundary_is_subcomplex
    (X : simplicial_complex ℕ)
  : simplicial_complex_boundary X ⊆ X
:= begin
  simp only [simplicial_complex.has_subset, is_subcomplex, set.subset_def],
  intros s s_in_bd_X,
  apply simplicial_complex_boundary_subcomplex X s s_in_bd_X,
end

lemma simplicial_complex_boundary_subcomplex_vertices
    (X : simplicial_complex ℕ)
    (x : ℕ)
    (x_in_X_bd : x ∈ vertices (simplicial_complex_boundary X))
  : x ∈ vertices X
:= sorry

lemma simplicial_complex_boundary_subcomplex_vertices_contra
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

lemma simplicial_complex_boundary_preserves_is_subcomplex
    (X Y : simplicial_complex ℕ)
    (Y_sub_X : Y ⊆ X)
  : simplicial_complex_boundary Y ⊆ simplicial_complex_boundary X
:= sorry

lemma simplicial_complex_boundary_preserves_subcomplex
    (X Y : simplicial_complex ℕ)
    (s : finset ℕ)
    (s_in_Y : s ∈ (simplicial_complex_boundary Y).simplices)
    (Y_sub_X : Y ⊆ X)
  : s ∈ (simplicial_complex_boundary X).simplices
:= sorry

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
    (φ : simplicial_coe (X ⋆ Y) ℕ)
    (m n : ℤ)
  : -1 ≤ m → -1 ≤ n →
      is_stellar_n_ball X m →
        is_stellar_n_ball Y n →
          is_stellar_n_ball (φ[X ⋆ Y]) (m + n + 1)
:= begin
  intros m_geq_neg_one n_geq_neg_one X_stellar_ball Y_stellar_ball,
  unfold is_stellar_n_ball at *,

  apply stellar_equiv_iso (X ⋆ Y) (D(m + n + 1) ⋆ empty_sc),
  apply φ.iso_onto_image,
  apply simplicial_join_id_left,

  apply stellar_equiv_trans (X ⋆ Y) (D(m) ⋆ D(n)),
  apply simplicial_join_stellar_equiv;
  assumption,

  apply stellar_equiv_preserves_iso,
  rw [simplicial_iso_symm],
  apply simplicial_iso_trans (D(m + n + 1) ⋆ empty_sc) D(m + n + 1),
  apply simplicial_join_id_left,
  rw [simplicial_iso_symm],
  apply join_stellar_disk,
end

-- Lemma 3.3 (2), p.12
lemma join_stellar_spheres
    (X Y : simplicial_complex ℕ)
    (m n : ℕ)
    (φ : simplicial_coe (X ⋆ Y) ℕ)
  : is_stellar_n_sphere X m → is_stellar_n_sphere Y n → is_stellar_n_sphere (φ[X ⋆ Y]) (m + n + 1)
:= begin
  intros X_stellar_sphere Y_stellar_sphere,
  unfold is_stellar_n_sphere at *,

  apply stellar_equiv_trans (φ[X ⋆ Y]) (φˢ⟨m, n⟩[S(m) ⋆ S(n)]),

  apply stellar_equiv_iso (X ⋆ Y) (S(m) ⋆ S(n)),
  apply φ.iso_onto_image,
  apply φˢ⟨m, n⟩.iso_onto_image,
  apply simplicial_join_stellar_equiv;
  assumption,
  
  apply join_stellar_sphere,
end

lemma join_stellar_spheres_gen
    (X Y : simplicial_complex ℕ)
    (φ : simplicial_coe (X ⋆ Y) ℕ)
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
  apply join_stellar_spheres,
  apply X_m_sphere,
  apply Y_n_sphere,

  -- m ≥ 0, n < 0
  use m, split, tauto,
  simp only [stellar_n_sphere] at Y_n_sphere,
  apply stellar_equiv_trans (φ[X ⋆ Y]) X,

  apply stellar_equiv_iso (X ⋆ Y) (X ⋆ empty_sc),
  apply φ.iso_onto_image,
  apply simplicial_join_id_left,
  apply simplicial_join_stellar_equiv_right,
  assumption,

  apply X_m_sphere,

  -- m < 0, n ≥ 0
  use n, split, tauto,
  simp only [stellar_n_sphere] at X_m_sphere,
  apply stellar_equiv_trans (φ[X ⋆ Y]) Y,

  apply stellar_equiv_iso (X ⋆ Y) (empty_sc ⋆ Y),
  apply φ.iso_onto_image,
  apply simplicial_join_id_right,
  apply simplicial_join_stellar_equiv_left,
  assumption,

  apply Y_n_sphere,

  -- m, n < 0
  use (-[1+ 0]), split, tauto,
  simp only [stellar_n_sphere] at *,
  apply stellar_equiv_trans (φ[X ⋆ Y]) empty_sc,

  apply stellar_equiv_iso (X ⋆ Y) (empty_sc ⋆ empty_sc),
  apply φ.iso_onto_image,
  apply simplicial_join_id_left,
  apply simplicial_join_stellar_equiv;
  assumption,

  refl,
end

lemma stellar_subdiv_disk
    (n x : ℕ)
    (x_nin_disk : x ∉ vertices D(n + 1))
  : σ(D(n + 1), finset.range(n + 2), x; sorry, sorry, x_nin_disk) ≅ D(0) ⋆ S(n)
:= sorry

-- Lemma 3.3 (3), p.12
lemma join_stellar_ball_and_sphere
    (X Y : simplicial_complex ℕ)
    (φ : simplicial_coe (X ⋆ Y) ℕ)
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
  apply stellar_equiv_iso (X ⋆ Y) (D(m + n + 1) ⋆ empty_sc),
  apply φ.iso_onto_image,
  apply simplicial_join_id_left,
  
  apply stellar_equiv_trans (X ⋆ Y) (D(m) ⋆ S(n)),
  apply join_comm_stellar_equiv;
  assumption,

  apply stellar_equiv_trans (D(m) ⋆ S(n)) (φᵈ⟨0, ↑m - 1⟩[D(0) ⋆ D(↑m - 1)] ⋆ S(n)),
  
  apply simplicial_join_stellar_equiv_left,
  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_trans D(m) (D(↑m - 1) ⋆ D(0)),
  rw [simplicial_iso_symm],
  have H_rw : D(↑m) = D(↑m - int.of_nat 1 + 0 + 1), by simp,
  rw [H_rw],
  apply join_stellar_disk,

  apply simplicial_iso_trans (D(↑m - 1) ⋆ D(0)) (D(0) ⋆ D(↑m - 1)),
  apply simplicial_join_comm,
  apply φᵈ⟨0, ↑m - 1⟩.iso_onto_image,
  
  apply stellar_equiv_trans
    (φᵈ⟨0, ↑m - 1⟩[D(0) ⋆ D(↑m - 1)] ⋆ S(n))
    (D(↑m - 1) ⋆ φᵈˢ⟨0, n⟩[D(0) ⋆ S(n)]),
  apply stellar_equiv_preserves_iso,

  apply simplicial_iso_trans
    (φᵈ⟨0, ↑m - 1⟩[D(0) ⋆ D(↑m - 1)] ⋆ S(n))
    (S(n) ⋆ φᵈ⟨0, ↑m - 1⟩[D(0) ⋆ D(↑m - 1)]),
  apply simplicial_join_comm,

  apply simplicial_iso_trans
    (S(n) ⋆ φᵈ⟨0, ↑m - 1⟩[D(0) ⋆ D(↑m - 1)])
    (φˢᵈ⟨n, 0⟩[S(n) ⋆ D(0)] ⋆ D(↑m - 1)),
  rw [simplicial_iso_symm],
  apply simplicial_join_assoc,

  apply simplicial_iso_trans
    (φˢᵈ⟨n, 0⟩[S(n) ⋆ D(0)] ⋆ D(↑m - 1))
    (D(↑m - 1) ⋆ φˢᵈ⟨n, 0⟩[S(n) ⋆ D(0)]),
  apply simplicial_join_comm,

  apply simplicial_join_iso_right,
  apply coe_preserves_iso,
  apply simplicial_join_comm,

  apply stellar_equiv_trans (D(↑m - 1) ⋆ φᵈˢ⟨0, n⟩[D(0) ⋆ S(n)]) (D(↑m - 1) ⋆ D(n + 1)),
  apply simplicial_join_stellar_equiv_right,
  apply relation.refl_trans_gen.single,

  unfold stellar_move,
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

  apply simplicial_iso_trans (φᵈˢ⟨0, n⟩[D(0) ⋆ S(n)]) (D(0) ⋆ S(n)),
  rw [simplicial_iso_symm],
  apply φᵈˢ⟨0, n⟩.iso_onto_image,
  rw [simplicial_iso_symm],
  apply stellar_subdiv_disk,

  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_trans (D(↑m - 1) ⋆ D(n + 1)) D(↑m - 1 + (n + 1) + 1),
  apply join_stellar_disk,

  apply simplicial_iso_trans D(↑m - 1 + (n + 1) + 1) D(↑m + n + 1),
  apply simplicial_iso_preserves_equiv,
  simp,
  rw [simplicial_iso_symm],
  apply simplicial_join_id_left,

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

  apply stellar_equiv_trans (φ[X ⋆ Y]) (φᵈˢ⟨m, -1⟩[D(m) ⋆ S(-1)]),
  apply stellar_equiv_iso (X ⋆ Y) (D(m) ⋆ S(-1)),
  apply φ.iso_onto_image,
  apply φᵈˢ⟨m, -1⟩.iso_onto_image,
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
  apply φᵈˢ⟨m, -1⟩.iso_onto_image,

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
      sorry,

      unfold is_stellar_ball,
      unfold is_stellar_n_ball at n_ball,
      use (↑(X.dim) - dim s - 1),
      sorry,
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
      sorry,

      unfold is_stellar_ball,
      unfold is_stellar_n_ball at n_ball,
      use (↑(X.dim) - dim s - 1),
      sorry,
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
    (X : simplicial_complex ℕ) [fintype X.simplices]
    (s : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : dim_of_complex X = 0 →
      σ(X, s, x; s_ne, s_in_X, x_nin_X) ≅ X
:= sorry

-- Proposition 3.4 (2), p.13
lemma stellar_eq_preserves_stellar_mfd
    (X : stellar_manifold)
    (Y : simplicial_complex ℕ)
  : X.complex ≅ₛₜ Y → is_stellar_n_manifold Y X.dim
:= begin
  intros X_eq_Y,
  destruct (X.dim),

  have X_fin := stellar_manifold.fintype X,
  have Y_fin := @stellar_equiv.fintype ℕ _ X.complex Y X_fin X_eq_Y,

  -- 0-dim case
  intro H_ind,
  induction X_eq_Y with K L X_eq_K K_move_L K_mfd_ih,
  apply X.is_manifold,

  have K_fin : fintype K.simplices := @stellar_equiv.fintype ℕ _ X.complex K X_fin X_eq_K,
  specialize K_mfd_ih K_fin,

  intros l l_in_L,
  unfold stellar_move at K_move_L,
  cases K_move_L with K_subdiv_L K_move_L,

  choose t Ht Ht_ne y Hy K_subdiv_L using K_subdiv_L,
  let K_subdiv_L_cases := K_subdiv_L,
  unfold is_simplicially_iso at K_subdiv_L_cases,
  choose f f_iso using K_subdiv_L_cases,
  have f_iso_cases := f_iso,
  unfold is_simplicial_iso at f_iso_cases,
  choose g fg_inv using f_iso_cases,

  rw [H_ind] at *,
  let Km := stellar_manifold.mk K 0 K_mfd_ih,
  have L_dim : @dim_of_complex ℕ L Y_fin = 0, from
  begin
    rw [@stellar_subdiv_preserves_dim ℕ _ L Y_fin t Ht_ne y Ht Hy],
    sorry,
    -- rw [←@simplicial_iso_preserves_dim ℕ ℕ _ _ K K_fin (@stellar_subdivision ℕ _ L t Ht_ne y Ht Hy φ) K_subdiv_L],
  end,

  have subdiv_ident := @stellar_subdiv_zero_dim_ident L Y_fin t Ht_ne y Ht Hy L_dim,
  have subdiv_ident_cases := subdiv_ident,

  unfold is_simplicially_iso at subdiv_ident_cases,
  choose fL fL_iso using subdiv_ident_cases,
  have fL_iso_cases := fL_iso,
  unfold is_simplicial_iso at fL_iso_cases,
  choose gL fgL_inv using fL_iso_cases,

  let g_comp := simplicial_map.comp gL g,
  have g_comp_iso : is_simplicial_iso g_comp, from
  begin
    apply iso_comp_is_iso,
    apply iso_inv_is_iso fL; assumption,
    apply iso_inv_is_iso f; assumption,
  end,

  have k_in_K : {g_comp.map l} ∈ K.simplices, from
  begin
    rw [←finset.image_singleton],
    apply g_comp.is_simplicial,
    assumption,
  end,

  unfold is_stellar_n_manifold at K_mfd_ih,
  specialize K_mfd_ih (g_comp.map l),
  specialize K_mfd_ih k_in_K,
  cases K_mfd_ih with K_sphere K_ball,

  left,
  apply stellar_equiv_preserves_stellar_n_sphere (Lk(K, {g_comp.map l}) k_in_K),
  assumption,
  apply stellar_equiv_preserves_iso,
  rw [simplicial_iso_symm],
  apply link_iso _ _ _ _ g_comp,
  assumption,
  rw [finset.image_singleton],

  right,
  apply stellar_equiv_preserves_stellar_n_ball (Lk(K, {g_comp.map l}) k_in_K),
  assumption,
  apply stellar_equiv_preserves_iso,
  rw [simplicial_iso_symm],
  apply link_iso _ _ _ _ g_comp,
  assumption,
  rw [finset.image_singleton],

  cases K_move_L with L_subdiv_K K_iso_L,
  choose s Hs Hs_ne x Hx L_subdiv_K using L_subdiv_K,

  let L_subdiv_K_cases := L_subdiv_K,
  unfold is_simplicially_iso at L_subdiv_K_cases,
  choose f f_iso using L_subdiv_K_cases,
  have f_iso_cases := f_iso,
  unfold is_simplicial_iso at f_iso_cases,
  choose g fg_inv using f_iso_cases,

  rw [H_ind] at *,
  let Km := stellar_manifold.mk K 0 K_mfd_ih,
  have K_dim : @dim_of_complex ℕ K K_fin = 0, from
  begin
    have H : Km.complex = K, by refl,
    sorry,
    -- rw [←H, ←manifold_dim_is_complex_dim Km],
  end,
  have subdiv_ident := @stellar_subdiv_zero_dim_ident K K_fin s Hs_ne x Hs Hx K_dim,
  have subdiv_ident_cases := subdiv_ident,

  unfold is_simplicially_iso at subdiv_ident_cases,
  choose fL fL_iso using subdiv_ident_cases,
  have fL_iso_cases := fL_iso,
  unfold is_simplicial_iso at fL_iso_cases,
  choose gL fgL_inv using fL_iso_cases,

  let f_comp := simplicial_map.comp f fL,
  have f_comp_iso : is_simplicial_iso f_comp, from
  begin
    apply iso_comp_is_iso;
    assumption,
  end,

  have k_in_K : {f_comp.map l} ∈ K.simplices, from
  begin
    rw [←finset.image_singleton],
    apply f_comp.is_simplicial,
    assumption,
  end,

  unfold is_stellar_n_manifold at K_mfd_ih,
  specialize K_mfd_ih (f_comp.map l),
  specialize K_mfd_ih k_in_K,
  cases K_mfd_ih with K_sphere K_ball,

  left,
  apply stellar_equiv_preserves_stellar_n_sphere (Lk(K, {f_comp.map l}) k_in_K),
  assumption,
  apply stellar_equiv_preserves_iso,
  rw [simplicial_iso_symm],
  apply link_iso _ _ _ _ f_comp,
  assumption,
  rw [finset.image_singleton],

  right,
  apply stellar_equiv_preserves_stellar_n_ball (Lk(K, {f_comp.map l}) k_in_K),
  assumption,
  apply stellar_equiv_preserves_iso,
  rw [simplicial_iso_symm],
  apply link_iso _ _ _ _ f_comp,
  assumption,
  rw [finset.image_singleton],

  have K_iso_L_cases := K_iso_L,
  unfold is_simplicially_iso at K_iso_L_cases,
  choose f f_iso using K_iso_L_cases,
  have f_iso_cases := f_iso,
  unfold is_simplicial_iso at f_iso_cases,
  choose g fg_inv using f_iso_cases,

  have g_iso : is_simplicial_iso g, from
  begin
    apply iso_inv_is_iso f;
    assumption,
  end,

  have k_in_K : {g.map l} ∈ K.simplices, from
  begin
    rw [←finset.image_singleton],
    apply g.is_simplicial,
    assumption,
  end,

  unfold is_stellar_n_manifold at K_mfd_ih,
  specialize K_mfd_ih (g.map l),
  specialize K_mfd_ih k_in_K,
  cases K_mfd_ih with K_sphere K_ball,

  left,
  apply stellar_equiv_preserves_stellar_n_sphere (Lk(K, {g.map l}) k_in_K),
  assumption,
  apply stellar_equiv_preserves_iso,
  rw [simplicial_iso_symm],
  apply link_iso _ _ _ _ g,
  assumption,
  rw [finset.image_singleton],

  right,
  apply stellar_equiv_preserves_stellar_n_ball (Lk(K, {g.map l}) k_in_K),
  assumption,
  apply stellar_equiv_preserves_iso,
  rw [simplicial_iso_symm],
  apply link_iso _ _ _ _ g,
  assumption,
  rw [finset.image_singleton],

  -- dim > 0 case
  induction X_eq_Y with K L X_eq_K K_move_L K_mfd_ih,
  intros n H_ind,
  apply X.is_manifold,

  intros n H_ind,
  unfold is_stellar_n_manifold,
  intros l l_in_L,

  specialize K_mfd_ih n H_ind,

  unfold stellar_move at K_move_L,
  cases K_move_L with L_subdiv_K K_move_L,
  choose t Ht Ht_ne y Hy L_subdiv_K using L_subdiv_K,

  sorry, -- incomplete

  cases K_move_L with K_subdiv_L K_iso_L,
  choose s Hs Hs_ne x Hx K_subdiv_L using K_subdiv_L,
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
:= begin
  intro s_nontriv,
  apply simplicial_iso_preserves_equiv,
  dsimp only [simplicial_complex_boundary, simplicial_complex.simplices],
  rw [set.ext_iff],
  intro u,
  split,

  { intro s_in_bd,
    have s_in_X : s ∈ X.complex.simplices := (simplicial_complex_boundary_subcomplex X.complex s s_in_bd_X),
    have Xu_dim_non_deg : -1 ≤ ↑X.dim - dim u - 1 := sorry,
    simp only [set.mem_union, set.mem_sep_iff] at s_in_bd,
    cases s_in_bd with u_in_link u_empty,
    cases u_in_link with u_in_link_ne link_not_sphere,
    have u_in_link := u_in_link_ne,
    cases u_in_link with u_in_link u_ne,
    specialize link_not_sphere u_in_link,
    
    simp only [link, simplicial_complex.simplices],
    simp only [set.mem_sep_iff, set.mem_union],
    split, left,
    
    split,
    rw [set.mem_diff],
    split,
    apply link_subcomplex X.complex s u,
    apply u_in_link,
    assumption,
    
    intro u_in_X,
    simp only [link, set.mem_sep_iff] at u_in_link,
    choose u_in_X us_in_X us_empty using u_in_link,

    have X_mfd_u : is_stellar_sphere (Lk(X.complex, u) u_in_X) ∨ is_stellar_ball (Lk(X.complex, u) u_in_X), from
    begin
      simp only [is_stellar_sphere, is_stellar_ball],
      rw [←exists_or_distrib],
      use (X.dim - dim u - 1),
      rw [←exists_or_distrib],
      use Xu_dim_non_deg,
      apply stellar_link_is_stellar_ball_or_sphere,
      simp,
      change (0 < u.card),
      rw [finset.card_pos, finset.nonempty_iff_ne_empty],
      rw [set.mem_singleton_iff] at u_ne,
      assumption,
    end,
    
    have u_in_bd_X : u ∈ (simplicial_complex_boundary X.complex).simplices, from
    begin
      -- TODO: lemma here just isn't true.
      apply simplicial_complex_boundary_preserves_subcomplex X.complex (Lk(X.complex, s) s_in_X) u,
      simp only [simplicial_complex_boundary, set.mem_union],
      left,

      simp only [set.mem_sep_iff],
      split, assumption,
      intro u_in_link,
      assumption,
      simp only [is_subcomplex, set.subset_def],
      intro x,
      apply link_subcomplex,
    end,
    
    simp only [simplicial_complex_boundary, set.mem_union] at u_in_bd_X,
    cases u_in_bd_X with u_in_bd_X u_contra,
    
    simp only [set.mem_sep_iff] at u_in_bd_X,
    cases u_in_bd_X with u_in_link u_not_sphere,
    specialize u_not_sphere u_in_X,
    assumption,
    
    contradiction,
    
    split, left, split,
    simp only [link, simplicial_complex.simplices, set.mem_sep_iff] at u_in_link,
    choose u_in_X su_in_X su_empty using u_in_link,
    simp only [set.mem_diff],
    split, assumption,
    dsimp only [set.mem_singleton_iff, set.union_empty_iff],
    sorry, -- TODO: stupid. set.union_empty_iff won't rw on negation.
    
    intro su_in_X,
    simp only [link, set.mem_sep_iff] at u_in_link,
    choose u_in_X su_in_X su_empty using u_in_link,

    have su_rw : u = (s ∪ u) \ s, from
    begin
      symmetry,
      rw [finset.union_sdiff_left, finset.sdiff_eq_self_iff_disjoint, disjoint.comm, finset.disjoint_iff_inter_eq_empty],
      assumption,
    end,

    have link_rw : Lk(Lk(X.complex, s) s_in_X, u) u_in_link
                    ≅ Lk(Lk(X.complex, s) s_in_X, (s ∪ u) \ s) (by { rw [←su_rw], assumption }), from
    begin
      apply simplicial_iso_preserves_equiv,
      conv_lhs {
        congr, congr, skip, rw [su_rw],
      },
    end,

    have sphere_rw : Lk(X.complex, s ∪ u) su_in_X ≅ₛₜ Lk(Lk(X.complex, s) s_in_X, u) u_in_link, from
    begin
      apply stellar_equiv_preserves_iso,
      rw [simplicial_iso_symm],
      apply simplicial_iso_trans
        (Lk(Lk(X.complex, s) s_in_X, u) u_in_link)
        (Lk(Lk(X.complex, s) s_in_X, (s ∪ u) \ s) (by { rw [←su_rw], assumption })),
      assumption,
      rw [simplicial_iso_symm],
      apply link_of_face_complement X.complex (s ∪ u) s,
      apply finset.subset_union_left,
    end,
    
    apply stellar_equiv_preserves_not_stellar_sphere (Lk(Lk(X.complex, s) s_in_X, u) u_in_link),
    assumption,
    rw [stellar_equiv_symm],
    assumption,
    
    simp only [link, set.mem_sep_iff] at u_in_link,
    choose u_in_X su_in_X su_empty using u_in_link,
    assumption,
    
    dsimp only [link, simplicial_complex.simplices, set.mem_sep_iff],
    split,
    
    simp only [set.mem_union],
    right, assumption,
    
    split,
    simp only [set.mem_union],
    left,
    simp only [set.mem_singleton_iff] at u_empty,
    simp only [u_empty, finset.union_empty, set.mem_sep_iff],
    split,
    simp only [set.mem_diff],
    split, assumption,
    simp only [set.mem_singleton_iff],
    rw [dim_geq_zero_iff_nonempty] at s_nontriv,
    assumption,
    
    intro s_in_X,
    simp only [simplicial_complex_boundary, set.mem_union] at s_in_bd_X,
    cases s_in_bd_X with s_in_bd_X s_contra,
    simp only [set.mem_sep_iff] at s_in_bd_X,
    cases s_in_bd_X with s_in_X s_not_sphere,
    simp only [set.mem_diff] at s_in_X,
    cases s_in_X with s_in_X s_ne,
    specialize s_not_sphere s_in_X,
    assumption,
    
    simp only [set.mem_singleton_iff] at s_contra,
    rw [dim_geq_zero_iff_nonempty] at s_nontriv,
    contradiction,
    
    simp only [set.mem_singleton_iff] at u_empty,
    simp only [u_empty, finset.inter_empty], },

  { intro u_in_link_of_bd,
    simp only [link, simplicial_complex.simplices, set.mem_sep_iff] at u_in_link_of_bd,
    choose u_in_bd_X su_in_bd_X su_empty using u_in_link_of_bd,
    simp only [set.mem_union] at u_in_bd_X su_in_bd_X ⊢,
    cases u_in_bd_X with u_in_bd_X u_empty,
    
    -- u ≠ ∅
    cases su_in_bd_X with su_in_bd_X su_contra,
    
    -- s ∪ u ≠ ∅
    left,
    simp only [set.mem_sep_iff, set.mem_diff] at u_in_bd_X su_in_bd_X ⊢,
    cases u_in_bd_X with u_in_bd_X u_not_sphere,
    cases u_in_bd_X with u_in_X u_ne,
    cases su_in_bd_X with su_in_bd_X su_not_sphere,
    cases su_in_bd_X with su_in_X su_ne,
    specialize u_not_sphere u_in_X,
    specialize su_not_sphere su_in_X,

    split, split,
    simp only [link, simplicial_complex.simplices, set.mem_sep_iff],
    repeat { split };
    assumption,

    assumption,

    intro u_in_link,
    apply stellar_equiv_preserves_not_stellar_sphere (Lk(X.complex, s ∪ u) su_in_X),
    assumption,

    have su_rw : u = (s ∪ u) \ s, from
    begin
      symmetry,
      rw [finset.union_sdiff_left, finset.sdiff_eq_self_iff_disjoint, disjoint.comm, finset.disjoint_iff_inter_eq_empty],
      assumption,
    end,

    have link_rw : Lk(Lk(X.complex, s) _, u) u_in_link
                    ≅ Lk(Lk(X.complex, s) _, (s ∪ u) \ s) (by { rw [←su_rw], assumption }), from
    begin
      apply simplicial_iso_preserves_equiv,
      conv_lhs {
        congr, congr, skip, rw [su_rw],
      },
    end,

    have sphere_rw : Lk(X.complex, s ∪ u) su_in_X ≅ₛₜ Lk(Lk(X.complex, s) _, u) u_in_link, from
    begin
      apply stellar_equiv_preserves_iso,
      rw [simplicial_iso_symm],
      apply simplicial_iso_trans
        (Lk(Lk(X.complex, s) _, u) u_in_link)
        (Lk(Lk(X.complex, s) _, (s ∪ u) \ s) (by { rw [←su_rw], assumption })),
      assumption,
      rw [simplicial_iso_symm],
      apply link_of_face_complement X.complex (s ∪ u) s,
      apply finset.subset_union_left,
    end,

    assumption,

    -- s ∪ u = ∅
    simp only [set.mem_singleton_iff, finset.union_eq_empty_iff] at su_contra,
    cases su_contra with s_contra u_contra,
    simp only [set.mem_sep_iff, set.mem_diff] at u_in_bd_X,
    cases u_in_bd_X with u_in_bd_X u_not_sphere,
    cases u_in_bd_X with u_in_X u_ne,
    simp only [set.mem_singleton_iff] at u_ne,
    contradiction,
    
    -- u = ∅
    right,
    assumption, }
end

lemma stellar_subdiv_link_of_star_complement_is_sphere
    (X : simplicial_complex ℕ)
    (s t : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : s ∉ (simplicial_complex_boundary X).simplices →
      t ∉ (simplicial_complex_boundary X).simplices →
        t ∈ (X\St(X, s) s_in_X).simplices →
          t ∉ ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices →
            is_stellar_sphere (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry)
:= begin
  intros s_nin_bd t_nin_bd t_in_star_comp t_nin_star_bd,
  simp only[simplicial_complex_boundary, is_stellar_sphere] at s_nin_bd t_nin_bd,
  simp only[set.mem_union, set.mem_sep_iff, set.mem_diff] at s_nin_bd t_nin_bd,
  simp only[not_or_distrib, not_and_distrib, not_forall, not_not] at s_nin_bd t_nin_bd,

  cases s_nin_bd with s_nin_bd s_ne,
  cases s_nin_bd with contra link_s_sphere,
  cases contra; contradiction,

  choose s_in_X k k_ge_neg_one link_s_sphere using link_s_sphere,

  let t_in_star_comp' := t_in_star_comp,
  simp only[star_complement, set.mem_sep_iff] at t_in_star_comp,
  choose t_in_X s_nss_t using t_in_star_comp,

  cases t_nin_bd with t_nin_bd t_ne,
  cases t_nin_bd with contra link_t_sphere,
  cases contra; contradiction,

  choose t_in_X n n_ge_neg_one link_t_sphere using link_t_sphere,
  
  apply stellar_equiv_preserves_stellar_sphere
    (Lk(X, t) t_in_X),
  simp only[is_stellar_sphere, is_stellar_n_sphere],
  use n, split; assumption,

  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_preserves_equiv,
  symmetry,
  apply stellar_subdiv_link_of_star_complement;
  assumption,
end

lemma stellar_subdiv_link_of_star_is_sphere
    (X : simplicial_complex ℕ)
    (s t : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : s ∉ (simplicial_complex_boundary X).simplices →
      (∃ (t₁ t₂ t₃ : finset ℕ),
          nonempty t₁ ∧ t₁ ∈ (Lk(X, s) s_in_X).simplices ∧
          nonempty t₂ ∧ t₂ ∈ (∂s).simplices ∧
          nonempty t₃ ∧ t₃ ∈ (@simplex ℕ {x}).simplices ∧
          t = t₁ ∪ t₂ ∪ t₃) →
        is_stellar_sphere (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry)
:= begin
  intro s_nin_bd,
  simp only[simplicial_complex_boundary, is_stellar_sphere] at s_nin_bd,
  simp only[set.mem_union, set.mem_sep_iff, set.mem_diff] at s_nin_bd,
  simp only[not_or_distrib, not_and_distrib, not_forall, not_not] at s_nin_bd,

  cases s_nin_bd with s_nin_bd s_ne,
  cases s_nin_bd with contra link_s_sphere,
  cases contra; contradiction,

  choose s_in_X k k_ge_neg_one link_s_sphere using link_s_sphere,

  intro t_in_join,
  choose t₁ t₂ t₃ t₁_ne t₁_in_link t₂_ne t₂_in_bd t₃_ne t₃_in_barycenter t_decomp using t_in_join,

  apply stellar_equiv_preserves_stellar_sphere (@empty_sc ℕ),
  simp only[is_stellar_sphere, is_stellar_n_sphere],
  use -1, split,
  trivial,
  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_preserves_equiv,
  have H_neg : -1 = int.neg_succ_of_nat 0, by tauto,
  rw [H_neg],
  unfold stellar_n_sphere,

  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_preserves_equiv,
  symmetry,
  apply stellar_subdiv_link_of_star,
  use t₁, use t₂, use t₃,
  split, assumption,
  split, assumption,
  split, assumption,
  split, assumption,
  split, assumption,
  split, assumption,
  assumption,
end

lemma stellar_subdiv_link_of_link_barycenter_is_sphere
    (X : simplicial_complex ℕ)
    (s t : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : s ∉ (simplicial_complex_boundary X).simplices →
      (∃ (t₁ t₂ : finset ℕ),
          nonempty t₁ ∧ t₁ ∈ (Lk(X, s) s_in_X).simplices ∧
          nonempty t₂ ∧ t₂ ∈ (@simplex ℕ {x}).simplices ∧
          t = t₁ ∪ t₂) →
        is_stellar_sphere (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry)
:= begin
  intro s_nin_bd,
  simp only[simplicial_complex_boundary, is_stellar_sphere] at s_nin_bd,
  simp only[set.mem_union, set.mem_sep_iff, set.mem_diff] at s_nin_bd,
  simp only[not_or_distrib, not_and_distrib, not_forall, not_not] at s_nin_bd,

  cases s_nin_bd with s_nin_bd s_ne,
  cases s_nin_bd with contra link_s_sphere,
  cases contra; contradiction,

  choose s_in_X k k_ge_neg_one link_s_sphere using link_s_sphere,

  intro t_in_join,
  choose t₁ t₂ t₁_ne t₁_in_link t₂_ne t₂_in_barycenter t_decomp using t_in_join,

  apply stellar_equiv_preserves_stellar_sphere (∂s),
  simp only[is_stellar_sphere, is_stellar_n_sphere],
  use (dim s), split,
  sorry,
  apply stellar_equiv_preserves_iso,
  apply simplex_boundary_is_sphere s,

  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_preserves_equiv,
  symmetry,
  apply stellar_subdiv_link_of_link_barycenter,
  use t₁, use t₂,
  split, assumption,
  split, assumption,
  split, assumption,
  split, assumption,
  assumption,
end

lemma stellar_subdiv_link_of_boundary_barycenter_is_sphere
    (X : simplicial_complex ℕ)
    (s t : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : s ∉ (simplicial_complex_boundary X).simplices →
      (∃ (t₁ t₂ : finset ℕ),
          nonempty t₁ ∧ t₁ ∈ (@simplex ℕ {x}).simplices ∧
          nonempty t₂ ∧ t₂ ∈ (∂s).simplices ∧
          t = t₁ ∪ t₂) →
        is_stellar_sphere (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry)
:= begin
  intro s_nin_bd,
  simp only[simplicial_complex_boundary, is_stellar_sphere] at s_nin_bd,
  simp only[set.mem_union, set.mem_sep_iff, set.mem_diff] at s_nin_bd,
  simp only[not_or_distrib, not_and_distrib, not_forall, not_not] at s_nin_bd,

  cases s_nin_bd with s_nin_bd s_ne,
  cases s_nin_bd with contra link_s_sphere,
  cases contra; contradiction,

  choose s_in_X k k_ge_neg_one link_s_sphere using link_s_sphere,

  intro t_in_join,
  choose t₁ t₂ t₁_ne t₁_in_barcenter t₂_ne t₂_in_bd t_decomp using t_in_join,

  apply stellar_equiv_preserves_stellar_sphere
    (Lk(X, s) s_in_X),
  simp only[is_stellar_sphere, is_stellar_n_sphere],
  use k, split; assumption,

  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_preserves_equiv,
  symmetry,
  apply stellar_subdiv_link_of_boundary_barycenter,
  use t₁, use t₂,
  split, assumption,
  split, assumption,
  split, assumption,
  split; assumption,
end

lemma stellar_subdiv_link_of_barycenter_is_sphere
    (X : simplicial_complex ℕ)
    (s : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : s ∉ (simplicial_complex_boundary X).simplices →
      is_stellar_sphere (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), {x}) sorry)
:= begin
  intro s_nin_bd,
  simp only[simplicial_complex_boundary, is_stellar_sphere] at s_nin_bd,
  simp only[set.mem_union, set.mem_sep_iff, set.mem_diff] at s_nin_bd,
  simp only[not_or_distrib, not_and_distrib, not_forall, not_not] at s_nin_bd,

  cases s_nin_bd with s_nin_bd s_ne,
  cases s_nin_bd with contra link_s_sphere,
  cases contra; contradiction,

  choose s_in_X k k_ge_neg_one link_s_sphere using link_s_sphere,

  apply stellar_equiv_preserves_stellar_sphere
    ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]),
  apply join_stellar_spheres_gen;
  simp only[is_stellar_sphere, is_stellar_n_sphere],
  use k, split; assumption,
  use (dim s), split,
  sorry,
  apply stellar_equiv_preserves_iso,
  apply simplex_boundary_is_sphere s,

  apply stellar_equiv_preserves_iso,
  apply simplicial_iso_preserves_equiv,
  symmetry,
  apply stellar_subdiv_link_of_barycenter,
end

lemma stellar_subdiv_star_comp_link_is_sphere
    (X : simplicial_complex ℕ)
    (s t : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : s ∉ (simplicial_complex_boundary X).simplices →
      t ∉ (simplicial_complex_boundary X).simplices →
        t ∈ (star_complement X s s_in_X).simplices →
          is_stellar_sphere (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry)
:= begin
  intros s_nin_bd t_nin_bd t_in_star_comp,

  let t_in_star_comp' := t_in_star_comp,
  simp only[star_complement, set.mem_sep_iff] at t_in_star_comp',
  choose t_in_X s_nss_t using t_in_star_comp',

  let t_nin_bd' := t_nin_bd,
  simp only[simplicial_complex_boundary] at t_nin_bd,
  simp only[set.mem_union, set.mem_sep_iff, set.mem_diff] at t_nin_bd,
  simp only[not_or_distrib, not_and_distrib, not_forall, not_not] at t_nin_bd,

  choose link_t_sphere t_ne using t_nin_bd,
  cases link_t_sphere with contra link_t_sphere,
  cases contra; contradiction,

  choose t_in_X link_t_sphere using link_t_sphere,

  by_cases t_in_join : t ∈ ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices,

  { apply stellar_equiv_preserves_stellar_sphere
      (σ((Lk(X, t) t_in_X), s\t, x; sorry, sorry, sorry)),
    apply stellar_equiv_preserves_stellar_sphere
      (Lk(X, t) t_in_X),
    assumption,
    
    apply relation.refl_trans_gen.single,
    simp only[stellar_move],
    right, left,
    use (s \ t),
    
    have st_in_link : s \ t ∈ (Lk(X, t) t_in_X).simplices, by sorry,
    use st_in_link,
    
    have st_ne : nonempty ↥(s \ t), by sorry,
    use st_ne,
    
    use x,
    
    have x_nin_link : x ∉ vertices (Lk(X, t) t_in_X), by sorry,
    use x_nin_link,
    
    apply stellar_equiv_preserves_iso,
    apply simplicial_iso_preserves_equiv,
    symmetry,
    apply stellar_subdiv_anticomm_link,
    assumption, },

  { apply stellar_equiv_preserves_stellar_sphere
      (Lk(X, t) t_in_X),
    assumption,
    
    apply stellar_equiv_preserves_iso,
    apply simplicial_iso_preserves_equiv,
    symmetry,
    apply stellar_subdiv_link_of_star_complement;
    assumption, },
end

lemma stellar_subdiv_join_link_is_sphere
    (X : simplicial_complex ℕ)
    (s t : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : s ∉ (simplicial_complex_boundary X).simplices →
      t ∉ (simplicial_complex_boundary X).simplices →
        t ∈ ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices →
          is_stellar_sphere (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry)
:= begin
  intros s_nin_bd t_nin_bd t_in_join,

  let t_in_join' := t_in_join,
  rw [join_proj_mem] at t_in_join',
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join',
  rw [join_proj_mem] at t'_in_join,
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join,
  subst t'_decomp,

  let t_nin_bd' := t_nin_bd,
  simp only[simplicial_complex_boundary] at t_nin_bd,
  simp only[set.mem_union, set.mem_sep_iff, set.mem_diff] at t_nin_bd,
  simp only[not_or_distrib, not_and_distrib, not_forall, not_not] at t_nin_bd,

  by_cases t_in_star_comp : t ∈ (star_complement X s s_in_X).simplices,
  { apply stellar_subdiv_star_comp_link_is_sphere;
    assumption, },

  { choose link_t_sphere t_ne using t_nin_bd,
    cases link_t_sphere with contra link_t_sphere,
    cases contra with t_nin_X contra,
    
    { by_cases t₃_ne : t₃ = ∅,
      have contra : t₃ ≠ ∅, by sorry,
      contradiction,

      have t₃_eq_x : t₃ = {x}, by sorry,
      by_cases t₁_ne : t₁ = ∅;
      by_cases t₂_ne : t₂ = ∅,

      -- t₁ = ∅, t₂ = ∅
      rw [t₁_ne, t₂_ne, t₃_eq_x] at t_decomp,
      simp only[finset.union_empty] at t_decomp,
      simp only[t_decomp],
      apply stellar_subdiv_link_of_barycenter_is_sphere,
      assumption,

      -- t₁ = ∅, t₂ ≠ ∅
      rw [t₁_ne] at t_decomp,
      simp only[finset.union_empty] at t_decomp,
      rw [←ne.def, ←finset.nonempty_iff_ne_empty, ←finset.nonempty_coe_sort] at t₂_ne t₃_ne,
      apply stellar_subdiv_link_of_boundary_barycenter_is_sphere,
      assumption,
      use t₃, use t₂,
      split, assumption,
      split, assumption,
      split, assumption,
      split; assumption,

      -- t₁ ≠ ∅, t₂ = ∅
      rw [t₂_ne] at t_decomp,
      simp only[finset.union_empty] at t_decomp,
      rw [←ne.def, ←finset.nonempty_iff_ne_empty, ←finset.nonempty_coe_sort] at t₁_ne t₃_ne,
      apply stellar_subdiv_link_of_link_barycenter_is_sphere,
      assumption,
      use t₁, use t₃,
      split, assumption,
      split, assumption,
      split, assumption,
      split, assumption,
      rw [finset.union_comm],
      assumption,

      -- t₁ ≠ ∅, t₂ ≠ ∅
      rw [←ne.def, ←finset.nonempty_iff_ne_empty, ←finset.nonempty_coe_sort] at t₁_ne t₂_ne t₃_ne,
      apply stellar_subdiv_link_of_star_is_sphere,
      assumption,
      use t₁, use t₂, use t₃,
      split, assumption,
      split, assumption,
      split, assumption,
      split, assumption,
      split, assumption,
      split, assumption,
      rw [finset.union_comm, finset.union_comm t₁ t₂, ←finset.union_assoc],
      assumption, },
      
    contradiction,
    
    choose t_in_X link_t_sphere using link_t_sphere,
    have contra : t ∈ (star_complement X s s_in_X).simplices, from
    begin
      simp only[star_complement, set.mem_sep_iff],
      split, assumption,

      sorry,
    end,
    contradiction, },
end

lemma stellar_mfd_boundary_incl_left
    (X : simplicial_complex ℕ)
    (s : finset ℕ) [s_ne : nonempty s]
    (x n : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : is_stellar_n_manifold X n →
      s ∉ (simplicial_complex_boundary X).simplices →
        (simplicial_complex_boundary (@stellar_subdivision _ _ X s s_ne x s_in_X x_nin_X)).simplices
          ⊆ (simplicial_complex_boundary X).simplices
:= begin
  intros X_mfd s_nin_bd,
  rw [set.subset_def],
  intros t,
  contrapose,
  intros t_nin_bd,

  let t_nin_bd' := t_nin_bd,
  simp only[simplicial_complex_boundary] at t_nin_bd' ⊢,
  simp only[set.mem_union, set.mem_sep_iff, set.mem_diff] at t_nin_bd' ⊢,
  simp only[not_or_distrib, not_and_distrib, not_forall, not_not] at t_nin_bd' ⊢,

  cases t_nin_bd' with t_nin_bd' t_ne,
  split,

  by_cases t_in_subdiv : t ∉ (stellar_subdivision X s x s_in_X x_nin_X).simplices,

  -- t ∉ σX 
  left, left,
  assumption,

  -- t ∈ σX
  simp only[not_not] at t_in_subdiv,
  let t_in_subdiv' := t_in_subdiv,
  simp only[stellar_subdivision, simplicial_union, set.mem_union] at t_in_subdiv',

  cases t_in_subdiv' with t_in_star_comp t_in_join;
  right; use t_in_subdiv,

  apply stellar_subdiv_star_comp_link_is_sphere;
  assumption,

  apply stellar_subdiv_join_link_is_sphere;
  assumption,

  assumption,
end

lemma stellar_subdiv_star_comp_link_is_not_sphere
    (X : simplicial_complex ℕ)
    (s t : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : s ∉ (simplicial_complex_boundary X).simplices →
      t ∈ (simplicial_complex_boundary X).simplices \ {∅} →
        t ∈ (star_complement X s s_in_X).simplices →
          ¬is_stellar_sphere (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry)
:= begin
  intros s_nin_bd t_in_bd t_in_star_comp,

  let t_in_star_comp' := t_in_star_comp,
  simp only[star_complement, set.mem_sep_iff] at t_in_star_comp',
  choose t_in_X s_nss_t using t_in_star_comp',

  let t_in_bd' := t_in_bd,
  simp only[simplicial_complex_boundary] at t_in_bd',
  simp only[set.mem_union, set.mem_sep_iff, set.mem_diff] at t_in_bd',
  choose t_in_bd' t_ne using t_in_bd',

  cases t_in_bd' with t_in_bd' contra,
  choose t_in_X link_t_not_sphere using t_in_bd',
  choose t_in_X t_ne using t_in_X,
  specialize link_t_not_sphere t_in_X,

  by_cases t_in_join : t ∈ ((π₁ (boundary_disjoint_link X s s_in_X))[Lk(X, s) s_in_X ⋆ ∂s]).simplices,

  { apply stellar_equiv_preserves_not_stellar_sphere
      (σ((Lk(X, t) t_in_X), s\t, x; sorry, sorry, sorry)),
    apply stellar_equiv_preserves_not_stellar_sphere
      (Lk(X, t) t_in_X),
    assumption,
    
    apply relation.refl_trans_gen.single,
    simp only[stellar_move],
    right, left,
    use (s \ t),
    
    have st_in_link : s \ t ∈ (Lk(X, t) t_in_X).simplices, by sorry,
    use st_in_link,
    
    have st_ne : nonempty ↥(s \ t), by sorry,
    use st_ne,
    
    use x,
    
    have x_nin_link : x ∉ vertices (Lk(X, t) t_in_X), by sorry,
    use x_nin_link,
    
    apply stellar_equiv_preserves_iso,
    apply simplicial_iso_preserves_equiv,
    symmetry,
    apply stellar_subdiv_anticomm_link,
    assumption, },

  { apply stellar_equiv_preserves_not_stellar_sphere
      (Lk(X, t) t_in_X),
    assumption,
    
    apply stellar_equiv_preserves_iso,
    apply simplicial_iso_preserves_equiv,
    symmetry,
    apply stellar_subdiv_link_of_star_complement;
    assumption, },

  contradiction,
end

lemma stellar_subdiv_join_link_is_not_sphere
    (X : simplicial_complex ℕ)
    (s t : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : s ∉ (simplicial_complex_boundary X).simplices →
      t ∈ (simplicial_complex_boundary X).simplices \ {∅} →
        t ∈ ((π₁ (barycenter_join_boundary_disjoint_link X s x s_in_X x_nin_X))[((π₁ (barycenter_disjoint_boundary X s x s_in_X x_nin_X))[(simplex {x} ⋆ ∂s)] ⋆ Lk(X, s) s_in_X)]).simplices →
          ¬is_stellar_sphere (Lk(σ(X, s, x; s_ne, s_in_X, x_nin_X), t) sorry)
:= begin
  intros s_nin_bd t_in_bd t_in_join,

  let t_in_join' := t_in_join,
  rw [join_proj_mem] at t_in_join',
  choose t' t'_in_join t₁ t₁_in_link t_decomp using t_in_join',
  rw [join_proj_mem] at t'_in_join,
  choose t₃ t₃_in_barycenter t₂ t₂_in_bd t'_decomp using t'_in_join,
  subst t'_decomp,

  let t_in_bd' := t_in_bd,
  simp only[simplicial_complex_boundary] at t_in_bd',
  simp only[set.mem_union, set.mem_sep_iff, set.mem_diff] at t_in_bd',
  choose t_in_bd' t_ne using t_in_bd',
  
  cases t_in_bd' with t_in_bd' contra,
  choose t_in_X link_t_not_sphere using t_in_bd',
  choose t_in_X t_ne using t_in_X,
  specialize link_t_not_sphere t_in_X,

  by_cases t_in_star_comp : t ∈ (star_complement X s s_in_X).simplices,
  { apply stellar_subdiv_star_comp_link_is_not_sphere;
    assumption, },

  { simp only[star_complement, set.mem_sep_iff, not_and_distrib, not_not] at t_in_star_comp,
    cases t_in_star_comp with t_nin_X s_ss_t,
    contradiction,
    
    have contra : s ∈ (simplicial_complex_boundary X).simplices, from
    begin
      simp only[set.mem_diff] at t_in_bd,
      choose t_in_bd t_ne using t_in_bd,
      apply (simplicial_complex_boundary X).subset_closed t;
      assumption,
    end,
    contradiction, },

  contradiction,
end

lemma stellar_mfd_boundary_incl_right
    (X : simplicial_complex ℕ)
    (s : finset ℕ) [s_ne : nonempty s]
    (x n : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : is_stellar_n_manifold X n →
      s ∉ (simplicial_complex_boundary X).simplices →
        (simplicial_complex_boundary X).simplices
          ⊆ (simplicial_complex_boundary (@stellar_subdivision _ _ X s s_ne x s_in_X x_nin_X)).simplices
:= begin
  intros X_mfd s_nin_bd,
  rw [set.subset_def],
  intros t t_in_bd,

  let t_in_bd' := t_in_bd,
  simp only[simplicial_complex_boundary] at t_in_bd' ⊢,
  simp only[set.mem_union, set.mem_sep_iff, set.mem_diff] at t_in_bd' ⊢,
  cases t_in_bd' with link_t_sphere t_empty,

  choose t_in_X link_t_sphere using link_t_sphere,
  choose t_in_X t_ne using t_in_X,
  specialize link_t_sphere t_in_X,

  left, split, split,
  sorry,
  assumption,

  intro t_in_subdiv,
  let t_in_subdiv' := t_in_subdiv,
  simp only[stellar_subdivision, simplicial_union, set.mem_union] at t_in_subdiv',

  cases t_in_subdiv' with t_in_star_comp t_in_join,

  apply stellar_subdiv_star_comp_link_is_not_sphere,
  assumption,
  simp only[set.mem_diff],
  split; assumption,
  assumption,

  apply stellar_subdiv_join_link_is_not_sphere,
  assumption,
  simp only[set.mem_diff],
  split; assumption,
  assumption,

  right, assumption,
end

-- Lemma 3.8, p.17
lemma stellar_mfd_boundary_ident
    (X : simplicial_complex ℕ)
    (s : finset ℕ) [s_ne : nonempty s]
    (x n : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
  : is_stellar_n_manifold X n →
      s ∉ (simplicial_complex_boundary X).simplices →
        simplicial_complex_boundary (@stellar_subdivision _ _ X s s_ne x s_in_X x_nin_X)
          ≅ simplicial_complex_boundary X
:= begin
  intros X_mfd s_nin_bd,
  have s_link_sphere : is_stellar_sphere (Lk(X, s) s_in_X), from
  begin
    simp only [simplicial_complex_boundary] at s_nin_bd,
    simp only [set.mem_union, set.mem_sep_iff] at s_nin_bd,
    simp only [not_or_distrib, not_and_distrib, not_forall, not_not] at s_nin_bd,
    cases s_nin_bd with link_sphere s_ne,

    cases link_sphere with contra link_sphere,
    finish,

    choose s_in_X link_sphere using link_sphere,
    assumption,
  end,
  
  apply simplicial_iso_preserves_equiv,
  rw [set.subset.antisymm_iff],
  split,
  apply (@stellar_mfd_boundary_incl_left X s s_ne x n s_in_X x_nin_X X_mfd s_nin_bd),
  apply (@stellar_mfd_boundary_incl_right X s s_ne x n s_in_X x_nin_X X_mfd s_nin_bd),
end

lemma stellar_ball_boundary_comm
    (X : simplicial_complex ℕ)
    (s : finset ℕ) [s_ne : nonempty s]
    (x : ℕ)
    (s_in_X : s ∈ X.simplices)
    (x_nin_X : x ∉ vertices X)
    (s_in_bd : s ∈ (simplicial_complex_boundary X).simplices)
  : is_stellar_ball X →
      simplicial_complex_boundary (σ(X, s, x; s_ne, s_in_X, x_nin_X))
        ≅ σ(simplicial_complex_boundary X, s, x; s_ne, s_in_bd, sorry)
:= sorry

lemma disk_boundary_is_sphere
    (n : ℤ)
  : simplicial_complex_boundary D(n + 1) ≅ S(n)
:= sorry

lemma stellar_equiv_factors_stellar_ball_boundary
    (X Y : simplicial_complex ℕ)
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
  cases K_move_L with L_subdiv_K K_subdiv_L,

  choose t Ht Ht_ne y Hy L_subdiv_K using L_subdiv_K,
  apply stellar_equiv_trans
    (simplicial_complex_boundary K)
    (simplicial_complex_boundary (σ(L, t, y; Ht_ne, Ht, Hy))),
  apply stellar_equiv_preserves_iso,
  apply simplicial_complex_boundary_iso,
  assumption,

  by_cases (t ∈ (simplicial_complex_boundary L).simplices),

  -- t ∈ ∂L case
  rw [stellar_equiv_symm],
  apply stellar_equiv_trans
    (simplicial_complex_boundary L)
    (σ(simplicial_complex_boundary L, t, y; Ht_ne, h, sorry)),
  apply relation.refl_trans_gen.single,
  unfold stellar_move,
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
  simp only[is_stellar_ball] at L_ball,
  choose l l_ge_neg_one L_ball using L_ball,
  have L_mfd : is_stellar_n_manifold L l.to_nat, by sorry,

  apply stellar_equiv_preserves_iso,
  apply stellar_mfd_boundary_ident;
  assumption,

  cases K_subdiv_L with K_subdiv_L K_iso_L,
  choose s Hs Hs_ne x Hx K_subdiv_L using K_subdiv_L,
  rw [stellar_equiv_symm],
  apply stellar_equiv_trans
    (simplicial_complex_boundary L)
    (simplicial_complex_boundary (σ(K, s, x; Hs_ne, Hs, Hx))),
  apply stellar_equiv_preserves_iso,
  apply simplicial_complex_boundary_iso,
  assumption,

  by_cases (s ∈ (simplicial_complex_boundary K).simplices),

  -- s ∈ ∂K case
  rw [stellar_equiv_symm],
  apply stellar_equiv_trans
    (simplicial_complex_boundary K)
    (σ(simplicial_complex_boundary K, s, x; Hs_ne, h, sorry)),
  apply relation.refl_trans_gen.single,
  unfold stellar_move,
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
  simp only[is_stellar_ball] at K_ball,
  choose k k_ge_neg_one K_ball using K_ball,
  have K_mfd : is_stellar_n_manifold K k.to_nat, by sorry,

  apply stellar_equiv_preserves_iso,
  apply stellar_mfd_boundary_ident;
  assumption,

  apply stellar_equiv_preserves_iso,
  apply simplicial_complex_boundary_iso,
  assumption,
end

-- Corollary 3.9, p.17
lemma boundary_of_ball_is_sphere
    (X : simplicial_complex ℕ)
    (n : ℕ)
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

lemma join_simplicial_complex_boundary_is_subcomplex_left
    (X Y : simplicial_complex ℕ)
  : (simplicial_complex_boundary X) ⋆ Y ⊆ X ⋆ Y
:= begin
  apply simplicial_join_subcomplex,
  apply simplicial_complex_boundary_is_subcomplex,
  refl,
end

lemma join_simplicial_complex_boundary_is_subcomplex_right
    (X Y : simplicial_complex ℕ)
  : X ⋆ (simplicial_complex_boundary Y) ⊆ X ⋆ Y
:= begin
  apply simplicial_join_subcomplex,
  refl,
  apply simplicial_complex_boundary_is_subcomplex,
end

lemma union_join_simplicial_complex_boundary_is_subcomplex
    (X Y : simplicial_complex ℕ)
  : ((X ⋆ (simplicial_complex_boundary Y) ∪ (simplicial_complex_boundary X) ⋆ Y)) ⊆ X ⋆ Y
:= begin
  simp only [simplicial_complex.has_subset, is_subcomplex],
  apply set.union_subset,
  apply join_simplicial_complex_boundary_is_subcomplex_right,
  apply join_simplicial_complex_boundary_is_subcomplex_left,
end

lemma union_join_simplicial_complex_boundary_is_subcomplex_vertices
    (X Y : simplicial_complex ℕ)
  : vertices ((X ⋆ (simplicial_complex_boundary Y)) ∪ ((simplicial_complex_boundary X) ⋆ Y)) ⊆ vertices (X ⋆ Y)
:= begin
  apply is_subcomplex_vertices,
  apply union_join_simplicial_complex_boundary_is_subcomplex,
end

lemma stellar_ball_boundary_distr_join_union_left
    (X Y : stellar_manifold)
    (m n : ℕ)
    (φ : simplicial_coe (X.complex ⋆ Y.complex) ℕ)
  : is_stellar_n_ball X.complex m →
      is_stellar_n_ball Y.complex n →
        φ[X.complex ⋆ (simplicial_complex_boundary Y.complex); sorry] ⊆ simplicial_complex_boundary (φ[X.complex ⋆ Y.complex])
:= begin
  intros X_ball Y_ball,
  unfold is_stellar_n_ball at *,

  simp only [simplicial_complex.has_subset, is_subcomplex, set.subset_def],
  intros s s_in_bd,
  dsimp only [simplicial_complex_boundary, simplicial_image, simplicial_complex.simplices],
  simp only [set.mem_sep_iff, set.mem_diff, set.mem_set_of],
  
  simp only [simplicial_image, simplicial_complex.simplices] at s_in_bd,
  simp only [set.mem_set_of] at s_in_bd,
  choose s' s'_in_bd s'_eq_s using s_in_bd,
  dsimp only [simplicial_complex_boundary, simplicial_join, simplicial_complex.simplices] at s'_in_bd,
  simp only [set.mem_set_of] at s'_in_bd,

  choose t t_in_X u u_in_Y tu_eq_s' using s'_in_bd,
  simp only [set.mem_union, set.mem_sep_iff, set.mem_diff] at u_in_Y,
  cases u_in_Y with u_in_bd u_empty,

  -- u ∈ ∂Y
  cases u_in_bd with u_in_bd u_not_sphere,
  cases u_in_bd with u_in_Y u_ne,
  specialize u_not_sphere u_in_Y,
  
  left, split, split,
  use s', split,
  rw [←tu_eq_s', simplicial_join_sep],
  split; assumption,
  assumption,
  rw [set.mem_singleton_iff] at u_ne ⊢,
  rw [←s'_eq_s, ←tu_eq_s', finset.image_eq_empty, simplex_disjoint_empty],
  simp only [not_and_distrib],
  sorry, -- TODO: previous tauto call
  
  -- Lk(φ[X ⋆ Y], s) is not stellar sphere
  intro s''_in_XY_img,
  choose s'' s''_in_XY s''_eq_s using s''_in_XY_img,
  
  apply stellar_equiv_preserves_not_stellar_sphere
    (φ[Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y; sorry]),
  have link_Y_ne : ¬Lk(Y.complex, u) u_in_Y ≅ @empty_sc ℕ, from
  begin
    apply not_stellar_sphere_imp_nonempty,
    assumption,
  end,
  have u_dim : 0 ≤ dim u, by sorry,

  rw [link_not_sphere_iff_ball _ _ _ u_dim link_Y_ne] at u_not_sphere,
  unfold is_stellar_ball at u_not_sphere,
  choose z z_bound link_Y_z_ball using u_not_sphere,

  have Hz : 0 ≤ z, from
  begin
    sorry,
  end,

  apply stellar_equiv_preserves_not_stellar_sphere
    (ν⟨D(z), Lk(X.complex, t) t_in_X⟩[D(z) ⋆ Lk(X.complex, t) t_in_X])
    (φ[Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y; sorry]),
  have H_cases := stellar_link_is_stellar_ball_or_sphere X t t_in_X,

  by_cases (t = ∅),
      
  -- t = ∅
  { apply stellar_equiv_preserves_not_stellar_sphere
      (ν⟨X.complex, D(z)⟩[X.complex ⋆ D(z)]),
    apply stellar_equiv_preserves_not_stellar_sphere
      (φᵈ⟨m, z⟩[D(m) ⋆ D(z)]),
    
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
    apply simplicial_iso_trans (φᵈ⟨m, z⟩[D(m) ⋆ D(z)]) (D(m) ⋆ D(z)),
    rw [simplicial_iso_symm],
    apply φᵈ⟨m, z⟩.iso_onto_image,
    apply join_stellar_disk,
    
    apply stellar_equiv_iso
      (D(m) ⋆ D(z))
      (X.complex ⋆ D(z)),
    apply φᵈ⟨m, z⟩.iso_onto_image,
    apply ν⟨X.complex, D(z)⟩.iso_onto_image,
    apply simplicial_join_stellar_equiv_left,
    rw [stellar_equiv_symm],
    apply X_ball,
    
    apply stellar_equiv_iso
      (X.complex ⋆ D(z))
      (Lk(X.complex, t) t_in_X ⋆ D(z)),
    apply ν⟨X.complex, D(z)⟩.iso_onto_image,
    apply simplicial_iso_trans
      (Lk(X.complex, t) t_in_X ⋆ D(z))
      (D(z) ⋆ Lk(X.complex, t) t_in_X),
    apply simplicial_join_comm,
    apply ν⟨D(z), Lk(X.complex, t) t_in_X⟩.iso_onto_image,
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
      (ν⟨D(z), S(↑(X.dim) - dim t - 1)⟩[D(z) ⋆ S(↑(X.dim) - dim t - 1)]),
    apply stellar_equiv_preserves_not_stellar_sphere
      (D(z + (↑(X.dim) - dim t - 1) + 1)),
    simp only [is_stellar_sphere, not_exists],
    intros x x_bound,
    rw [disk_is_sphere_iff_empty],
    simp only [not_and_distrib],
    left,
    simp only [not_lt],
    sorry, -- TODO: previous omega call
    
    have H_join_ball := join_stellar_ball_and_sphere
      D(z) S(↑(X.dim) - dim t - 1) ν⟨D(z), S(↑(X.dim) - dim t - 1)⟩
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
    apply ν⟨D(z), S(↑(X.dim) - dim t - 1)⟩.iso_onto_image,
    apply simplicial_iso_trans
      (Lk(X.complex, t) t_in_X ⋆ D(z))
      (D(z) ⋆ Lk(X.complex, t) t_in_X),
    apply simplicial_join_comm,
    apply ν⟨D(z), Lk(X.complex, t) t_in_X⟩.iso_onto_image,
    
    apply simplicial_join_stellar_equiv_left,
    unfold is_stellar_n_sphere at link_X_sphere,
    rw [stellar_equiv_symm],
    assumption,
    
    -- X ≅ₛₜ D(n)
    apply stellar_equiv_preserves_not_stellar_sphere
      (ν⟨D(z), D(↑(X.dim) - dim t - 1)⟩[D(z) ⋆ D(↑(X.dim) - dim t - 1)]),
    apply stellar_equiv_preserves_not_stellar_sphere
      (D(z + (↑(X.dim) - dim t - 1) + 1)),
    simp only [is_stellar_sphere, not_exists],
    intros x x_bound,
    rw [disk_is_sphere_iff_empty],
    simp only [not_and_distrib],
    left,
    simp only [not_lt],
    sorry, -- TODO: previous omega call
    
    have Hz_neg_one : -1 ≤ z, by sorry, -- TODO: previous omega call
    have H_join_ball := join_stellar_balls
      D(z) D(↑(X.dim) - dim t - 1) ν⟨D(z), D(↑(X.dim) - dim t - 1)⟩
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
    apply ν⟨D(z), D(↑(X.dim) - dim t - 1)⟩.iso_onto_image,
    apply simplicial_iso_trans
      (Lk(X.complex, t) t_in_X ⋆ D(z))
      (D(z) ⋆ Lk(X.complex, t) t_in_X),
    apply simplicial_join_comm,
    apply ν⟨D(z), Lk(X.complex, t) t_in_X⟩.iso_onto_image,
    
    apply simplicial_join_stellar_equiv_left,
    unfold is_stellar_n_ball at link_X_ball,
    rw [stellar_equiv_symm],
    assumption, },
  
  { apply stellar_equiv_iso
      (Lk(X.complex, t) t_in_X ⋆ D(z))
      (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y),
    apply simplicial_iso_trans
      (Lk(X.complex, t) t_in_X ⋆ D(z))
      (D(z) ⋆ Lk(X.complex, t) t_in_X),
    apply simplicial_join_comm,
    apply ν⟨D(z), Lk(X.complex, t) t_in_X⟩.iso_onto_image,
    apply (φ.restrict (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y) sorry).iso_onto_image,
    
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
      (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y)
      (Lk(X.complex ⋆ Y.complex, s') s'_in_XY),
    apply (φ.restrict (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y) sorry).iso_onto_image,
    let φs := simplicial_map.mk φ.coe (map_is_simplicial_onto_image (X.complex ⋆ Y.complex) φ.coe φ.injective),
    apply link_iso _ _ _ _ _ _ _ (coe_is_iso _ φ) s'_eq_s,
    
    rw [stellar_equiv_symm],
    apply stellar_equiv_preserves_iso,
    simp only [←tu_eq_s'],
    apply join_fact_link, },
  
  -- u = ∅
  by_cases (t = ∅),
  
  -- t = ∅
  rw [set.mem_singleton_iff] at u_empty,
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
  rw [set.mem_singleton_iff] at u_empty,
  rw [u_empty],
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
    (φᵈˢ⟨n, ↑(X.dim) - dim t - 1⟩[D(n) ⋆ S(↑(X.dim) - dim t - 1)]),
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
  sorry, -- TODO: previous omega call

  have H_join_ball := join_stellar_ball_and_sphere
    D(n) S(↑(X.dim) - dim t - 1) φᵈˢ⟨n, ↑(X.dim) - dim t - 1⟩
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
    rw [set.mem_singleton_iff] at u_empty,
    rw [u_empty],
    apply simplicial_complex_empty_simplex,
  end,
  apply stellar_equiv_iso
    (S(↑(X.dim) - dim t - 1) ⋆ D(n))
    (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y),
  apply simplicial_iso_trans
    (S(↑(X.dim) - dim t - 1) ⋆ D(n))
    (D(n) ⋆ S(↑(X.dim) - dim t - 1)),
  apply simplicial_join_comm,
  apply φᵈˢ⟨n, ↑(X.dim) - dim t - 1⟩.iso_onto_image,

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
  rw [set.mem_singleton_iff] at u_empty,
  simp only [u_empty],
  apply stellar_equiv_preserves_iso,
  apply link_ident,
  apply Y_ball,
  
  apply simplicial_join_stellar_equiv_left,
  unfold is_stellar_n_sphere at link_X_sphere,
  rw [stellar_equiv_symm],
  assumption,
  
  -- X ≅ₛₜ D(n)
  apply stellar_equiv_preserves_not_stellar_sphere
    (φᵈ⟨n, ↑(X.dim) - dim t - 1⟩[D(n) ⋆ D(↑(X.dim) - dim t - 1)]),
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
  sorry, -- TODO: previous omega call
  
  have H_join_ball := join_stellar_balls
    D(n) D(↑(X.dim) - dim t - 1) φᵈ⟨n, ↑(X.dim) - dim t - 1⟩
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
    rw [set.mem_singleton_iff] at u_empty,
    rw [u_empty],
    apply simplicial_complex_empty_simplex,
  end,
  apply stellar_equiv_iso
    (D(↑(X.dim) - dim t - 1) ⋆ D(n))
    (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y),
  apply simplicial_iso_trans
    (D(↑(X.dim) - dim t - 1) ⋆ D(n))
    (D(n) ⋆ D(↑(X.dim) - dim t - 1)),
  apply simplicial_join_comm,
  apply φᵈ⟨n, ↑(X.dim) - dim t - 1⟩.iso_onto_image,

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
  rw [set.mem_singleton_iff] at u_empty,
  simp only [u_empty],
  apply stellar_equiv_preserves_iso,
  apply link_ident,
  apply Y_ball,
  
  apply simplicial_join_stellar_equiv_left,
  unfold is_stellar_n_ball at link_X_ball,
  rw [stellar_equiv_symm],
  assumption,
end

lemma stellar_ball_boundary_distr_join_union_right
    (X Y : stellar_manifold)
    (m n : ℕ)
    (φ : simplicial_coe (X.complex ⋆ Y.complex) ℕ)
  : is_stellar_n_ball X.complex m →
      is_stellar_n_ball Y.complex n →
        φ[(simplicial_complex_boundary X.complex) ⋆ Y.complex; sorry] ⊆ simplicial_complex_boundary (φ[X.complex ⋆ Y.complex])
:= begin
  intros X_ball Y_ball,

  let H_comm := simplicial_join_comm X.complex Y.complex,

  unfold is_simplicially_iso at H_comm,
  choose f f_iso using H_comm,
  let f_iso_cases := f_iso,
  unfold is_simplicial_iso at f_iso_cases,
  choose g fg_inv using f_iso_cases,

  have ψ_injective : set.inj_on (φ.coe ∘ g.map) (vertices (Y.complex ⋆ X.complex)), from
  begin
    apply set.inj_on.comp φ.injective,
    sorry,
    sorry,
  end,
  let ψ := simplicial_coe.mk (φ.coe ∘ g.map) ψ_injective,

  apply simplicial_iso_preserves_subcomplex
    (ψ[Y.complex ⋆ (simplicial_complex_boundary X.complex); sorry])
    (simplicial_complex_boundary (ψ[Y.complex ⋆ X.complex])),
  apply coe_preserves_iso,
  apply simplicial_join_comm,

  apply simplicial_complex_boundary_iso,
  apply coe_preserves_iso,
  apply simplicial_join_comm,

  apply stellar_ball_boundary_distr_join_union_left Y X n m ψ Y_ball X_ball,
end

-- Proposition 3.11 (1), p.18
lemma stellar_ball_boundary_distr_join_union
    (X Y : stellar_manifold)
    (m n : ℕ)
    (φ : simplicial_coe (X.complex ⋆ Y.complex) ℕ)
  : is_stellar_n_ball X.complex m →
      is_stellar_n_ball Y.complex n →
        simplicial_complex_boundary (φ[X.complex ⋆ Y.complex])
        ≅ (X.complex ⋆ (simplicial_complex_boundary Y.complex)) ∪ ((simplicial_complex_boundary X.complex) ⋆ Y.complex)
:= begin
  intros X_ball Y_ball,
  unfold is_stellar_n_ball at *,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans
    (X.complex ⋆ simplicial_complex_boundary Y.complex ∪ simplicial_complex_boundary X.complex ⋆ Y.complex)
    (φ[X.complex ⋆ simplicial_complex_boundary Y.complex ∪ simplicial_complex_boundary X.complex ⋆ Y.complex; union_join_simplicial_complex_boundary_is_subcomplex_vertices X.complex Y.complex]),
  apply (φ.restrict (X.complex ⋆ simplicial_complex_boundary Y.complex ∪ simplicial_complex_boundary X.complex ⋆ Y.complex) _).iso_onto_image,
  rw [simplicial_iso_symm],

  apply simplicial_iso_preserves_equiv,
  apply set.eq_of_subset_of_subset,

  { intros s s_in_bd,
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
    sorry,
    
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
    
    have H_link_sep : ¬is_stellar_sphere (φ[Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y; sorry]), from
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

      apply (φ.restrict (Lk(X.complex, t) t_in_X ⋆ Lk(Y.complex, u) u_in_Y) _).iso_onto_image,
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

  { rw [simplicial_coe_union_simplices],
    apply set.union_subset,
    apply stellar_ball_boundary_distr_join_union_left X Y m n φ X_ball Y_ball,
    apply stellar_ball_boundary_distr_join_union_right X Y m n φ X_ball Y_ball, },
end

lemma stellar_sphere_boundary_empty
    (n : ℤ)
  : simplicial_complex_boundary S(n) ≅ @empty_sc ℕ
:= sorry

lemma stellar_sphere_boundary_empty'
    (X : simplicial_complex ℕ)
    (n : ℤ)
  : is_stellar_n_sphere X n → simplicial_complex_boundary X ≅ @empty_sc ℕ
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
    (x_nin_X : x ∉ vertices X)
  : Cone(X, x) x_nin_X ≅ D(0) ⋆ X
:= begin
  unfold cone,
  apply simplicial_join_iso_left,
  apply neg_one_ball_is_zero_disk,
end

-- Corollary 3.12, p.20
lemma stellar_ball_boundary_comm_cone_union
    (X : stellar_manifold)
    (x n : ℕ)
    (x_nin_X : x ∉ vertices X.complex)
    (φ : simplicial_coe (Cone(X.complex, x) x_nin_X) ℕ)
    (ψ : simplicial_coe (Cone((simplicial_complex_boundary X.complex), x) (simplicial_complex_boundary_subcomplex_vertices_contra X.complex x x_nin_X)) ℕ)
    (X_ball : is_stellar_n_ball X.complex n)
  : simplicial_complex_boundary (φ[Cone(X.complex, x) x_nin_X]) ≅ ψ[(Cone((simplicial_complex_boundary X.complex), x) (simplicial_complex_boundary_subcomplex_vertices_contra X.complex x x_nin_X))] ∪ X.complex
:= begin
  set x_nin_X_bd := simplicial_complex_boundary_subcomplex_vertices_contra X.complex x x_nin_X,

  apply simplicial_iso_trans
    (simplicial_complex_boundary (φ[Cone(X.complex, x) x_nin_X]))
    (simplicial_complex_boundary (ν⟨D(0), X.complex⟩[D(0) ⋆ X.complex])),
  apply simplicial_complex_boundary_iso,
  
  apply simplicial_iso_trans (φ[Cone(X.complex, x) x_nin_X]) (Cone(X.complex, x) x_nin_X),
  rw [simplicial_iso_symm],
  apply φ.iso_onto_image,

  rw [simplicial_iso_symm],
  apply simplicial_iso_trans (ν⟨D(0), X.complex⟩[D(0) ⋆ X.complex]) (D(0) ⋆ X.complex),
  rw [simplicial_iso_symm],
  apply ν⟨D(0), X.complex⟩.iso_onto_image,
  
  rw [simplicial_iso_symm],
  apply cone_is_zero_disk_join_boundary,

  apply simplicial_iso_trans
    (simplicial_complex_boundary (ν⟨D(0), X.complex⟩[D(0) ⋆ X.complex]))
    ((D(0) ⋆ simplicial_complex_boundary X.complex) ∪ (simplicial_complex_boundary D(0) ⋆ X.complex)),
  let Dm := stellar_manifold.mk D(0) 0 (by { apply stellar_n_ball_is_stellar_mfd }),
  apply stellar_ball_boundary_distr_join_union Dm X 0 n ν⟨D(0), X.complex⟩
    (by { unfold is_stellar_n_ball, simp only [nat.cast_zero], }) X_ball,

  apply simplicial_iso_trans
    ((D(0) ⋆ simplicial_complex_boundary X.complex) ∪ (simplicial_complex_boundary D(0) ⋆ X.complex))
    ((D(0) ⋆ simplicial_complex_boundary X.complex) ∪ (empty_sc ⋆ X.complex)),
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
    (D(0) ⋆ simplicial_complex_boundary X.complex)
    (Cone(simplicial_complex_boundary X.complex, x) x_nin_X_bd),
  rw [simplicial_iso_symm],
  apply cone_is_zero_disk_join_boundary,
  apply ψ.iso_onto_image,
end