import Pachner.Basic.Dimension
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

variable {E : Type _}

noncomputable def edge_fun : Finset E → Option (Sym2 E) :=
  fun s => match s.toList with
  | [a, b] => s(a, b)
  | _ => none

def AbstractSimplicialComplex.edges
    (X : AbstractSimplicialComplex E)
  : Set (Sym2 E) := { edge_fun s | s ∈ X.faces }

def SimpleGraph.ofAbstract
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (_ : X.dim ≤ 1) -- Note: since higher dimensional faces are just "forgotten" this is not necessary,
                    --    but it is there to prevent unexpected behaviour
  : SimpleGraph E := SimpleGraph.fromEdgeSet (AbstractSimplicialComplex.edges X)

def Graph.ofAbstract
    [DecidableEq E]
    (X : AbstractSimplicialComplex E) [Fintype X.faces]
    (_ : X.dim ≤ 1) -- Note: since higher dimensional faces are just "forgotten" this is not necessary,
                    --    but it is there to prevent unexpected behaviour
  : Graph E (Sym2 E) where
      vertexSet := X.vertices
      IsLink e x y := e = s(x, y) ∧ e ∈ X.edges
      edgeSet := X.edges
      isLink_symm e e_in_E := by simp only [Symmetric, Sym2.eq_swap, imp_self, forall_true_iff]
      eq_or_eq_of_isLink_of_isLink e x y v w e_eq_xy e_eq_vw := by
        choose e_eq_xy _ using e_eq_xy
        choose e_eq_vw _ using e_eq_vw
        subst e_eq_xy
        simp only [Sym2.eq, Sym2.rel_iff', Prod.swap, Prod.ext_iff] at e_eq_vw
        cases' e_eq_vw with x_eq_v x_eq_w
        · left
          exact x_eq_v.1
        · right
          exact x_eq_w.1
      left_mem_of_isLink e x y e_eq_xy := by
        choose e_eq_xy e_in_E using e_eq_xy
        subst e
        simp only [AbstractSimplicialComplex.edges, Set.mem_setOf] at e_in_E
        choose s s_in_X fs_eq_e using e_in_E
        simp only [edge_fun] at fs_eq_e
        split at fs_eq_e
        · case h_1 a b s_eq_ab =>
          apply Option.some.inj at fs_eq_e
          simp only [Sym2.eq, Sym2.rel_iff', Prod.swap, Prod.ext_iff] at fs_eq_e
          apply_fun List.toFinset at s_eq_ab
          simp only [Finset.toList_toFinset, Finset.ext_iff] at s_eq_ab
          specialize s_eq_ab x
          simp only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false] at s_eq_ab
          cases' fs_eq_e with a_eq_x b_eq_x
          · choose a_eq_x _ using a_eq_x
            simp only [a_eq_x, true_or, iff_true] at s_eq_ab
            exact vertex_if_mem_face s_in_X s_eq_ab
          · choose _ b_eq_x using b_eq_x
            simp only [b_eq_x, or_true, iff_true] at s_eq_ab
            exact vertex_if_mem_face s_in_X s_eq_ab
        · case h_2 s_eq_ab_false =>
          simp only [reduceCtorEq] at fs_eq_e
      edge_mem_iff_exists_isLink e := by
        constructor
        · intro e_in_E
          let e_in_E' := e_in_E
          simp only [AbstractSimplicialComplex.edges, Set.mem_setOf] at e_in_E'
          choose s s_in_X fs_eq_e using e_in_E'
          simp only [edge_fun] at fs_eq_e
          split at fs_eq_e
          · case h_1 a b s_eq_ab =>
            apply Option.some.inj at fs_eq_e
            subst e
            use a, b
          · case h_2 s_eq_ab_false =>
            simp only [reduceCtorEq] at fs_eq_e
        · intro e_in_E
          choose x y _ e_in_E using e_in_E
          exact e_in_E
