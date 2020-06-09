import data.fintype.basic linear_algebra.matrix data.matrix.basic data.real.basic
import sym_matrix findicator 

open_locale classical
noncomputable theory

section graph


structure simple_graph (V: Type*) :=
(E: V → V → Prop)
(loopless: irreflexive E)
(undirected: symmetric E)


class fin_graph (V: Type*) [fintype V] extends simple_graph V

def neighbors {V: Type*} [fintype V] (G: fin_graph V) (v: V):finset V:=
begin
  have E:= G.E,
  have vset:=_inst_1.elems,
  have nbrs:= {w ∈ vset | E v w},
  exact nbrs,
end

@[simp] lemma neighbor_iff_adjacent  {V: Type*} [fintype V] (G: fin_graph V) (v w:V):
  w ∈ neighbors G v ↔ G.E v w:=
begin
  unfold neighbors,
  simp,
  split,
  intro h,
  exact h.right,
  intro h,
  split,
  apply finset.mem_univ,
  exact h,
end

def degree {V: Type*} [fintype V] (G: fin_graph V) (v: V):=
(neighbors G v).card

def regular_graph {V:Type*} [fintype V] (G:fin_graph V) (d:ℕ ) :Prop:=
  ∀ v:V, degree G v=d

end graph
section adjacency_matrix

def adjacency_matrix {V:Type*} [fintype V] (G: fin_graph V): matrix V V ℤ :=
  λ v w:V, (prop_to_nat(G.E v w):ℤ)

@[simp] lemma adjacency_matrix_el_idem {V:Type*} [fintype V] (G: fin_graph V) (i j: V):
  (adjacency_matrix G i j)*(adjacency_matrix G i j)=adjacency_matrix G i j :=
begin
  unfold adjacency_matrix,
  norm_cast, simp,
end

theorem adjacency_matrix_symm {V:Type*} [fintype V] (G: fin_graph V):
  sym_matrix (adjacency_matrix G):=
begin
  unfold sym_matrix,
  ext,
  unfold matrix.transpose,
  have E:= G.E,
  unfold adjacency_matrix, norm_cast,
  --simp,
  refine congr _ _, refl,
  refine propext _,
  split; apply G.undirected,
end

lemma adjacency_matrix_row_ind {V:Type*} [fintype V] (G: fin_graph V): 
  ∀ v:V, get_row (adjacency_matrix G) v = findicator (neighbors G v):=
begin
  intro v, ext, 
  by_cases G.E v x,
  {transitivity (1:ℤ),
  { unfold get_row,
  unfold adjacency_matrix, simp [h]},
  symmetry,
  rwa [ind_one_iff_mem, neighbor_iff_adjacent]},
  
  transitivity (0:ℤ),
  { unfold get_row, unfold adjacency_matrix, simp [h] },
  symmetry,
  rwa [ind_zero_iff_not_mem, neighbor_iff_adjacent],
end

lemma adjacency_matrix_col_ind {V:Type*} [fintype V] (G: fin_graph V): 
  ∀ v:V, get_col (adjacency_matrix G) v = findicator (neighbors G v):=
begin
  intro v,
  rw ← sym_matrix_col_eq_row (adjacency_matrix G) (adjacency_matrix_symm G) v,
  apply adjacency_matrix_row_ind,
end

@[simp] lemma adj_mat_diag_zero {V:Type*} [fintype V] {G: fin_graph V}{v:V}:
  (adjacency_matrix G v v)=0:=
begin
  unfold adjacency_matrix, norm_cast,
  apply false_to_nat,
  apply simple_graph.loopless,
end

theorem adj_mat_traceless {V:Type*} [fintype V] (G: fin_graph V) :
  matrix.trace V ℤ ℤ (adjacency_matrix G: matrix V V ℤ) = 0 := by simp

theorem deg_from_adj_mat_sq {V:Type*} [fintype V] (G: fin_graph V):
  ∀ (i:V), ((adjacency_matrix G) * (adjacency_matrix G)) i i=degree G i:=
begin
  intro i,
  have M:=adjacency_matrix G,
  change (adjacency_matrix G).mul (adjacency_matrix G) i i= degree G i,
  rw mul_val_eq_dot_row_col (adjacency_matrix G) (adjacency_matrix G) i i,
  rw adjacency_matrix_row_ind G i,
  rw adjacency_matrix_col_ind G i,
  rw dot_inds_eq_card_inter,
  rw finset.inter_self,
  refl,
end

-- def real_adjacency_matrix {V:Type*} [fintype V] (G: fin_graph V): matrix V V ℝ :=
  -- matrix_compose (coe:ℕ → ℝ) (adjacency_matrix G)

lemma reg_adj_mat_mul_vec_ones_is_degs {V:Type*} [fintype V] (G: fin_graph V)(d: ℕ):
  regular_graph G d → (adjacency_matrix G).mul_vec (λ i:V, 1)=(λ i:V,d):=
begin
  intro reg,
  ext,
  unfold matrix.mul_vec,
  change matrix.dot_product (get_row (adjacency_matrix G) x) (λ (i : V), 1) = d,
  rw adjacency_matrix_row_ind G x,
  have hfind : (λ (i:V), (1 : ℤ)) = findicator finset.univ,
  ext,
  symmetry,
  rw ind_one_iff_mem,
  apply finset.mem_univ,
  rw hfind,
  rw dot_inds_eq_card_inter,
  simp,
  unfold regular_graph at reg,
  apply reg x,
end

end adjacency_matrix