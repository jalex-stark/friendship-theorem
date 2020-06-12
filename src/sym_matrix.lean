import data.matrix.basic linear_algebra.matrix data.polynomial linear_algebra.determinant linear_algebra.basic

open_locale classical
noncomputable theory

section matrix_coe
def matrix_compose {m n α β:Type*} [fintype m] [fintype n] (f:α → β) :
  (matrix m n α)→(matrix m n β):=
  λ (M: matrix m n α) (i:m) (j:n), f(M i j)

def matrix_coe {m n α β:Type*} [fintype m] [fintype n] [has_coe α β] :
  (matrix m n α)→(matrix m n β):=
  λ (M: matrix m n α) (i:m) (j:n), (M i j:β)

@[instance] def matrix.has_coe {m n α β:Type*} [fintype m][fintype n][has_coe α β]:
  has_coe (matrix m n α) (matrix m n β):=⟨matrix_coe⟩

@[simp] lemma matrix_coe_comm {m n α β:Type*} [fintype m][fintype n][has_coe α β] {M:matrix m n α} {i:m} {j:n}:
  (M: matrix m n β) i j = (M i j:β):= rfl

end matrix_coe

def sym_matrix {m α : Type*} [fintype m] (M: matrix m m α): Prop :=
  M=M.transpose

lemma sym_matrix' {m α : Type*} [fintype m] (M: matrix m m α):
  sym_matrix M→ ∀ i j:m,  M i j = M j i:=
begin
  intro h,
  intros i j,
  transitivity M.transpose j i,
  refl,
  refine congr _ rfl,
  refine congr _ rfl,
  symmetry,
  apply h,
end

def get_row {m n α : Type*} [fintype m] [fintype n] (M: matrix m n α) (i: m): n → α :=
  λ (j: n), M i j

def get_col {m n α : Type*} [fintype m] [fintype n] (M: matrix m n α) (j: n): m → α :=
  λ (i: m), M i j
  
theorem mul_val_eq_dot_row_col {n α : Type*} [fintype n] [has_mul α] [add_comm_monoid α] (M N : matrix n n α):
  ∀ i k:n, (M.mul N) i k = matrix.dot_product (get_row M i) (get_col N k):=
begin
  intros i k,
  unfold get_row,
  unfold get_col,
  unfold matrix.mul,
end

@[simp] lemma transpose_col_eq_row {m α: Type*} [fintype m] (M: matrix m m α):
  ∀ (i:m), get_col M.transpose i = get_row M i :=
begin
  intro i,
  unfold get_col,
  unfold get_row,
  ext,
  refl,
end

@[simp] lemma transpose_row_eq_col {m α: Type*} [fintype m] (M: matrix m m α):
  ∀ (i:m), get_row M.transpose i = get_col M i :=
begin
  intro i,
  unfold get_col,
  unfold get_row,
  ext,
  refl,
end

theorem sym_matrix_col_eq_row {m α: Type*} [fintype m] (M: matrix m m α):
  sym_matrix M → ∀ (i:m), get_row M i = get_col M i :=
begin
  intro h,
  intro i,
  transitivity get_col M.transpose i,
  simp,
  unfold sym_matrix at h,
  rw ← h,
end

def matrix_J (m:Type*) [fintype m] : matrix m m ℤ :=
  λ (i j:m), 1

lemma trace_J (m:Type*) [fintype m] :
matrix.trace m ℤ ℤ (matrix_J m) = fintype.card m :=
begin
  rw matrix.trace,
  rw matrix_J,
  change (finset.univ.sum ∘ ⇑(matrix.diag m ℤ ℤ)) (λ (i j : m), 1) =
    ↑(fintype.card m),
  rw function.comp_apply,
  rw fintype.card,
  simp,
end