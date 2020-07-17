import data.matrix.basic linear_algebra.matrix data.polynomial linear_algebra.determinant linear_algebra.basic

open_locale classical
noncomputable theory

def sym_matrix {m α : Type*} [fintype m] (M: matrix m m α) : Prop :=
  M = M.transpose

lemma sym_matrix_apply {m α : Type*} [fintype m] {M: matrix m m α} (h : sym_matrix M) (i j : m):
  M i j = M j i:=
by { unfold sym_matrix at h, conv_rhs {rw h}, refl, }

variables (R : Type*) [ring R] -- should be semiring, but trace needs rings now

def matrix_J (m:Type*) [fintype m] : matrix m m R :=
  λ (i j:m), 1

@[simp] lemma matrix_J_apply (m:Type*) [fintype m] {i j : m} : matrix_J R m i j = 1 := rfl

lemma trace_J (m:Type*) [fintype m] :
matrix.trace m R R (matrix_J R m) = fintype.card m :=
begin
  rw matrix.trace,
  rw matrix_J,
  change (finset.univ.sum ∘ ⇑(matrix.diag m R R)) (λ (i j : m), 1) =
    ↑(fintype.card m),
  rw function.comp_apply,
  rw fintype.card,
  simp,
end