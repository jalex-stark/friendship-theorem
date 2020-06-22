import data.matrix.basic
import ring_theory.tensor_product

noncomputable theory
open_locale classical
open_locale tensor_product big_operators

open tensor_product finset
open algebra.tensor_product


variables {R : Type} [comm_ring R] {n : Type} [fintype n] [inhabited n]
variables {A : Type} [ring A] [algebra R A]
variables {B : Type} [ring B] [algebra R B]

example (f : matrix n n R) :
  ∀ (x y : matrix n n A),
    (∑ (i j : n), (x + y) i j ⊗ₜ[R] f i j) =
      (∑ (i j : n), x i j ⊗ₜ[R] f i j) +
        ∑ (i j : n), y i j ⊗ₜ[R] f i j :=
begin
  intros,
  rw ← sum_add_distrib,
  conv_rhs { congr, skip, funext, rw ← sum_add_distrib,}, 
  apply sum_congr, {refl}, intro i, norm_num,
  apply sum_congr, {refl}, intro j, norm_num,
  rw add_tmul
end



def elem_matrix (i j : n) : matrix n n R :=
λ i' j', if (i = i' ∧ j = j') then 1 else 0

instance : algebra R (matrix n n A) :=
begin 
  refine algebra.of_semimodule _ _;
  { intros, 
    ext, dsimp, unfold matrix.mul matrix.dot_product, 
    simp [smul_sum]}
end

lemma finset.sum_tmul {α : Type} (s : finset α) (f : α → A ) (x : B) : 
(∑ i in s, f i ⊗ₜ[R] x) = (∑ i in s, f i) ⊗ₜ[R] x   :=
begin
  induction s using finset.induction with a s ha hs, { simp },
  rw [sum_insert ha, hs, sum_insert ha, add_tmul]
end 

-- f : A ⊗[R] B ≃ₗ[R] C)
example : matrix n n A →ₗ[R] A ⊗[R] matrix n n R :=
{ to_fun := λ x, ∑ i j : n, (x i j) ⊗ₜ[R] (elem_matrix i j),
    map_add' := by { intros, simp only [add_tmul, sum_add_distrib, matrix.add_val] },
    map_smul' := by { intros, simp_rw smul_sum, congr }
}


def matrix_lin_equiv : matrix n n A ≃ₗ[R] A ⊗[R] matrix n n R :=
begin
-- now prove it's invertible by showing it takes a basis to a basis
  sorry
end

example : matrix n n A ≃ₐ[R] A ⊗[R] matrix n n R := 
begin
  symmetry, 
  -- why doesn't this work?
  sorry
  --simp_rw alg_equiv_of_linear_equiv_tensor_product,
end

variables {m : Type} [fintype m] [inhabited m]
variables {m' : Type} [fintype m'] [inhabited m'] {n' : Type} [fintype n'] [inhabited n'] 

--def matrix_to_vec_prod : matrix m n R → (m × n) → R := function.uncurry

def matrix_matrix_rearrange : matrix m m' (matrix n n' R) → matrix m n (matrix m' n' R) :=
λ (M : matrix m m' (matrix n n' R)), λ (m₁ : m) (n₁ : n) (m₂ : m') (n₂ : n'), M m₁ m₂ n₁ n₂

def matrix_matrix_to_matrix_prod (M : matrix m m' (matrix n n' R)) : matrix (m × n) (m' × n') R :=
function.uncurry ∘ (function.uncurry (matrix_matrix_rearrange M))

/--matrix.vec_mul_vec as a linear map-/
def outer_product_left_linear (v : m → R) : (n → R) →ₗ[R] (matrix m n R) :=
begin
  refine linear_map.mk (matrix.vec_mul_vec v) _ _; intros; ext,
  { simp only [matrix.vec_mul_vec, matrix.add_val], rw ← mul_add, refl },
  { simp only [matrix.vec_mul_vec, algebra.id.smul_eq_mul, pi.smul_apply], ring }
end

/--converts a tensor between explicit vector spaces to its matrix representation -/
def tensor_product.tensor_to_matrix : ((m → R) ⊗[R] (n → R)) →ₗ[R] (matrix m n R) :=
begin
  refine tensor_product.lift _,
  refine linear_map.mk outer_product_left_linear _ _; intros; ext;
  simp [outer_product_left_linear, matrix.vec_mul_vec],
  rw ← add_mul, refl, ring
end

/--constructs a tensor between explicit vector spaces from its matrix representation -/
def tensor_product.matrix_to_tensor : (matrix m n R) →ₗ[R] ((m → R) ⊗[R] (n → R)) :=
begin
  refine linear_map.mk _ _ _,
  { intro M, refine ∑ (i : m), ∑ (j : n), (M i j) • (λ k : m, ite (k=i) 1 0)
    ⊗ₜ[R] (λ k : n, ite (k=j) 1 0) },
  { intros, simp [add_smul, finset.sum_add_distrib] },
  { intros, simp [finset.smul_sum, smul_smul] }
end


def tensor_product.vector_tmul_equiv :
  ((m → R) ⊗[R] (n → R)) ≃ₗ[R] (matrix m n R) :=
begin
  apply linear_equiv.of_linear tensor_product.tensor_to_matrix tensor_product.matrix_to_tensor,
  sorry,
  sorry
end