import data.matrix.basic
import ring_theory.tensor_product

noncomputable theory
open_locale classical
open_locale tensor_product big_operators

open tensor_product finset
open algebra.tensor_product


variables {R : Type*} [comm_ring R] {n : Type*} [fintype n] [inhabited n]
variables {A : Type*} [ring A] [algebra R A]
variables {B : Type*} [ring B] [algebra R B]

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

lemma finset.sum_tmul {α : Type*} (s : finset α) (f : α → A ) (x : B) : 
(∑ i in s, f i ⊗ₜ[R] x) = (∑ i in s, f i) ⊗ₜ[R] x   :=
begin
  induction s using finset.induction with a s ha hs, { simp },
  rw [sum_insert ha, hs, sum_insert ha, add_tmul]
end 

-- f : A ⊗[R] B ≃ₗ[R] C)
example : matrix n n A →ₗ[R] A ⊗[R] matrix n n R :=
{ to_fun := λ x, ∑ i j : n, (x i j) ⊗ₜ[R] (elem_matrix i j),
    map_add' := by { intros,
      rw ← sum_add_distrib,
      conv_rhs { congr, skip, funext, rw ← sum_add_distrib,}, 
      apply sum_congr, {refl}, intro i, norm_num,
      apply sum_congr, {refl}, intro j, norm_num,
      rw add_tmul },
    map_smul' := by { intros, simp_rw smul_sum, congr }}


def matrix_lin_equiv : matrix n n A ≃ₗ[R] A ⊗[R] matrix n n R :=
begin
-- now prove it's invertible by showing it takes a basis to a basis
end

example : matrix n n A ≃ₐ[R] A ⊗[R] matrix n n R := 
begin
  symmetry, 
  -- why doesn't this work?
  have := alg_equiv_of_linear_equiv_tensor_product matrix_lin_equiv,
end
