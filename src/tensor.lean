import data.matrix.basic
import ring_theory.tensor_product

noncomputable theory
open_locale classical
open_locale tensor_product big_operators
open tensor_product finset

variables {R : Type*} [comm_ring R] {n : Type*} [fintype n] [inhabited n]
variables {A : Type*} [ring A] [algebra R A]

def elem_matrix (i j : n) : matrix n n R :=
λ i' j', if (i = i' ∧ j = j') then 1 else 0

instance : algebra R (matrix n n A) :=
begin 
  refine algebra.of_semimodule _ _;
  { intros, 
    ext, dsimp, unfold matrix.mul matrix.dot_product, 
    simp [smul_sum]},
end

instance : algebra R (A ⊗ matrix n n R) :=
begin
  exact algebra.tensor_product.algebra,
end

example : matrix n n A →ₐ[R] A ⊗ matrix n n R :=
begin
  refine {to_fun := λ x, ∑ i j : n, (x i j) ⊗ₜ[R] (elem_matrix i j), 
  map_one' := _, map_mul' := _, map_zero' := _, map_add' := _, commutes' := _},
end
