/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
-/

import linear_algebra.nonsingular_inverse
import linear_algebra.basic
import data.polynomial
import changing_scalars
import linear_algebra.determinant

open polynomial matrix
/-
# Cayley-Hamilton Theorem

## Notations

## Implementation Notes

## References 
https://people.reed.edu/~jerry/332/28ch.pdf
-/

universe u

noncomputable theory

variables {n : Type u} [fintype n] [decidable_eq n] [inhabited n] {R : Type u} [ring R]

section general_matrix_ops


variables (n) (R)
def scalar_matrix (x : R) : matrix n n R := x • 1

lemma scalar_matrix_def (x : R) : 
scalar_matrix n R x = x • 1 := rfl

variables {n} {R}

lemma scalar_matrix_diagonal (x : R) :
scalar_matrix n R x = matrix.diagonal (λ i : n, x) :=
begin
  rw scalar_matrix,
  ext,
  rw matrix.smul_val,
  by_cases i = j,
  {
    rw h,
    simp,
  },
  {
    rw matrix.one_val_ne,
    rw matrix.diagonal_val_ne,
    rw mul_zero,
    exact h,
    exact h,
  }
end

@[simp]
lemma scalar_matrix_val (x : R) (i j : n): 
(scalar_matrix n R x) i j = ite (i = j) x 0 := 
begin
  rw scalar_matrix_diagonal,
  by_cases i = j,
  {
    rw if_pos h,
    rw h,
    simp,
  },
  {
    rw if_neg h,
    rw diagonal_val_ne h,
  }
end


def choose_index : n := arbitrary n

def vec_to_one_row (vec : n → R): matrix n n R :=
λ (i : n), ite (i = choose_index) vec 0

@[simp]
lemma undo_vec_to_one_row {vec : n → R}:
vec_to_one_row vec choose_index = vec :=
begin
  rw vec_to_one_row,
  simp,
end

/-
def vec_to_one_row_add_hom : (n → R) →+ matrix n n R :=
begin
  refine add_monoid_hom.mk vec_to_one_row _ _,
  {
    rw vec_to_one_row,
    ext,
    simp only [if_t_t, zero_val],
    refl,
  },
  {
    intros x y,
    repeat {rw vec_to_one_row},
    ext,
    by_cases (i = choose_index),
    {
      simp only [add_val],
      repeat {rw if_pos h},
      refl,
    },
    {
      simp only [add_val],
      repeat {rw if_neg h},
      simp,
    }
  }
end

lemma vec_to_one_row_add_hom_to_fun :
(vec_to_one_row_add_hom : (n → R) →+ matrix n n R).to_fun = vec_to_one_row := rfl
-/

lemma vec_to_one_row_other {vec : n → R} {i : n} (h : ¬ i = choose_index):
vec_to_one_row vec i = 0 :=
begin
  rw vec_to_one_row,
  change ite (i = choose_index) vec 0 = 0,
  rw if_neg h,
end

lemma vec_to_one_row_mul (vec : n → R) (M : matrix n n R) :
(vec_to_one_row vec) * M = vec_to_one_row (vec_mul vec M) :=
begin
  ext,
  --rw mul_eq_mul,
  --rw mul_val',
  by_cases i = choose_index,
  {
    rw h,
    rw mul_eq_mul,
    rw mul_val',
    simp only [undo_vec_to_one_row],
    rw vec_mul,
  },
  {
    refine congr _ rfl,
    rw vec_to_one_row_other h,
    ext,
    rw mul_eq_mul,
    rw mul_val',
    simp only [pi.zero_apply],
    rw vec_to_one_row_other h,
    simp,
  }
end

def row_elt (i : n) : matrix n n R := vec_to_one_row (λ j : n, ite (i = j) 1 0)

@[simp]
lemma row_elt_mul (i : n) (M : matrix n n R) :
(row_elt i) * M = vec_to_one_row (M i) :=
begin
  rw row_elt,
  rw vec_to_one_row_mul,
  refine congr rfl _,
  ext,
  rw vec_mul,
  rw dot_product,
  simp,
end

lemma vec_to_one_row_inj (vec : n → R) :
vec_to_one_row vec = 0 → vec = 0 :=
begin
  intro h,
  transitivity (vec_to_one_row vec) choose_index,
  {
    simp,
  },
  {
    rw h,
    simp,
  }
end

lemma vec_to_one_row_comp_inj (M : matrix n n R) :
vec_to_one_row ∘ M = 0 → M = 0 :=
begin
  intro h,
  ext,
  refine congr _ rfl,
  transitivity (vec_to_one_row ∘ M) i choose_index,
  {
    simp,
  },
  {
    rw h,
    simp,
  }
end

lemma vec_mul_scalar_matrix (x:R) {vec: n → R} {i: n}:
vec_mul vec (scalar_matrix n R x) i = (vec i) * x :=
begin
  rw scalar_matrix_diagonal,
  rw vec_mul_diagonal,
end

lemma vec_to_one_row_row_elt_mul_scalar (M : matrix n n R) :
(vec_to_one_row row_elt) * (scalar_matrix n (matrix n n R) M) = vec_to_one_row (vec_to_one_row ∘ M) :=
begin
  rw vec_to_one_row_mul,
  refine congr rfl _,
  ext,
  rw vec_mul_scalar_matrix,
  rw row_elt_mul,
end

lemma vec_to_one_row_row_elt_mul_big (M : matrix n n R) :
(vec_to_one_row row_elt) * (fun_apply (scalar_matrix n R) M) = vec_to_one_row (vec_to_one_row ∘ M.transpose) :=
begin
  rw vec_to_one_row_mul,
  refine congr rfl _,
  ext,
  rw fun_apply,
  rw vec_mul,
  --
  rw dot_product,
  simp only [row_elt_mul],
  rw finset.sum_apply,
  rw finset.sum_apply,

  rw function.comp_apply,
  by_cases i = choose_index,
  {
    rw h,
    simp,
  },
  {
    rw vec_to_one_row_other h,
    have hlam: (λ (g : n), vec_to_one_row (scalar_matrix n R (M g x) g) i j) = 0,
    {
      ext,
      simp only [pi.zero_apply],
      rw vec_to_one_row_other h,
      simp,
    },
    rw hlam,
    simp,
  }
end

lemma zero_of_vec_to_one_row_row_elt_mul_scalar_zero (M : matrix n n R) :
(vec_to_one_row row_elt) * (scalar_matrix n (matrix n n R) M) = 0 → M = 0:=
begin
  intro h,
  rw vec_to_one_row_row_elt_mul_scalar at h,
  apply vec_to_one_row_comp_inj,
  apply vec_to_one_row_inj,
  apply h,
end

instance is_semiring_hom_scalar_matrix : is_semiring_hom (scalar_matrix n R) :=
begin
  split,
  {
    unfold scalar_matrix,
    simp,
  },
  {
    unfold scalar_matrix,
    simp,
  },
  {
    intros x y,
    repeat {rw scalar_matrix_diagonal},
    simp,
  },
  {
    intros x y,
    repeat {rw scalar_matrix_diagonal},
    simp,
  }
end

lemma scalar_matrix_mul_eq_smul (x:R) {M: matrix n n R} :
(scalar_matrix n R x).mul M = x • M :=
begin
  rw scalar_matrix_diagonal,
  ext,
  simp,
end

lemma scalar_matrix_mul_vec_eq_smul (x:R) {vec: n → R} :
(scalar_matrix n R x).mul_vec vec = x • vec :=
begin
  rw scalar_matrix_diagonal,
  ext,
  rw matrix.mul_vec_diagonal,
  simp,
end


def matrix.mul_vec.add_monoid_hom_left (vec: n → R) : (matrix n n R) →+ (n → R) :=
begin
  refine add_monoid_hom.mk (λ M : matrix n n R, M.mul_vec vec) _ _,
  sorry,
  sorry,
end

lemma matrix.mul_vec.add_monoid_hom_left_to_fun (vec: n → R) {M: matrix n n R} : 
add_monoid_hom.to_fun (matrix.mul_vec.add_monoid_hom_left vec) M = M.mul_vec vec := rfl



end general_matrix_ops

variables {n} {R} [comm_ring R]

def m_C : matrix n n R → matrix n n (polynomial R) :=
  matrix.fun_apply C

def char_poly (M : matrix n n R) : polynomial R :=
  matrix.det ((X:polynomial R) • 1 - m_C (M))

lemma char_poly_transpose_eq (M : matrix n n R) : 
char_poly (M.transpose) = char_poly M :=
begin
  repeat {rw char_poly},
  rw ← det_transpose,
  refine congr rfl _,
  change (X • 1 + (- m_C M.transpose)).transpose = X • 1 + (- m_C M),
  rw transpose_add,
  rw ← scalar_matrix_def n (polynomial R) X,
  rw scalar_matrix_diagonal,
  rw diagonal_transpose,
  refine congr rfl _,
  rw m_C,
  repeat {rw fun_apply},
  ext,
  simp,
end

def eval_at_matrix (M : matrix n n R) : polynomial R →+* matrix n n R :=
begin
  refine ring_hom.mk (eval₂ (λ x : R, x • (1: matrix n n R)) M) _ _ _ _,
  {
    sorry,
  },
  {
    sorry,
  },
  {
    sorry,
  },
  {
    sorry,
  }
end

-- lemma eval_at_matrix_to_fun

lemma scalar_eval_commute (M : matrix n n R) (p : polynomial R):
scalar_matrix n (matrix n n R) ((eval_at_matrix M).to_fun p) = (matrix.ring_hom_apply (eval_at_matrix M)).to_fun (scalar_matrix n (polynomial R) p) :=
begin
  rw eval_at_matrix,
  rw matrix.ring_hom_apply_to_fun,
  repeat {rw scalar_matrix},
  ext,
  iterate 2 {refine congr _ rfl},
  by_cases i = j,
  {
    simp only [matrix.smul_val, matrix.mul_eq_mul, matrix.one_val, if_pos h, mul_one],
    change eval₂ (λ (x : R), x • (1 : matrix n n R)) M p = fun_apply (eval₂ (λ (x : R), x • 1) M) (p • 1) i j,
    rw fun_apply,
    rw ← scalar_matrix,
    simp only [scalar_matrix_val],
    refine congr rfl _,
    rw if_pos h,
  },
  {
    simp only [matrix.smul_val, matrix.mul_eq_mul, matrix.one_val, if_neg h, mul_zero],
    symmetry,
    --have inst: is_semiring_hom (scalar_matrix n R):=is_semiring_hom_scalar_matrix n R,
    --rw polynomial.eval₂_zero (scalar_matrix n R) M,
    sorry,
  }
end

lemma eval_at_matrix_comp_C {M : matrix n n R}:
(eval_at_matrix M) ∘ C = scalar_matrix n R := --polynomial.eval₂_C (scalar_matrix n R) M
begin
  sorry
end

lemma eval_at_matrix_X {M : matrix n n R}:
(eval_at_matrix M).to_fun X = M := --polynomial.eval₂_X (scalar_matrix n R) M
begin
  sorry
end



theorem cayley_hamilton (M : matrix n n R) :
eval₂ (λ x : R, x • (1: matrix n n R)) M (char_poly M) = 0 :=
begin
  rw ← char_poly_transpose_eq,
  change eval_at_matrix M (char_poly M.transpose) = 0,
  apply zero_of_vec_to_one_row_row_elt_mul_scalar_zero,
  change vec_to_one_row row_elt * scalar_matrix n (matrix n n R) ((eval_at_matrix M).to_fun (char_poly M.transpose)) = 0,
  rw scalar_eval_commute,
  rw scalar_matrix,
  rw char_poly,
  rw ← mul_adjugate,
  rw ← mul_eq_mul,
  change vec_to_one_row row_elt *
      (ring_hom_apply (eval_at_matrix M)) ((X • 1 - m_C M.transpose) * (X • 1 - m_C M.transpose).adjugate) = 0,
  rw ring_hom.map_mul,
  have hzero : vec_to_one_row row_elt * ((ring_hom_apply (eval_at_matrix M)) (X • 1 - m_C M.transpose)) = 0,
  {
    rw ring_hom.map_sub,
    rw mul_sub,
    rw ← scalar_matrix,
    change vec_to_one_row row_elt * (ring_hom_apply (eval_at_matrix M)).to_fun (scalar_matrix n (polynomial R) X) -
      vec_to_one_row row_elt * (ring_hom_apply (eval_at_matrix M)) (m_C M.transpose) =
    0,
    rw ← scalar_eval_commute,
    rw vec_to_one_row_row_elt_mul_scalar,
    change vec_to_one_row (vec_to_one_row ∘ (eval_at_matrix M).to_fun X) -
      vec_to_one_row row_elt * (fun_apply (eval_at_matrix M)) (m_C M.transpose) =
    0,
    rw m_C,
    rw fun_apply_comp,
    rw eval_at_matrix_comp_C,
    rw vec_to_one_row_row_elt_mul_big,
    rw transpose_transpose,
    rw eval_at_matrix_X,
    simp,
  },
  rw ← mul_assoc,
  rw hzero,
  simp,
end