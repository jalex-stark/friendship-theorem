/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
-/

import linear_algebra.basic
import linear_algebra.matrix
import linear_algebra.determinant
import data.polynomial
import ring_theory.polynomial
import data.equiv.basic

open polynomial

--open_locale classical
noncomputable theory

variables {n : Type*} [fintype n] [inhabited n] [decidable_eq n] 
variables {R : Type*} [comm_ring R] [nonzero R] --[decidable_eq R]

def char_poly (M : matrix n n R) : polynomial R :=
  matrix.det (λ (i j : n), (ite (i=j) X 0)-C(M i j))

variable [integral_domain R]

def poly_of_perm (M : matrix n n R) (σ : equiv.perm n) : polynomial R :=
  (σ.sign) * finset.univ.prod (λ (i : n), (ite (i= σ i) X 0) - C (M i (σ i)))

lemma nat_degree_of_mat_val  (M : matrix n n R) (σ : equiv.perm n) (i j:n) :
  ((ite (i=j) X 0)-C(M i j)).nat_degree = ite (i=j) 1 0 :=
begin
  by_cases i=j,
  {
  repeat {rw if_pos h},
  have pos:1>0, omega,
  change (X + (-C (M i j))).nat_degree = 1,
  rw add_comm,
  rw ← polynomial.C_neg,
  rw ← polynomial.degree_eq_iff_nat_degree_eq_of_pos pos,
  rw with_bot.coe_one,
  transitivity X.degree,
  {apply polynomial.degree_add_eq_of_degree_lt,
  rw degree_X,
  have leqzero:(C (-M i j)).degree≤ 0:= polynomial.degree_C_le,
  rw le_iff_eq_or_lt at leqzero,
  cases leqzero with eqzero ltzero,
  --rw eqzero,
  sorry,
  sorry,
  },
  simp,
  },
  repeat {rw if_neg h},
  ring,
  simp,
end

lemma nat_deg_prod_le_sum_nat_deg (f:n → polynomial R) (s:finset n) :
(s.prod f).nat_degree ≤ s.sum (nat_degree ∘ f) :=
begin
  sorry,
end

variable [decidable_eq R]

lemma deg_poly_of_perm (M : matrix n n R) (σ : equiv.perm n): 
  (poly_of_perm M σ).nat_degree ≤ (finset.filter (λ x : n, σ x = x) finset.univ).card:=
begin
  unfold poly_of_perm,
  have h1: (λ i:n, (ite (i= σ i) X 0) - C (M i (σ i)) )= λ i:n, ite (i= σ i) (X - C (M i (σ i))) (- C (M i (σ i))),
  {sorry,},
  rw h1,
  rw finset.prod_ite (λ i:n, (X - C (M i (σ i)))) (λ i:n, (- C (M i (σ i)))),
  by_cases (finset.filter (λ (x : n), ¬x = σ x) finset.univ).prod (λ (x : n), (λ (i : n), -C (M i (σ i))) x)=0,
  {
    rw h,
    repeat {rw ring.mul_zero},
    simp,
  },
  {
    sorry,
  }
end

lemma not_all_but_one_fixed_point (σ : equiv.perm n) :
σ ≠ equiv.refl n → (finset.filter (λ (x : n), ¬x = σ x) finset.univ).card ≥ 2 :=
begin
  sorry
end

lemma sum_poly_of_non_refl_low_degree (M : matrix n n R) :
  ((finset.univ.erase (equiv.refl n)).sum (poly_of_perm M)).degree ≤ ↑((fintype.card n) - 2):=
begin
  rw ← polynomial.mem_degree_le,
  -- show they're all in the submodule, then add with a lemma
  sorry
end

lemma char_poly_eq_poly_of_refl_plus_others (M: matrix n n R):
char_poly M = (finset.univ.erase (equiv.refl n)).sum (poly_of_perm M)+poly_of_perm M (equiv.refl n):=
begin
  sorry
end

lemma poly_of_refl_nat_degree_eq_dim (M: matrix n n R) :
(poly_of_perm M (equiv.refl n)).nat_degree = fintype.card n :=
begin
  sorry
end

lemma poly_of_refl_degree_eq_dim (M: matrix n n R) :
(poly_of_perm M (equiv.refl n)).degree = ↑(fintype.card n) :=
begin
  have pos:fintype.card n > 0,
  {simp only [gt_iff_lt],
  rw fintype.card_pos_iff,
  simp,},
  rw polynomial.degree_eq_iff_nat_degree_eq_of_pos pos,
  apply poly_of_refl_nat_degree_eq_dim,
end

lemma poly_of_refl_monic (M: matrix n n R) :
monic (poly_of_perm M (equiv.refl n)) :=
begin
  sorry
  --induct on polynomial.leading_coeff_mul
end

lemma degree_lt_of_degree_le_nat_lt {x: with_bot ℕ} {y z: ℕ} :
y<z → x ≤ ↑y → x < ↑z:=sorry

theorem deg_char_poly_eq_dim (M: matrix n n R) :
(char_poly M).degree = fintype.card n := 
begin
  rw char_poly_eq_poly_of_refl_plus_others,
  rw polynomial.degree_add_eq_of_degree_lt,
  {apply poly_of_refl_degree_eq_dim},
  {
    rw poly_of_refl_degree_eq_dim,
    have h:=sum_poly_of_non_refl_low_degree M,
    have ineq:(fintype.card n -2)<fintype.card n, sorry,
    apply degree_lt_of_degree_le_nat_lt ineq h,
  }
end

lemma char_poly_monic (M : matrix n n R):
  monic (char_poly M):=
begin
  rw monic.def,
  rw char_poly_eq_poly_of_refl_plus_others,
  rw polynomial.leading_coeff_add_of_degree_lt,
    apply poly_of_refl_monic,
  rw poly_of_refl_degree_eq_dim M,
  have ineq:(fintype.card n -2)<fintype.card n, sorry,
  apply degree_lt_of_degree_le_nat_lt ineq (sum_poly_of_non_refl_low_degree M),
end

theorem trace_from_char_poly (M: matrix n n R) :
(matrix.trace n R R) M = -(char_poly M).coeff (fintype.card n - 1) := 
begin
  rw char_poly_eq_poly_of_refl_plus_others,
  rw polynomial.coeff_add,
  have ineq : (fintype.card n - 2) < fintype.card n - 1, sorry,
  have h1 := sum_poly_of_non_refl_low_degree M,
  have h2 := degree_lt_of_degree_le_nat_lt ineq h1,
  have h3 := polynomial.coeff_eq_zero_of_degree_lt h2,
  rw h3,
  sorry,
end

theorem det_from_char_poly (M: matrix n n R) :
M.det = (-1)^(fintype.card n) * (char_poly M).coeff 0:= 
begin
  rw polynomial.coeff_zero_eq_eval_zero,
  sorry,
end


