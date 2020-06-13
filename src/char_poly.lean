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
import data.zmod.basic
import cayley_hamilton

open polynomial

universe u

open_locale classical
noncomputable theory

variables {n : Type u} [fintype n] [inhabited n] [decidable_eq n] 
variables {R : Type u} [comm_ring R] [nonzero R] --[decidable_eq R]

def poly_of_perm (M : matrix n n R) (σ : equiv.perm n) : polynomial R :=
  (σ.sign) * finset.univ.prod (λ (i : n), (ite (i= σ i) X 0) - C (M i (σ i)))
#check @nat_degree_mul_eq
#check @degree_mul_le


lemma nat_degree_mul_le {R : Type u} [comm_semiring R] (p q : polynomial R) :
(p * q).nat_degree ≤ p.nat_degree + q.nat_degree :=
begin
  have := degree_mul_le p q,
  sorry
end


lemma nat_degree_of_mat_val (M : matrix n n R) (σ : equiv.perm n) (i j:n) :
  ((ite (i=j) X 0)-C(M i j)).nat_degree = ite (i = j) 1 0 :=
begin
  split_ifs,
  { rw ← polynomial.degree_eq_iff_nat_degree_eq_of_pos (by omega),
    simp },
  simp,
end


--variable [decidable_eq R]

lemma gt_one_nonfixed_point_of_nonrefl {σ : equiv.perm n} :
σ ≠ equiv.refl n → 1 < (finset.filter (λ (x : n), ¬ x = σ x) finset.univ).card :=
begin
  contrapose,
  rw finset.one_lt_card_iff,
  intro hyp,
  push_neg,
  ext,
  simp,
  by_cases σ x = x, exact h,
  { exfalso, apply hyp,
    existsi x,
    existsi σ x,
    split,
    {rw finset.mem_filter,
      split, apply finset.mem_univ,
    {intro contra, apply h, symmetry, apply contra, }, },
  {rw finset.mem_filter,
    split, split,
    apply finset.mem_univ,
    {intro contra, 
      rw equiv.apply_eq_iff_eq σ x (σ x) at contra,
      apply h, symmetry, apply contra },
    {intro contra, apply h, symmetry, apply contra } } }
end

lemma lt_card_sub_one_fixed_point_of_nonrefl {σ : equiv.perm n} :
σ ≠ equiv.refl n → (finset.filter (λ (x : n), x = σ x) finset.univ).card < fintype.card n - 1:=
begin
  intro nonrefl,
  have hcard := gt_one_nonfixed_point_of_nonrefl nonrefl,
  have hun : (finset.filter (λ (x : n), x = σ x) finset.univ) ∪ (finset.filter (λ (x : n), ¬ x = σ x) finset.univ) = finset.univ :=  finset.filter_union_filter_neg_eq finset.univ,
  have hin : (finset.filter (λ (x : n), x = σ x) finset.univ) ∩ (finset.filter (λ (x : n), ¬ x = σ x) finset.univ) = ∅ :=  finset.filter_inter_filter_neg_eq finset.univ,
  rw ← finset.disjoint_iff_inter_eq_empty at hin,
  rw fintype.card,
  have h : ((finset.filter (λ (x : n), x = σ x) finset.univ) ∪ (finset.filter (λ (x : n), ¬ x = σ x) finset.univ)).card = (finset.filter (λ (x : n), x = σ x) finset.univ).card + (finset.filter (λ (x : n), ¬ x = σ x) finset.univ).card,
  {rw finset.card_disjoint_union hin,},
  rw hun at h,
  rw h,
  omega,
end

lemma poly_of_perm_factor_degree_card_fixed_points (M : matrix n n R) (σ : equiv.perm n) : 
(finset.filter (λ (x : n), x = σ x) finset.univ).prod (λ (i : n), (ite (i= σ i) X 0) - C (M i (σ i))).degree = (finset.filter (λ (x : n), x = σ x) finset.univ).card:=
begin

end

lemma poly_of_perm_in_low_deg_submodule (M : matrix n n R) (σ : equiv.perm n) : 
  σ ≠ equiv.refl n → (poly_of_perm M σ) ∈ polynomial.degree_lt R ↑((fintype.card n) - 1):=
begin
  intro nonrefl,
  have hfixed := not_all_but_one_fixed_point nonrefl,
end

lemma sum_poly_of_non_refl_low_degree (M : matrix n n R) :
  ((finset.univ.erase (equiv.refl n)).sum (poly_of_perm M)).degree < ↑((fintype.card n) - 1):=
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
  rw eval,
  --rw eval₂_
  sorry,
end

lemma poly_pow_p_char_p  {p : ℕ} [char_p R p] (f : polynomial R) :
f ^ p = f.comp (polynomial.X ^ p) :=
begin
  sorry
end

lemma char_poly_pow_p_char_p {p : ℕ} [char_p R p] (M : matrix n n R) :
char_poly (M ^ p) = char_poly M :=
begin
  sorry
end
