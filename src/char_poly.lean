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

open_locale big_operators
open_locale classical
noncomputable theory

variables {n : Type u} [fintype n] [inhabited n] [decidable_eq n] 
variables {R : Type u} [integral_domain R] [nonzero R] --[decidable_eq R]

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

lemma gt_one_nonfixed_point_of_nonrefl {σ : equiv.perm n} (h : σ ≠ equiv.refl n) : 
1 < (finset.filter (λ (x : n), ¬ x = σ x) finset.univ).card :=
begin
  rw finset.one_lt_card_iff,
  contrapose! h,
  ext, dsimp,
  have := h x (σ x), 
  cases this, swap, cases this,
  all_goals { symmetry, revert this, simp }
end

lemma lt_card_sub_one_fixed_point_of_nonrefl {σ : equiv.perm n} (h : σ ≠ equiv.refl n) :
(finset.filter (λ (x : n), x = σ x) finset.univ).card < fintype.card n - 1:=
begin
  have hun := @finset.filter_union_filter_neg_eq _ (λ (x : n), x = σ x) _ _ _ finset.univ,
  have hin : (finset.filter (λ (x : n), x = σ x) finset.univ) ∩ (finset.filter (λ (x : n), ¬ x = σ x) finset.univ) = ∅ :=  finset.filter_inter_filter_neg_eq finset.univ,
  rw ← finset.disjoint_iff_inter_eq_empty at hin,
  rw fintype.card, conv_rhs { rw ← hun }, 
  rw finset.card_disjoint_union hin, 
  have := gt_one_nonfixed_point_of_nonrefl h, omega,
end


lemma degree_prod_eq_sum_degree (s : finset n) (f : n → polynomial R) (h : ∀ k ∈ s, f k ≠ 0) :
nat_degree (∏ k in s, f k) = ∑ k in s, nat_degree (f k) :=
begin
  revert h, apply finset.induction_on s, { simp },
  intros x s' hx hs' h, 
  rw finset.prod_insert hx, 
  rw nat_degree_mul_eq, swap, { apply h, simp }, 
  swap,
  { contrapose! h, rw finset.prod_eq_zero_iff at h,
    rcases h with ⟨ k, hk, hk'⟩, use k, 
    rw finset.mem_insert, tauto },
  rw finset.sum_insert hx, 
  simp only [add_right_inj], apply hs',
  intros k hk, apply h, simp [hk], 
end

lemma poly_of_perm_factor_degree_card_fixed_points (M : matrix n n R) (σ : equiv.perm n) : 
((finset.filter (λ (x : n), x = σ x) finset.univ).prod (λ (i : n), (ite (i= σ i) X 0) - C (M i (σ i)))).nat_degree 
= (finset.filter (λ (x : n), x = σ x) finset.univ).card :=
begin
  have nonzero : (∀ (k : n),
     k ∈ finset.filter (λ (x : n), x = σ x) finset.univ →
     (λ (i : n), ite (i = σ i) X 0 - C (M i (σ i))) k ≠ 0),
  { intros k hk, dsimp,
    rw finset.mem_filter at hk, rw if_pos hk.right,
    intro contra, 
    have h := polynomial.degree_X_sub_C (M k (σ k)), 
    rw contra at h, simp at h, tauto, },
  have h := degree_prod_eq_sum_degree (finset.filter (λ (x : n), x = σ x) finset.univ)
    (λ (i : n), (ite (i= σ i) X 0) - C (M i (σ i))) nonzero,
  rw h,
  rw ← mul_one (finset.filter (λ (x : n), x = σ x) finset.univ).card,
  apply finset.sum_const_nat,
  intros x hx,
  rw nat_degree_of_mat_val M σ,
  rw finset.mem_filter at hx,
  rw if_pos hx.right,
end

lemma poly_of_perm_in_low_deg_submodule (M : matrix n n R) (σ : equiv.perm n) : 
  σ ≠ equiv.refl n → (poly_of_perm M σ) ∈ polynomial.degree_lt R ↑((fintype.card n) - 1):=
begin
  intro nonrefl,
  have hfixed := lt_card_sub_one_fixed_point_of_nonrefl nonrefl,
  rw poly_of_perm,
  rw finset.prod_apply_ite,
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
  have pos : fintype.card n > 0, { simp [fintype.card_pos_iff] },
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
y<z → x ≤ ↑y → x < ↑z := sorry

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

section char_p

instance polynomial_char_p (p : ℕ) [char_p R p] : char_p (polynomial R) p :=
{ cast_eq_zero_iff :=
  begin
    intro k,
    have := _inst_6.cast_eq_zero_iff, have hk := this k, clear this,
    rw ← hk,
    rw polynomial.nat_cast_eq_C k,
    rw ← polynomial.C_0,
    rw polynomial.C_inj,
  end }

instance matrix_char_p (p : ℕ) [char_p R p] : char_p (matrix n n R) p :=
{ cast_eq_zero_iff :=
  begin
    intro k,
    have := _inst_6.cast_eq_zero_iff, have hk := this k, clear this,
    rw ← hk,
    sorry,
  end }

lemma poly_pow_p_char_p  (p : ℕ) [fact p.prime] [char_p R p] (f : polynomial R) :
f ^ p = f.comp (polynomial.X ^ p) :=
begin
  sorry
end

lemma pow_commutes_with_det (k : ℕ) (M : matrix n n R) :
(M ^ k).det = (M.det) ^ k :=
begin
  induction k with k hk, simp,
  repeat {rw pow_succ}, rw ← hk, simp,
end

lemma pow_commutes_with_m_C (k : ℕ) (M : matrix n n R) :
m_C (M ^ k) = (m_C M) ^ k :=
begin
  unfold m_C,
  change matrix.ring_hom_apply (ring_hom.of C) (M ^ k) = matrix.ring_hom_apply (ring_hom.of C) M ^ k,
  induction k with k hk, simp, simp
end

theorem add_pow_char_comm_elts (α : Type u) [ring α] {p : ℕ} [fact p.prime]
  [char_p α p] (x y : α) : 
  commute x y → (x + y)^p = x^p + y^p :=
begin
  intro comm,
  rw [commute.add_pow comm, finset.sum_range_succ, nat.sub_self, pow_zero, nat.choose_self],
  rw [nat.cast_one, mul_one, mul_one, add_right_inj],
  transitivity,
  { refine finset.sum_eq_single 0 _ _,
    { intros b h1 h2,
      have := nat.prime.dvd_choose_self (nat.pos_of_ne_zero h2) (finset.mem_range.1 h1) hp,
      rw [← nat.div_mul_cancel this, nat.cast_mul, char_p.cast_eq_zero α p],
      simp only [mul_zero] },
    { intro H, exfalso, apply H, exact finset.mem_range.2 hp.pos } },
  rw [pow_zero, nat.sub_zero, one_mul, nat.choose_zero_right, nat.cast_one, mul_one]
end

lemma comp_commutes_with_det (p : polynomial R) (M : matrix n n (polynomial R)) :
(matrix.fun_apply (λ q : polynomial R, q.comp p) M).det = (M.det).comp p :=
begin
  sorry
end

lemma char_poly_pow_p_char_p (p : ℕ) [fact p.prime] [char_p R p] (M : matrix n n R) :
char_poly (M ^ p) = char_poly M :=
begin
  have := poly_pow_p_char_p p (char_poly M),
  unfold char_poly at *,
  apply frobenius_inj (polynomial R) p,
  repeat {rw frobenius_def},
  rw poly_pow_p_char_p,
  rw ← pow_commutes_with_det,
  repeat {rw sub_eq_add_neg},
  rw add_pow_char_comm_elts, swap,
  { rw commute, rw semiconj_by, simp, },
  rw pow_commutes_with_m_C,
  rw ← comp_commutes_with_det,
  refine congr rfl _,
  ext,
  refine congr (congr rfl _) rfl,
  rw matrix.fun_apply,
  simp only [add_comp, X_comp, matrix.neg_val, mul_comp, matrix.add_val, matrix.smul_val, m_C, matrix.one_val],
  
  -- rw polynomial.eval_comp at this
  -- apply poly_pow_p_char_p,
  sorry,
end

end char_p
