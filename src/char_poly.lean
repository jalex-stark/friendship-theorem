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
import algebra.module

open polynomial

universe u

open_locale big_operators
open_locale classical
noncomputable theory

variables {n : Type u} [fintype n] [inhabited n] [decidable_eq n] 
variables {R : Type u} [integral_domain R] [nonzero R] --[decidable_eq R]

def poly_of_perm (M : matrix n n R) (σ : equiv.perm n) : polynomial R :=
  (σ.sign) * finset.univ.prod (λ (i : n), (ite (σ i = i) X 0) - C (M (σ i) i))
#check @nat_degree_mul_eq
#check @degree_mul_le

@[simp]
lemma nat_degree_of_mat_val (M : matrix n n R) (i j:n) :
  ((ite (i=j) X 0)-C(M i j)).nat_degree = ite (i = j) 1 0 :=
begin
  split_ifs,
  { rw ← polynomial.degree_eq_iff_nat_degree_eq_of_pos (by omega),
    simp },
  simp,
end


--variable [decidable_eq R]

lemma gt_one_nonfixed_point_of_nonrefl {σ : equiv.perm n} (h : σ ≠ equiv.refl n) : 
1 < (finset.filter (λ (x : n), ¬ σ x = x) finset.univ).card :=
begin
  rw finset.one_lt_card_iff,
  contrapose! h,
  ext, dsimp,
  have := h (σ x) x, 
  cases this, swap, cases this,
  all_goals { revert this, simp }
end

lemma lt_card_sub_one_fixed_point_of_nonrefl {σ : equiv.perm n} (h : σ ≠ equiv.refl n) :
(finset.filter (λ (x : n), σ x = x) finset.univ).card < fintype.card n - 1:=
begin
  have hun := @finset.filter_union_filter_neg_eq _ (λ (x : n), σ x = x) _ _ _ finset.univ,
  have hin : (finset.filter (λ (x : n), σ x = x) finset.univ) ∩ (finset.filter (λ (x : n), ¬ σ x = x) finset.univ) = ∅ :=  finset.filter_inter_filter_neg_eq finset.univ,
  rw ← finset.disjoint_iff_inter_eq_empty at hin,
  rw fintype.card, conv_rhs { rw ← hun }, 
  rw finset.card_disjoint_union hin, 
  have := gt_one_nonfixed_point_of_nonrefl h, omega,
end


lemma degree_prod_eq_sum_degree_of_nonzero (s : finset n) (f : n → polynomial R) (h : ∀ k ∈ s, f k ≠ 0) :
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

lemma degree_prod_eq_sum_degree_of_prod_nonzero (s : finset n) (f : n → polynomial R) (h : (∏ k in s, f k) ≠ 0) :
nat_degree (∏ k in s, f k) = ∑ k in s, nat_degree (f k) :=
begin
  apply degree_prod_eq_sum_degree_of_nonzero,
  rwa ← finset.prod_ne_zero_iff,
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
  have h := degree_prod_eq_sum_degree_of_nonzero (finset.filter (λ (x : n), x = σ x) finset.univ)
    (λ (i : n), (ite (i= σ i) X 0) - C (M i (σ i))) nonzero,
  rw h,
  rw ← mul_one (finset.filter (λ (x : n), x = σ x) finset.univ).card,
  apply finset.sum_const_nat,
  intros x hx,
  rw nat_degree_of_mat_val M,
  rw finset.mem_filter at hx,
  rw if_pos hx.right,
end

lemma poly_of_perm_in_low_deg_submodule (M : matrix n n R) (σ : equiv.perm n) : 
  σ ≠ equiv.refl n → (poly_of_perm M σ) ∈ polynomial.degree_lt R ((fintype.card n) - 1):=
begin
  intro nonrefl,
  have hfixed := lt_card_sub_one_fixed_point_of_nonrefl nonrefl,
  rw poly_of_perm,
  simp only [nat.cast_id, coe_coe],
  rw polynomial.int_cast_eq_C,
  rw polynomial.C_mul',
  apply submodule.smul_mem (degree_lt R (fintype.card n - 1)) ↑↑(σ.sign),
  
  by_cases (∏ (i : n), (ite (σ i = i) X 0 - C (M (σ i) i)) = 0),
  { rw h, simp, },
  { rw mem_degree_lt,
    rw polynomial.degree_eq_nat_degree h,
    rw degree_prod_eq_sum_degree_of_prod_nonzero finset.univ _ h,
    simp only [finset.sum_boole, nat.cast_id, nat_degree_of_mat_val],
    rw with_bot.coe_lt_coe,
    apply lt_card_sub_one_fixed_point_of_nonrefl nonrefl,
  }
end

lemma sum_poly_of_non_refl_low_degree (M : matrix n n R) :
  ((finset.univ.erase (equiv.refl n)).sum (poly_of_perm M)).degree < ↑((fintype.card n) - 1):=
begin
  rw ← polynomial.mem_degree_lt,
  apply submodule.sum_mem (degree_lt R (fintype.card n - 1)),
  intros σ hσ,
  rw finset.mem_erase at hσ,
  rw ← poly_of_perm,
  apply poly_of_perm_in_low_deg_submodule M σ hσ.left,
end

lemma finset.sum_erase {α : Type u} {β : Type u} {s : finset α} {a : α} {f : α → β} [add_comm_monoid β] [decidable_eq α] :
a ∈ s → f a + (s.erase a).sum f = s.sum f :=
begin
  intro h,
  symmetry,
  conv_lhs {rw ← finset.insert_erase h},
  apply finset.sum_insert (finset.not_mem_erase a s),
end

lemma char_poly_eq_poly_of_refl_plus_others (M: matrix n n R):
char_poly M = (finset.univ.erase (equiv.refl n)).sum (poly_of_perm M)+poly_of_perm M (equiv.refl n):=
begin
  rw char_poly,
  rw matrix.det,
  rw ← finset.sum_erase (finset.mem_univ (equiv.refl n)),
  rw add_comm,
  simp [poly_of_perm, m_C, matrix.fun_apply, matrix.one_val],
end

lemma monic_prod_monic {α : Type u} (s : finset α) (f : α → polynomial R) (h : ∀ a : α, a ∈ s → monic (f a)) :
monic (s.prod f) :=
begin
  revert h, apply finset.induction_on s, simp,
  intros a s' ha hs' mon,
  rw finset.prod_insert ha,
  apply polynomial.monic_mul,
  { apply mon, simp },
  { apply hs', intros b bs', apply mon, rw finset.mem_insert, right, apply bs' }
end

lemma poly_of_refl_monic (M: matrix n n R) :
monic (poly_of_perm M (equiv.refl n)) :=
begin
  rw poly_of_perm,
  --rw equiv.perm.sign_refl,
  simp only [one_mul, if_true, equiv.perm.sign_refl, id.def, eq_self_iff_true, int.cast_one, units.coe_one, equiv.coe_refl, coe_coe],
  apply monic_prod_monic,
  intros a h,
  apply monic_X_sub_C,
end

lemma poly_of_refl_nat_degree_eq_dim (M: matrix n n R) :
(poly_of_perm M (equiv.refl n)).nat_degree = fintype.card n :=
begin
  rw poly_of_perm,
  simp only [one_mul, if_true, equiv.perm.sign_refl, id.def, eq_self_iff_true, int.cast_one, units.coe_one, equiv.coe_refl, coe_coe],
  rw fintype.card,
  rw finset.card_eq_sum_ones,
  rw degree_prod_eq_sum_degree_of_prod_nonzero,
  { refine congr rfl _, ext,
  have pos : 1 > 0 := by omega,
  rw ← polynomial.degree_eq_iff_nat_degree_eq_of_pos pos,
  simp },
  {
    apply polynomial.ne_zero_of_monic,
    apply monic_prod_monic,
    intros a h,
    apply monic_X_sub_C
  }
end

lemma poly_of_refl_degree_eq_dim (M: matrix n n R) :
(poly_of_perm M (equiv.refl n)).degree = ↑(fintype.card n) :=
begin
  have pos : fintype.card n > 0, { simp [fintype.card_pos_iff] },
  rw polynomial.degree_eq_iff_nat_degree_eq_of_pos pos,
  apply poly_of_refl_nat_degree_eq_dim,
end

theorem deg_char_poly_eq_dim (M: matrix n n R) :
(char_poly M).degree = fintype.card n := 
begin
  rw char_poly_eq_poly_of_refl_plus_others,
  rw polynomial.degree_add_eq_of_degree_lt,
  {apply poly_of_refl_degree_eq_dim},
  {
    rw poly_of_refl_degree_eq_dim,
    transitivity ↑(fintype.card n - 1), apply sum_poly_of_non_refl_low_degree M,
    rw with_bot.coe_lt_coe,
    have h : 0 < fintype.card n, { rw fintype.card_pos_iff, simp, },
    omega,
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
  transitivity ↑(fintype.card n - 1), apply sum_poly_of_non_refl_low_degree M,
  rw with_bot.coe_lt_coe,
  have h : 0 < fintype.card n, { rw fintype.card_pos_iff, simp, },
  omega,
end

def next_coeff (p : polynomial R) : R := ite (p.nat_degree = 0) 0 p.coeff (p.nat_degree - 1)

lemma add_smul_X_pow_erase (p : polynomial R) :
p = p.leading_coeff • X ^ p.nat_degree + finsupp.erase p.nat_degree p :=
begin
  ext,
  by_cases n = p.nat_degree,
  { rw h,
    rw coeff_add,
    unfold leading_coeff,
    simp only [coeff_smul, mul_one, coeff_X_pow, if_true, eq_self_iff_true],
    unfold coeff,
    change p.to_fun p.nat_degree = p.to_fun p.nat_degree + (finsupp.erase p.nat_degree p) p.nat_degree,
    rw finsupp.erase_same,
    rw add_zero },
  { rw coeff_add,
    simp only [mul_boole, coeff_smul, coeff_X_pow],
    rw if_neg h,
    unfold coeff,
    change p.to_fun n = 0 + (finsupp.erase p.nat_degree p) n,
    rw finsupp.erase_ne h,
    rw zero_add,
    refl }
end

lemma monic_add_X_pow_erase {p : polynomial R} :
monic p → p = X ^ p.nat_degree + finsupp.erase p.nat_degree p :=
begin
  intro mon,
  rw monic at mon,
  conv_lhs {rw add_smul_X_pow_erase p},
  rw mon,
  simp
end

lemma next_coeff_erase (p : polynomial R) :
(finsupp.erase p.nat_degree p) (p.nat_degree - 1) = next_coeff p :=
begin
  unfold next_coeff,
  by_cases p.nat_degree = 0,
  { rw if_pos h,
  have h0 : p.nat_degree - 1 = 0 := by omega,
  rw h0, rw h, rw finsupp.erase_same, refl,
  },
  { rw if_neg h,
  have h0 : p.nat_degree - 1 ≠ p.nat_degree := by omega,
  rw finsupp.erase_ne h0, refl,
  }
end

lemma next_coeff_mul_monic {p q : polynomial R} (hp : monic p) (hq : monic q) :
next_coeff (p * q) = next_coeff p + next_coeff q :=
begin
  repeat {rw next_coeff},
  rw polynomial.nat_degree_mul_eq (polynomial.ne_zero_of_monic hp) (polynomial.ne_zero_of_monic hq),
  by_cases p.nat_degree = 0,
  { rw h,
    simp only [true_and, if_true, nat.zero_sub, pi.zero_apply, eq_self_iff_true, add_eq_zero_iff, zero_add],
    have h' := h,
    rw polynomial.nat_degree_eq_zero_iff_degree_le_zero at h',
    rw polynomial.degree_le_zero_iff at h',
    rw ← h at h',
    rw ← leading_coeff at h',
    rw polynomial.monic.leading_coeff hp at h',
    rw  polynomial.C_1 at h',
    rw h', simp },
  { have hp' := h,
    by_cases q.nat_degree = 0,
    { rw h,
      simp only [true_and, if_true, nat.zero_sub, pi.zero_apply, eq_self_iff_true, add_eq_zero_iff, zero_add],
      have h' := h,
      rw polynomial.nat_degree_eq_zero_iff_degree_le_zero at h',
      rw polynomial.degree_le_zero_iff at h',
      rw ← h at h',
      rw ← leading_coeff at h',
      rw polynomial.monic.leading_coeff hq at h',
      rw polynomial.C_1 at h',
      rw h', simp },
      { rw if_neg hp', rw if_neg h,
        have hpq : ¬ p.nat_degree + q.nat_degree = 0 := by omega,
        rw if_neg hpq,
        sorry
      } }
end

@[simp]
lemma next_coeff_C_eq_zero (c : R) :
next_coeff (C c) = 0 := by {rw next_coeff, simp}

lemma next_coeff_prod_monic {α : Type u} (s : finset α) (f : α → polynomial R) (h : ∀ a : α, a ∈ s → monic (f a)) :
next_coeff (s.prod f) = s.sum (λ (a : α), next_coeff (f a)) :=
begin
  revert h, apply finset.induction_on s,
  { simp only [finset.not_mem_empty, forall_prop_of_true, forall_prop_of_false, finset.sum_empty, finset.prod_empty, not_false_iff,
 forall_true_iff],
  rw ← C_1, rw next_coeff_C_eq_zero },
  { intros a s ha hs monic,
    rw finset.prod_insert ha,
    rw finset.sum_insert ha,
    rw next_coeff_mul_monic (monic a (finset.mem_insert_self a s)), swap,
    { apply monic_prod_monic, intros b bs,
      apply monic, apply finset.mem_insert_of_mem bs },
    {
      refine congr rfl (hs _),
      intros b bs, apply monic, apply finset.mem_insert_of_mem bs }}
end

theorem trace_from_char_poly (M: matrix n n R) :
(matrix.trace n R R) M = -(char_poly M).coeff (fintype.card n - 1) := 
begin
  rw char_poly_eq_poly_of_refl_plus_others,
  rw polynomial.coeff_add,
  have h1 := sum_poly_of_non_refl_low_degree M,
  rw polynomial.coeff_eq_zero_of_degree_lt h1,
  rw poly_of_perm, rw equiv.perm.sign_refl, simp only [one_mul, if_true, id.def, eq_self_iff_true, int.cast_one, units.coe_one, zero_add, equiv.coe_refl, matrix.trace_diag,
 matrix.diag_apply, coe_coe],
  have h2 : (∏ (i : n), (X - C (M i i))).coeff (fintype.card n - 1) = next_coeff (∏ (i : n), (X - C (M i i))),
  {
    have mon : monic ∏ (i : n), (X - C (M i i)),
    { apply monic_prod_monic, intros a ha, apply monic_X_sub_C },
    unfold next_coeff,
    have h3 := degree_prod_eq_sum_degree_of_prod_nonzero finset.univ (λ i : n, X - C (M i i)) (ne_zero_of_monic mon),
    rw h3,
    have h4 : (λ (i : n), (X - C (M i i)).nat_degree) = λ i : n, 1,
    { ext, 
      have pos : 1 > 0 := by omega,
      rw ← polynomial.degree_eq_iff_nat_degree_eq_of_pos pos,
      simp,
    },
    simp only [h4, mul_one, nat.nsmul_eq_mul, finset.sum_const],
    have cardne0 : ¬ finset.univ.card = 0 :=  finset.card_ne_zero_of_mem (finset.mem_univ (arbitrary n)),
    rw if_neg cardne0,
  }
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
