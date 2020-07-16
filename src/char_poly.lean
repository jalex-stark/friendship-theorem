/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark.
-/

import linear_algebra.char_poly
import linear_algebra.matrix
import ring_theory.polynomial.basic
import data.zmod.basic
import number_theory.quadratic_reciprocity
import tactic.squeeze
import data.polynomial

noncomputable theory


universes u v w

open polynomial matrix
open_locale big_operators

variables {R : Type u} [comm_ring R]
variables {n : Type w} [fintype n] [decidable_eq n]
variables {α : Type w} [decidable_eq α]

open finset
open polynomial

section fixed_points

lemma gt_one_nonfixed_point_of_nonrefl {σ : equiv.perm n} (h : σ ≠ equiv.refl n) :
1 < (filter (λ (x : n), ¬ σ x = x) univ).card :=
begin
  rw one_lt_card_iff,
  contrapose! h, ext, dsimp,
  have := h (σ x) x,
  squeeze_simp at this; tauto,
end

lemma lt_card_sub_one_fixed_point_of_nonrefl {σ : equiv.perm n} (h : σ ≠ equiv.refl n) :
(filter (λ (x : n), σ x = x) univ).card < fintype.card n - 1:=
begin
  have hun := @filter_union_filter_neg_eq _ (λ (x : n), σ x = x) _ _ _ univ,
  have hin : (filter (λ (x : n), σ x = x) univ) ∩ (filter (λ (x : n), ¬ σ x = x) univ) = ∅
    := filter_inter_filter_neg_eq univ,
  rw ← disjoint_iff_inter_eq_empty at hin,
  rw fintype.card, conv_rhs { rw ← hun },
  rw card_disjoint_union hin,
  have := gt_one_nonfixed_point_of_nonrefl h, omega,
end

end fixed_points

variable {M : matrix n n R}

lemma nat_degree_char_matrix_val [nontrivial R] (i j : n) :
  (char_matrix M i j).nat_degree = ite (i = j) 1 0 :=
by { by_cases i = j, simp [h, ← degree_eq_iff_nat_degree_eq_of_pos (nat.succ_pos 0)], simp [h], }

lemma nat_degree_char_matrix_val_le (i j : n) :
  (char_matrix M i j).nat_degree ≤ ite (i = j) 1 0 :=
begin
  by_cases i = j, swap, simp [h],
  rw [if_pos h, h, char_matrix_apply_eq], apply nat_degree_X_sub_C_le,
end

variable (M)
lemma low_degree_char_poly_sub_diagonal :
(char_poly M - ∏ (i : n), (X - C (M i i))).degree < ↑(fintype.card n - 1) :=
begin
  rw [char_poly, det, ← insert_erase (mem_univ (equiv.refl n)),
    sum_insert (not_mem_erase (equiv.refl n) univ), add_comm],
  simp only [char_matrix_apply_eq, one_mul, equiv.perm.sign_refl, id.def, int.cast_one,
    units.coe_one, add_sub_cancel, equiv.coe_refl],
  rw ← mem_degree_lt, apply submodule.sum_mem (degree_lt R (fintype.card n - 1)),
  intros c hc, rw [← C_eq_int_cast, C_mul'],
  apply submodule.smul_mem (degree_lt R (fintype.card n - 1)) ↑↑(equiv.perm.sign c),
  rw mem_degree_lt, apply lt_of_le_of_lt degree_le_nat_degree _, rw with_bot.coe_lt_coe,
  apply lt_of_le_of_lt _ (lt_card_sub_one_fixed_point_of_nonrefl (ne_of_mem_erase hc)),
  apply le_trans (polynomial.nat_degree_prod_le univ (λ i : n, (char_matrix M (c i) i))) _,
  rw card_eq_sum_ones, rw sum_filter, apply sum_le_sum,
  intros, apply nat_degree_char_matrix_val_le,
end

lemma high_coeff_char_poly_eq_coeff_prod_diag {k : ℕ} (h : fintype.card n - 1 ≤ k) :
  (char_poly M).coeff k = (univ.prod (λ (i : n), X - C (M i i))).coeff k :=
begin
  apply eq_of_sub_eq_zero, rw ← coeff_sub, apply polynomial.coeff_eq_zero_of_degree_lt,
  apply lt_of_lt_of_le (low_degree_char_poly_sub_diagonal M) _, rw with_bot.coe_le_coe, apply h,
end

lemma det_of_dim_zero (h : fintype.card n = 0) (M : matrix n n R) : M.det = 1 :=
begin
  rw fintype.card_eq_zero_iff at h,
  have hone : M = 1, ext, exfalso, apply h i, rw hone, simp,
end

theorem degree_char_poly_eq_dim [nontrivial R] (M: matrix n n R) :
(char_poly M).degree = fintype.card n :=
begin
  by_cases fintype.card n = 0, rw h, unfold char_poly, rw det_of_dim_zero, simpa,
  rw ← sub_add_cancel (char_poly M) (∏ (i : n), (X - C (M i i))),
  have h1 : (∏ (i : n), (X - C (M i i))).degree = fintype.card n,
  { rw degree_eq_iff_nat_degree_eq_of_pos, swap, apply nat.pos_of_ne_zero h,
    rw nat_degree_prod_eq', simp_rw nat_degree_X_sub_C, unfold fintype.card, simp,
    simp_rw (monic_X_sub_C _).leading_coeff, simp, },
  rw degree_add_eq_of_degree_lt, exact h1, rw h1,
  apply lt_trans (low_degree_char_poly_sub_diagonal M), rw with_bot.coe_lt_coe,
  rw ← nat.pred_eq_sub_one, apply nat.pred_lt, apply h,
end

theorem nat_degree_char_poly_eq_dim [nontrivial R] (M: matrix n n R) :
  (char_poly M).nat_degree = fintype.card n :=
nat_degree_eq_of_degree_eq_some (degree_char_poly_eq_dim M)

lemma char_poly_monic_of_nontrivial [nontrivial R] (M : matrix n n R):
  monic (char_poly M):=
begin
  by_cases fintype.card n = 0, rw [char_poly, det_of_dim_zero h], apply monic_one,
  have mon : (∏ (i : n), (X - C (M i i))).monic,
  { apply monic_prod_monic univ (λ i : n, (X - C (M i i))), simp [monic_X_sub_C], },
  rw ← sub_add_cancel (∏ (i : n), (X - C (M i i))) (char_poly M) at mon,
  rw monic at *, rw leading_coeff_add_of_degree_lt at mon, rw ← mon,
  rw degree_char_poly_eq_dim, rw ← neg_sub, rw degree_neg,
  apply lt_trans (low_degree_char_poly_sub_diagonal M), rw with_bot.coe_lt_coe,
  rw ← nat.pred_eq_sub_one, apply nat.pred_lt, apply h,
end

lemma char_poly_monic (M : matrix n n R):
  monic (char_poly M):=
begin
  classical,
  by_cases h : nontrivial R,
  { apply @char_poly_monic_of_nontrivial _ _ _ _ _ h, },
  { unfold monic, rw nontrivial_iff at h, push_neg at h, apply h, }
end

@[simp]
lemma monic_degree_one {p : polynomial R} (hp : p.monic) :
p.nat_degree = 0 ↔ p = 1 :=
begin
  split; intro h,
  swap, { rw h, exact nat_degree_one },
  have h' := h,
  rw polynomial.nat_degree_eq_zero_iff_degree_le_zero at h,
  rw polynomial.degree_le_zero_iff at h,
  rw h, rw ← h',
  rw ← leading_coeff,
  rw polynomial.monic.leading_coeff hp,
  simp,
end

example {p : polynomial R} {n : ℕ} (hpn : p.coeff n ≠ 0) :
n ≤ p.nat_degree :=
begin
  exact le_nat_degree_of_ne_zero hpn,
end
example {p : polynomial R} {n : ℕ} :
 p.nat_degree < n → p.coeff n = 0 :=
begin
  exact coeff_eq_zero_of_nat_degree_lt,
end

lemma quux {α : Type} [decidable_eq α] (a : α) (s : finset α) :
  card (filter (λ x , x = a) s) = 1 ↔ a ∈ s :=
begin
  set t := (filter (λ x , x = a) s),
  have hts : t ⊆ s, { simp },
  split; intro h,
  { apply hts, rw card_eq_one at h,
    have : ∀ b ∈ t, b = a, { intro, simp },
    cases h with a' ha', rw this a' at ha',
    iterate 2 { rw ha', simp }},

  rw finset.card_eq_one, use a, ext x, rw mem_singleton,
  split, { simp },
  intro ha, rw ha, simpa,
end


lemma monic.nat_degree_mul_eq [nontrivial R] [decidable_eq R] {p q : polynomial R} (hp : p.monic) (hq : q.monic) :
(p*q).nat_degree = p.nat_degree + q.nat_degree :=
begin
  suffices : p.nat_degree + q.nat_degree ≤ (p*q).nat_degree,
  have : (p*q).nat_degree ≤ p.nat_degree + q.nat_degree, exact nat_degree_mul_le,
  linarith,

  apply le_nat_degree_of_ne_zero,
  suffices : (p * q).coeff (p.nat_degree + q.nat_degree) = 1,
  { rw this, simp },
  rw coeff_mul,
  transitivity ∑ (x : ℕ × ℕ) in _, ite (x = ⟨p.nat_degree, q.nat_degree⟩) (1:R) 0,
  { apply sum_congr, refl,
    intros x hx,
    simp only [nat.mem_antidiagonal] at hx,
    split_ifs with h, rw h, dsimp,
    iterate 2 {rw [← leading_coeff, monic.leading_coeff]}; try {assumption <|> simp},
    by_cases h1 : x.fst < p.nat_degree,
    { suffices : q.coeff x.snd = 0, simp [this],
      apply coeff_eq_zero_of_nat_degree_lt,
      linarith,},
    suffices : p.coeff x.fst = 0, simp [this],
    apply coeff_eq_zero_of_nat_degree_lt,
    have key : p.nat_degree ≠ x.fst,
    { contrapose! h, ext, { dsimp, rw h }, linarith },
    omega },
  rw sum_ite, rw sum_const_zero, rw sum_const,
  suffices : (filter (λ (x : ℕ × ℕ), x = (p.nat_degree, q.nat_degree)) (nat.antidiagonal (p.nat_degree + q.nat_degree))).card = 1,
  { rw this, simp },
  rw quux, simp,
end

/-- The second-highest coefficient, or 0 for constants -/
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

lemma monic_add_X_pow_erase {p : polynomial R} (hp : p.monic) :
p = X ^ p.nat_degree + finsupp.erase p.nat_degree p :=
begin
  conv_lhs {rw add_smul_X_pow_erase p},
  rw monic.leading_coeff, simpa,
end

lemma next_coeff_erase (p : polynomial R) :
(finsupp.erase p.nat_degree p) (p.nat_degree - 1) = next_coeff p :=
begin
  unfold next_coeff,
  split_ifs,
  { have h0 : p.nat_degree - 1 = 0 := by omega,
    rw h0, rw h, rw finsupp.erase_same, refl,
  },
  {
    have h0 : p.nat_degree - 1 ≠ p.nat_degree := by omega,
    rw finsupp.erase_ne h0, refl,
  }
end

lemma next_coeff_mul_monic {p q : polynomial R} (hp : monic p) (hq : monic q) :
next_coeff (p * q) = next_coeff p + next_coeff q :=
begin
  classical,
  by_cases h : nontrivial R, swap,
  { rw nontrivial_iff at h, push_neg at h, apply h, },
  letI := h,
  have := monic.nat_degree_mul_eq hp hq,
  dsimp [next_coeff], rw this, simp [hp, hq], clear this,
  split_ifs; try {tauto <|> simp *},
  rename h_2 hp0, rename h_3 hq0, clear h_1,
  rw ← monic_degree_one at hp0 hq0, any_goals {assumption},
  rw coeff_mul,
  transitivity ∑ (x : ℕ × ℕ) in _, ite (x.fst = p.nat_degree ∨ x.snd = q.nat_degree) (p.coeff x.fst * q.coeff x.snd) 0,
  { apply sum_congr rfl,
    intros x hx, split_ifs with hx1, refl,
    simp only [nat.mem_antidiagonal] at hx,
    push_neg at hx1, cases hx1 with hxp hxq,
    by_cases h_deg : x.fst < p.nat_degree,
    { suffices : q.coeff x.snd = 0, simp [this],
      apply coeff_eq_zero_of_nat_degree_lt, omega },
    suffices : p.coeff x.fst = 0, simp [this],
    apply coeff_eq_zero_of_nat_degree_lt, omega,
  },
  rw sum_ite, simp,
  have : filter (λ (x : ℕ × ℕ), x.fst = p.nat_degree ∨ x.snd = q.nat_degree) (nat.antidiagonal (p.nat_degree + q.nat_degree - 1))
    = {(p.nat_degree - 1, q.nat_degree),(p.nat_degree, q.nat_degree - 1)},
  { ext, rw mem_filter, simp only [mem_insert, mem_singleton, nat.mem_antidiagonal],
    split; intro ha,
    { rcases ha with ⟨ha, _ | _ ⟩,
      { right, ext, assumption, omega, },
      left, ext, omega, assumption },
    split, cases ha; { rw ha, ring, omega },
    cases ha; { rw ha, simp }},
  rw [this, sum_insert, sum_singleton],
  iterate 2 { rw [← leading_coeff, monic.leading_coeff] };
  { assumption <|> simp },
  rw mem_singleton,
  suffices : p.nat_degree - 1 ≠ p.nat_degree, simp [this],
  omega,
end

@[simp]
lemma next_coeff_C_eq_zero (c : R) :
next_coeff (C c) = 0 := by {rw next_coeff, simp}

lemma next_coeff_of_pos_nat_degree (p : polynomial R) :
  0 < p.nat_degree → next_coeff p = p.coeff (p.nat_degree - 1) :=
by { intro h, rw next_coeff, rw if_neg, intro contra, rw contra at h, apply lt_irrefl 0 h, }

@[simp]
lemma next_coeff_X_sub_C_eq_neg_C [nontrivial R] (c : R) : next_coeff (X - C c) = - c :=
by { rw next_coeff_of_pos_nat_degree; simp [nat_degree_X_sub_C] }

lemma next_coeff_prod_monic
  (s : finset α) (f : α → polynomial R) (h : ∀ a : α, a ∈ s → monic (f a)) :
next_coeff (s.prod f) = s.sum (λ (a : α), next_coeff (f a)) :=
begin
  revert h, apply finset.induction_on s,
  { simp only [finset.not_mem_empty, forall_prop_of_true, forall_prop_of_false, finset.sum_empty,
  finset.prod_empty, not_false_iff, forall_true_iff],
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

--sort of a special case of Vieta?
lemma card_pred_coeff_prod_X_sub_C' [nontrivial R] {s : finset α} (hs : 0 < s.card) (f : α → R) :
next_coeff ∏ i in s, (X - C (f i)) = -s.sum f :=
by { rw next_coeff_prod_monic; { simp [monic_X_sub_C] } }

lemma card_pred_coeff_prod_X_sub_C [nontrivial R] (s : finset α) (f : α → R) :
  0 < s.card → (∏ i in s, (X - C (f i))).coeff (s.card - 1) = -s.sum f :=
begin
  intro hs,
  convert card_pred_coeff_prod_X_sub_C' _ _, any_goals { assumption },
  rw next_coeff, split_ifs,
  { rw nat_degree_prod_eq_of_monic at h,
    swap, { intros, apply monic_X_sub_C },
    rw sum_eq_zero_iff at h,
    simp_rw nat_degree_X_sub_C at h, contrapose! h, norm_num,
    exact multiset.card_pos_iff_exists_mem.mp hs },
  congr, rw nat_degree_prod_eq_of_monic; { simp [nat_degree_X_sub_C, monic_X_sub_C] },
end

--shouldn't need these instances, but might need casework
theorem trace_from_char_poly [nontrivial R] [inhabited n] (M: matrix n n R) :
(matrix.trace n R R) M = -(char_poly M).coeff (fintype.card n - 1) :=
begin
  rw high_coeff_char_poly_eq_coeff_prod_diag, swap, refl,
  rw [fintype.card, card_pred_coeff_prod_X_sub_C univ (λ i : n, M i i)], simp,
  rw [← fintype.card, fintype.card_pos_iff], apply_instance,
end

lemma hom_det {S : Type*} [comm_ring S] {M : matrix n n R} {f : R →+* S} :
  f M.det = matrix.det (λ i j : n, f (M i j)) :=
begin
  unfold matrix.det, simp [f.map_sum, f.map_prod],
end

lemma matrix.scalar.commute (r : R) (M : matrix n n R) : commute (scalar n r) M :=
by { unfold commute, unfold semiconj_by, simp }

lemma eval_mat_poly_equiv (M : matrix n n (polynomial R)) (r : R) (i j : n) :
  polynomial.eval r (M i j) = polynomial.eval ((scalar n) r) (mat_poly_equiv M) i j :=
begin
  unfold polynomial.eval, unfold eval₂,
  transitivity finsupp.sum (mat_poly_equiv M) (λ (e : ℕ) (a : matrix n n R),
    (a * (scalar n) r ^ e) i j),
  { simp_rw ← (scalar n).map_pow, simp_rw ← (matrix.scalar.commute _ _).eq,
    simp only [coe_scalar, matrix.one_mul, ring_hom.id_apply,
      smul_val, mul_eq_mul, algebra.smul_mul_assoc],
    have h : ∀ x : ℕ, (λ (e : ℕ) (a : R), r ^ e * a) x 0 = 0 := by simp,
    rw ← finsupp.sum_map_range_index h, swap, refl,
    refine congr (congr rfl _) (by {ext, rw mul_comm}), ext, rw finsupp.map_range_apply,
    simp [apply_eq_coeff], },
  { unfold finsupp.sum, rw sum_apply, rw sum_apply, dsimp, refl, }
end

lemma eval_det (M : matrix n n (polynomial R)) (r : R) :
  polynomial.eval r M.det = (polynomial.eval (matrix.scalar n r) (mat_poly_equiv M)).det :=
begin
  rw [polynomial.eval, ← coe_eval₂_ring_hom, hom_det], refine congr rfl _,
  rw [coe_eval₂_ring_hom, ← polynomial.eval],
  ext, apply eval_mat_poly_equiv,
end

theorem det_from_char_poly (M: matrix n n R) :
M.det = (-1)^(fintype.card n) * (char_poly M).coeff 0:=
begin
  rw [coeff_zero_eq_eval_zero, char_poly, eval_det, mat_poly_equiv_char_matrix, ← det_smul],
  simp
end

section char_p

lemma matrix.scalar_inj [inhabited n] {r s : R} : scalar n r = scalar n s ↔ r = s :=
begin
  split; intro h, rw [← scalar_apply_eq r (arbitrary n), ← scalar_apply_eq s (arbitrary n), h],
  rw h,
end

instance matrix.char_p [inhabited n] (p : ℕ) [char_p R p] : char_p (matrix n n R) p :=
{ cast_eq_zero_iff :=
  begin
    intro k, rw ← char_p.cast_eq_zero_iff R p k,
    rw ← nat.cast_zero, repeat {rw ← (scalar n).map_nat_cast},
    rw matrix.scalar_inj, refl,
  end }

lemma det_pow (k : ℕ) (M : matrix n n R) :
(M ^ k).det = (M.det) ^ k :=
begin
  induction k with k hk, simp,
  repeat {rw pow_succ}, rw ← hk, simp,
end

theorem add_pow_char_of_commute (α : Type u) [ring α] {p : ℕ} [fact p.prime]
  [char_p α p] (x y : α) :
  commute x y → (x + y)^p = x^p + y^p :=
begin
  intro comm,
  rw [commute.add_pow comm, finset.sum_range_succ, nat.sub_self, pow_zero, nat.choose_self],
  rw [nat.cast_one, mul_one, mul_one, add_right_inj],
  transitivity,
  { refine finset.sum_eq_single 0 _ _,
    { intros b h1 h2,
      -- have := nat.prime.dvd_choose_self,
      have := nat.prime.dvd_choose_self (nat.pos_of_ne_zero h2) (finset.mem_range.1 h1) (by assumption),
      rw [← nat.div_mul_cancel this, nat.cast_mul, char_p.cast_eq_zero α p],
      simp only [mul_zero], },
    { intro H, contrapose! H, rw finset.mem_range, apply nat.prime.pos, assumption, } },
  rw [pow_zero, nat.sub_zero, one_mul, nat.choose_zero_right, nat.cast_one, mul_one]
end

lemma comp_det (p : polynomial R) (M : matrix n n (polynomial R)) :
  (M.det).comp p = matrix.det (λ i j : n, (M i j).comp p) :=
by { unfold comp, rw ← coe_eval₂_ring_hom, rw hom_det }

lemma pow_comp (p q : polynomial R) (k : ℕ) : (p ^ k).comp q = (p.comp q) ^ k :=
begin
  unfold comp, rw ← coe_eval₂_ring_hom, apply ring_hom.map_pow,
end

variables (p : ℕ) [fact p.prime]

lemma frobenius_fixed (a : zmod p): a ^ p = a :=
begin
  have posp : 0 < p, { apply nat.prime.pos, assumption, },
  by_cases a = 0, rw h, rw zero_pow posp,
  conv_rhs {rw ← one_mul a, rw ← pow_one a}, rw ← zmod.fermat_little p h,
  rw ← pow_add, refine congr rfl _, symmetry, apply nat.succ_pred_eq_of_pos posp,
end

lemma poly_pow_p_char_p (f : polynomial (zmod p)) :
f ^ p = f.comp (X ^ p) :=
begin
  apply f.induction_on', intros, rw add_pow_char, rw [a, a_1], simp, assumption,
  intros, repeat {rw single_eq_C_mul_X}, rw mul_comp, rw mul_pow,  simp [pow_comp],
  repeat {rw ← pow_mul}, rw mul_comm p n, rw ← C.map_pow, rw frobenius_fixed p a,
end

variables {S : Type u} [ring S] [algebra R S]
--def alg_hom_on_matrix_vals (f : R →ₐ[R] S) : (matrix n n R) →ₐ[R] (matrix n n S) :=
--(matrix_equiv_tensor R S n).comp (algebra.tensor_product.map f id).comp
--  (matrix_equiv_tensor R R n).symm

--def mat_C : (matrix n n R) →ₐ[R] (matrix n n (polynomial R)) :=
--  alg_hom_on_matrix_vals (algebra_map R (polynomial R))

--lemma alg_hom_on_matrix_vals_apply (f : R →ₐ[R] S) (M : matrix n n R) (i j : n):
--  (alg_hom_on_matrix_vals n f M) i j = f (M i j) :=
--begin
--  simp,

--end

def mat_C : (matrix n n R) →+* (matrix n n (polynomial R)) :=
  mat_poly_equiv.symm.to_ring_equiv.to_ring_hom.comp C

@[simp]
lemma mat_C_apply (M : matrix n n R) (i j : n):
  (mat_C M) i j = C (M i j) :=
begin
  unfold mat_C,
  transitivity mat_poly_equiv.symm (C M) i j, simp, refl,
  ext, by_cases n_1 = 0; simp [h, coeff_C],
end


--lemma foobar (M : matrix n n R) (i j : n):
--  (mat_C M) ^ p = mat_C (M ^ p) :=
--begin
--  unfold mat_C,
--  rw ring_hom.map_pow,
--end

@[simp]
lemma empty_matrix_eq_zero {R : Type*} [ring R] (hn : ¬ nonempty n) (M : matrix n n R) :
M = 0 :=
begin
  ext, contrapose! hn, use i,
end


lemma char_poly_pow_p_char_p (M : matrix n n (zmod p)) (hp : p % 2 = 1) :
char_poly (M ^ p) = char_poly M :=
begin
  classical,
  by_cases hn : nonempty n, letI := hn, haveI : inhabited n := by { inhabit n, assumption },
  clear _inst_1 hn,
  swap, { congr, rw empty_matrix_eq_zero hn M, apply empty_matrix_eq_zero hn },

  apply frobenius_inj (polynomial (zmod p)) p, repeat {rw frobenius_def},
  rw poly_pow_p_char_p p,-- (char_poly (M ^ p)),
    sorry,
  -- unfold char_poly, unfold char_matrix, rw ← det_pow,
  -- repeat {rw sub_eq_add_neg},
  -- rw add_pow_char_of_commute (matrix n n (polynomial (zmod p))), swap, apply matrix.scalar.commute,
  -- swap, apply_instance,
  -- swap, exact matrix.char_p p,
  -- rw ← (scalar n).map_pow, rw comp_det,
  -- rw neg_pow, rw neg_one_pow_eq_pow_mod_two, rw hp,
  -- simp only [neg_val, neg_mul, matrix.one_mul, pow_one, neg_inj, mul_eq_mul],
  -- refine congr rfl _, ext, refine congr (congr rfl _) rfl,
  -- simp only [add_comp, neg_val, X_comp, coeff_add, mul_comp, add_val],
  -- refine congr (congr rfl _) _,
  -- { by_cases i = j; simp [h], },
  -- rw ← ring_hom.map_neg, rw C_comp, rw ring_hom.map_neg,
  -- simp_rw ← mat_C_apply,
  -- rw ring_hom.map_pow,
end

end char_p
