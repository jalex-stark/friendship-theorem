import data.fintype.basic data.fintype.card data.finset data.indicator_function linear_algebra.matrix algebra.big_operators --core.init.logic

open_locale classical
noncomputable theory

def prop_to_nat: Prop → ℕ:=
    λ (p:Prop), ite p 1 0

def prop_two_nat: Prop → ℕ:=
begin
    intro p,
    by_cases p,
    exact 1,
    exact 0,
end

@[simp] lemma true_to_nat {p: Prop} (hpos:p):
    prop_to_nat p = 1:= if_pos hpos

@[simp] lemma false_to_nat {p: Prop} (hneg:¬p):
    prop_to_nat p = 0:= if_neg hneg


@[simp] lemma prop_to_nat_idem {p:Prop}:
    (prop_to_nat p)*(prop_to_nat p)=prop_to_nat p:=
begin
    by_cases p,
    rw true_to_nat h,
    simp,
    rw false_to_nat h,
    simp,
end

def findicator {α : Type*} [fintype α] [decidable_eq α] (s: finset α):α → ℕ:=
    λ (a:α), prop_to_nat (a ∈ s)

lemma ind_one_of_mem {α : Type*} [fintype α] [decidable_eq α] {s: finset α} {x: α}:
    x ∈ s → findicator s x = 1:= true_to_nat

lemma ind_zero_of_not_mem {α : Type*} [fintype α] [decidable_eq α] {s: finset α} {x: α}:
    x ∉ s → findicator s x = 0:= false_to_nat

lemma ind_one_iff_mem {α : Type*} [fintype α] [decidable_eq α] {s: finset α} {x: α}:
    findicator s x = 1 ↔ x ∈ s:=
begin
    by_cases x∈ s,
    rw ind_one_of_mem h,
    simp,
    exact h,
    rw ind_zero_of_not_mem h,
    simp,
    exact h,
end

lemma ind_zero_iff_not_mem {α : Type*} [fintype α] [decidable_eq α] {s: finset α} {x: α}:
    findicator s x = 0 ↔ x ∉ s:=
begin
    by_cases x∈ s,
    rw ind_one_of_mem h,
    simp,
    exact h,
    rw ind_zero_of_not_mem h,
    simp,
    exact h,
end

theorem sum_ind_eq_card {α : Type*} [fintype α] [decidable_eq α] (s: finset α):
    (finset.univ: finset α).sum (findicator s)= s.card :=
begin
    transitivity s.sum (findicator s),
    symmetry,
    apply finset.sum_subset,
    apply finset.subset_univ,
    intros a h0 ha,
    rw false_to_nat ha,
    symmetry,
    transitivity s.sum (λ x:α, 1),
    apply finset.card_eq_sum_ones,
    apply finset.sum_congr,
    refl,
    intros x hx,
    rw ind_one_of_mem hx,
end

lemma prod_inds_eq_ind_inter {n : Type*} [fintype n] [decidable_eq n] (s t: finset n):
    (findicator s)*(findicator t) =findicator (s ∩ t):=
begin
    ext,
    simp,
    by_cases x ∈ s,
    have hs := h,
    rw ind_one_of_mem h,
    simp,
    by_cases x ∈ t,
    rw ind_one_of_mem h,
    have hint: x ∈ s ∩ t,
    apply finset.mem_inter.2,
    split,
    exact hs,
    exact h,
    symmetry,
    apply ind_one_of_mem hint,
    have hint: x ∉ s ∩ t,
    intro hint,
    apply h,
    apply finset.mem_of_mem_inter_right hint,
    rw ind_zero_of_not_mem h,
    rw ind_zero_of_not_mem hint,
    have hint: x ∉ s ∩ t,
    intro hint,
    apply h,
    apply finset.mem_of_mem_inter_left hint,
    rw ind_zero_of_not_mem h,
    rw ind_zero_of_not_mem hint,
    simp,
end

lemma dot_inds_eq_card_inter {n : Type*} [fintype n] [decidable_eq n] (s t: finset n):
    matrix.dot_product (findicator s) (findicator t) = (s ∩ t).card:=
begin
    unfold matrix.dot_product,
    transitivity finset.univ.sum((findicator s)*(findicator t)),
    refl,
    rw prod_inds_eq_ind_inter,
    apply sum_ind_eq_card,
end