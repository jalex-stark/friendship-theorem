import sym_matrix linear_algebra.basic data.matrix.basic linear_algebra.finite_dimensional linear_algebra.nonsingular_inverse data.polynomial data.fintype.basic

open_locale classical
noncomputable theory

universe u

variables {n:Type u} {K:Type u} [fintype n][field K][decidable_eq n][inhabited n]

def char_poly (M:matrix n n K): polynomial K:=
    ((matrix_compose polynomial.C M) - (polynomial.X:polynomial K) • (matrix_compose polynomial.C 1)).det

theorem has_left_inverse_of_injective (M:matrix n n K):
    linear_map.ker M.to_lin = ⊥ → ∃ N:matrix n n K, N.mul M = 1:=
begin
    intro inj,
    have surj: linear_map.range M.to_lin = ⊤,
    apply linear_map.ker_eq_bot_iff_range_eq_top.1,
    exact inj,
    apply finite_dimensional.finite_dimensional_fintype_fun,
    let bij:=  linear_equiv.of_bijective M.to_lin inj surj,
    have bijworks:=  linear_equiv.of_bijective_apply M.to_lin,
    let inv:= linear_map.inverse bij.to_linear_map (linear_equiv.inv_fun bij) (linear_equiv.left_inv bij) (linear_equiv.right_inv bij),
    have invworks:inv.to_fun = linear_equiv.inv_fun bij,
    refl,
    existsi inv.to_matrix,
    have invworks1: inv.comp M.to_lin = 1,
    ext,
    refine congr _ rfl,
    change inv.to_fun (M.to_lin x) = x,
    rw ← bijworks x,
    change inv.to_fun (bij x) = x,
    change bij.inv_fun (bij.to_fun x)=x,
    rw bij.left_inv,
    have h:M=bij.to_linear_map.to_matrix,
    change M=M.to_lin.to_matrix,
    rw to_lin_to_matrix,
    rw h,
    rw ← matrix.comp_to_matrix_mul inv bij.to_linear_map,
    change (inv.comp M.to_lin).to_matrix = 1,
    rw invworks1,
    rw ← linear_map.to_matrix_id,
    refl,
end

variables {V:Type u} [add_comm_group V] [vector_space K V] (f:V →ₗ[K] V) (l:K)


def is_eigenvalue :Prop:=
    (f-l• 1).ker ≠ ⊥

def is_eigenvector_of_eigenvalue (v:V): Prop:=
     f.to_fun(v)=l • v


def eigenspace:
    submodule K V:=
    (f-l•1).ker

variable {l}

def is_eigenvector (v:V): Prop:=
    ∃ x:K, f.to_fun(v)=x • v


def set_eigenvalues:set K:={x:K|is_eigenvalue f x}

def is_eigenbasis (b: set V):Prop:=
    (is_basis K (subtype.val : b → V)) ∧ ∀ v : {x// x ∈ b}, is_eigenvector f v

def has_eigenbasis :Prop:=
    ∃ b:set V, is_eigenbasis f b

variable [finite_dimensional K V]

def has_fin_eigenbasis :Prop:=
    ∃ b:finset V, is_eigenbasis f ↑b

variable {f}

def change_of_basis_to (b: finset (n → K)):
    is_basis K (subtype.val : (↑b: set (n → K)) → n → K) → matrix {x:n → K//x ∈ b} n K:=
    λ hb:is_basis K (subtype.val : (↑b: set (n → K)) → n → K), (equiv_fun_basis hb).to_linear_map.to_matrix

def change_of_basis_from (b: finset (n → K)):
    is_basis K (subtype.val : (↑b: set (n → K)) → n → K) → matrix n {x:n → K//x ∈ b} K:=
    λ hb:is_basis K (subtype.val : (↑b: set (n → K)) → n → K), (equiv_fun_basis hb).symm.to_linear_map.to_matrix

lemma change_of_basis_from_apply {b: finset (n → K)}{h:is_basis K (subtype.val : (↑b: set (n → K)) → n → K)}:
    ∀ x:{x:n → K//x ∈ b} → K,((change_of_basis_from b h).mul_vec x = finset.univ.sum(λ i:{x:n → K//x ∈ b}, (x i) • i)):=
begin
    intro x,
    rw ← matrix.to_lin_apply,
    unfold change_of_basis_from,
    change (linear_map.to_matrix ((equiv_fun_basis h).symm.to_linear_map)).to_lin x = finset.univ.sum (λ (i : {x // x ∈ b}), x i • ↑i),
    rw to_matrix_to_lin,
    change ((equiv_fun_basis h).symm) x = finset.univ.sum (λ (i : {x // x ∈ b}), x i • ↑i),
    rw equiv_fun_basis_symm_apply,
    refl,
end

lemma change_of_basis_mul_vec_std {b: finset (n → K)}{h:is_basis K (subtype.val : (↑b: set (n → K)) → n → K)}{i:{x//x ∈ b}}:
    ((change_of_basis_from b h).mul_vec (λ k:{x//x ∈ b}, ite (i=k) 1 0) = i):=
begin
    rw change_of_basis_from_apply (λ k:{x//x ∈ b}, ite (i=k) 1 0),
    simp,
    
    --have hsub :(λ (i_1 : {x // x ∈ b}), ite (i = i_1) 1 0 • ↑i_1) =λ (i_1 : {x // x ∈ b}), ite (i = i_1) i_1.val 0,
    --ext,
    --by_cases i=x,
    --repeat {rw if_pos h},
    --simp,
    --refl,
    --repeat {rw if_neg h},
    --simp,
    transitivity finset.univ.sum (λ (i_1 : {x // x ∈ b}), ite (i = i_1) i_1.val 0),
    refine congr rfl _,
    ext,
    by_cases i=x,
    repeat {rw if_pos h},
    simp,
    refl,
    repeat {rw if_neg h},
    simp,

    simp,
    refl,
end

lemma change_of_basis_inverses {b: finset (n → K)}{h:is_basis K (subtype.val : (↑b: set (n → K)) → n → K)}:
    (change_of_basis_from b h).mul (change_of_basis_to b h)=1 ∧ (change_of_basis_to b h).mul (change_of_basis_from b h)=1:=
begin
    unfold change_of_basis_from,
    unfold change_of_basis_to,
    split,

    rw ← matrix.comp_to_matrix_mul (equiv_fun_basis h).symm.to_linear_map (equiv_fun_basis h).to_linear_map,
    rw ← linear_map.to_matrix_id,
    refine congr rfl _,
    ext,
    refine congr _ rfl,
    change (equiv_fun_basis h).symm ((equiv_fun_basis h) x) = linear_map.id x,
    rw linear_equiv.symm_apply_apply,
    refl,

    rw ← matrix.comp_to_matrix_mul (equiv_fun_basis h).to_linear_map (equiv_fun_basis h).symm.to_linear_map,
    rw ← linear_map.to_matrix_id,
    refine congr rfl _,
    ext,
    refine congr _ rfl,
    change (equiv_fun_basis h) ((equiv_fun_basis h).symm x) = linear_map.id x,
    rw linear_equiv.apply_symm_apply,
    refl,
end

def change_basis (M: matrix n n K)(b: finset (n → K))(h:is_basis K (subtype.val : (↑b: set (n → K)) → n → K)):
    matrix {x//x ∈ b} {x// x ∈ b} K:=
    matrix.mul (matrix.mul (change_of_basis_to b h) M) (change_of_basis_from b h)

def diagonal_of_fin_eigenbasis (M: matrix n n K)(b: finset (n → K))(h: is_eigenbasis (M.to_lin) ↑b):
    matrix {x//x ∈ b} {x//x ∈ b} K:=
    change_basis M b h.left

lemma matrix_val_from_mul_vec {a b c:Type*}[fintype a][fintype b][semiring c](M: matrix a b c)(i:a)(j:b):
    M i j = M.mul_vec (λ k:b, ite (j=k) 1 0) i:=
begin
    unfold matrix.mul_vec,
    unfold matrix.dot_product,
    simp,
end


lemma diagonal_of_eigenvalues_of_fin_eigenbasis (M: matrix n n K)(b: finset (n → K))(hb:is_eigenbasis (M.to_lin) ↑b):
    ∀ i:{x//x ∈ b}, is_eigenvector_of_eigenvalue M.to_lin ((diagonal_of_fin_eigenbasis M b hb) i i) i:=
begin
    intros i,
    
    change M.to_lin ↑i = ((diagonal_of_fin_eigenbasis M b hb) i i) • ↑i,
    rw matrix.to_lin_apply,
    have hi:= hb.right i,
    change ∃ (x : K), M.to_lin ↑i = x • ↑i at hi,
    rw matrix.to_lin_apply at hi,
    cases hi with li hli,
    rw hli,
    refine congr _ rfl,
    refine congr rfl _,

    rw matrix_val_from_mul_vec (diagonal_of_fin_eigenbasis M b hb) i i,
    unfold diagonal_of_fin_eigenbasis,
    unfold change_basis,
    rw ← matrix.mul_vec_mul_vec _ ((change_of_basis_to b hb.left).mul M) (change_of_basis_from b hb.left),
    rw change_of_basis_mul_vec_std,
    
    
end


variables (f l)
def geom_mult {V:Type*} [add_comm_group V] [vector_space K V][finite_dimensional K V] (f:V →ₗ[K] V) (l:K):ℕ:=
    finite_dimensional.findim K (eigenspace f l)

variable {f}
theorem trace_is_sum_eigenvals_of_fin_eigenbasis (M: matrix n n K)(b:finset (n → K)):
    is_eigenbasis (M.to_lin) b → M.trace= b.sum():=

