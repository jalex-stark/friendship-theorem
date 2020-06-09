import data.real.basic adjacency_matrix sym_matrix double_counting old_double_counting data.fintype.basic
import tactic

open_locale classical
noncomputable theory

lemma exists_unique_rewrite {X:Type*}{p: X → Prop}{q: X → Prop}:
    (∀ x:X,p(x)↔ q(x))→ (∃!x:X,p(x)) → ∃!x:X, q(x):= 
begin
    intros iff exun,
    have h:=exists_unique_congr iff,
    rw ← h,
    exact exun,
end

variables {V:Type*} [fintype V] [inhabited V]

def friendship (G:fin_graph V):Prop:=
∀ v w :V, v ≠ w →  ∃! u:V, G.E v u ∧ G.E w u 

def is_friend (G:fin_graph V)(v w:V):V → Prop:=
    λ x:V, G.E v x ∧ G.E w x

@[simp] lemma friend_symm {G:fin_graph V}{v w x:V}:
    G.E v x ∧ G.E x w ↔ G.E v x ∧ G.E w x:=
begin
    split,
    intro h,
    split,
    apply h.left,
    apply G.undirected h.right,
    intro h,
    split,
    apply h.left,
    apply G.undirected h.right,
end

def find_friend (G:fin_graph V)(friendG: friendship G)(v w:V)(vneqw:v ≠ w):V:=
    fintype.choose (is_friend G v w) (friendG v w vneqw)

lemma find_friend_spec (G:fin_graph V)(friendG: friendship G)(v w:V)(vneqw: v ≠ w):
    is_friend G v w (find_friend G friendG v w vneqw):= by apply fintype.choose_spec

lemma find_friend_unique (G:fin_graph V)(friendG: friendship G)(v w:V)(vneqw: v ≠ w):
    ∀ y:V, is_friend G v w y → y=(find_friend G friendG v w vneqw):= 
begin
    intros y hy,
    apply exists_unique.unique(friendG v w vneqw),
    apply hy,
    apply (find_friend_spec G friendG v w vneqw),
end

lemma friendship' (G:fin_graph V){friendG: friendship G}{v w:V}:
    v ≠ w → exists_unique (is_friend G v w):=
begin
    unfold exists_unique,
    intro vneqw,
    use find_friend G friendG v w vneqw,
    split,
    exact find_friend_spec G friendG v w vneqw,
    unfold is_friend,
    intros,
    apply exists_unique.unique (friendG v w vneqw),
    exact a,
    exact find_friend_spec G friendG v w vneqw,
end

def exists_politician (G:fin_graph V):Prop:=
    ∃ v:V, ∀ w:V, v=w ∨ G.E v w

def no_pol (G:fin_graph V):Prop:=
    ∀ v:V, ∃ w:V, v ≠ w ∧ ¬ G.E v w

lemma exists_pol_of_not_no_pol {G:fin_graph V}:
    (¬ no_pol G) ↔ exists_politician G:=
begin
    unfold no_pol,
    unfold exists_politician,
    rw classical.not_forall,
    apply exists_congr,
    intro a,
    rw ← not_exists_not,
    apply not_congr,
    apply exists_congr,
    intro b,
    rw ← not_or_distrib,
end

def path_bigraph (G:fin_graph V)(A B:finset V):bigraph V V:=
    bigraph.mk A B G.E

lemma path_bigraph_swap {G: fin_graph V}{A B:finset V}:
    (path_bigraph G A B).swap = path_bigraph G B A:=
begin
    ext,
    refl,
    refl,
    split,
    apply G.undirected,
    apply G.undirected,
end

def friends (G:fin_graph V)(v w:V):finset V:=
    finset.filter (is_friend G v w) (finset.univ:finset V)

lemma friends_eq_inter_neighbors {G:fin_graph V}{v w:V}:
    friends G v w = neighbors G v ∩ neighbors G w:=
begin
    ext,
    rw finset.mem_inter,
    unfold friends,
    rw finset.mem_filter,
    unfold is_friend,
    simp,
end

lemma friends_size_one {G:fin_graph V}{v w:V}:
    friendship G → v ≠ w → (friends G v w).card=1:=
begin
    intros fG vneqw,
    rw finset.card_eq_one,
    rw finset.singleton_iff_unique_mem,
    unfold friends,
    refine exists_unique_rewrite _ (fG v w vneqw),
    intro x,
    rw finset.mem_filter,
    unfold is_friend,
    split,
    intro h,
    split,
    apply finset.mem_univ,
    exact h,
    tauto,
end

lemma left_fiber_eq_nbrs_inter_A {G:fin_graph V}{A B: finset V}{v:V}:
    v ∈ B → left_fiber (path_bigraph G A B) v = A ∩ (neighbors G v):=
begin
    intro vB,
    ext,
    simp,
    change a ∈ A ∧ G.E a v ↔ a ∈ A ∧ G.E v a,
    have h:G.E a v↔ G.E v a,
    split,
    apply G.undirected,
    apply G.undirected,
    rw h,
end

lemma right_fiber_eq_nbrs_inter_B {G:fin_graph V}{A B: finset V}{v:V}:
    v ∈ A → right_fiber (path_bigraph G A B) v = B ∩ (neighbors G v):=
begin
    intro vA,
    rw ← left_fiber_swap,
    rw path_bigraph_swap,
    apply left_fiber_eq_nbrs_inter_A,
    exact vA,
end

lemma lunique_paths {G:fin_graph V}{v:V}{B: finset V}:
    friendship G→ v∉ B→left_unique (path_bigraph G (neighbors G v) B):=
begin
    intros fG vninB,
    rw left_unique_one_reg,
    unfold left_regular,
    intros b hb,
    have hsub: left_fiber (path_bigraph G (neighbors G v) B) b = (neighbors G v) ∩ (neighbors G b),
    apply left_fiber_eq_nbrs_inter_A hb,
    rw hsub,
    rw ← friends_eq_inter_neighbors,
    apply friends_size_one fG,
    intro veqb,
    rw veqb at vninB,
    change b ∈ B at hb,
    apply vninB hb,
end

lemma runique_paths {G:fin_graph V}{v:V}{A: finset V}:
    friendship G→ v∉ A→right_unique (path_bigraph G A (neighbors G v)):=
begin
    intros fG vninA,
    rw ← path_bigraph_swap,
    rw right_unique_swap,
    apply lunique_paths fG vninA,
end

lemma counter_non_adj_deg_eq {G:fin_graph V}:
    (friendship G ∧ no_pol G)→ ∀ v w :V, ¬ G.E v w → degree G v = degree G w:=
begin
    intros hG v w hvw,
    cases hG with fG npG,
    by_cases v=w,
    rw h,
    
    let b:= bigraph.mk (neighbors G v) (neighbors G w) (λ (x:V), λ (y:V), G.E x y),

    apply card_eq_of_lunique_runique b,
    split,
    apply lunique_paths fG,
    rw neighbor_iff_adjacent,
    intro contra,
    apply hvw,
    apply G.undirected contra,

    apply runique_paths fG,
    rw neighbor_iff_adjacent,
    apply hvw,
end

theorem counter_reg {G:fin_graph V}:
    (friendship G ∧ no_pol G)→ ∃ d:ℕ, regular_graph G d :=
begin
    intro hG,
    have friend := hG.left,
    have np:=hG.right,
    have h2:=counter_non_adj_deg_eq hG,
    have v:= _inst_2.default,
    use degree G v,
    intro x,
    by_cases G.E v x,

    have hvx := h,
    cases np v with w wworks,
    cases np x with y yworks,
    have degvw:=counter_non_adj_deg_eq hG v w wworks.right,
    have degxy:=counter_non_adj_deg_eq hG x y yworks.right,
    by_cases G.E x w,
    have hxw:=h,
    rw degxy,
    by_cases G.E v y,
    have hvy := h,
    rw degvw,
    apply counter_non_adj_deg_eq hG,
    intro hcontra,
    apply yworks.left,
    unfold friendship at friend,
    apply exists_unique.unique (friend v w wworks.left),
    split,
    exact hvx,
    apply G.undirected hxw,
    split,
    exact hvy,
    apply G.undirected hcontra,
    
    apply counter_non_adj_deg_eq hG,
    intro hcontra,
    apply h,
    apply G.undirected hcontra,

    rw degvw,
    apply counter_non_adj_deg_eq hG,
    apply h,
    
    apply counter_non_adj_deg_eq hG,
    intro hcontra,
    apply h,
    apply G.undirected hcontra,
end


theorem friendship_adj_sq_off_diag_eq_one (G:fin_graph V):
    friendship G→ ∀ v w:V, v ≠ w → ((adjacency_matrix G)*(adjacency_matrix G)) v w = 1:=
begin
    intros friend v w distinct,
    change (adjacency_matrix G).mul (adjacency_matrix G) v w = 1,
    rw mul_val_eq_dot_row_col,
    rw adjacency_matrix_row_ind,
    rw adjacency_matrix_col_ind,
    rw dot_inds_eq_card_inter,
    unfold friendship at friend,
    have h:∀ (x:V), (x ∈ (neighbors G v ∩ neighbors G w) ↔ G.E v x ∧ G.E w x),
    intro u,
    repeat {rw ← neighbor_iff_adjacent},
    simp,
    have hu := friend v w distinct,
    have uexists:=hu.exists,
    cases uexists with u uworks,
    have singu : (neighbors G v ∩ neighbors G w)={u},
    apply finset.eq_singleton_iff_unique_mem.2,
    split,
    rw h u,
    exact uworks,
    intro x,
    intro hx,
    rw h at hx,
    symmetry,
    apply exists_unique.unique hu uworks hx,
    rw singu,
    simp,
end

def two_path_from_v (G:fin_graph V) (v:V):(V × V → Prop):=
    λ x:V × V, G.E v x.fst ∧ G.E x.fst x.snd

lemma friendship_reg_card_count_1 {G:fin_graph V} {d:ℕ}(v:V):
    (friendship G ∧ regular_graph G d)→ card_edges (path_bigraph G (neighbors G v) (finset.erase finset.univ v))=(finset.erase finset.univ v).card:=
begin
    intro hG,
    cases hG with friend,
    apply card_edges_of_lunique,
    apply lunique_paths friend,
    apply finset.not_mem_erase,
end

lemma friendship_reg_card_count_2 {G:fin_graph V} {d:ℕ}(v:V):
    (friendship G ∧ regular_graph G d)→ card_edges (path_bigraph G (neighbors G v) {v})=d:=
begin
    intro hG,
    cases hG with friend reg,
    unfold regular_graph at reg,
    have regv:= reg v,
    rw ← regv,
    apply card_edges_of_runique,
    rw right_unique_one_reg,
    unfold right_regular,
    intros a ha,
    change a ∈ neighbors G v at ha,
    rw right_fiber_eq_nbrs_inter_B,
    have h:neighbors G a∩ {v} = {v},
    apply finset.inter_singleton_of_mem,
    rw neighbor_iff_adjacent,
    rw neighbor_iff_adjacent at ha,
    apply G.undirected,
    exact ha,
    rw finset.inter_comm,
    rw h,
    simp,
    exact ha,
end

lemma friendship_reg_card_count_3 {G:fin_graph V} {d:ℕ}(v:V):
    (friendship G ∧ regular_graph G d)→ card_edges (path_bigraph G (neighbors G v) finset.univ)=d*d:=
begin
    intro hG,
    cases hG with friend reg,
    unfold regular_graph at reg,
    unfold degree at reg,

    transitivity d*(neighbors G v).card,
    apply card_edges_of_rreg,
    unfold right_regular,
    intros a ha,
    rw right_fiber_eq_nbrs_inter_B,
    rw finset.univ_inter,
    rw reg a,
    exact ha,
    rw reg v,
end

lemma finset.erase_disj_sing {α:Type*}{s:finset α}{a:α}:
    disjoint (s.erase a) {a}:=
begin
    rw finset.disjoint_singleton,
    apply finset.not_mem_erase,
end

lemma finset.erase_union_sing {α:Type*}{s:finset α}{a:α}:
    a ∈ s → s.erase a ∪ {a}=s:=
begin
    intro h,
    rw finset.union_comm,
    rw ← finset.insert_eq,
    apply finset.insert_erase h,
end

theorem friendship_reg_card {G:fin_graph V} {d:ℕ}:
    (friendship G ∧ regular_graph G d) → (fintype.card V)-1+d=d*d:=
begin
    intro hG,
    have v:= _inst_2.default,
    have hv:v ∈ finset.univ,
    apply finset.mem_univ,

    have un:(finset.erase finset.univ v)∪ {v}=finset.univ,
    apply finset.erase_union_sing,
    apply finset.mem_univ,

    rw ← friendship_reg_card_count_3 v hG,
    rw ← un,

    rw ← finset.card_univ,
    rw ← nat.pred_eq_sub_one,
    rw ← finset.card_erase_of_mem hv,

    rw ← friendship_reg_card_count_1 v hG,
    
    rw ← friendship_reg_card_count_2 v hG,

    symmetry,
    apply card_edges_add_of_eq_disj_union_eq,
    apply finset.erase_disj_sing,
end

lemma le_one_of_pred_zero {n:ℕ}:
    n-1=0 → n ≤ 1:=
begin
    cases n,
    simp,
    cases n,
    simp,
    rw ← nat.pred_eq_sub_one,
    rw nat.pred_succ,
    intro h,
    exfalso,
    apply nat.succ_ne_zero n h,
end



theorem friendship_reg_adj_sq (G:fin_graph V) (d:ℕ)(pos:0<d):
    (friendship G ∧ regular_graph G d) → (adjacency_matrix G)*(adjacency_matrix G) = matrix_J+(d-1)•1:=
begin
    intro hG,
    ext,
    by_cases i=j,
    rw ←  h,
    rw deg_from_adj_mat_sq,
    have hreg:= hG.right,
    unfold regular_graph at hreg,
    have hi:= hreg i,
    rw hi,
    unfold matrix_J,
    simp,
    cases d,
    exfalso,
    rw  nat.pos_iff_ne_zero at pos,
    apply pos,
    refl,
    ring,
    have friend:=friendship_adj_sq_off_diag_eq_one G hG.left i j h,
    rw friend,
    unfold matrix_J,
    simp,
    rw matrix.one_val_ne h,
    ring,
end

lemma subsingleton_graph_has_pol {G:fin_graph V}:
    fintype.card V ≤ 1 → exists_politician G:=
begin
    intro subsing,
    rw fintype.card_le_one_iff at subsing,
    let v:=_inst_2.default,
    existsi v,
    intro w,
    left,
    apply subsing v w,
end

lemma deg_le_one_friendship_has_pol {G:fin_graph V}{d:ℕ}:
    (friendship G ∧ regular_graph G d) → d ≤ 1 → exists_politician G:=
begin
    intros hG dleq1,
    have sq:d*d=d,
    cases d,
    simp,
    cases d,
    simp,
    exfalso,
    have h:= nat.le_of_succ_le_succ dleq1,
    apply nat.not_succ_le_zero d h,
    
    have hfr:=friendship_reg_card hG,
    rw sq at hfr,
    change fintype.card V - 1 + d = d+0 at hfr,
    rw add_comm at hfr,
    have hfr':= add_left_cancel hfr,

    apply subsingleton_graph_has_pol,
    apply le_one_of_pred_zero hfr',
end

lemma deg_two_friendship_has_pol {G:fin_graph V}{d:ℕ}:
    (friendship G ∧ regular_graph G d) → d = 2 → exists_politician G:=
begin
    intros hG deq2,
    have v:=_inst_2.default,
    have hfr:=friendship_reg_card hG,
    rw deq2 at hfr,
    have h2: fintype.card V - 1=2,
    linarith,
    have herase:(finset.univ.erase v).card = fintype.card V-1,
    apply finset.card_erase_of_mem,
    apply finset.mem_univ,
    rw h2 at herase,

    existsi v,
    intro w,
    by_cases v=w,
    left, exact h, right,
    have h':neighbors G v = finset.univ.erase v,
    apply finset.eq_of_subset_of_card_le,
    rw finset.subset_iff,
    intro x,
    rw neighbor_iff_adjacent,
    rw finset.mem_erase,
    intro h,
    split,
    intro hxv,
    rw hxv at h,
    apply G.loopless v,
    exact h,
    apply finset.mem_univ,
    rw herase,
    have hreg:=hG.right v,
    unfold degree at hreg,
    rw hreg,
    rw deq2,
    rw ← neighbor_iff_adjacent,
    rw h',
    rw finset.mem_erase,
    split,
    symmetry,
    apply h,
    apply finset.mem_univ,
end

lemma deg_le_two_friendship_has_pol {G:fin_graph V}{d:ℕ}:
    (friendship G ∧ regular_graph G d) → d ≤ 2 → exists_politician G:=
begin
    intros hG dleq2,
    by_cases d=2,
    apply deg_two_friendship_has_pol hG,
    apply h,
    have hlt:=nat.eq_or_lt_of_le dleq2,
    cases hlt,
    exfalso,
    apply h hlt,
    apply deg_le_one_friendship_has_pol hG,
    linarith,

end

lemma eigenval_constraints_contra {n:Type*}[fintype n]{d:ℕ}{f:n → ℝ}{hd:d>2}:
    (∃ a:n, f(a)=d ∧ ∀ b:n, a ≠ b → f(b)=real.sqrt(d-1)∨ f(b)=-real.sqrt(d-1)) → finset.univ.sum f ≠ 0:=
begin
    intro h,
    intro contra,
    cases h with a ha,
    have hsum: finset.univ.sum f = (finset.univ.erase a).sum f+finset.sum {a} f,
    rw ← finset.sum_union,
    rw finset.erase_union_sing,
    apply finset.mem_univ,

    apply finset.erase_disj_sing,

    simp at hsum,
    rw ha.left at hsum,
    rw hsum at contra,

    have hfilter: finset.univ.erase a = finset.filter (λ x:n, f(x)=real.sqrt(d-1)) (finset.univ.erase a) ∪ finset.filter (λ x:n, f(x)=-real.sqrt(d-1)) (finset.univ.erase a),
    rw ← finset.filter_or,
    transitivity finset.filter (λ (_x : n), true) (finset.univ.erase a),
    rw finset.filter_true,
    apply finset.filter_congr,
    intros x hx,
    simp,
    apply ha.right x,
    intro aeqx,
    rw aeqx at hx,
    apply finset.ne_of_mem_erase hx,
    refl,
    have hfiltersum: (finset.univ.erase a).sum f = (finset.filter (λ x:n, f(x)=real.sqrt(d-1)) (finset.univ.erase a)).sum f + (finset.filter (λ x:n, f(x)=-real.sqrt(d-1)) (finset.univ.erase a)).sum f,
    transitivity (finset.filter (λ x:n, f(x)=real.sqrt(d-1)) (finset.univ.erase a) ∪ finset.filter (λ x:n, f(x)=-real.sqrt(d-1)) (finset.univ.erase a)).sum f,
    rw ← hfilter,
    apply finset.sum_union,
    rw finset.disjoint_iff_inter_eq_empty,
    rw ← finset.filter_and,
    rw ← finset.filter_false,
    apply finset.filter_congr,
    intros x hx,
    simp,
    intro hpos,
    rw hpos,
    intro contra2,
    have h:real.sqrt(d-1)+(-real.sqrt(d-1))=0,
    simp,
    rw ← contra2 at h,
    have h':real.sqrt(d-1)=0,
    linarith,
    have hsq:(d - 1:ℝ)=(0:ℝ),
    transitivity real.sqrt(↑d - 1) * real.sqrt(↑d - 1),
    symmetry,
    apply real.mul_self_sqrt,
    sorry,
    sorry,
    sorry,
    sorry,

end

lemma exists_eigenbasis_of_sq_eq_J_plus_smul_id {n:Type*}[fintype n]{a:ℝ}{M: matrix n n ℝ}:
    (M.mul M = (a • 1) + matrix_J) →  ∃ b: finset (n→ ℝ), is_eigenbasis M.to_lin ↑b ∧ ((λ x:n, (1:ℝ)) ∈ b):=
begin
    intro Msq,
    have pos_space:=eigenspace M.to_lin (real.sqrt a),
    have neg_space:=eigenspace M.to_lin (- real.sqrt a),
    have ex_pos_basis:=finite_dimensional.exists_is_basis_finite ℝ pos_space,
    have ex_neg_basis:=finite_dimensional.exists_is_basis_finite ℝ neg_space,
    cases ex_pos_basis with pos_basis_set h_pos_basis,
    cases ex_neg_basis with neg_basis_set h_neg_basis,
    have pos_basis:=h_pos_basis.right.to_finset,
    have neg_basis:=h_neg_basis.right.to_finset,
    

end
    

lemma three_le_deg_friendship_contra {G:fin_graph V}{d:ℕ}:
    (friendship G ∧ regular_graph G d) → 3 ≤ d → false:=
begin
    intros hG threeled,
    have dpos:0<d,
    linarith,
    have hadj:=friendship_reg_adj_sq G d dpos hG,
    have traceless:=adj_mat_traceless G,

end

theorem friendship_theorem {G:fin_graph V}:
    friendship G → exists_politician G:=
begin
    intro fG,
    apply exists_pol_of_not_no_pol.1,
    intro npG,
    have regG: ∃ (d:ℕ), regular_graph G d,
    apply counter_reg,
    split,
    exact fG,
    exact npG,
    cases regG with d dreg,
    have hG:(friendship G∧ regular_graph G d),
    split,
    exact fG,
    exact dreg,
    by_cases d<3,
    have ex_pol: exists_politician G,
    apply deg_le_two_friendship_has_pol hG,
    linarith,
    apply exists_pol_of_not_no_pol.2 ex_pol npG,
    
    have threeleqd:3≤ d,
    linarith,
    apply three_le_deg_friendship_contra hG threeleqd,
end