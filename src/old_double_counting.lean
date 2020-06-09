import data.fintype.basic data.finset data.prod

variables {α β:Type*}[decidable_eq α][decidable_eq β]

variables (a:finset α)(b: finset β)(p:(α × β) → Prop)[decidable_pred p]

def correspondence:finset (α × β):=
    finset.filter p (finset.product a b)

def inj_on:Prop:=
    (∀ (x:α),x∈ a →  ∃!(y : β), y ∈ b ∧ p (x,y))

variables {a} {b} {p}

lemma corr_snd_union {c:finset β}:
    correspondence a (b ∪ c) p=(correspondence a b p)∪ (correspondence a c p):=
begin
    unfold correspondence,
    rw ← finset.filter_union,
    apply congr rfl _,
    ext,
    simp,
    tauto,
end

lemma corr_snd_disjoint {c:finset β}:
    disjoint b c→ disjoint (correspondence a b p) (correspondence a c p):=
begin
    unfold correspondence,
    intro h,
    apply finset.disjoint_filter_filter,
    rw finset.disjoint_left,
    simp,
    rw finset.disjoint_left at h,
    tauto,
end


lemma corr_sub_swap:
    ∀ x : (α × β), x ∈ correspondence a b p → x.swap ∈ correspondence b a (p ∘ prod.swap):=
begin
    unfold correspondence,
    simp,
    tauto,
end

lemma corr_swap:
    ∀ x : (α × β), x ∈ correspondence a b p ↔ x.swap ∈ correspondence b a (p∘ prod.swap):=
begin
    intro x,
    split,
    apply corr_sub_swap,
    intro h,
    have h1:=corr_sub_swap x.swap h,
    simp at h1,
    have heq: correspondence a b p = correspondence a b ((p ∘ prod.swap) ∘ prod.swap),
    unfold correspondence,
    ext,
    simp,
    rw heq,
    exact h1,
end

theorem fst_card_eq_of_inj_on:
    (inj_on a b p) → (correspondence a b p).card=a.card:=
begin
    intro hinj,
    have himage:a.card= (finset.image prod.fst (finset.filter p (finset.product a b))).card,
    apply congr rfl _,
    ext,
    simp,
    split,
    intro ha1,
    have h:= (hinj a_1 ha1).exists,
    simp at h,
    cases h with b_1 hb1,
    use b_1,
    tauto,
    tauto,
    symmetry,
    rw himage,
    apply finset.card_image_of_inj_on,
    intros x hx y hy hxy,
    simp at hx,
    simp at hy,
    rw ← hxy at hy,
    ext,
    exact hxy,
    have h:= hinj x.fst hx.left.left,
    apply h.unique,
    simp,
    tauto,
    rw hxy,
    simp,
    tauto,
end

theorem snd_card_eq_of_inj_on:
    (inj_on b a (p∘ prod.swap)) → (correspondence a b p).card=b.card:=
begin
    intro hinj,
    rw ← fst_card_eq_of_inj_on hinj,
    apply nat.le_antisymm,
    apply finset.card_le_card_of_inj_on prod.swap,
    intro x,
    apply (corr_swap x).1,
    intros x h1 y h2 h3,
    rw ← prod.swap_swap x,
    rw ← (prod.swap_swap y),
    rw h3,
    apply finset.card_le_card_of_inj_on prod.swap,
    intro x,
    rw ← prod.swap_swap x,
    rw prod.swap_swap x.swap,
    apply (corr_swap x.swap).2,
    intros x h1 y h2 h3,
    rw ← prod.swap_swap x,
    rw ← (prod.swap_swap y),
    rw h3,
end

theorem cards_eq_of_injs_on:
    (inj_on a b p)∧ (inj_on b a (p ∘ prod.swap)) → a.card=b.card:=
begin
    intro hinj,
    cases hinj with inj1 inj2,
    transitivity (correspondence a b p).card,
    symmetry,
    apply fst_card_eq_of_inj_on inj1,
    apply snd_card_eq_of_inj_on inj2,
end
