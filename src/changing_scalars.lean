/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
-/

import linear_algebra.matrix
import data.matrix.basic
import tactic


/-
# Applying maps to the scalars of rings

## Notations

## Implementation Notes

## References 

-/

universes u v

noncomputable theory

variables {m : Type u} [fintype m] {n : Type u} [fintype n] {α : Type v} {β : Type v} {γ : Type v}

def matrix.fun_apply (f : α → β) (M : matrix m n α) : matrix m n β :=
  λ (i : m) (j : n), f (M i j)

def matrix.fun_apply_comp (f : α → β) (g : β → γ) {M : matrix m n α} :
(matrix.fun_apply g) ((matrix.fun_apply f) M) = matrix.fun_apply (g ∘ f) M :=
begin
  ext,
  repeat {rw matrix.fun_apply},
end

variable [decidable_eq n]

def matrix.ring_hom_apply [ring α] [ring β] (f: α →+* β) : matrix n n α →+* matrix n n β :=
begin
  refine {to_fun := (matrix.fun_apply f), map_one' := _, map_mul' := _, map_zero' := _, map_add' := _};
  unfold matrix.fun_apply,
  { ext,
    repeat {rw matrix.one_val},
    by_cases i=j,
    { rw h, simp },
    repeat {rw if_neg h}, simp },
  { intros M N, ext,
    simp only [matrix.mul_eq_mul, matrix.mul_val],
    rw ← coe_add_monoid_hom, simp only [add_monoid_hom.map_sum],
    rw coe_add_monoid_hom,
    refine congr rfl _,
    ext, rw ring_hom.map_mul },
  { ext, repeat {rw matrix.zero_val}, simp },
  { intros M N, ext,
    rw [matrix.add_val, ring_hom.map_add], simp }
end

lemma matrix.ring_hom_apply_to_fun [ring α] [ring β] (f: α →+* β) (M : matrix n n α) : 
(matrix.ring_hom_apply f).to_fun M = (matrix.fun_apply f) M := rfl


def matrix.ring_hom_apply.smul 
  [ring α] [ring β] (f: α →+* β) (M : matrix n n α) {a₁ a₂ : α} (ha : f a₁ = f a₂) : 
(matrix.ring_hom_apply f) (a₁ • M) = (matrix.ring_hom_apply f) (a₂ • M) :=
begin
  ext, 
  change (matrix.ring_hom_apply f).to_fun (a₁ • M) i j = (matrix.ring_hom_apply f).to_fun (a₂ • M) i j,
  repeat {rw matrix.ring_hom_apply_to_fun},
  repeat {rw matrix.fun_apply},
  simp only [matrix.smul_val, ring_hom.map_mul],
  rw ha,
end

lemma matrix.ring_hom_apply.diag [ring α] [ring β] (f: α →+* β) (M : matrix n n α) : 
matrix.diag n β β (matrix.ring_hom_apply f M) = f ∘ (matrix.diag n α α) M :=
begin
  ext,
  rw matrix.ring_hom_apply,
  dsimp,
  rw matrix.fun_apply,
end

def matrix.ring_hom_apply.trace
  [ring α] [ring β] (f: α →+* β) (M : matrix n n α) : 
matrix.trace n β β (matrix.ring_hom_apply f M) = f (matrix.trace n α α M) :=
begin
  simp only [matrix.trace_diag, matrix.diag_apply], 
  sorry
  -- rw matrix.ring_hom_apply.diag,
  -- rw finset.sum_hom,
end
