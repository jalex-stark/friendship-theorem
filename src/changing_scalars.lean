/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
-/

import linear_algebra.matrix
import data.matrix.basic


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
  refine ring_hom.mk (matrix.fun_apply f) _ _ _ _; unfold matrix.fun_apply,
  {
    ext,
    repeat {rw matrix.one_val},
    by_cases i=j,
    {
      repeat {rw if_pos h},
      rw ring_hom.map_one,
    },
    {
      repeat {rw if_neg h},
      rw ring_hom.map_zero,
    },
  },
  {
    intros M N,
    ext,
    repeat {rw matrix.mul_eq_mul},
    repeat {rw matrix.mul_val},
    rw ← coe_add_monoid_hom,
    repeat {rw add_monoid_hom.map_sum ↑f _ finset.univ},
    rw coe_add_monoid_hom,
    refine congr rfl _,
    ext,
    rw ring_hom.map_mul,
  },
  {
    ext,
    repeat {rw matrix.zero_val},
    rw ring_hom.map_zero,
  },
  {
    intros M N,
    ext,
    rw matrix.add_val,
    rw ring_hom.map_add,
    simp,
  }
end

lemma matrix.ring_hom_apply_to_fun [ring α] [ring β] (f: α →+* β) (M : matrix n n α) : 
(matrix.ring_hom_apply f).to_fun M = (matrix.fun_apply f) M:= rfl

