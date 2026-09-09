/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

-- ## how to define new types from old types

-- Terms can be anonnymous functions (also called λ-expressions)
#check ℕ

-- New types can be created by defining a function between types
#check ℕ → ℤ

#check fun (x : ℕ) ↦ x
#check fun (x : ℕ) ↦ (x : ℤ)
#check fun (x : ℕ) ↦ (x^2 + x - 10 : ℤ)

def f' := fun (x : ℕ) ↦ (x^2 + x - 10: ℤ)

#check ℕ → ℕ → Prop
#check fun x : ℕ ↦ fun y ↦ x = y

def f := fun x : ℕ ↦ fun y : ℕ  ↦ x = y
#check f
#check (f)

-- function can be partially applied
#check f 0
#check f 0 0

example : f 0 0 := by rfl

/-! New tactics
* `rewrite` [h] - replace a term in the goal with an equivalent term [h].
* `assumption` - we are done because ∃`h` s.t. `exact h` can close the goal
* `rw` -- rewrite, followed by trying to close the goal by rfl.
-/

example (x : ℕ) : f 0 x → x = 0 := by
  intro h
  rw [f] at h
  symm at h
  assumption

example (x : ℕ) : f 0 x → x = 0 := by
  intro h
  unfold f at h
  rewrite [← h]
  rfl

-- Give a direct proof

example (x : ℕ) : f x 1 → x ≠ 2 := by
  rw [f]
  intro h h1
  rw [h] at h1
  exact (Nat.succ_ne_self 1) h1.symm

example (x y: ℕ): f 0 x ∧ f 0 y → x = y := by
  repeat rw [f]
  intro h
  obtain ⟨h1, h2⟩ := h
  rewrite [← h1, ← h2]
  rfl

/-! Bonus:
* `by_contra` - assume the negation of the goal and prove False
* `contradiction` - we are done because we have a proof of `h : P` and `h' : ¬ P`
* `trivial` - apply `rfl` or `assumption` or `contradiction` tactics
-/

-- Prove by contradiction
example (h1 : a = b) : a = b := by
  trivial

example (x : ℕ) : f x 1 → x ≠ 2 := by
  intro h1 h2
  rw [h1] at h2
  contradiction
