/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


/-!
## Universal quantifier (∀) and Existential (∃) Quantifiers
* `∀ x : α, P x` means for every element x of type α, the property P x holds.
   In Lean, this is the same as (x : α) → P x
* `∃ x : α, P x` means there exists some element x of type α such that P x holds
-/

-- Working with universal quantifier

/-!
  Another useage of `intro` tactic
  * `intro` -- to reduce a goal of the form `∀ x : ℕ , P(x)` to `P(x)` and obtain `x : ℕ` as a variable
    i.e., to prove for-all statement, let fix an arbitrary element x, and then we prove P(x)
    This is because, in Lean, ∀ x : N, P(x) is equivalent to (x :ℕ) →  P(x)
-/

def f (x : ℕ) := x = 0

example : (∀ x : ℕ, f x) ↔ ((x : ℕ) → f x) := by rfl

example : ∀ n : ℕ, n + 0 = n := by
  intro b
  rfl

/-! tactics for working with the existential quantifier
* `use` -- The use tactic is used to provide a witness for an existential statement: ∃ x, P x
* `obtain` -- The obtain tactic is the reverse of use. When you have a hypothesis that states h : ∃ x, P x, you can use obtain to "extract" the witness x and its property P x from h
           -- so you can use them in your proof.
           -- obtain ⟨x, hx⟩ := h extracts witness and property from h: ∃ x, P x
           -- Use obtain ⟨a, ⟨b, c⟩⟩ := h for nested existentials
-/

#check (fun x => x + 3 = 7) 4

example : ∃ n : ℕ, n + 3 = 7 := by
  apply Exists.intro 4
  rfl

example : ∃ n : ℕ, n + 3 = 7 := by
  use 4

example : ∃ n m : ℕ, n + m = 5 := by
  use 2
  use 3

-- Definition of an even number.
def IsEven (n : ℤ) : Prop := ∃ k, n = 2 * k

-- If there exists an even number `n` that is greater than 10,
-- then there must exist some integer `m` that is greater than 5.
theorem lixo (h : ∃ n : ℤ, IsEven n ∧ n > 10) : ∃ m : ℤ, m > 5 := by
  -- Use `obtain` to get the number `n` and its properties from `h`.
  -- The syntax is: `obtain ⟨n, hn_prop⟩ := h`
  obtain ⟨b, hb⟩ := h
  use b
  have h₁ := hb.2
  linarith

def IsOdd (n : ℤ) : Prop := ∃ k, n = 2 * k + 1

example (n : ℤ) (h : IsEven n) :  IsOdd (n + 1) := by
  unfold IsOdd
  unfold IsEven at h
  obtain ⟨a,ha⟩ := h
  use a
  rw [ha]


-- Exercise 0. Prove that the sum of two even numbers is even.
example (a b : ℤ) (ha : IsEven a) (hb : IsEven b) : IsEven (a + b) := by
  unfold IsEven at ha hb
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  use (x + y)
  rw [hx,hy]
  linarith
