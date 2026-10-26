/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
import Lectures.Week03.Sheet0
set_option autoImplicit false


/-!
## Induction Proofs

  Let's say P: ℕ → Prop is a proposition indexed by a natural number. If you
  prove

  · P 0 · ∀ i : ℕ, P i → P (i+1) then P n holds for all natural numbers

  In lean, you can use induction' tactics to do so.
-/

#check Nat.and_forall_add_one

-- Let's define a recursive funciton:
def I : ℕ → ℕ
  | 0 => 0
  | n + 1 => I n + 1

#eval [I 0, I 1, I 2]

-- running examples
example (n:ℕ): I n = n := by
  induction' n with n ih
  · rfl
  · unfold I
    rw [ih]

-- Exercise 1
def I2 : ℕ → ℕ
  | 0 => 0
  | n + 1 => I2 n + 2

#eval [I2 0, I2 1, I2 2]

example (n : ℕ) : I2 n = 2 * n := by
  induction n with
  | zero =>
    rw [I2]
  | succ a ih =>
    rw [I2, ih, Nat.mul_add]


-- Another example
example (n:ℕ): Even (I2 n) := by
  induction' n with n ih
  · rw [I2]
    rw [Even]
    use 0
  · unfold I2
    unfold Even
    rw [Even] at ih
    obtain ⟨r ,hr⟩ := ih
    use (r+1)
    rw [hr]
    omega

-- Exercise 2
theorem even_or_odd (n : ℕ) : (∃ k, n = 2*k) ∨ (∃ k, n = 2*k+1) := by
  induction' n with a ih
  · left
    use 0
  · apply Or.elim ih
    · intro h
      obtain ⟨b, hb⟩ := h
      right
      use b
      rw [hb]
    · intro h
      obtain ⟨b, hb⟩ := h
      left
      use b + 1
      rw [hb, Nat.mul_add]

def S : ℕ → ℕ
  | 0 => 0
  | n + 1 => S n + (n + 1)

#eval S 1
#eval S 2
#eval S 3

#check mul_comm

-- Exercise 3
lemma Sn_two (n : ℕ) : 2*(S n) = n * (n + 1)  := by sorry

example (n : ℕ) : (S n) = n * (n + 1)/2  := by sorry

-- It is much easier to work with type ℚ
-- Example
def SQ : ℕ → ℚ
  | 0 => 0
  | n + 1 => SQ n + (n + 1)

example (n : ℕ) : (SQ n) = n * (n + 1)/2  := by
  induction' n with n ih
  · simp [SQ]
  · simp [SQ,ih]
    linarith

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

#eval [0!,1!,2!,3!,4!]

/- Induction principle starting at a non-zero number. To use in an induction
proof, the syntax is `induction n, hn using Nat.le_induction` (or the same for
`induction'`). -/

#check Nat.le_induction

-- In general, you can choose a version of induction.
#check Nat.decreasingInduction
#check Nat.div2Induction

-- Example
example : ∀ n ≥ 5, 2 ^ n > n ^ 2 := by
  intro n h
  induction' n,h using Nat.le_induction with n ih
  · simp
  · rename_i h
    exact power_two_ih n ih h

-- Exercise 4
lemma le_fact (n : ℕ) : 1 ≤ n ! := by
  induction' n with x ih
  · trivial
  · rw [factorial]
    grw [← ih]
    omega

-- Exercise 5
example (n : ℕ) : 2^n ≤ (n + 1)! := by
  induction' n with a ih
  · rw [Nat.pow_zero, factorial, factorial]
  · rw [Nat.pow_add_one]
    grw [ih]
    nth_rw 2 [factorial]
    rw [Nat.mul_comm]
    gcongr
    omega
