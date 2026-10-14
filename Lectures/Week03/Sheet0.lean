/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

set_option pp.proofs true

/-!
## Calculation Proofs
Lean provides a powerful suite of "tactics" that can perform calculations,
simplify expressions, and even solve entire goals automatically.
-/

/-! basic tactics
* `simp` -- perform a sequence of simplifications.
* `grw` -- same as rw [e], but e can be a relation other than = or ↔
* `rel` -- apply `grw` to solve a relational goal by "substitution"
* `rw??` -- specific rw by clicking in the info view
* `gcongr` -- reduce a relational goal between a LHS and RHS matching the same pattern and outputs new simplified subgoals

-- Solver
* `norm_num` -- solve equalities/inequality involving literals (e.g., 3+1 ≤ 4, 1+1 = 2, 3 ≠ 4)
* `ring` --   solve expressions in commutative (semi)rings, allowing for variables in the exponent.
* `ring_nf` -- put the expression into a `normal' form
* `omega` --  solve integer and natural linear arithmetic problems.
* `linarith` -- solve linear arithmetic over the rationals

-- Remark
* `aesop` and `grind` -- too powerful automation (we will not use these two this week)
-/


example : (1 : ℕ) + 1 ≠ 6 := by
  norm_num

example : (3.141 : ℝ) + 2.718 = 5.859 := by
  norm_num


example {a b x c d : ℝ} : x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr
  sorry
  sorry

-- Example on grw/rel/gcongr
example {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d)
  : x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr

example (a b c d: ℝ)(h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [h₁ ,h₂]

example (a b c d: ℝ)(h₁ : a < b) (h₂ : c ≥ b) : a + d ≤ c + d := by
  grw [h₂, ← h₁]

-- Example
theorem power_two_ih (n : ℕ) (ih : 5 ≤ n) (h : 2 ^ n > n ^ 2)
  : 2 ^ (n + 1) > (n + 1) ^ 2 := by
  grw [Nat.pow_add_one',h, add_sq n 1,Nat.two_mul (n ^ 2), add_assoc]
  simp only [mul_one, one_pow, gt_iff_lt, add_lt_add_iff_left]
  rw [Nat.pow_two n]
  calc
    2 * n + 1 < 5 * n := by linarith
    _         ≤ n*n   := by grw [ih]

--Alternate Proof
theorem power_two_ih_alt (n : ℕ) (ih : 5 ≤ n) (h : 2 ^ n > n ^ 2) : 2 ^ (n + 1) > (n + 1) ^ 2 := by
   calc 2 ^ (n + 1) = 2 * 2 ^ n     := by ring
        _           > 2 * n ^ 2     := by omega
        _           = n ^ 2 + n*n   := by ring
        _           ≥ n ^ 2 + 5 * n := by
          simp only [ge_iff_le, add_le_add_iff_left]
          exact Nat.mul_le_mul_right n ih
        _           > n ^ 2 + 2 * n + 1 := by omega
        _           = (n + 1) ^ 2       := by ring

-- Exercise 1
-- try without omega

#check Nat.mul_add

theorem power_two_linear (n : ℕ) (ih : 3 ≤ n) (h : 2*n < 2^n)
  : 2*(n+1) < 2^(n+1) := by
  calc
     2 * (n + 1) = 2*n + 2   := by rw [Nat.mul_add 2 n 1]
              _  < 2^n + 2   := by gcongr ?_ + 2
              _  < 2^n + 2^n := by linarith
              _  = 2 * 2^n   := by linarith
              _  = 2^(n + 1) := by ring

-- Exericse 2
-- prove this without omega
example (n: ℕ) (h: 5 ≤ n) : 1 + n * 2 < 5*n := by
  calc
    1 + n * 2 < n + n * 2 := by linarith
           _  = 3 * n     := by linarith
           _  < 5 * n     := by gcongr ; trivial
