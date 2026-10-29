/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
import Lectures.Week03.Sheet0
import Lectures.Week03.Sheet1

set_option autoImplicit false


-- strong induction and two-step induction
#check  Nat.strong_induction_on

def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

#eval fib 1
#eval fib 2
#eval fib 3
#eval fib 4
#eval fib 5

-- Example
example (x: ℕ): fib x ≤ 2^x := by
  induction x using Nat.strong_induction_on
  rename_i n h
  unfold fib
  if h: n ≤ 1 then
    split
    · norm_num
    · norm_num
    · contradiction
  else
    simp at h
    split <;> all_goals (simp)
    simp_all
    rename_i n x
    have fxp: fib (x + 1) ≤ 2^(x+1) := by
      apply h
      omega
    have fx : fib x ≤ 2^x := by
      apply h
      omega
    grw [fxp,fx]
    omega

#check Nat.twoStepInduction

-- Exercise 5
example (x: ℕ): fib x ≤ 2^x := by
  induction' x using Nat.twoStepInduction with n ih₁ ih₂
  · simp [fib]
  · simp [fib]
  · rw [fib]
    calc fib (n + 1) + fib n ≤ 2^(n + 1) + 2^n := by grw [ih₁, ih₂]
        _ ≤ 2^(n + 1) + 2 * 2^n := by linarith
        _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by omega
        _ ≤ 2 * 2 ^ (n + 1) := by linarith
        _ ≤ 2 ^ (n + 2) := by
         rewrite (occs := .pos [1]) [← Nat.pow_one 2]
         rw [← Nat.pow_add]
         grind only

-- Define the following recurrence relation
-- f (n) ≤ n + 2* f(n/2)
-- f (1) = 1

def f (n : ℕ): ℕ :=
  if n = 0 then 0
  else 2*f (n/2) + n

def f_closed (n : ℕ) : ℚ := n * (Nat.log 2 n)+n

#eval (List.map f [0,1,2,3,4,5,6,7,8])
#eval (List.map f_closed [0,1,2,3,4,5,6,7,8])

-- Example
 example (n : ℕ): f (2^n) ≤ (n+1)*2^n   := by
  induction' n with i ih
  · simp [f]
  · unfold f
    simp only [Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, and_true, ↓reduceIte]
    ring_nf
    -- use rw?? tactic to simplify a specific expression
    rw [Nat.mul_div_left (2 ^ i) (by norm_num)]
    grw [ih]
    linarith

-- Exercise 6: the cost of binary search
def g (n : ℕ): ℕ :=
  if n = 0 then 0
  else g (n / 2) + 1

def g_close (n : ℕ) : ℕ  :=  Nat.log 2 n + 1

#eval (List.map g [0,1,2,3,4,5,6,7,8,1000])
#eval (List.map g_close [0,1,2,3,4,5,6,7,8,1000])

#check Nat.div2Induction

example (n : ℕ): g (2^n) ≤ n + 1 := by
  induction' n with a h
  · simp; simp [g]
  · simp [Nat.pow_add]
    rw [g]; simp; trivial -- why simp [g] fails!!!
