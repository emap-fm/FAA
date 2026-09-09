/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
set_option autoImplicit false
set_option tactic.hygienic false

-- DO NOT CHANGE THE THEOREM STATEMENT
-- Fill in the sorry

-- All tactics are welcome.

-- # Problem 1
-- Prove that the list reverse operation does not change the length of the list.
def reverse {α : Type} : List α → List α
| [] => []
| a :: xs => reverse xs ++ [a]

def len {α : Type} : List α → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

-- Hint: use induction over the list
theorem problem1 (xs: List ℕ): len xs = len (reverse xs) := by sorry

-- # Problem 2: Consider the following rescursive function
def S : ℕ → ℕ  → ℕ
  | 0, 0 => 1
  | 0, _ => 0
  | _, 0 => 0
  | n+1, k =>
    if n + 1 = k then 1
    else k* (S n k) + (S n (k-1))

#check Nat.twoStepInduction

-- Hint: use induction over n
theorem problem2 (n: ℕ) (h: 0 < n): (S n 1) = 1 := by sorry
-- # Problem 3
-- This is a continuation of Problem 2
-- You may want to use the result from theorem problem2 to prove problem3
theorem problem3 (n: ℕ): (S n 2) = 2^(n-1) - 1  := by sorry

-- # Problem 4
/-
Define R(r,s):
  R(r,2) = r
  R(2,s) = s
  R(r,s) = R(r-1,s) + R(r,s-1)
  Prove that R(r,s) ≤ (r+s-2).choose (r-1)
-/

def R (r s : ℕ ): ℕ :=
  if r = 0 ∨ s = 0 then 0
  else if r ≤ 1 ∨ s ≤ 1 then 1
  else if r = 2 ∨ s = 2 then 2
  else (R (r-1) s) + (R r (s-1))

-- You may find this useful
#check Nat.choose_eq_choose_pred_add

-- Hint: you may find functional induction useful
lemma problem4 (r s : ℕ): R r s ≤ (r+s-2).choose (r-1) := by sorry


-- # Problem 5.1

-- Part 1: Defining interleave function
-- Define a function called interleave that takes two lists, xs and ys, and returns a new list where the elements of xs and ys are alternated.
-- If one list is longer than the other, the remaining elements of the longer list should be appended at the end.

def interleave : List ℕ → List ℕ → List ℕ  := sorry

/--
 * interleave [1, 2, 3] [4, 5, 6] should produce [1, 4, 2, 5, 3, 6].
 * interleave [1, 2] [3, 4, 5, 6] should produce [1, 3, 2, 4, 5, 6].
 * interleave [1, 2, 3, 4] [5, 6] should produce [1, 5, 2, 6, 3, 4].
 * interleave [] [1, 2] should produce [1, 2].
 * interleave [1, 2] [] should produce [1, 2].
 --/

-- # Problem 5.2
-- Recall len and reverse functions from Problem 1
theorem problem5_part2 (xs ys: List ℕ): len (reverse (interleave xs ys))  = len (reverse (xs)) + len ys  := by sorry
