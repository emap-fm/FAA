/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Divisibility.Basic


/- # Instruction
In this homework, you are not allowed to use tactics outside the basic tactics listed below.
Basic tactics: `rfl`, `intro`, `exact`, `constructor`, `apply`, `rw`
- `rfl` - close the goal of the form a = b where a and b are definitionally equal.
- `intro` - introduce hypotheses for implications
- `exact` - provide exact proof terms
- `constructor` - split conjunctions and biconditionals
- `apply` - use implications and functions backwards
- `rw` / `rewrite` - rewrite using equalities
- `use` - provide witnesses for existentials
- `obtain` - extract components from conjunctions

**Instructions**: Replace each `sorry` with the appropriate proof tactics.
**Submission**: Submit your HW0.lean file in Moodle.
-/

section Logic

variable (P Q R : Prop)

-- Question 1: Fill-in-the-blank proof
-- Hint: Break down the compound implication step by step. You'll need to assume the conjunction,
-- then a premise P, and show how to get to R by going through Q as an intermediate step.
theorem Q1 : (P → Q) ∧ (Q → R) → (P → R) := by
  sorry

-- Question 2: Prove a logical equivalence
-- Hint: Split the biconditional into two directions.
theorem Q2 : P → (Q → R) ↔ (P ∧ Q) → R := by sorry

-- Question 3: Transitivity of divisibility
-- Hint: You can might need follow theorem:
#check Nat.dvd_trans
theorem Q3 (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := sorry

-- Question 4:  Proving Even Numbers
def even_number (n : ℕ) : Prop := ∃ k, n = 2 * k
theorem Q4 : even_number 4 ∧ even_number 6 := by sorry

-- Question 5: Some divisibility problem
-- The following lemma has partial proof on it. Fill in the sorry to finish the proof.
-- You may find these theorems helpful
#check Dvd.dvd.mul_left
#check Nat.dvd_add_right

-- 'have' tactics is basically a sub-claim that to be filled by the proof.
-- In this problem, you are asked to prove the subclaims and then finish the proof.

lemma Q5 (n k : ℕ) (h1 : k ∣ 21 * n + 4) (h2 : k ∣ 14 * n + 3) : k ∣ 1 := by
  -- Step 1: If k divides both terms, then k divides their linear combinations
  have h3 : k ∣ 2 * (21 * n + 4) := by
    sorry
  have h4 : k ∣ 3 * (14 * n + 3) := by
    sorry
  -- Step 2: Key arithmetic calculation
  have h5 : 3 * (14 * n + 3) = 2 * (21 * n + 4) + 1 := by ring
  -- Hint: Nat.dvd_add_right is helpful here
  sorry
