/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option tactic.hygienic false

/- # Instruction
In this homework, you are not allowed to use tactics outside the basic tactics listed below.
Basic tactics: `rfl`, `intro`, `exact`, `constructor`, `apply`, `rw`, `left`, `right`, `cases`, `by_cases`, `ext`, `trivial`,`contradiction`,`assumption`,`have`, `by_contra`, `rintro`

If you need to use different tactics, please justify why basic tactics in the list above are not sufficient.
In particular, you are not allowed to use automation (simp, aesop, grind, ring, omega, etc) to finish the goal.

**Instruction**:
(1) Fill each `sorry` with the appropriate tactics.
(2) For each problem, give an informal explanation of the proof strategy. This should correspond to your Lean proof.
**Submission**:  HW1.lean file in Moodle. The grading will be based on (1) and (2).

-/
section
open Set
variable {α : Type*}
variable (A B C : Set α)

/-
  Proof strategy for P1 is:
-/

lemma P1 : (B ∪ C) ⊆ A ↔ B ⊆ A ∧ C ⊆ A := by sorry


/-
  Proof strategy for P2 is:
-/

theorem P2 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by sorry

/-
  Proof strategy for P3 is:
-/

theorem P3 : (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C) := by sorry

-- The set difference operation is denoted by B \ A
-- This can be simplified using rw [mem_diff] where
#check mem_diff

-- In this theorem, the partial proof has been outlined.
-- Your task is to fill in the sorry
-- the following theorem can be helpful
#check subset_union_left

/-
  Proof strategy for P4 is:
-/

theorem P4 : (∃ X : Set α, A ∪ X = B) ↔ A ⊆ B := by
  constructor
  · -- Forward direction: if there exists X such that A ∪ X = B, then A ⊆ B
    sorry
  · -- Reverse direction: if A ⊆ B, then there exists X such that A ∪ X = B
    intro h           -- "Assume A ⊆ B"
    use B \ A         -- "Let X = B \ A"
    ext x
    sorry
end

section
variable {α : Type*} [DecidableEq α]
variable (A B C : Finset α)

open Finset
-- Finset is a set whose cardinality is bounded
-- If A is a Finset, then #A is the cardinality of the set

/- Recall rw tactics:
If thm is a theorem a = b, then as a rewrite rule,
  rw [thm] means to replace a with b, and
  rw [← thm] means to replace b with a.
-/

def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k
def IsDisjoint (A B: Finset α) : Prop := A ∩ B = ∅

-- you may find the following operations useful
#check card_union
#check card_eq_zero
#check Nat.two_mul


/-
  Proof strategy for P5 is:
-/

theorem P5 (U : Finset α) (A B : Finset α)
(hAB : IsDisjoint A B) (hcard : #A = #B) (htotal : A ∪ B = U) : IsEven (#U) := by
  -- Hint: First prove the following claim:
  have AB_eq: #(A ∪ B) = #A + #B := by sorry
  -- Then use AB_eq to finish the proof
  sorry
