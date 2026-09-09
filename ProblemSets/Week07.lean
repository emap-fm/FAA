/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false

-- For Problem 1 and 2, we work on the binary search algorithm for bitonic sorted array

def Bitonic (f : ℕ → ℤ) (n : ℕ) : Prop :=
  ∃ k,  k < n ∧
    StrictMonoOn f (Set.Icc 0 k) ∧   -- nondecreasing on [0,k]
    StrictAntiOn f (Set.Ici k)       -- nonincreasing on [k, ∞)

-- A "bitonic" array is an array that strictly increases and then strictly decreases, like [1, 4, 8, 10, 5, 2]. The goal is to find the "peak" element (10). The search logic is:
-- Look at mid and mid+1.
-- If arr.get mid < arr.get (mid+1), the peak must be in the right half.
-- If arr.get mid > arr.get (mid+1), the peak is in the left half (and mid could be it).

 def IsMaximum (f : ℕ → ℤ) (n : ℕ) (k : ℕ) : Prop :=
  k < n ∧ ∀ i < n, f i ≤ f k

structure BitonicSortedArrayFun (n :ℕ) where
  get : ℕ → ℤ
  size : ℕ := n
  bitonic: Bitonic get n

-- This property appears in the analysis, marking noncomoputable is fine.
noncomputable
def BitonicSortedArrayFun.peak_idx {n :ℕ} (arr: BitonicSortedArrayFun n) := (arr.bitonic).choose
lemma BitonicSortedArrayFun.peak_idx_spec {n :ℕ} (arr: BitonicSortedArrayFun n) : arr.peak_idx < n ∧
  StrictMonoOn arr.get (Set.Icc 0 arr.peak_idx) ∧ StrictAntiOn arr.get (Set.Ici arr.peak_idx) := (arr.bitonic).choose_spec

-- # Problem 1 (20 pts): prove that BitonicSortedArrayFun has a unique maximum which is arr.peak_idx
theorem Problem1 {n : ℕ} (arr : BitonicSortedArrayFun n) :
  IsMaximum arr.get n arr.peak_idx ∧ ∀ (y : ℕ), IsMaximum arr.get n y → y = arr.peak_idx := by sorry

-- # Problem 2 (30 pts): Prove that the following binary search algorithm returns index of maximum value in an bitonic array.
def find_idx_peak {n : ℕ}(arr : BitonicSortedArrayFun n) : ℕ :=
     aux 0 (n-1)
  where
    aux (a b : ℕ) (h : a ≤ b := by omega) : ℕ :=
      if h_eq : a = b then a
      else
        let mid := (a+b) / (2 :ℕ)
        if arr.get mid < arr.get (mid + 1) then
          -- We are on the increasing slope, so the peak is in the right half.
          aux (mid + 1) b
        else
          -- We are on the decreasing slope (or mid is the peak).
          -- The peak is in the left half, including mid.
          aux a mid

def IsPeakInRange {n :ℕ }(arr : BitonicSortedArrayFun n) (a b: ℕ): Prop :=
  arr.peak_idx ∈ Set.Icc a b

-- (20 pts)
-- Formulate and prove the following intermediate statement statement in Lean:
-- The index of the peak is in the range [a,b] if and only if the algorithm find_idx_peak.aux is correct on [a,b].

-- State the theorem and prove it
-- [theorem Problem2A_find_peak_correct_range]

-- (10 pts): Use the formulation in the previous step to prove the correctness of this algorithm.
theorem Problem2B_find_peak_correct {n :ℕ }(h: 0 < n)(arr : BitonicSortedArrayFun n):
 (find_idx_peak arr) = arr.peak_idx := by sorry


-- # Problem 3 (20 pts): Implement this function

def safeDivide (x y : ℕ) : Option ℕ :=
  if y = 0 then none else some (x / y)

/-
Implement a function that computes: ((a * b) / c) - ((d * e) / f)

Requirements:
1. Multiply a * b, then divide by c (use safeDivide)
2. Multiply d * e, then divide by f (use safeDivide)
3. Subtract the second result from the first
4. Return none if any division fails or if subtraction would be negative

You'll need this helper:
-/
def safeSub (x y : ℕ) : Option ℕ :=
  if x >= y then some (x - y) else none

/-
Part A: Implement using do notation
-/

def Problem3A (a b c d e f : ℕ) : Option ℕ := do
  sorry  -- Your code here

/-
Part B: Implement the SAME function WITHOUT do notation
(translate your do notation to explicit >>= operator:)
-/

def Problem3B (a b c d e f : ℕ) : Option ℕ :=
  sorry  -- Your code here


/- ## Problem 4 (30 pts): Monadic structure on lists
`List` can be viewed as a monad—like `Option`, but allowing multiple possible results. The code below defines `List` as a monad. -/

namespace List

def bind {α β : Type} : List α → (α → List β) → List β
  | [],      _ => []
  | a :: as, f => f a ++ bind as f

def pure {α : Type} (a : α) : List α := [a]

-- Problem 4A (10 pt): Prove the following.
theorem Problem4A {α β : Type} (a : α) (f : α → List β) :
    bind (pure a) f = f a := by sorry

-- Problem 4B (10 pt): Provce the following
theorem Problem4B {α : Type} :
    ∀as : List α, bind as pure = as := by sorry

-- Helper lemma: bind distributes over append
theorem bind_append {α β : Type} (f : α → List β) :
    ∀xs ys : List α, bind (xs ++ ys) f = bind xs f ++ bind ys f := by sorry

-- Problem 4C (10 pt): Prove the following
-- the bind_append theorem may be useful
theorem Problem4C {α β γ : Type} (f : α → List β) (g : β → List γ) :
    ∀as : List α, bind (bind as f) g = bind as (fun a ↦ bind (f a) g) := sorry


end List
