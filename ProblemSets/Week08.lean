/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library


set_option autoImplicit false
set_option tactic.hygienic false


-- We will use the following Monad
structure TimeM (α : Type) where
  ret : α
  time : ℕ

namespace TimeM

def pure {α} (a : α) : TimeM α :=
  ⟨a, 0⟩

def bind {α β} (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance : Monad TimeM where
  pure := pure
  bind := bind

-- Increment time

@[simp] def tick {α : Type} (a : α) (c : ℕ := 1) : TimeM α :=
  ⟨a, c⟩

notation "✓" a:arg ", " c:arg => tick a c
notation "✓" a:arg => tick a  -- Default case with only one argument

def tickUnit : TimeM Unit :=
  ✓ () -- This uses the default time increment of 1


-- We define `@[simp]` lemmas for the `.time` field, similar to how we did for `.ret`.
@[grind, simp] theorem time_of_pure {α} (a : α) : (pure a).time = 0 := rfl
@[grind, simp] theorem time_of_bind {α β} (m : TimeM α) (f : α → TimeM β) :
 (TimeM.bind m f).time = m.time + (f m.ret).time := rfl
@[grind, simp] theorem time_of_tick {α} (a : α) (c : ℕ) : (tick a c).time = c := rfl
@[grind, simp] theorem ret_bind {α β} (m : TimeM α) (f : α → TimeM β) :
  (TimeM.bind m f).ret = (f m.ret).ret := rfl

-- allow us to simplify the chain of compositions
attribute [simp] Bind.bind Pure.pure TimeM.pure

end TimeM

-- ============================================================================
-- Problem 1: Maximum element
-- ============================================================================
-- Implement maxT that finds the maximum element in a non-empty list
-- Each comparison should cost 1 time unit
-- Expected time complexity: n-1 comparisons for a list of length n

@[grind] def maxT : List ℕ → TimeM ℕ
| []  => return 0
| [x] => sorry
| x :: xs =>  sorry

@[grind] def mymax : List ℕ → ℕ
| [] => 0
| [x] => x
| x :: xs => max x (mymax xs)

theorem Problem1_maxT_correctness (xs : List ℕ):
  (maxT xs).ret = mymax xs :=  sorry

theorem Problem1_maxT_time (xs : List ℕ) (h : xs.length ≥ 1):
  (maxT xs).time = xs.length - 1 :=  sorry

-- ============================================================================
-- Problem 2: Analysis of binary search
-- ============================================================================

structure SortedArrayFun (n :ℕ) where
  get : ℕ → ℕ
  size : ℕ := n
  sorted: Monotone get

-- consider the following binary search algorithm on time monad

def contains_bs_monad {n :ℕ }(arr : SortedArrayFun n) (q : ℕ) : TimeM (Option ℕ) :=
  bs_aux 0 (n-1)
  where bs_aux (a b :ℕ) (h: a ≤ b := by omega): TimeM (Option ℕ) := do
  if h: a = b then
    if q = arr.get a then return some a
    else return none
  else
    let mid := (a+b)/(2 :ℕ)
    if q < arr.get mid then
      let result ← bs_aux a mid
      ✓ result
    else if  arr.get mid < q then
      let result ← bs_aux (mid+1) b
      ✓ result
    else return (some mid)

-- You can use these two theorems without proof
-- subinterval_to_interval_qlt
-- subinterval_to_interval_qgt

theorem subinterval_to_interval_qlt {n : ℕ} (arr : SortedArrayFun n) (q a mid b: ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b)
  (h_q: q < arr.get mid):
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (∃ i, a ≤ i ∧ i ≤ mid ∧ arr.get i = q)  :=  sorry

theorem subinterval_to_interval_qgt {n : ℕ} (arr : SortedArrayFun n) (q a mid b: ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b)
  (h_q: arr.get mid < q ):
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (∃ i, (mid+1) ≤ i ∧ i ≤ b ∧ arr.get i = q)  := sorry

-- # Problem 2.1: Prove the correctness of this algorithm.
-- Hint: Your solution should be minimally changed from the non-monad version
theorem Problem2_part1 (n q :ℕ)(h: 0 < n)(arr : SortedArrayFun n):
  (∃ i, i < n ∧ arr.get i = q) ↔ ((contains_bs_monad arr q).ret ≠ none) := sorry

-- Next, we will prove the running time
def g (n : ℕ) : ℕ :=
  if n = 0 then 0
  else g (n/2) + 1

-- This was a previous problem set; so you can assume this theorem without proof.
theorem g_close_form (n : ℕ) : g n ≤  Nat.log 2 n +1  :=  sorry

-- # Problem 2.2: Prove the following theorems
theorem g_monotone : Monotone g := sorry

-- # Problem 2.3: Prove the running time of this algorithm.
-- Hint: Formulate an intermediate lemma that works for general range [a,b] and then specialize to [0, n-1] to prove this

theorem Problem2_part3 (n q :ℕ)(arr : SortedArrayFun n) : (contains_bs_monad arr q).time ≤ Nat.log 2 (n-1) +1 := sorry
