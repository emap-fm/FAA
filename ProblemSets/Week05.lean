/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
set_option autoImplicit false
set_option tactic.hygienic false

-- All tactics are welcome.

-- # Problem 1: Predicate AllEven
-- Define Predicate `AllEven` is true if every number in the list is even.
-- e.g., [], [2], [8, 0, 4]
-- Complete the definition for AllEven. It should take a list of natural numbers (List ℕ) and return a Prop

def isEven (n :ℕ) : Prop := ∃k, n = 2*k

-- Your AllEven must use isEven function above
inductive AllEven : List ℕ → Prop

-- Prove that your AllEven predicate is equivalent to checking if every element in the list is even.
-- Let's split into two parts

-- # Part 1
theorem Problem1_1 (l : List ℕ)  :
  AllEven l → ∀ n ∈ l, isEven n := by sorry

-- # Part 2
theorem Problem1_2 (l : List ℕ)  :
  (h : ∀ n ∈ l, isEven n) → AllEven l := by sorry

-- # Sorted
-- We will use the following version of Sorted

def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

inductive Sorted: List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t  → Sorted (t) →  Sorted (a :: t)

-- # Problem 2: Prove that a list of length at most 1 is sorted.
def len : List ℕ → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

theorem Problem2 (l : List ℕ) (h: len l ≤ 1): Sorted l := by sorry


-- # Problem 3: Prove basic properties of Sorted
theorem Problem3_1 {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := by sorry
theorem Problem3_2 {x y : ℕ} {t : List ℕ} (hsort : Sorted (x :: y :: t)) : y.MinOfList t := by sorry


-- # Problem 4: Alternate Definitions of Sorted
-- Consider the following inductive predicate
inductive Sorted2: List ℕ  → Prop
  | nil : Sorted2 []
  | single (a : ℕ) : Sorted2 [a]
  | cons (a b : ℕ ) (t : List ℕ ) : a ≤ b → Sorted2 (b :: t) → Sorted2 (a :: b :: t)

-- Prove that Sorted2 is equivalent to Sorted
-- You may find `ext` tactic useful
theorem Problem4 : Sorted2 = Sorted := by sorry

-- # Problem 5: Binary Tree
-- Consider the following version of BinaryTree
inductive BinaryTree
  | nil
  | node (left : BinaryTree) (key : ℕ) (right : BinaryTree)

-- Define mirror operation as reversing the tree
def mirror : BinaryTree → BinaryTree
  | BinaryTree.nil        => BinaryTree.nil
  | BinaryTree.node l key r => BinaryTree.node (mirror r) key (mirror l)

-- A binary tree is complete if every node has either two non-empty subtrees or two empty subtrees.
-- We can define it using inductive predicate as follows.

inductive Complete : BinaryTree  → Prop
  | leaf : Complete BinaryTree.nil
  | node  (l : BinaryTree) (key : ℕ) (r : BinaryTree)
      (hl : Complete l) (hr : Complete r)
      (hiff : l = BinaryTree.nil ↔ r = BinaryTree.nil) :
    Complete (BinaryTree.node l key r)

-- Prove that if a mirror of t is complete then t is complete
theorem Problem5: ∀t : BinaryTree, Complete (mirror t) → Complete t := by sorry
