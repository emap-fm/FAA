/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false


-- # Problem 1: Finding Min Recursively
def minimum (a b:ℕ ): ℕ := if a < b then a else b

-- Consider the following FindMin function
def FindMin (l : List ℕ) : ℕ :=
  match h: l with
  | [] => 0   -- Base case for empty list (0 is minimum in ℕ)
  | x::xs =>
      if he: xs = [] then x
      else
        have: 1 < l.length := by
          simp [h]
          by_contra!
          observe: xs.length = 0
          simp_all only [le_refl, List.length_eq_zero_iff]
        let n := l.length
        let left  := l.take (n / 2)
        let right := l.drop (n / 2)
        -- Recursive step: find max of each half and compare
        minimum (FindMin left) (FindMin right)
termination_by l.length decreasing_by all_goals grind

def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- You can use the following APIs.
-- # In this problem, prove that the FindMin algorithm correctly returns the minimum element for any non-empty input list of size n.
-- You may find the following theorems useful
theorem x_minlist_of_x_lt_minlist {x y: ℕ} {l: List ℕ } (h1: x ≤ y) (h2 : y.MinOfList l) : x.MinOfList l := by grind [Nat.MinOfList]
theorem min_list_of_left_right {x : ℕ} {l : List ℕ} (left right: List ℕ) (h_lr: left ++ right = l)
(h_min_left: x.MinOfList left)(h_min_right: x.MinOfList right): x.MinOfList (l) := by grind [Nat.MinOfList]

theorem Problem1 (l : List ℕ) (h_nonempty : l.length > 0) :
   let z := FindMin l
   z.MinOfList l := by sorry

-- # Problem 2: Finding Min Sequentially
-- Define minimum property
def Option.MinOfList (result : Option ℕ) (l : List ℕ) : Prop :=
  match result with
  | none => l = []
  | some m => m ∈ l ∧ ∀ x ∈ l, m ≤ x

def List.minHelper (xs : List ℕ)(val_so_far : ℕ) : ℕ := match xs with
  | [] => val_so_far
  | x :: xs => xs.minHelper (min x val_so_far)

def List.FindMin : List ℕ → Option ℕ
  | [] => none
  | x :: xs => some (xs.minHelper x)

-- # In problem 2, prove that FindMIn function correctly compute the mininmum
lemma Problem2 (l : List ℕ) : l.FindMin.MinOfList l := by sorry


-- For problem 3 and 4, we will use the following version of Merge and Sorted
-- # Merge
def Merge: List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys

-- # Sorted
inductive Sorted: List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t  → Sorted (t) →  Sorted (a :: t)

-- # Problem 3: Prove that y ∈ Merge xs (y :: ys)
-- You may find this List functions helpful
#check List.mem_cons_of_mem
#check List.mem_cons_self

theorem Problem3 (y : ℕ) (xs ys: List ℕ) : y ∈ Merge xs (y :: ys) := by sorry

-- # Problem 4: Prove that Merge function is commutative on sorted inputs
-- `nth_rewrite` tactic can be useful to rewrite a specific occurence
-- You may find this function useful and you may find the API about merge and sorted helpful
#check Merge.eq_def

-- # API about Merge
-- In this homework, let's assume you have access to the following theorems.
-- Proving these theorems are optional.
theorem sorted_suffix {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := sorry
theorem sorted_min {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) :  x.MinOfList xs  := by sorry
theorem merge_min_out (x : ℕ) (xs ys : List ℕ) (h_min_in_xs : ∀ y ∈ xs, x ≤ y) : Merge (x :: ys) xs = x :: Merge ys xs := sorry
theorem merge_min_out_sym(x : ℕ) (xs ys : List ℕ) (h_min_in_xs : ∀ y ∈ xs, x ≤ y) (h_min_in_ys : ∀ y ∈ ys, x ≤ y) : Merge ys (x ::xs)  = x :: Merge ys xs := by sorry

theorem Problem4  (xs ys: List ℕ) (h1: Sorted xs) (h2: Sorted ys): Merge xs ys = Merge ys xs := by sorry

-- # Problem 5: Prove that the index returned by this contain_bs correctly corresponds to q
-- Consider the following SortedArrayFun and contain_bs function

structure SortedArrayFun (n :ℕ) where
  get : ℕ → ℕ
  size : ℕ := n
  sorted: Monotone get

def contains_bs {n :ℕ }(arr : SortedArrayFun n) (q : ℕ) : Option ℕ :=
  bs_aux 0 (n-1) (by omega)
  where bs_aux (a b :ℕ) (h: a ≤ b): Option ℕ  :=
  if h: a = b then
    if q = arr.get a then some a
    else none
  else
    let mid := (a+b)/(2 :ℕ )
    if      q < arr.get mid then bs_aux a mid  (by omega)
    else if  arr.get mid < q then bs_aux (mid+1) b (by omega)
    else some mid

theorem Problem5 (n q :ℕ)(h: 0 < n)(arr : SortedArrayFun n):
    ∀ i, contains_bs arr q = some i → arr.get i = q := by sorry
