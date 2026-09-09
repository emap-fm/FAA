/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!

Lean = Functional Programming Language + Interactive Proof Assistant

We start with how to prove a logical statement in Lean using basic tactics

## term and type in Lean
In Lean, we manipulate data using `term` and `type` of objects.
We can think of `type` as a collection of objects and `term` as an object/data point/element of that type
Let's define some constant
-/

opaque m : ℕ
#eval m

def n : ℕ := 100 -- n has type ℕ with specific value of 100
#eval n + 10

def z : ℚ := -0.1

def P1 : Prop := 1 = 1 -- P has type proposition, and its term is 1 = 1
def Q1 : Prop := 1 ≠ 1

#check 1 < 2

/-!
## How to state a theorem in Lean

theorem [name] {optional parameters/assumptions} : [proposition] := [proof]
-/

theorem one_eq_one : 1 = 1 := sorry
theorem one_eq_one': P1 := sorry

-- Let's check type of these thoerems
#check one_eq_one
-- one_eq_one has type 1 = 1

/-! Every true proposition has a proof. In Lean, a proof is represented as a term of the proposition.
* P : Prop` means `P` is a (specfic) proposition
* `h : P` means `h` is a proof of `P`.
-- `theorem` tells Lean to treat every proof as a black-box.
-/

-- another example
theorem x_pos (x : ℤ) (h: 1 < x) : 0 ≤ x := sorry

#check x_pos

/-!
## How to prove a theorem in Lean
Under the hood, Lean verifies a proof by type-checking. The details how type-checking works are not our main focus here.
Given a theorem statement, our objective is to tell Lean the proof by using basic tactics.
This is a game: we start with initial goal given by the theorem and provide a sequence of tactics to close the goal.
There are ∼ 20 tactics that will be often used. We will introduce new tactics as we go along.

* `rfl` -- reflexive property a = a: the goal can be closed because two objects are defitionally equal
* `exact` -- the goal can be closed by exactly this hypothesis (i.e., because the goal is definitionally equal to it)
* `intro` -- reduce a goal of the form `P → Q` to `Q` and obtain `h : P` as a new hypothesis
          -- i.e., to prove implication, let's assume P and then we prove Q
* `constructor` -- break down the goals of the form P ∧ Q or P ↔ Q into subgoals
                -- i.e., to prove P ∧ Q, let's prove P     and Q     separately
                --       to prove P ↔ Q, let's prove P → Q and Q → P separately
-/

section
-- Throughout this sheet, `P`, `Q` denote propositions.
variable (P Q: Prop)

example : P = P := rfl
example : 2 + 1 + 1 = 4 := rfl

example : P → P :=
  fun x ↦ x

example : P → (Q → P) :=
  fun hp _hq ↦ hp

example (hP: P) (hQ: Q) : P ∧ Q := by
  constructor
  all_goals assumption

example: P ∧ Q ↔ Q ∧ P:= by
  constructor
  · intro h
    exact And.intro h.2 h.1
  · intro h
    obtain ⟨hq, hp⟩ := h
    exact ⟨hp, hq⟩
