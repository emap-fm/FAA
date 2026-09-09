/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Metric

structure FinSimpleGraph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance  fintypeFinSimpleGraph {V : Type u} [Fintype V] [DecidableEq V] (G : FinSimpleGraph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)

open Finset SimpleGraph

variable  {V : Type*} [Fintype V] [DecidableEq V]

-- We will use the following version of BFS algorithm.
noncomputable
def bfs_rec
(G : FinSimpleGraph V)
(queue : List V)
(visited : Finset V)
  :=
  match queue with
  | [] => visited
  | v :: queue =>
    let new_neighbors := (G.neighborFinset v) \ visited
    let queue' := queue ++ new_neighbors.toList
    let visited' := visited ∪ new_neighbors
    bfs_rec G queue' visited'
    termination_by G decreasing_by sorry

#check bfs_rec.induct

noncomputable def bfs
  (G : FinSimpleGraph V)
  (s : V)
  : Finset V :=
  bfs_rec G {s} {s}

/-
## Problem 1: Prove that BFS never returns an empty set.
-/

theorem Problem1 (G : FinSimpleGraph V) (s : V) :
  (bfs G s).Nonempty := by sorry

/-
## Problem 2: Prove that the visited set only grows during BFS.
-/

theorem Problem2 (G : FinSimpleGraph V) (queue : List V) (visited : Finset V) :
  visited ⊆ bfs_rec G queue visited := by sorry

/-
## Problem 3:
Prove that on a complete graph (where every vertex is connected to every other),
BFS from any vertex s returns all vertices.
-/

def FinSimpleGraph.IsComplete (G : FinSimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v

theorem Problem3 (G : FinSimpleGraph V) (s : V) (hG : G.IsComplete) :
  bfs G s = Finset.univ := by sorry
