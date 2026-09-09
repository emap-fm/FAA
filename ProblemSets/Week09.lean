/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk

structure FinSimpleGraph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance  fintypeFinSimpleGraph {V : Type u} [Fintype V] [DecidableEq V] (G : FinSimpleGraph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)

open Finset SimpleGraph

variable  {V : Type*} [Fintype V] [DecidableEq V]

-- # Problem 1 : Prove that BFS terminates
-- We will use the following BFS algorithm
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

noncomputable
def bfs
  (G : FinSimpleGraph V)
  (s : V)
  : Finset V :=
  bfs_rec G {s} {s}

-- In Problem 2 and 3, you are asked to prove the following simple properties of BFS algorithms

-- #  Problem 2 : Prove the following theorem
theorem Problem2 {G : FinSimpleGraph V}
  {v : V}
  (queue : List V)
  (visited : Finset V)
  (h_queue_nodes_in_visited : ∀ x ∈ queue, x ∈ visited)
  (h: v ∈ queue.toFinset ∪ visited):
  v ∈ bfs_rec G queue visited :=  by sorry

-- #  Problem 3 : Prove the following theorem
theorem Problem3 (G : FinSimpleGraph V)
  (queue : List V)
  (visited : Finset V)
  (w v: V) :
  let new_neighbors := G.neighborFinset v \ visited
  let queue' := queue ++ new_neighbors.toList
  let visited' := visited ∪ new_neighbors
  w ∈ bfs_rec G (v :: queue) visited → w ∈ bfs_rec G queue' visited' := sorry
