import Mathlib
open BigOperators
open Finset

-- SMALL TASKS

-- 1.) Formalize the recursive definition of the catalan numbers

def catalan_number : (n : ℕ) → ℕ
| 0 => 1
| n + 1 => ∑ i in range (n + 1), catalan i * catalan (n - i)

-- 2.) Formalize the concept of plane trees.

inductive plane_tree : Type
| node : List (plane_tree) → plane_tree

-- 3.) Formalize the concept of full binary trees.

inductive full_binary_tree: Type
| leaf : full_binary_tree
| node : (T1 T2 : full_binary_tree) → full_binary_tree

-- 4.) Construct the type of full binary trees with n nodes, not counting the leaves.

inductive full_binary_tree_with_nodes : ℕ → Type
| leaf : full_binary_tree_with_nodes 0
| join : {n m : ℕ} → full_binary_tree_with_nodes n → full_binary_tree_with_nodes m →
          full_binary_tree_with_nodes (n + m + 1)

-- 5.) Define the type of ballot sequences of length n.

inductive BallotSeq : ℕ → ℕ → Type
  | nil : BallotSeq 0 0
  | cons_A {a b : ℕ} (s : BallotSeq a b) : BallotSeq (a + 1) b
  | cons_B {a b : ℕ} (s : BallotSeq a b) (h : a > b) : BallotSeq a (b + 1)
