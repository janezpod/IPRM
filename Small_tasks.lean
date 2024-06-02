import Mathlib
open BigOperators
open Finset

-- SMALL TASKS

-- 1.) Formalize the recursive definition of the catalan numbers

def catalan_number : (n : ℕ) → ℕ
| 0 => 1
| n + 1 => ∑ i : Fin (n + 1), catalan_number i * catalan_number (n - i)

-- 2.) Formalize the concept of plane trees.

inductive plane_tree : Type
| parent_of : List plane_tree → plane_tree

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


-- BIG TASKS

-- 4.) Construct a bijection list plane_tree ≃ plane_tree.

def bijection_listPT_and_PT : List plane_tree ≃ plane_tree where
  toFun := plane_tree.parent_of
  invFun := fun
    | .parent_of children => children
  left_inv := fun
    | .nil => rfl
    | .cons _ _ => rfl
  right_inv := fun
    | .parent_of _ => rfl

-- 5.) Construct the rotating isomorphism, which is the isomorphism between plane trees and full binary trees.
