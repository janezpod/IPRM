import algebra.big_operators.basic


-- SMALL TASKS

-- 1.) Formalize the recursive definition of the catalan numbers

open_locale big_operators --enables notation

def catalan_number : (n : ℕ) → ℕ
| 0 => 0
| succ n => ∑ i in (Finset (succ n)) (catalan_number i) * (catalan_number (n-i))

#check catalan_number


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

inductive ballot_sequence : ℕ → ℕ → Type
| zero : ballot_sequence 0 0
| plus :
