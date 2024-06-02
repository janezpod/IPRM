import Mathlib
open BigOperators
open Finset

-- SMALL TASKS

-- 1.) Formalize the recursive definition of the catalan numbers

/--Follows directly from the recursive definition and the initial condition:
Cₙ₊₁ = ∑ₖ₌₀,₁,.,ₙ CₖCₙ₋₁  and C₀ = 0.-/
def catalan_number : (n : ℕ) → ℕ
| 0 => 1
| n + 1 => ∑ i in range (n + 1), catalan i * catalan (n - i)

-- 2.) Formalize the concept of plane trees.

/--A plane tree (also called ordered tree) P is defined recursively. One specially
designated vertex v is called the root of P. Then either P consists of the single vertex v,
or else it has a sequence (P_1, . . . ,P_m) of subtrees P_i, 1 ≤ i ≤ m,
each of which is a plane tree. We define plane trees recursively from bottom-up.-/
inductive plane_tree : Type
| parent_of : List (plane_tree) → plane_tree

-- 3.) Formalize the concept of full binary trees.

/--A full binary tree is a tree in which every node has either 0 or 2 children.
We define it recursively as follows. A full binary tree is either a single vertex
(a single node as the root vertex) or a tree whose root node has two subtrees,
both of which are full binary trees.-/
inductive full_binary_tree: Type
| leaf : full_binary_tree
| node : (T1 T2 : full_binary_tree) → full_binary_tree

-- 4.) Construct the type of full binary trees with n nodes, not counting the leaves.

/--A full binary tree wiyh 0 nodes is a leaf. If it has more nodes then it is must
be constructed from two full binary trees.-/
inductive full_binary_tree_with_nodes : ℕ → Type
| leaf : full_binary_tree_with_nodes 0
| join : {n m : ℕ} → full_binary_tree_with_nodes n → full_binary_tree_with_nodes m →
          full_binary_tree_with_nodes (n + m + 1)

-- 5.) Define the type of ballot sequences of length n.

/--A ballot sequence of a sequence of 1’s and −1’ssuch that every partial
sum isnonnegative. We construct ballot sequences recursively as follows. Start with the
empty ballot sequence. We can always add a 1 to a ballot sequence. We can only add a -1
to a ballot sequence if it has more 1's than -1's.-/
inductive BallotSeq : ℕ → ℕ → Type
| nil : BallotSeq 0 0
| cons_A {a b : ℕ} (s : BallotSeq a b) : BallotSeq (a + 1) b
| cons_B {a b : ℕ} (s : BallotSeq a b) (h : a > b) : BallotSeq a (b + 1)
