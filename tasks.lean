import Mathlib
open BigOperators
open Finset

-- SMALL TASKS

-- 1.) Formalize the recursive definition of the catalan numbers

/--Follows directly from the recursive definition and the initial condition:
Cₙ₊₁ = ∑ₖ₌₀,₁,.,ₙ CₖCₙ₋₁  and C₀ = 0.-/
def catalan_number : (n : ℕ) → ℕ
| 0 => 1
| n + 1 => ∑ i : Fin (n + 1), catalan_number i * catalan_number (n - i)

-- 2.) Formalize the concept of plane trees.

/--A plane tree (also called ordered tree) P is defined recursively. One specially
designated vertex v is called the root of P. Then either P consists of the single vertex v,
or else it has a sequence (P_1, . . . ,P_m) of subtrees P_i, 1 ≤ i ≤ m,
each of which is a plane tree. We define plane trees recursively from bottom-up.-/
inductive plane_tree : Type
| parent_of : List (plane_tree) → plane_tree

def plane_tree.node : plane_tree → plane_tree → plane_tree
| hd, (.parent_of tl) => .parent_of (List.cons hd tl)

-- 3.) Formalize the concept of full binary trees.

/--A full binary tree is a tree in which every node has either 0 or 2 children.
We define it recursively as follows. A full binary tree is either a single vertex
(a single node as the root vertex) or a tree whose root node has two subtrees,
both of which are full binary trees.-/
inductive full_binary_tree: Type
| leaf : full_binary_tree
| node : (T1 T2 : full_binary_tree) → full_binary_tree

-- 4.) Construct the type of full binary trees with n nodes, not counting the leaves.

/--A full binary tree with 0 nodes is a leaf. If it has more nodes then it is must
be constructed from two full binary trees.-/
inductive full_binary_tree_with_nodes : ℕ → Type
| leaf : full_binary_tree_with_nodes 0
| join : {n m : ℕ} → full_binary_tree_with_nodes n → full_binary_tree_with_nodes m →
          full_binary_tree_with_nodes (n + m + 1)

-- 5.) Define the type of ballot sequences of length n.

/--A ballot sequence of a sequence of 1’s and −1’s such that every partial
sum is non negative. We construct ballot sequences recursively as follows. Start with the
empty ballot sequence. We can always add a 1 to a ballot sequence. We can only add a -1
to a ballot sequence if it has more 1's than -1's.-/
inductive BallotSeq : ℕ → ℕ → Type
| nil : BallotSeq 0 0
| cons_A {a b : ℕ} (s : BallotSeq a b) : BallotSeq (a + 1) b
| cons_B {a b : ℕ} (s : BallotSeq a b) (h : a > b) : BallotSeq a (b + 1)
-- e-mail ??

-- BIG TASKS

-- 4.) Construct a bijection list plane_tree ≃ plane_tree.

theorem bijection_listPT_and_PT : List plane_tree ≃ plane_tree where
  toFun := plane_tree.parent_of
  invFun := fun
    | .parent_of children => children
  left_inv := fun
    | .nil => rfl
    | .cons _ _ => rfl
  right_inv := fun
    | .parent_of _ => rfl

-- 5.) Construct the rotating isomorphism, which is the isomorphism between plane trees and full binary trees.

-- FBT → PT
/-- Function from full binary trees (FBT) to plane trees (PT). -/
def FBT_to_PT : full_binary_tree → plane_tree := fun
  | .leaf => .parent_of []
  | .node T1 T2 => plane_tree.node (FBT_to_PT T1) (FBT_to_PT T2)

-- PT → FBT
/-- Function from plane trees (PT) to full binary trees (FBT). -/
def PT_to_FBT : plane_tree → full_binary_tree := fun
  | .parent_of [] => .leaf
  | .parent_of (hd :: tl) => .node (PT_to_FBT hd) (PT_to_FBT (.parent_of tl))

theorem bijection_FBT_and_PT : full_binary_tree ≃ plane_tree where
  toFun := FBT_to_PT
  invFun := PT_to_FBT
  left_inv := by
    intro fbt
    induction fbt with
    |leaf => rfl
    |node T1 T2 ih1 ih2 =>
      rw [FBT_to_PT]
      cases to_parent : (FBT_to_PT T2) with -- cases h : e, where e is a variable or an expression, performs cases on e as above, but also adds a hypothesis h : e = ... to each hypothesis, where ... is the constructor instance for that particular case.
      |parent_of a =>
        dsimp [plane_tree.node]
        rw[PT_to_FBT]
        rw[ih1]
        rw[← to_parent]
        rw[ih2]
  right_inv := by
     intro pt
     cases first : pt with
     |parent_of children =>
        induction children with
         |nil =>
            rw [PT_to_FBT]
            rw [FBT_to_PT]
         |cons hd tl ih1 => sorry
            -- ATTEMPT:
            -- rw [PT_to_FBT]
            -- rw [FBT_to_PT]
            -- rw [ih1]
            -- dsimp [plane_tree.node]
            -- GOAL: plane_tree.parent_of (FBT_to_PT (PT_to_FBT hd) :: tl) = plane_tree.parent_of (hd :: tl)
            -- use induction hypothesis for hd, that is (FBT_to_PT (PT_to_FBT hd) = hd, to get plane_tree.parent_of (hd :: tl) = plane_tree.parent_of (hd :: tl)
            -- rw [rfl]
