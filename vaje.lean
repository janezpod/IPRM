import Mathlib
open BigOperators
open Finset
open Finset.antidiagonal

/- 5. 4. 2024 -/

/- Binary trees -/
inductive binary_tree : Type
| leaf
| succ : binary_tree → binary_tree
| join : (T1 T2 : binary_tree) → binary_tree

/- height of binary tree -/
def binary_tree.height : binary_tree → ℕ
| .leaf => 1
| .succ T => 1 + T.height
| .join T1 T2 => 1 + max T1.height T2.height

/- The number of leaves of binary tree -/
def binary_tree.number_of_leaves : binary_tree → ℕ
| .leaf => 1
| .succ T => T.number_of_leaves
| .join T1 T2 => T1.number_of_leaves + T2.number_of_leaves

/- full binary trees -/

inductive full_binary_tree : Type
| leaf
| join : (T1 T2 : full_binary_tree) → full_binary_tree

/- height of full binary tree -/
def full_binary_tree.height : full_binary_tree → ℕ
| .leaf => 1
| .join T1 T2 => 1 + max T1.height T2.height

/- converting full_binary_tree to binary_tree -/
def binary_tree_of_full_binary_tree :
  full_binary_tree → binary_tree
| .leaf => .leaf
| .join T1 T2 => .join (binary_tree_of_full_binary_tree T1) (binary_tree_of_full_binary_tree T2)

/- converting binary_tree to full_binary_tree -/
def full_binary_tree_of_binary_tree :
  binary_tree → full_binary_tree
| .leaf => .leaf
| .succ T => full_binary_tree_of_binary_tree T
| .join T1 T2 => .join (full_binary_tree_of_binary_tree T1) (full_binary_tree_of_binary_tree T2)

def eq_height_binary_tree_of_full_binary_tree :
  (T : full_binary_tree) →
  T.height = (binary_tree_of_full_binary_tree T).height := by
intro T
induction' T with _ _ T1_H T2_H
· rfl
simp [full_binary_tree.height]
simp [binary_tree.height]
rw [T1_H, T2_H]

def full_binary_tree.number_of_leaves :
  full_binary_tree → ℕ
| .leaf => 1
| .join T1 T2 => T1.number_of_leaves + T2.number_of_leaves

def eq_number_of_leaves_binary_tree_of_full_binary_tree :
  (T : full_binary_tree) →
  T.number_of_leaves =
  (binary_tree_of_full_binary_tree T).number_of_leaves := by
sorry

inductive binary_tree_with_nodes : ℕ → Type
| leaf : binary_tree_with_nodes 1
| succ : {n : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes (n + 1)
| join : {n m : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes m →
          binary_tree_with_nodes (n + m + 1)

def binary_tree_of_binary_tree_with_nodes (n : ℕ):
  binary_tree_with_nodes n → binary_tree
| .leaf => .leaf
| .succ T => .succ (binary_tree_of_binary_tree_with_nodes _ T)
| .join T1 T2 => .join (binary_tree_of_binary_tree_with_nodes _ T1) (binary_tree_of_binary_tree_with_nodes _ T2)


/- 12. 4. 2024 -/
inductive plane_tree : Type
/- | make_plane_tree : (n : ℕ) → (Fin n → plane_tree) → plane_tree -/
| make_plane_tree : List (plane_tree) → plane_tree

/- ex: n = 0, Fin n = 0 -/

/-def plane_tree_to_full_binary_tree_aux : plane_tree → full_binary_tree
| plane_tree.make_plane_tree (h :: List.nil) => full_binary_tree.join (plane_tree_to_full_binary_tree_aux h) full_binary_tree.leaf
| plane_tree.make_plane_tree (h :: t) => full_binary_tree.join (plane_tree_to_full_binary_tree_aux h) (plane_tree_to_full_binary_tree_aux (plane_tree.make_plane_tree t))
| plane_tree.make_plane_tree (List.nil) => .leaf-/

def plane_tree_to_full_binary_tree : plane_tree → full_binary_tree
/- | plane_tree.make_plane_tree (h :: List.nil) => full_binary_tree.join (plane_tree_to_full_binary_tree h) full_binary_tree.leaf -/
| plane_tree.make_plane_tree (h :: t) => full_binary_tree.join (plane_tree_to_full_binary_tree h) (plane_tree_to_full_binary_tree (plane_tree.make_plane_tree t))
| plane_tree.make_plane_tree (List.nil) => .leaf

def full_binary_tree_to_plane_tree : full_binary_tree → plane_tree
| .leaf => plane_tree.make_plane_tree (List.nil)
| .join T1 T2 => (
  match (full_binary_tree_to_plane_tree T2) with
  | plane_tree.make_plane_tree l => plane_tree.make_plane_tree ( (full_binary_tree_to_plane_tree T1) :: l)
)

theorem inv1 ( T : plane_tree ) : T = full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree T) := by sorry

/- 19. 4. 2024 -/
#check catalan

inductive full_binary_tree_with_nodes : ℕ → Type
| leaf : full_binary_tree_with_nodes 0
| join : {n m : ℕ} → full_binary_tree_with_nodes n → full_binary_tree_with_nodes m →
          full_binary_tree_with_nodes (n + m + 1)

def F (n : ℕ) : full_binary_tree_with_nodes (n + 1) → Σ i : Fin (n + 1), Fin (catalan i) × (Fin (catalan (n - i))) := by
| .leaf =>
