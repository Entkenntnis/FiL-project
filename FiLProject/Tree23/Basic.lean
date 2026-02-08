import Mathlib.Tactic
-- set_option profiler true

inductive Tree23 (α : Type u)
| nil
| node2 (l : Tree23 α) (a : α) (r : Tree23 α)
| node3 (l : Tree23 α) (a : α) (m : Tree23 α) (b : α) (r : Tree23 α)
deriving DecidableEq

namespace Tree23

universe u

variable {α : Type u}

#print Tree23.nil
#eval Tree23.node2 (Tree23.nil) 2 (Tree23.nil)
#eval Tree23.node3 (Tree23.nil) 2 (Tree23.nil) 3 (Tree23.nil)

def numNodes : Tree23 α  → ℕ
| nil => 0
| node2 l _ r => numNodes l + numNodes r + 1
| node3 l _ m _ r => numNodes l + numNodes m + numNodes r + 1

@[simp, grind =]
lemma numNodesNil : numNodes (nil : Tree23 α) = 0 := by simp [numNodes]

@[simp, grind =]
lemma numNodesNode2 : numNodes (node2 l a r : Tree23 α) = numNodes l + numNodes r + 1
  := by simp [numNodes]

@[simp, grind =]
lemma numNodesNode3 : numNodes (node3 l a m b r : Tree23 α) =  numNodes l + numNodes m + numNodes r + 1
  := by simp [numNodes]


def numLeaves : Tree23 α  → ℕ
| nil => 1
| node2 l _ r => numLeaves l + numLeaves r
| node3 l _ m _ r => numLeaves l + numLeaves m + numLeaves r

def height : Tree23 α  → ℕ
| nil => 0
| node2 l _ r => max (height l) (height r) + 1
| node3 l _ m _ r => max (height l) (max (height m) (height r)) + 1

@[simp, grind =]
lemma heightNil : height (nil : Tree23 α) = 0 := by simp [height]

@[simp, grind =]
lemma heightNode2 : height (node2 l a r : Tree23 α) = max (height l) (height r) + 1
  := by simp [height]

@[simp, grind =]
lemma heightNode3 : height (node3 l a m b r : Tree23 α) = max (height l) (max (height m) (height r)) + 1
  := by simp [height]

def minHeight : Tree23 α  → ℕ
| nil => 0
| node2 l _ r => min (height l) (height r) + 1
| node3 l _ m _ r => min (height l) (min (height m) (height r)) + 1

@[grind]
def inorder : Tree23 α  → List α
| nil => []
| node2 l a r => inorder l ++ [a] ++ inorder r
| node3 l a m b r => inorder l ++ [a] ++ inorder m ++ [b] ++ inorder r
