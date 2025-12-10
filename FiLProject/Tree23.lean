import Mathlib.Tactic

inductive Tree23.{u} (α : Type u) : Type u
| nil : Tree23 α
| node2 : (Tree23 α) → α → (Tree23 α) → (Tree23 α)
| node3 : (Tree23 α) → α → (Tree23 α) → α → (Tree23 α) → (Tree23 α)
deriving DecidableEq, Repr
compile_inductive% Tree23

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

def numLeaves : Tree23 α  → ℕ
| nil => 1
| node2 l _ r => numLeaves l + numLeaves r
| node3 l _ m _ r => numLeaves l + numLeaves m + numLeaves r

lemma num_leaves_nodes_plus_1 (t : Tree23 α) :
    numNodes t = numLeaves t + 1 := by sorry

def height : Tree23 α  → ℕ
| nil => 0
| node2 l _ r => max (height l) (height r) + 1
| node3 l _ m _ r => max (height l) (max (height m) (height r)) + 1

def minHeight : Tree23 α  → ℕ
| nil => 0
| node2 l _ r => min (height l) (height r) + 1
| node3 l _ m _ r => min (height l) (min (height m) (height r)) + 1

def complete : Tree23 α  → Bool
| nil => true
| node2 l _ r => height l = height r ∧ complete l ∧ complete r
| node3 l _ m _ r => height l = height m ∧ height m = height r ∧ complete l ∧ complete m ∧ complete r

lemma complete_height_numNodes (t : Tree23 α) :
    complete t → 2 ^ (height t) ≤ numNodes t + 1 := by
  induction t with
  | nil => intro h; rfl
  | node2 l a r ihl ihr  =>
    intro h
    unfold complete at h
    simp at h
    obtain ⟨hheight, hl, hr⟩ := h
    specialize ihr hr
    specialize ihl hl
    unfold height
    unfold numNodes
    have h1 : 2 ^ l.height + 2 ^ r.height ≤ l.numNodes + r.numNodes + 1 + 1 := by grind
    have h2 : 2 ^ ((max l.height r.height) + 1) ≤ 2 ^ l.height + 2 ^ r.height := by grind
    grind
  | node3 _ _ _ _ _ _ _ _ => sorry
