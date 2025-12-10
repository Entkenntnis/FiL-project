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
  | node2 l a r ihl ihr  => grind[complete, height, numNodes]
  | node3 l a m b r ihl ihm ihr => grind[complete, height, numNodes]

-- Exercise 7.1
def maxt : ℕ → Tree23 Unit
| .zero => Tree23.nil
| .succ n => Tree23.node3 (maxt n) () (maxt n) () (maxt n)

#eval numLeaves (maxt 3)

lemma numNodes_maxt (n : ℕ) :
    numNodes (maxt n) = (((3 : ℝ) ^ (n : ℝ))- 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    unfold maxt
    unfold numNodes
    simp
    rw[ih]
    have h_mul : 2 * (((3 : ℝ) ^ (n : ℝ) - 1) / 2 + (3 ^ (n : ℝ) - 1) / 2 + (3 ^ (n : ℝ) - 1) / 2 + 1) = 2 * ((3 ^ ((n : ℝ) + 1) - 1) / 2) := by
      ring_nf
      simp only [add_right_inj]
      rw [Real.rpow_add (by norm_num : (3 : ℝ) > 0)]
      simp
      grind
    exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) h_mul

lemma height_maxt_helper (t : Tree23 α) :
    (numNodes t) * 2 + 1 ≤ 3 ^ (height t) := by
  induction t with
  | nil => grind[numNodes, height]
  | node2 l a r ihl ihr =>
    unfold numNodes
    unfold height
    ring_nf
    have h1 : 3 ^ r.height ≤ 3 ^ max l.height r.height := by
      refine Nat.pow_le_pow_right ?_ ?_ <;> grind
    have h2 : 3 ^ l.height ≤ 3 ^ max l.height r.height := by
      refine Nat.pow_le_pow_right ?_ ?_ <;> grind
    grind
  | node3 l a m b r ihl ihm ihr =>
    unfold numNodes
    unfold height
    ring_nf
    have h1 : 3 ^ l.height ≤ 3 ^ max l.height (max m.height r.height):= by
      refine Nat.pow_le_pow_right ?_ ?_ <;> grind
    have h2 : 3 ^ m.height ≤ 3 ^ max l.height (max m.height r.height):= by
      refine Nat.pow_le_pow_right ?_ ?_ <;> grind
    have h3 : 3 ^ r.height ≤ 3 ^ max l.height (max m.height r.height):= by
      refine Nat.pow_le_pow_right ?_ ?_ <;> grind
    grind

lemma height_maxt (t : Tree23 α) :
    numNodes t ≤ ((3: ℝ) ^ (height t) - 1) / 2 := by
  obtain h := height_maxt_helper t
  rify at h
  have h2 : (2:ℝ) * (t.numNodes: ℝ) ≤ (2:ℝ) * ((3 ^ t.height - 1) / 2) := by
    have : (2:ℝ) * ((3 ^ t.height - 1) / 2) = (3 ^ t.height - 1) := by grind
    rw [this]
    have h3 : 1 + 2 * (t.numNodes: ℝ) ≤ 1 + (3 ^ t.height - 1) := by
      simp
      rw[add_comm]
      rw[mul_comm]
      exact h
    exact @le_of_add_le_add_left ℝ _ _ _ 1 _ _ h3
  exact le_of_mul_le_mul_left h2 (by simp : (0: ℝ) < (2:ℝ))
