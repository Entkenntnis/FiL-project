import FiLProject.Tree23.Basic

namespace Tree23

universe u

variable {α : Type u}


@[grind]
def complete : Tree23 α  → Bool
| nil => true
| node2 l _ r => height l = height r ∧ complete l ∧ complete r
| node3 l _ m _ r => height l = height m ∧ height m = height r ∧ complete l ∧ complete m ∧ complete r

@[simp, grind =]
lemma complete_nil :
    complete (nil : Tree23 α) = true := by
  rfl

@[simp, grind =]
lemma complete_node2 :
    complete (node2 l a r) = (height l = height r ∧ complete l ∧ complete r) := by
  simp[complete]

@[simp, grind =]
lemma complete_node3 :
    complete (node3 l a m b r) = (height l = height m ∧ height m = height r ∧ complete l ∧ complete m ∧ complete r) := by
  simp[complete]


lemma complete_height_numNodes (t : Tree23 α) :
    complete t → 2 ^ (height t) ≤ numNodes t + 1 := by
  induction t <;> grind

-- Exercise 7.1
@[grind]
def maxt : ℕ → Tree23 Unit
| .zero => Tree23.nil
| .succ n => Tree23.node3 (maxt n) () (maxt n) () (maxt n)

#eval numLeaves (maxt 3)


@[grind! .]
lemma numNodes_maxt_helper  (n : ℕ) :
    2 * numNodes (maxt n) + 1 = 3 ^ n := by
  induction n <;> grind

lemma numNodes_maxt (n : ℕ) :
    numNodes (maxt n) = ((3 ^ n) - 1) / 2 := by
  grind

@[grind! .]
-- grind seems to fail to apply pow_le_pow_right in the suitable moment
-- this helper unlocks automations
lemma height_maxt_helper_subhelper (l : Tree23 α) (r : Tree23 α) :
    3 ^ l.height ≤ 3 ^ max l.height r.height := by
  refine Nat.pow_le_pow_right ?_ ?_ <;> grind

@[grind! .]
lemma height_maxt_helper (t : Tree23 α) :
    (numNodes t) * 2 + 1 ≤ 3 ^ (height t) := by
  induction t <;> grind

lemma height_maxt (t : Tree23 α) :
    numNodes t ≤ (3 ^ (height t) - 1) / 2 := by
  grind

@[grind! .]
lemma not_nil_height_pos (t : Tree23 α) :
    t ≠ nil → height t > 0 := by
  induction t <;> grind

lemma height_pos_not_nil (t : Tree23 α) :
    height t > 0 → t ≠ nil := by
  induction t <;> grind

-- TODO: iff only if
lemma height_zero_is_nil (t : Tree23 α) :
    height t = 0 → t = Tree23.nil := by
  induction t <;> grind
