import FiLProject.Tree23.Insert
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Tree23

universe u

variable {α : Type u}


lemma height_numNodes_log (t : Tree23 α) (ht : complete t):
    height t + 1 ≤ Real.logb 2 (2 * numNodes t + 2) := by
  have x := complete_height_numNodes t ht
  have x2 := mul_le_mul_of_nonneg_left (a := 2) x (by simp)
  have x3 := Real.logb_le_logb_of_le (b := 2) (x := 2 * 2 ^ t.height) (y := 2 * (t.numNodes + 1))
  have t : (2 : ℝ) * 2 ^ t.height ≤ 2 * (↑t.numNodes + 1) := by norm_cast
  specialize x3 (by simp) (by simp) t
  rw [← pow_succ'] at x3
  rw [Real.logb_pow] at x3
  simp at x3
  rw [mul_add] at x3
  simp at x3
  exact x3


variable [LinearOrder α]

def T_insert : α → Tree23 α → ℕ
| _, nil => 1
| x, node2 l a r => if x = a then 1
                    else if x < a then (T_insert x l) + 1
                    else (T_insert x r) + 1
| x, node3 l a m b r => if x = a then 1
                        else if x < a then
                          (T_insert x l) + 1
                        else if x = b then 1
                        else if x < b then
                          (T_insert x m) + 1
                        else (T_insert x r) + 1

lemma runtime_height (x : α) (t : Tree23 α) :
    T_insert x t ≤ height t + 1 := by
  induction t with
  | nil => simp[T_insert]
  | node2 l a r l_ih r_ih => grind[T_insert]
  | node3 l a m b r l_ih m_ih r_ih => grind[T_insert]


lemma insertion_time_approx (x : α) (t : Tree23 α) (ht: complete t) :
    T_insert x t ≤ Real.logb 2 (2 * numNodes t + 2) := by
  have := le_trans (α := ℝ) (a := T_insert x t) (b := height t + 1) (c := Real.logb 2 (2 * numNodes t + 2))
  have h1 := runtime_height x t
  rify at h1
  have h2 := height_numNodes_log t ht
  rify at h2
  specialize this h1 h2
  exact this

-- lemma insertion_time (x : α) (t : Tree23 α) (ht: complete t):
--   T_insert x t =O[l] log n := by
