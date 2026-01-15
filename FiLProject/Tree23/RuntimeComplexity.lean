import FiLProject.Tree23.Insert
import Mathlib.Analysis.Asymptotics.Defs

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
    T_insert x t ≤ (Real.log 2)⁻¹ * Real.log (2 * numNodes t + 2) := by
  have := le_trans (α := ℝ) (a := T_insert x t) (b := height t + 1) (c := Real.logb 2 (2 * numNodes t + 2))
  have h1 := runtime_height x t
  rify at h1
  have h2 := height_numNodes_log t ht
  rify at h2
  specialize this h1 h2
  rw [← div_eq_inv_mul]
  exact this

abbrev CompleteTree (α : Type u) := { t : Tree23 α // complete t }

def sizeAtTop : Filter (CompleteTree α) := -- why do we need a filter?
  Filter.atTop.comap (fun t ↦ numNodes t.val)

-- T_insert ∈ O(logn)
-- n is number of nodes for t
-- t is a complete tree
theorem T_insert_is_log_n (x : α) :
    (fun (t) ↦ (T_insert x t.val : ℝ))
      =O[sizeAtTop]
    (fun t ↦ Real.log (numNodes t.val)) := by
  apply Asymptotics.IsBigO.trans (g := fun t ↦ (Real.log 2)⁻¹ * Real.log (2 * (numNodes t.val) + 2))
  · apply Asymptotics.IsBigO.of_norm_le
    intro t
    simp
    grind[insertion_time_approx]
  · apply Asymptotics.IsBigO.trans ( g:= fun t ↦ Real.log (2 * (numNodes t.val) + 2))
    · apply Asymptotics.IsBigO.const_mul_left
      simp[Asymptotics.isBigO_refl]
    · apply Asymptotics.IsBigO.of_bound 3
      filter_upwards [Filter.preimage_mem_comap (Filter.Ici_mem_atTop 2)] with t ht
      have : numNodes t.val ≥ 2 := by grind
      simp
      set n := t.val.numNodes
      rw [abs_of_nonneg (by apply Real.log_nonneg; norm_cast; linarith)]
      rw [abs_of_nonneg (by apply Real.log_nonneg; norm_cast; linarith)]
      calc Real.log (2 * n + 2)
        _ ≤ Real.log (3 * n) := by
          apply Real.log_le_log
          · linarith
          · norm_cast
            linarith
        _ = Real.log 3 + Real.log n := by
          apply Real.log_mul
          · simp
          · norm_cast
            grind
        _ ≤ (2: ℕ) * Real.log n + Real.log n := by
          gcongr
          rw [← Real.log_pow]
          apply Real.log_le_log
          · simp
          · norm_cast
            nlinarith
        _ = 3 * Real.log n := by ring
