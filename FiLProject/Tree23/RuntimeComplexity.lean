import FiLProject.Tree23.Insert

namespace Tree23

universe u

variable {α : Type u}

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


lemma height_numNodes_log (t : Tree23 α) :
    height t ≤ Nat.log 2 (numNodes t + 1) := by sorry

lemma runtime_height (x : α) (t : Tree23 α) :
    T_insert x t ≤ height t + 1 := by
  induction t with
  | nil => simp[height, T_insert]
  | node2 l a r l_ih r_ih =>
    unfold height
    unfold T_insert
    by_cases x = a
    · sorry
    · sorry
  | node3 l a m b r l_ih m_ih r_ih => sorry


lemma insertion_time (x : α) (t : Tree23 α) :
    complete t → T_insert x t ≤ Nat.log 3 (numNodes t) + 1 := by
  induction t with
  | nil =>
    intro h
    simp[T_insert]
  | node2 l a r l_ih r_ih =>
    intro h
    specialize l_ih (by grind[complete])
    specialize r_ih (by grind[complete])
    by_cases x = a
    · grind[T_insert]
    · by_cases x < a
      · expose_names
        unfold T_insert
        split
        · contradiction
        ·
          sorry

      · sorry
  | node3 l a m b r l_ih m_ih r_ih => sorry
