import FiLProject.Tree23.Complete
import FiLProject.Tree23.Search

namespace Tree23

universe u

variable {α : Type u}

variable [LinearOrder α]



inductive InsertUp (α : Type u) where
| eq (t: Tree23 α)
| overflow (l: Tree23 α) (a: α)  (r: Tree23 α)


-- a bit of clean up
open InsertUp

def ins : α → Tree23 α → InsertUp α
| x, nil => InsertUp.overflow (Tree23.nil) x (Tree23.nil)
| x, node2 l a r => if x < a then
                      match ins x l with
                      | InsertUp.eq l' => eq (node2 l' a r)
                      | InsertUp.overflow l₁ b l₂ => InsertUp.eq (Tree23.node3 l₁ b l₂ a r)
                    else if x = a then
                      InsertUp.eq (Tree23.node2 l a r)
                    else
                      match ins x r with
                      | InsertUp.eq r' => InsertUp.eq (Tree23.node2 l a r')
                      | InsertUp.overflow r₁ b r₂ => InsertUp.eq (Tree23.node3 l a r₁ b r₂)
| x, node3 l a m b r => if x < a then
                          match ins x l with
                          | InsertUp.eq l' => InsertUp.eq (Tree23.node3 l' a m b r)
                          | InsertUp.overflow l₁ c l₂ => InsertUp.overflow (Tree23.node2 l₁ c l₂) a (Tree23.node2 m b r)
                        else if x = a then
                          InsertUp.eq (Tree23.node3 l a m b r)
                        else
                          if x < b then
                          match ins x m with
                          | InsertUp.eq m' => InsertUp.eq (Tree23.node3 l a m' b r)
                          | InsertUp.overflow m₁ c m₂ => InsertUp.overflow (Tree23.node2 l a m₁) c (Tree23.node2 m₂ b r)
                          else if x = b then
                            InsertUp.eq (Tree23.node3 l a m b r)
                          else
                            match ins x r with
                            | InsertUp.eq r' => InsertUp.eq (Tree23.node3 l a m b r')
                            | InsertUp.overflow r₁ c r₂ => InsertUp.overflow (Tree23.node2 l a m) b (Tree23.node2 r₁ c r₂)

def insertTree : InsertUp α → Tree23 α
| InsertUp.eq t => t
| InsertUp.overflow l a r => Tree23.node2 l a r

def insert (x : α) (t : Tree23 α) : Tree23 α :=
  insertTree (ins x t)

def insertHeigth : InsertUp α → ℕ
| InsertUp.eq t => height t
| InsertUp.overflow l _ _ => height l

lemma insert_preservation_completeness_helper (t : Tree23 α ) (a : α):
    complete t → complete (insertTree (ins a t)) ∧ insertHeigth (ins a t) = height t := by
  induction t <;> grind[insertTree, insertHeigth, complete, ins]

lemma insert_preservation_completeness (t : Tree23 α ) (a : α):
  complete t → complete (insert a t) := by
grind [insert_preservation_completeness_helper, insert]

lemma setTree_ins (t: Tree23 α) (x: α):
    setTree (insertTree (ins x t)) = {x} ∪ setTree t := by
  induction t <;> grind[setTree, insertTree, ins]

-- insertion is preserving search tree property
lemma searchTree_ins_searchTree (t: Tree23 α) (x: α):
    searchTree t → searchTree (insertTree (ins x t)) := by
  intro h
  induction t with
  | nil =>
    unfold searchTree ins insertTree
    simp
    grind[setTree]
  | node2 l a r l_ih r_ih =>
    obtain ⟨ hl, hr, hl', hr' ⟩ := h
    specialize l_ih hl'
    specialize r_ih hr'
    unfold ins
    split -- note: split_ifs
    · split <;>
      · expose_names
        have : setTree (insertTree (ins x l)) = {x} ∪ setTree l := by
          exact setTree_ins l x
        simp[insertTree, heq] at this
        grind[setTree, searchTree, insertTree]
    · split
      · expose_names
        grind[searchTree, insertTree]
      · have : setTree (insertTree (ins x r)) = {x} ∪ setTree r := by
            exact setTree_ins r x
        split
        · grind[setTree, searchTree, insertTree]
        · expose_names
          simp[heq, insertTree] at this
          grind[setTree, insertTree, searchTree]
  | node3 l a m b r l_ih m_ih r_ih =>
    obtain ⟨ hab, hl, hm, hmm, hr,  hl', hm', hr' ⟩ := h
    specialize l_ih hl'
    specialize m_ih hm'
    specialize r_ih hr'
    unfold ins
    split
    · split <;>
      · expose_names
        have := setTree_ins l x
        simp[insertTree, heq] at this
        grind[insertTree, searchTree, setTree]
    · split
      · grind[insertTree, searchTree]
      · split
        · split
          · rename_i m' heq
            have : setTree (insertTree (ins x m)) = {x} ∪ setTree m := by
              exact setTree_ins m x
            simp[insertTree, heq] at this
            grind[searchTree, insertTree]
          · rename_i b' m' heq
            have : setTree (insertTree (ins x m)) = {x} ∪ setTree m := by
              exact setTree_ins m x
            simp[insertTree, heq] at this
            have hab' : a < b' := by
              grind[setTree]
            grind[setTree, searchTree, insertTree]
        · split
          · simp[insertTree]
            grind[searchTree]
          · split
            · rename_i r' heq
              expose_names
              simp[heq, insertTree] at r_ih
              simp[insertTree]
              unfold searchTree
              refine ⟨ hab, hl, hm, hmm, ?_, hl', hm', r_ih ⟩
              have : setTree (insertTree (ins x r)) = {x} ∪ setTree r := by
                exact setTree_ins r x
              grind[setTree, insertTree]
            · rename_i c' r' heq
              expose_names
              simp[insertTree]
              have : setTree (insertTree (ins x r)) = {x} ∪ setTree r := by
                exact setTree_ins r x
              grind[searchTree, setTree, insertTree]

lemma isin_insert (t : Tree23 α) (x y : α) (h : searchTree t) :
    isin (insert x t) y = true ↔ x = y ∨ isin t y = true := by
  cases t with
  | nil => grind[insert, insertTree, ins, isin]
  | node2 l a r => grind[isin_el_setTree, insert, setTree_ins, searchTree, searchTree_ins_searchTree]
  | node3 l a m b r => grind[isin_el_setTree, insert, setTree_ins, searchTree, searchTree_ins_searchTree]
