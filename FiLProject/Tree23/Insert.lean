import FiLProject.Tree23.Complete
import FiLProject.Tree23.Search

namespace Tree23

universe u

variable {α : Type u}

variable [LinearOrder α]

@[grind]
inductive InsertUp (α : Type u) where
| eq (t: Tree23 α)
| overflow (l: Tree23 α) (a: α)  (r: Tree23 α)

-- a bit of clean up
open InsertUp

@[grind]
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

@[grind]
def insertTree : InsertUp α → Tree23 α
| InsertUp.eq t => t
| InsertUp.overflow l a r => Tree23.node2 l a r

@[grind]
def insert (x : α) (t : Tree23 α) : Tree23 α :=
  insertTree (ins x t)

@[grind]
def insertHeigth : InsertUp α → ℕ
| InsertUp.eq t => height t
| InsertUp.overflow l _ _ => height l

@[grind! .]
lemma insert_preservation_completeness_helper (t : Tree23 α ) (a : α):
    complete t → complete (insertTree (ins a t)) ∧ insertHeigth (ins a t) = height t := by
  induction t <;> grind

lemma insert_preservation_completeness (t : Tree23 α ) (a : α):
  complete t → complete (insert a t) := by
grind

@[grind! .]
lemma setTree_ins (t: Tree23 α) (x: α):
    setTree (insertTree (ins x t)) = {x} ∪ setTree t := by
  induction t <;> grind

@[grind! .]
lemma insertTree_setTree_helper (x : α) (t : Tree23 α):
    (insertTree (ins x t)).setTree = Insert.insert x t.setTree := by
  grind

-- insertion is preserving search tree property
@[grind! .]
lemma searchTree_ins_searchTree (t: Tree23 α) (x: α):
    searchTree t → searchTree (insertTree (ins x t)) := by
  intro h
  induction t with
  | nil => grind
  | node2 l a r l_ih r_ih =>
    -- this makes the goal a lot more complicated, so grind possibly avoids it
    -- explicitly handle it here
    unfold ins
    grind
  | node3 l a m b r l_ih m_ih r_ih =>
    unfold ins
    repeat (split <;> try (
      first
      | grind -- almost all cases are directly solvable
      | expose_names -- expect one case that is also difficult to extract as lemma due to the number of hs involed
        have hab' : a < b_1 := by
          grind
        grind
    ))

lemma isin_insert (t : Tree23 α) (x y : α) (h : searchTree t) :
    isin (insert x t) y = true ↔ x = y ∨ isin t y = true := by
  cases t <;> grind
