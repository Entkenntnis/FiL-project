import FiLProject.Tree23.Basic
namespace Tree23

variable [LinearOrder α]

def isin : Tree23 α → α → Bool
| nil,  _ => false
| node2 l a r,  x => if x < a then (isin l x) else
                            if x = a then true else (isin r x)
| node3 l a m b r, x => if x < a then (isin l x) else
                            if x = a then true else
                              if x < b then (isin m x) else
                                if x = b then true else (isin r x)

def setTree : (t : Tree23 α) → Set α
| Tree23.nil => ∅
| Tree23.node2 l a r => (setTree l) ∪ {a} ∪ (setTree r)
| Tree23.node3 l a m b r => (setTree l) ∪ {a} ∪ (setTree m) ∪ {b} ∪ (setTree r)

def searchTree : (t : Tree23 α) → Prop
| Tree23.nil => True
| Tree23.node2 l a r => (∀ x ∈ (setTree l), x < a) ∧ (∀ x ∈ (setTree r), a < x) ∧ searchTree l ∧ searchTree r
| Tree23.node3 l a m  b r =>
  a < b ∧
  (∀ x ∈ (setTree l), x < a) ∧ (∀ x ∈ (setTree m), a < x) ∧
  (∀ x ∈ (setTree m), x < b) ∧ (∀ x ∈ (setTree r), b < x) ∧
  searchTree l ∧ searchTree m ∧ searchTree r

lemma isin_el_setTree (t: Tree23 α) (x: α) (h: searchTree t):
    isin t x ↔ x ∈ setTree t := by
  induction t with
  | nil => grind[isin, setTree]
  | node2 l a r l_ih r_ih =>  grind[isin, setTree, searchTree]
  | node3 l a m b r l_ih m_ih r_ih => grind[isin, setTree, searchTree]

lemma isin_iff_setTree (t: Tree23 α) (x: α) (h: searchTree t):
    isin t x = true ↔ x ∈ setTree t := by
  induction t with
  | nil => grind[setTree, isin]
  | node2 l a r l_ih r_ih => grind[setTree, isin, searchTree]
  | node3 l a m b r l_ih m_ih r_ih => grind[setTree, isin, searchTree]
