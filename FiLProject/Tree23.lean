import Mathlib.Tactic

inductive Tree23 (α : Type u)
| nil
| node2 (l : Tree23 α) (a : α) (r : Tree23 α)
| node3 (l : Tree23 α) (a : α) (m : Tree23 α) (a : α) (r : Tree23 α)
deriving DecidableEq, Repr
compile_inductive% Tree23

namespace Tree23

universe u

variable {α : Type u} [LinearOrder α]

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

omit [LinearOrder α] in
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

omit [LinearOrder α] in
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

omit [LinearOrder α] in
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


-- Chapter 7.1

def isin : Tree23 α → α → Bool
| nil,  _ => false
| node2 l a r,  x => if x < a then (isin l x) else
                            if x = a then true else (isin r x)
| node3 l a m b r, x => if x < a then (isin l x) else
                            if x = a then true else
                              if x < b then (isin m x) else
                                if x = b then true else (isin r x)

#eval isin (Tree23.node3 (Tree23.node2 (Tree23.nil) 1 (Tree23.nil)) 2 (Tree23.nil) 3 (Tree23.nil)) 1

--insertion
inductive InsertUp (α : Type u) where
| eq (t: Tree23 α)
| overflow (l: Tree23 α) (a: α)  (r: Tree23 α)

def ins : α → Tree23 α → InsertUp α
| x, nil => InsertUp.overflow (Tree23.nil) x (Tree23.nil)
| x, node2 l a r => if x < a then
                      match ins x l with
                      | InsertUp.eq l' => InsertUp.eq (Tree23.node2 l' a r)
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
                            | InsertUp.overflow r₁ c r₂ => InsertUp.overflow (Tree23.node2 l a m) c (Tree23.node2 r₁ b r₂)

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
  induction t with
  | nil => grind[insertTree, insertHeigth, complete, ins]
  | node2 _ _ _ _ _ => grind [insertTree, ins, complete, insertHeigth, height]
  | node3 _ _ _ _ _ _ _ _ => grind [insertTree, ins, complete, insertHeigth, height]

lemma insert_preservation_completeness (t : Tree23 α ) (a : α):
    complete t → complete (insert a t) := by
  grind [insert_preservation_completeness_helper, insert]

omit [LinearOrder α] in
lemma height_zero_is_nil (t : Tree23 α) :
    height t = 0 → t = Tree23.nil := by
  induction t with
  | nil => simp
  | node2 l a r l_ih r_ih => grind[height]
  | node3 l a m a r l_ih m_ih r_ih => grind[height]


omit [LinearOrder α] in
lemma not_nil_height_pos (t : Tree23 α) :
    t ≠ nil → height t > 0 := by
  induction t with
  | nil => simp
  | node2 l a r l_ih r_ih => grind[height]
  | node3 l a m a r l_ih m_ih r_ih => grind[height]


omit [LinearOrder α] in
lemma height_pos_not_nil (t : Tree23 α) :
    height t > 0 → t ≠ nil := by
  induction t with
  | nil => grind[height]
  | node2 l a r l_ih r_ih => grind[height]
  | node3 l a m a r l_ih m_ih r_ih => grind[height]

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






--deletion
inductive DeleteUp (α : Type u) where
| eq (t: Tree23 α)
| underflow (t: Tree23 α)

def deleteTree : DeleteUp α → Tree23 α
| DeleteUp.eq t => t
| DeleteUp.underflow t => t

def node21 : DeleteUp α → α → (t: Tree23 α) → t ≠ nil → DeleteUp α
| DeleteUp.eq t₁, a, t₂, _ => DeleteUp.eq (Tree23.node2 t₁ a t₂)
| DeleteUp.underflow t₁, a, r, h =>
    match r with
    | nil => (by grind)
    | node2 t₂ b t₃ =>
      -- make sure that right side is also reduced in height by merging b into the node
      -- and propagate underflow up
      DeleteUp.underflow (Tree23.node3 t₁ a t₂ b t₃)
    | node3 t₂ b t₃ c t₄ =>
      -- fix left underflow by redistributing one element from node3 on the right sight to the top and
      -- the top element to the left, making both sides equal height
      DeleteUp.eq (Tree23.node2 (Tree23.node2 t₁ a t₂) b (Tree23.node2 t₃ c t₄))

def node22 : (t: Tree23 α) → α → DeleteUp α → t ≠ nil → DeleteUp α
| t₁, a, DeleteUp.eq t₂, _ => DeleteUp.eq (Tree23.node2 t₁ a t₂)
| l, a, DeleteUp.underflow t_r, h =>
    match l with
    | nil => (by grind)
    | node2 t₁ b t₂ =>
      DeleteUp.underflow (Tree23.node3 t₁ b t₂ a t_r)
    | node3 t₁ b t₂ c t₃ =>
      DeleteUp.eq (Tree23.node2 (Tree23.node2 t₁ b t₂) c (Tree23.node2 t₃ a t_r))

def node31 : DeleteUp α → α → (t₁ : Tree23 α) → α → (t₂ : Tree23 α) → t₁ ≠ nil → t₂ ≠ nil → DeleteUp α
| DeleteUp.eq t₁, a, t₂, b, t₃, _, _ => DeleteUp.eq (Tree23.node3 t₁ a t₂ b t₃)
| DeleteUp.underflow t₁, a,t_m, c, r, _, _ =>
    match t_m with
    | nil => (by grind)
    | node2 t₂ b t₃ => DeleteUp.eq (Tree23.node2 (Tree23.node3 t₁ a t₂ b t₃) c r)
    | node3 t₂ b t₃ c_inner t₄ => DeleteUp.eq (node3 (node2 t₁ a t₂) b (node2 t₃ c_inner t₄) c r)

def node32 : (t₁ : Tree23 α) → α → DeleteUp α → α → (t₂ : Tree23 α) →  t₁ ≠ nil → t₂ ≠ nil → DeleteUp α
| t₁, a, DeleteUp.eq t₂, b, t₃, _, _ =>  DeleteUp.eq (node3 t₁ a t₂ b t₃)
| t₁, a, DeleteUp.underflow t₂, b, t_m, _, _ =>
    match t_m with
    | nil => (by grind)
    | node2 t₃ c t₄ => DeleteUp.eq (node2 t₁ a (node3 t₂ b t₃ c t₄))
    | node3 t₃ c t₄ d t₅ => DeleteUp.eq (node3 t₁ a (node2 t₂ b t₃) c (node2 t₄ d t₅))

def node33 : (t₁ : Tree23 α) → α → (t₂ : Tree23 α) → α → DeleteUp α →  t₁ ≠ nil → t₂ ≠ nil → DeleteUp α
| t₁, a, t₂, b, DeleteUp.eq t₃, _, _ => DeleteUp.eq (node3 t₁ a t₂ b t₃)
| t₁, a, t_m, c, DeleteUp.underflow t_u, _, _ =>
    match t_m with
    | nil => (by grind)
    | node2 t₂ b t₃ => DeleteUp.eq (node2 t₁ a (node3 t₂ b t₃ c t_u))
    | node3 t₂ b t₃ c_inner t₄ => DeleteUp.eq (node3 t₁ a (node2 t₂ b t₃) c_inner (node2 t₄ c t_u))



def splitMin : (t : Tree23 α) → complete t → t ≠ nil → α × DeleteUp α
| nil, _, h => by grind[complete]
| node2 l a r, hc, _ =>
  if h: l = nil then
    (a, DeleteUp.underflow nil)
  else
    -- extract the smallest element merge reduced left side with right side
    -- ah, that is why this is called splitMin ...
    let (x, l') := splitMin l (by grind[complete]) (by assumption)
    have hr : r ≠ nil := by grind[height_pos_not_nil, complete, not_nil_height_pos]
    (a, node21 l' a r (by assumption))
| node3 l a m b r, _, _ =>
  if h: l = nil then
    (a, DeleteUp.underflow nil) --true?
  else
    let (x, l') := splitMin l (by grind[complete]) (by assumption)
    have hr : r ≠ nil := by grind[height_pos_not_nil, complete, not_nil_height_pos]
    have hm : m ≠ nil := by grind[height_pos_not_nil, complete, not_nil_height_pos]
    (a, node31 l' a m b r (by assumption) (by assumption))


def del : α → (t : Tree23 α) →  complete t → DeleteUp α
| _, nil, h => DeleteUp.eq Tree23.nil
| x, node2 l a r, h =>
  if hl: l = Tree23.nil then
    -- l and r are both nil
    if a = x then
      -- delete a, the leaf becomes nil, we need to borrow, return underflow
      DeleteUp.underflow Tree23.nil
    else
      -- no changes
      DeleteUp.eq (Tree23.node2 Tree23.nil a Tree23.nil)
  else
    -- not leaf, so l and r are both not nil
    have h2 : r ≠ nil := by grind[complete, not_nil_height_pos, height]

    if (x < a) then
      -- recursion on left subtree and handle underflow logic via node21
      node21 (del x l (by grind[complete])) a r (by assumption)
    else if (x = a) then
      let (a0, r0) := splitMin r (by grind[complete]) (by assumption)
      node22 l a0 r0 (by assumption)
    else
      -- recursion on right subtree and handle underflow logic via node22
      node22 l a (del x r (by grind[complete])) (by assumption)
| x, node3 l a m b r, h =>
  if hl: l = Tree23.nil then
    DeleteUp.eq (if x = a then
      Tree23.node2 Tree23.nil b Tree23.nil
    else if x = b then
      Tree23.node2 Tree23.nil a Tree23.nil
    else
      Tree23.node3 Tree23.nil a Tree23.nil b Tree23.nil
    )
  else
    have hr : r ≠ nil := by grind[complete, not_nil_height_pos, height]
    have hm : m ≠ nil := by grind[complete, not_nil_height_pos, height]

    if (x < a) then
      node31 (del x l (by grind[complete])) a m b r (by assumption) (by assumption)
    else if (x = a) then
      let (a', m') := splitMin m (by grind[complete]) (by assumption)
      node32 l a' m' b r (by assumption) (by assumption)
    else
      if (x < b) then
        node32 l a (del x m (by grind[complete])) b r (by assumption) (by assumption)
      else if (x = b) then
        let (b', r') := splitMin r (by grind[complete]) (by assumption)
        node33 l a m b' r' (by assumption) (by assumption)
      else
        node33 l a m b (del x r (by grind[complete])) (by assumption) (by assumption)


-- Example to test `del`
def exampleTree : Tree23 Nat :=
  Tree23.node3 (Tree23.node2 Tree23.nil 1 Tree23.nil) 2 (Tree23.node2 Tree23.nil 3 Tree23.nil) 4 (Tree23.node2 Tree23.nil 5 Tree23.nil)

lemma exampleTree_complete : complete exampleTree := by
  dsimp [exampleTree]
  -- each child is a node2 with nil children, so height = 1 and they are complete
  have h1 : complete (Tree23.node2 Tree23.nil 1 Tree23.nil) := by simp [complete, height]
  have h2 : complete (Tree23.node2 Tree23.nil 3 Tree23.nil) := by simp [complete, height]
  have h3 : complete (Tree23.node2 Tree23.nil 5 Tree23.nil) := by simp [complete, height]
  simp [complete, height]

#eval deleteTree (del 3 exampleTree exampleTree_complete) -- evaluates the deletion of 4 from `exampleTree`
