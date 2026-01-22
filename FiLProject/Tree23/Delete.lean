import FiLProject.Tree23.Complete
import FiLProject.Tree23.Search

namespace Tree23

universe u

variable {α : Type u}

-- investigate, add to grind
attribute [grind] complete

variable [LinearOrder α]

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
| DeleteUp.underflow t₁, a, t_m, c, r, _, _ =>
    match t_m with
    | nil => (by grind)
    | node2 t₂ b t₃ => DeleteUp.eq (Tree23.node2 (Tree23.node3 t₁ a t₂ b t₃) c r)
    | node3 t₂ b t₃ c_inner t₄ => DeleteUp.eq (node3 (node2 t₁ a t₂) b (node2 t₃ c_inner t₄) c r)

def node32 : (t₁ : Tree23 α) → α → DeleteUp α → α → (t₂ : Tree23 α) →  t₁ ≠ nil → t₂ ≠ nil → DeleteUp α
| t₁, a, DeleteUp.eq t₂, b, t₃, _, _ =>  DeleteUp.eq (node3 t₁ a t₂ b t₃)
| t₁, a, DeleteUp.underflow t₂, b, t_r, _, _ =>
    match t_r with
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
    have hr : r ≠ nil := by grind[height_pos_not_nil, complete]
    (x, node21 l' a r (by assumption))
| node3 l a m b r, _, _ =>
  if h: l = nil then
    (a, DeleteUp.eq (node2 nil b nil))
  else
    let (x, l') := splitMin l (by grind[complete]) (by assumption)
    have hr : r ≠ nil := by grind[height_pos_not_nil, complete]
    have hm : m ≠ nil := by grind[height_pos_not_nil, complete]
    (x, node31 l' a m b r (by assumption) (by assumption))

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
    have h2 : r ≠ nil := by grind[complete]

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
    have hr : r ≠ nil := by grind[complete]
    have hm : m ≠ nil := by grind[complete]

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

def delete (x : α) (t : Tree23 α) (hc : complete t) : Tree23 α :=
  deleteTree (del x t hc)

def deleteHeight : DeleteUp α → ℕ
| DeleteUp.eq t => height t
| DeleteUp.underflow t => height t + 1


omit [LinearOrder α] in
lemma completeness_preservation_deleteTree_node21 (a : α) (r : Tree23 α) (l' : DeleteUp α)
  (hr : complete r) (hl' : complete (deleteTree l'))
  (hheight : height r = deleteHeight l' ) (hrn : r ≠ nil) :
    complete (deleteTree (node21 l' a r hrn)) := by
  induction l' with
  | eq l => grind[complete, deleteTree, node21, deleteHeight]
  | underflow l =>
    unfold deleteTree node21
    grind[complete, deleteHeight, complete, deleteTree]

omit [LinearOrder α] in
lemma completeness_preservation_deleteTree_node22 (a : α) (l : Tree23 α) (r' : DeleteUp α)
  (hl : complete l) (hr' : complete (deleteTree r'))
  (hheight : height l = deleteHeight r' ) (hln : l ≠ nil) :
    complete (deleteTree (node22 l a r' hln)) := by
  induction r' with
  | eq r => grind[complete, deleteTree, node22, deleteHeight]
  | underflow r =>
    unfold deleteTree node22
    grind[complete, deleteHeight, complete, deleteTree]

omit [LinearOrder α] in
lemma completeness_preservation_deleteTree_node31 (a b : α) (m r : Tree23 α) (l' : DeleteUp α)
  (hm : complete m) (hr : complete r) (hl' : complete (deleteTree l'))
  (hhrl' : height r = deleteHeight l') (hhmr : height m = height r) (hrn : r ≠ nil) (hmn : m ≠ nil):
    complete (deleteTree (node31 l' a m b r hmn hrn)) := by
  induction l' with
  | eq l => grind[complete, deleteTree, node31, deleteHeight]
  | underflow l =>
    unfold deleteTree node31
    grind[complete, deleteHeight, complete, deleteTree]

omit [LinearOrder α] in
lemma completeness_preservation_deleteTree_node32 (a b : α) (l r : Tree23 α) (m' : DeleteUp α)
  (hl : complete l) (hr : complete r) (hm' : complete (deleteTree m'))
  (hhrm' : height r = deleteHeight m') (hhlr : height l = height r) (hln : l ≠ nil) (hrn : r ≠ nil):
    complete (deleteTree (node32 l a m' b r hln hrn)) := by
  induction m' with
  | eq m => grind[complete, deleteTree, node32, deleteHeight]
  | underflow m =>
    unfold deleteTree node32
    grind[complete, deleteHeight, complete, deleteTree]

omit [LinearOrder α] in
lemma completeness_preservation_deleteTree_node33 (a b : α) (l m : Tree23 α) (r' : DeleteUp α)
  (hl : complete l) (hm : complete m) (hr' : complete (deleteTree r'))
  (hhlr' : height l = deleteHeight r') (hhlm : height l = height m) (hln : l ≠ nil) (hmn : m  ≠ nil):
    complete (deleteTree (node33 l a m b r' hln hmn)) := by
  induction r' with
  | eq r => grind[complete, deleteTree, node33, deleteHeight]
  | underflow r =>
    unfold deleteTree node33
    grind[complete, deleteHeight, complete, deleteTree]

omit [LinearOrder α] in
lemma max_height_node21 (a : α) (r : Tree23 α)  (l' : DeleteUp α) (h : 0 < height r):
    deleteHeight (node21 l' a r (by grind[height_pos_not_nil])) = max (deleteHeight l') (height r) + 1 := by
  unfold deleteHeight
  cases l' with
  | eq l => grind[node21]
  | underflow t =>
    simp[node21]
    grind

omit [LinearOrder α] in
lemma max_height_node22 (a : α) (l : Tree23 α)  (r' : DeleteUp α) (h : 0 < height l):
    deleteHeight (node22 l a r' (by grind[height_pos_not_nil])) = max (deleteHeight r') (height l) + 1 := by
  unfold deleteHeight
  cases r' with
  | eq l => grind[node22]
  | underflow t =>
    simp[node22]
    grind

omit [LinearOrder α] in
lemma max_height_node31 (a b : α) (m r : Tree23 α) (l' : DeleteUp α) (hr : 0 < height r) (hm : 0 < height m) :
    deleteHeight (node31 l' a m b r (by grind[height_pos_not_nil]) (by grind[height_pos_not_nil])) = max (deleteHeight l') (max (height m) (height r)) + 1 := by
  unfold deleteHeight
  cases l' with
  | eq t => grind[node31]
  | underflow t =>
    simp[node31]
    grind

omit [LinearOrder α] in
lemma max_height_node32 (a b : α) (l r : Tree23 α) (m' : DeleteUp α) (hl : 0 < height l) (hr : 0 < height r) :
    deleteHeight (node32 l a m' b r (by grind[height_pos_not_nil]) (by grind[height_pos_not_nil])) = max (deleteHeight m') (max (height l) (height r)) + 1 := by
  unfold deleteHeight
  cases m' with
  | eq t => grind[node32]
  | underflow t =>
    simp[node32]
    grind

omit [LinearOrder α] in
lemma max_height_node33 (a b : α) (l m : Tree23 α) (r' : DeleteUp α) (hl : 0 < height l) (hm : 0 < height m) :
    deleteHeight (node33 l a m b r' (by grind[height_pos_not_nil]) (by grind[height_pos_not_nil])) = max (deleteHeight r') (max (height l) (height m)) + 1 := by
  unfold deleteHeight
  cases r' with
  | eq t => grind[node33]
  | underflow t =>
    simp[node33]
    cases m with
    | nil => grind
    | node2 lm am rm => grind
    | node3 l a m b r => grind

lemma splitMin_height_complete (t : Tree23 α )
  (hct: complete t) (hht : 0 < height t) :
    deleteHeight (splitMin t hct (by grind[height_pos_not_nil])).2 = height t := by
  induction t with
  | nil => grind
  | node2 l a r l_ih r_ih =>
    by_cases h : l = nil
    · grind[splitMin, deleteHeight, height_pos_not_nil, complete]
    · grind[splitMin, max_height_node21, complete]
  | node3 l a m b r l_ih m_ih r_ih =>
    by_cases h : l = nil
    · grind[splitMin, deleteHeight, height_pos_not_nil, complete]
    · grind[splitMin, max_height_node31, complete]

lemma splitMin_complete (t : Tree23 α)
  (hct : complete t) (hht : 0 < height t) :
    complete (deleteTree (splitMin t hct (by grind[height_pos_not_nil])).2) := by
  induction t with
  | nil => grind[complete]
  | node2 l a r l_ih r_ih =>
      unfold splitMin
      by_cases h : l = nil
      · grind[complete, deleteTree]
      · grind[completeness_preservation_deleteTree_node21, complete, splitMin_height_complete]
  | node3 l a m a r l_ih m_ih r_ih =>
      unfold splitMin
      by_cases h : l = nil
      · grind[complete, deleteTree]
      · grind[completeness_preservation_deleteTree_node31, complete, splitMin_height_complete]

lemma complete_deleteHeight (t : Tree23 α) (x : α) (h : complete t):
    deleteHeight (del x t (by assumption)) = height t := by
  induction t with
  | nil => grind[del, deleteHeight]
  | node2 l a r l_ih r_ih =>
    unfold del
    split
    · grind[deleteHeight, complete]
    · split
      · expose_names
        rw[max_height_node21]
        · grind
        · grind[complete]
      · split
        · expose_names
          rw[max_height_node22]
          · have hr: r ≠ nil := by grind[complete, height]
            have : deleteHeight (splitMin r (by grind[complete]) hr).2 = height r := by
              rw[splitMin_height_complete]
              grind
            grind[splitMin, deleteHeight, complete]
          · grind[complete]
        · expose_names
          rw[max_height_node22]
          · grind
          · grind[complete]
  | node3 l a m b r l_ih m_ih r_ih =>
    unfold del
    -- aesop (add norm [deleteHeight, complete, splitMin, splitMin_height_complete, max_height_node31, max_height_node32, max_height_node33] )
    split
    · grind[deleteHeight, complete]
    · split
      · rw[max_height_node31]
        · grind[height]
        · grind[complete]
        · grind[complete]
      · split
        · rw[max_height_node32]
          · have hm : m ≠ nil := by grind[complete]
            have : deleteHeight (splitMin m (by grind[complete]) hm).2 = height m := by
              rw[splitMin_height_complete]
              grind
            grind[splitMin, deleteHeight, complete]
          · grind[complete]
          · grind[complete]
        · split
          · rw[max_height_node32]
            · grind
            · grind[complete]
            · grind[complete]
          · split
            · rw[max_height_node33]
              have hr: r ≠ nil := by grind[complete]
              have : deleteHeight (splitMin r (by grind[complete]) hr).2 = height r := by
                rw[splitMin_height_complete]
                grind
              grind[height, splitMin, deleteHeight, complete]
              · grind[complete]
              · grind[complete]
            · rw[max_height_node33]
              · grind
              · grind[complete]
              · grind[complete]


lemma complete_complete_del (t : Tree23 α) (x : α) (h : complete t):
    complete (deleteTree (del x t h)) := by
  induction t with
  | nil => grind[complete, deleteTree, del]
  | node2 l a r l_ih r_ih =>
      grind[completeness_preservation_deleteTree_node21, completeness_preservation_deleteTree_node22, complete_deleteHeight, complete,  splitMin_height_complete, splitMin_complete, deleteTree, del]
  | node3 l a m b r l_ih m_ih r_ih =>
      grind[completeness_preservation_deleteTree_node31, completeness_preservation_deleteTree_node32, completeness_preservation_deleteTree_node33, complete_deleteHeight, complete, splitMin_height_complete, splitMin_complete, deleteTree, del]

lemma delete_completeness_preservation (t : Tree23 α) (x : α) (h : complete t):
    complete (delete x t h) := by
    grind[complete_complete_del, delete]




-- searchTree property

-- first prove a helper
omit [LinearOrder α] in
lemma node21_preserves_members
  (l_up : DeleteUp α)
  (a el: α)
  (l r : Tree23 α)
  (hr : r ≠ nil)
  (hx : ∀ x: α, x ∈ setTree (deleteTree l_up) → x ∈ setTree l):
    el ∈ setTree (deleteTree (node21 l_up a r hr)) → el ∈ setTree (node2 l a r) := by
  cases leq : l_up
  · grind[deleteTree, node21, setTree]
  · simp[node21]
    cases r with
    | nil => grind[setTree]
    | node2 l a r =>
      expose_names
      simp[deleteTree]
      rw [leq] at hx
      simp[deleteTree] at hx
      grind[setTree]
    | node3 l a m b r =>
      expose_names
      simp[deleteTree]
      rw [leq] at hx
      simp[deleteTree] at hx
      grind[setTree]



omit [LinearOrder α] in
lemma node22_preserves_members
  (r_up : DeleteUp α)
  (a el: α)
  (l r : Tree23 α)
  (hl : l ≠ nil)
  (hx : ∀ x: α, x ∈ setTree (deleteTree r_up) → x ∈ setTree r):
    el ∈ setTree (deleteTree (node22 l a r_up hl)) → el ∈ setTree (node2 l a r) := by
  cases req : r_up
  · grind[deleteTree, node22, setTree]
  · simp[node22]
    cases l with
    | nil => grind[setTree]
    | node2 l a r =>
      expose_names
      simp[deleteTree]
      rw [req] at hx
      simp[deleteTree] at hx
      grind[setTree]
    | node3 l a m b r =>
      expose_names
      simp[deleteTree]
      rw [req] at hx
      simp[deleteTree] at hx
      grind[setTree]

omit [LinearOrder α] in
lemma node31_preserves_members
  (l_up : DeleteUp α)
  (a b el: α)
  (l m r : Tree23 α)
  (hm : m ≠ nil)
  (hr : r ≠ nil)
  (hx : ∀ x: α, x ∈ setTree (deleteTree l_up) → x ∈ setTree l):
    el ∈ setTree (deleteTree (node31 l_up a m b r hm hr)) → el ∈ setTree (node3 l a m b r) := by
  cases leq: l_up
  · simp[deleteTree, node31]
    rw [leq] at hx
    simp[deleteTree] at hx
    specialize hx el
    grind[setTree]
  · simp[node31]
    cases m with
    | nil => grind[setTree]
    | node2 l a r =>
      expose_names
      simp[deleteTree]
      rw [leq] at hx
      simp[deleteTree] at hx
      grind[setTree]
    | node3 l a m b r =>
      expose_names
      simp[deleteTree]
      rw [leq] at hx
      simp[deleteTree] at hx
      grind[setTree]

omit [LinearOrder α] in
lemma node32_preserves_members
  (m_up : DeleteUp α)
  (a b el: α)
  (l m r : Tree23 α)
  (hl : l ≠ nil)
  (hr : r ≠ nil)
  (hx : ∀ x: α, x ∈ setTree (deleteTree m_up) → x ∈ setTree m):
    el ∈ setTree (deleteTree (node32 l a m_up b r hl hr)) → el ∈ setTree (node3 l a m b r) := by
  cases meq: m_up
  · simp[deleteTree, node32]
    rw [meq] at hx
    simp[deleteTree] at hx
    specialize hx el
    grind[setTree]
  · simp[node32]
    cases r with
    | nil => grind[setTree]
    | node2 l a r =>
      expose_names
      simp[deleteTree]
      rw [meq] at hx
      simp[deleteTree] at hx
      specialize hx el
      unfold setTree -- necessary for grind to get through
      grind[setTree]
    | node3 l a m b r =>
      expose_names
      simp[deleteTree]
      rw [meq] at hx
      simp[deleteTree] at hx
      grind[setTree]

omit [LinearOrder α] in
lemma node33_preserves_members
  (r_up : DeleteUp α)
  (a b el: α)
  (l m r : Tree23 α)
  (hl : l ≠ nil)
  (hm : m ≠ nil)
  (hx : ∀ x: α, x ∈ setTree (deleteTree r_up) → x ∈ setTree r):
    el ∈ setTree (deleteTree (node33 l a m b r_up hl hm)) → el ∈ setTree (node3 l a m b r) := by
  cases req: r_up
  · simp[deleteTree, node33]
    rw [req] at hx
    simp[deleteTree] at hx
    specialize hx el
    grind[setTree]
  · simp[node33]
    cases m with
    | nil => grind[setTree]
    | node2 l a r =>
      expose_names
      simp[deleteTree]
      rw [req] at hx
      simp[deleteTree] at hx
      specialize hx el
      unfold setTree -- necessary for grind to get through
      grind[setTree]
    | node3 l a m b r =>
      expose_names
      simp[deleteTree]
      rw [req] at hx
      simp[deleteTree] at hx
      grind[setTree]

lemma splitMin_preserves_members
  (t: Tree23 α)
  (htc : complete t)
  (htn : t ≠ nil)
  (el : α):
    el ∈ {(splitMin t htc htn).1} ∪ setTree (deleteTree (splitMin t htc htn).2) → el ∈ setTree t := by
  induction t generalizing el with
  | nil => grind
  | node2 l a r l_ih r_ih =>
    simp[splitMin]
    split
    · grind[setTree]
    · rename_i hnn
      simp
      specialize l_ih (by grind[complete]) (by grind)
      intro h'
      cases h'
      · specialize l_ih el
        grind[setTree]
      · grind[node21_preserves_members]
  | node3 l a m b r l_ih m_ih r_ih =>
    simp[splitMin]
    split
    · rename_i hnil
      simp[deleteTree]
      intro h'
      cases h'
      · rename_i hn
        rw [hn]
        unfold setTree
        grind
      · rename_i ht
        grind[setTree]
    · rename_i hnn
      simp[deleteTree]
      intro h'
      cases h'
      · rename_i hleft
        specialize l_ih (by grind) (by grind) el
        grind[setTree]
      · rename_i hright
        grind[node31_preserves_members]

lemma del_preserves_members (x : α ) (t : Tree23 α) (ht : complete t) (y : α ):
    y ∈ setTree (deleteTree (del x t ht)) → y ∈ setTree t := by
  intro h
  induction t generalizing y with
  | nil => grind
  | node2 l a r l_ih r_ih =>
    specialize l_ih (by grind[complete])
    specialize r_ih (by grind[complete])
    unfold del at h
    split at h
    · split at h
      · simp[deleteTree, setTree] at h
      · simp[deleteTree, setTree] at h
        grind[setTree]
    · split at h
      · cases del_eq : (del x l (by grind : complete l))
        · grind[node21, deleteTree, setTree]
        · simp [del_eq, deleteTree, node21] at h
          cases r <;> grind[setTree, deleteTree]
      · split at h
        · have : y ∈ setTree (deleteTree (node22
                                            l
                                            (splitMin r (by grind) (by grind)).1
                                            (splitMin r (by grind) (by grind)).2
                                            (by grind))) := by
            grind
          have: y ∈ setTree (node2 l (splitMin r (by grind) (by grind)).1 r) := by
            grind[splitMin_preserves_members, node22_preserves_members]
          grind[splitMin_preserves_members, setTree]
        · cases del_eq : (del x r (by grind : complete r))
          · grind[node22, deleteTree, setTree]
          · simp [del_eq, deleteTree, node22] at h
            grind[setTree, deleteTree]
  | node3 l a m b r l_ih m_ih r_ih =>
    specialize l_ih (by grind[complete])
    specialize m_ih (by grind[complete])
    specialize r_ih (by grind[complete])
    unfold del at h
    split at h
    · split at h
      · grind[setTree, deleteTree]
      · split at h
        · grind[setTree, deleteTree]
        · grind[setTree, deleteTree]
    · split at h
      · grind[node31_preserves_members]
      · split at h
        · have : y ∈ setTree (deleteTree (node32
                                            l
                                            (splitMin m (by grind) (by grind)).1
                                            (splitMin m (by grind) (by grind)).2
                                            b r
                                            (by grind) (by grind))) := by
            grind
          have: y ∈ setTree (node3 l (splitMin m (by grind) (by grind)).1 m b r) := by
            grind[splitMin_preserves_members, node32_preserves_members]
          unfold setTree at this ⊢
          grind[splitMin_preserves_members, setTree]
        · split at h
          · grind[node32_preserves_members]
          · split at h
            · have : y ∈ setTree (deleteTree (node33
                                                l a m
                                                (splitMin r (by grind) (by grind)).1
                                                (splitMin r (by grind) (by grind)).2
                                                (by grind) (by grind))) := by
                grind
              have: y ∈ setTree (node3 l a m (splitMin r (by grind) (by grind)).1 r) := by
                grind[splitMin_preserves_members, node33_preserves_members]
              unfold setTree at this ⊢
              grind[splitMin_preserves_members, setTree]
            · grind[node33_preserves_members]


-- main part of search tree preserveration
lemma searchTree_node21_searchTree (l' : DeleteUp α) (r : Tree23 α) (a : α) (h1: searchTree (deleteTree l')) (h2: searchTree r) (h3: ∀ x ∈ setTree (deleteTree l'), x < a) (h4: ∀ x ∈ setTree r, a < x) (hrn : r ≠ nil):
  searchTree (deleteTree (node21 l' a r hrn)) := by
  induction l' with
  | eq l' =>
    grind[node21, deleteTree, searchTree]
  | underflow l' =>
    simp[deleteTree] at ⊢ h1 h3
    simp[node21]
    cases r with
    | nil => grind
    | node2 m b r =>
      simp
      unfold searchTree
      -- direct call to grind fails here
      constructor
      · grind[setTree]
      · grind[setTree, searchTree]
    | node3 l a' m b r =>
      simp
      unfold searchTree
      refine ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ?_ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
      · unfold setTree
        intro x hx
        have : a < a' := by grind[setTree]
        grind[searchTree]
      · unfold setTree
        intro x xh
        have : a < a' := by grind[setTree]
        grind[searchTree]
      · simp[searchTree]
        refine ⟨ ?_,  ⟨ ?_,  ⟨ ?_, ?_ ⟩ ⟩ ⟩
        · assumption
        · grind[setTree]
        · assumption
        · grind[searchTree]
      · grind[searchTree]
      · grind[searchTree]
      · grind[searchTree]
      · grind[searchTree]

lemma searchTree_node22_searchTree (r': DeleteUp α) (l : Tree23 α) (a : α) (h1: searchTree (deleteTree r')) (h2: searchTree l) (h3: ∀ x ∈ setTree (deleteTree r'), a < x) (h4: ∀ x ∈ setTree l, x < a) (hln : l ≠ nil):
  searchTree (deleteTree (node22 l a r' hln)) := by
  induction r' with
  | eq r' =>
    grind[node22, deleteTree, searchTree]
  | underflow r' =>
    simp[deleteTree] at ⊢ h1 h3
    simp[node22]
    cases l with
    | nil => grind
    | node2 l a r =>
      simp
      unfold searchTree
      -- direct call to grind fails here
      constructor
      · grind[setTree]
      · grind[setTree, searchTree]
    | node3 l a' m b r =>
      simp
      unfold searchTree
      refine ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ?_ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
      · unfold setTree
        intro x hx
        have : a > b := by grind[setTree]
        grind[searchTree]
      · unfold setTree
        intro x xh
        have : a > b := by grind[setTree]
        grind[searchTree]
      · grind[searchTree]
      · intro x xh
        grind[searchTree, setTree]
      · grind[searchTree]
      · grind[searchTree]
      · grind[searchTree]

lemma searchTree_node31_searchTree (l' : DeleteUp α) (m : Tree23 α) (r : Tree23 α) (a : α) (b : α) (hsl': searchTree (deleteTree l')) (hsm: searchTree m) (hsr: searchTree r) (hab : a < b) (hl's: ∀ x ∈ setTree (deleteTree l'), x < a) (hms: ∀ x ∈ setTree m, a < x) (hmb: ∀ x ∈ setTree m, x < b) (hrs: ∀ x ∈ setTree r, b < x) (hmn : m ≠ nil) (hrn : r ≠ nil) :
    searchTree (deleteTree (node31 l' a m b r hmn hrn)) := by
  induction l' with
  | eq l' => grind[node31, deleteTree, searchTree]
  | underflow l' =>
    simp[deleteTree] at *
    simp[node31]
    cases m with
    | nil => grind
    | node2 ml ma mr =>
      simp
      unfold searchTree
      -- direct call to grind fails here
      constructor
      · grind[setTree]
      · constructor
        · grind[setTree, searchTree]
        · constructor
          · unfold searchTree -- direct call to grind fails here, again
            constructor
            · grind[setTree, searchTree]
            · grind[setTree, searchTree]
          · assumption
    | node3 ml ma m mb mr =>
      simp
      unfold searchTree
      refine ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ?_ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
      · have : ma ∈ (ml.node3 ma m mb mr).setTree := by grind[setTree, searchTree]
        grind
      · unfold setTree
        intro x xh
        have : a < ma := by grind[setTree]
        grind[searchTree]
      · unfold setTree
        intro x xh
        have : a < ma := by grind[setTree]
        grind[searchTree]
      · unfold setTree
        intro x xh
        have : x ∈ (ml.node3 ma m mb mr).setTree := by grind[setTree, searchTree]
        grind[searchTree]
      · assumption
      · simp[searchTree]
        refine ⟨ ?_,  ⟨ ?_,  ⟨ ?_, ?_ ⟩ ⟩ ⟩
        · assumption
        · grind[setTree]
        · assumption
        · grind[setTree, searchTree]
      · grind[searchTree]

lemma searchTree_node32_searchTree (m' : DeleteUp α) (l : Tree23 α) (r : Tree23 α) (a : α) (b : α) (hsm': searchTree (deleteTree m')) (hsl: searchTree l) (hsr: searchTree r) (hab : a < b) (hm's :  ∀ x ∈ setTree (deleteTree m'), a < x) (hm'b : ∀ x ∈ setTree (deleteTree m'), x < b) (hrs: ∀ x ∈ setTree r, b < x) (hls: ∀ x ∈ setTree l, x < a) (hln : l ≠ nil) (hrn : r ≠ nil) :
    searchTree (deleteTree (node32 l a m' b r hln hrn)) := by
  induction m' with
  | eq m' => grind[node32, deleteTree, searchTree]
  | underflow m' =>
    simp[deleteTree] at *
    simp[node32]
    cases r with
    | nil => grind
    | node2 l a r => grind[setTree, searchTree] --wow direct call to grind works here!
    | node3 rl ra rm rb r =>
      simp
      unfold searchTree
      refine ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ?_ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
      · have : ra ∈ (rl.node3 ra rm rb r).setTree := by
          unfold setTree
          simp
        grind
      · assumption
      · intro x hx
        specialize hrs x
        grind[searchTree, setTree]
      · intro x hx
        have : ra ∈ (rl.node3 ra rm rb r).setTree := by
          unfold setTree
          simp
        grind[searchTree, setTree]
      · intro x hx
        have : ra ∈ (rl.node3 ra rm rb r).setTree := by
          unfold setTree
          simp
        grind[searchTree, setTree]
      · assumption
      · constructor
        · simp[searchTree]
          refine ⟨ ?_,  ⟨ ?_,  ⟨ ?_, ?_ ⟩ ⟩ ⟩
          · assumption
          · grind[setTree]
          · assumption
          · grind[searchTree, setTree]
        · grind[searchTree, setTree]


lemma searchTree_node33_searchTree (r' : DeleteUp α) (l : Tree23 α) (m : Tree23 α) (a : α) (b : α) (hsr': searchTree (deleteTree r')) (hsl: searchTree l) (hsm: searchTree m) (hab : a < b) (hr's: ∀ x ∈ setTree (deleteTree r'), b < x) (hms: ∀ x ∈ setTree m, a < x) (hmb: ∀ x ∈ setTree m, x < b) (hls: ∀ x ∈ setTree l, x < a) (hln : l ≠ nil) (hmn : m ≠ nil) :
    searchTree (deleteTree (node33 l a m b r' hln hmn)) := by
  induction r' with
  | eq r' => grind[node33, deleteTree, searchTree]
  | underflow r' =>
    simp[deleteTree] at *
    simp[node33]
    cases m with
    | nil => grind
    | node2 ml ma mr =>
      simp
      unfold searchTree
      -- direct call to grind fails here
      constructor
      · grind[setTree]
      · constructor
        · grind[setTree, searchTree]
        · constructor
          · grind[setTree, searchTree]
          · unfold searchTree -- direct call to grind fails here, again
            constructor
            · grind[setTree, searchTree]
            · grind[setTree, searchTree]
    | node3 ml ma m mb mr =>
      simp
      unfold searchTree
      refine ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ⟨ ?_,  ?_ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
      · have : ma ∈ (ml.node3 ma m mb mr).setTree := by grind[setTree, searchTree]
        grind[searchTree]
      · assumption
      · intro x hx
        have : x ∈ (ml.node3 ma m mb mr).setTree := by grind[setTree]
        grind[searchTree]
      · unfold setTree
        intro x xh
        have : x ∈ (ml.node3 ma m mb mr).setTree := by grind[setTree]
        grind[searchTree]
      · intro x hx
        have h1: mb < b := by grind[setTree]
        grind[setTree, searchTree]
      · assumption
      · constructor
        · grind[searchTree]
        · grind[searchTree, setTree]

lemma deleteTree_splitMin_preserves_searchTree_2 (t : Tree23 α) (hc : complete t) (hn : t ≠ nil) (hs : searchTree t) :
    (deleteTree (t.splitMin hc hn).2).searchTree := by
  induction t with
  | nil => grind
  | node2 l a r l_ih r_ih =>
    unfold splitMin
    split
    · grind[searchTree, deleteTree]
    · expose_names
      specialize l_ih (by grind[complete]) h (by grind[searchTree])
      apply searchTree_node21_searchTree
      · assumption
      · grind[searchTree]
      · grind[searchTree, setTree, splitMin_preserves_members]
      · grind[ searchTree]
  | node3 l a m b r l_ih m_ih r_ih =>
    unfold splitMin
    split
    · grind[searchTree, setTree, deleteTree]
    · expose_names
      specialize l_ih (by grind[complete]) h (by grind[searchTree])
      apply searchTree_node31_searchTree <;> grind[searchTree, setTree, splitMin_preserves_members]

lemma deleteTree_splitMin_preserves_searchTree_1  (t : Tree23 α) (hc : complete t) (hn : t ≠ nil) (hs : searchTree t) :
     ∀ x ∈ (deleteTree (t.splitMin hc hn).2).setTree, (t.splitMin hc hn).1 < x := by
  induction t with
  | nil => grind
  | node2 l a r l_ih r_ih =>
    unfold splitMin
    split
    · grind[searchTree, deleteTree, setTree]
    · expose_names
      simp
      intro x hx
      apply node21_preserves_members (l := (deleteTree ((l.splitMin (by grind) h).2)) ) at hx
      · unfold setTree at hx
        simp at hx
        obtain h1 | h2 := hx
        · obtain h2 | h3 := h1
          · grind[splitMin_preserves_members, searchTree]
          · grind[splitMin_preserves_members, setTree, searchTree]
        · have : (l.splitMin (by grind) h).1 ∈ l.setTree := by
            grind[splitMin_preserves_members, setTree, searchTree]
          grind[searchTree, setTree]
      · grind[searchTree, splitMin_preserves_members]
  | node3 l a m b r l_ih m_ih r_ih =>
    unfold splitMin
    split
    · grind[searchTree, deleteTree, setTree]
    · expose_names
      simp
      intro x hx
      apply node31_preserves_members (l := (deleteTree ((l.splitMin (by grind) h).2)) ) at hx
      · unfold setTree at hx
        simp at hx
        obtain h1 | h2 := hx
        · obtain h2 | h3 := h1
          · have : a < b := by grind[searchTree]
            have : (l.splitMin (by grind) h).1 ∈ l.setTree := by
              grind[splitMin_preserves_members, setTree, searchTree]
            grind[splitMin_preserves_members, searchTree]
          · obtain h3 | h4 := h3
            · obtain h3 | h5 := h3
              · grind[splitMin_preserves_members, searchTree]
              · grind[splitMin_preserves_members, searchTree]
            · have : (l.splitMin (by grind) h).1 ∈ l.setTree := by
                grind[splitMin_preserves_members, setTree, searchTree]
              grind[searchTree, setTree]
        · have : (l.splitMin (by grind) h).1 ∈ l.setTree := by
            grind[splitMin_preserves_members, setTree, searchTree]
          grind[searchTree, setTree]
      · grind[searchTree, splitMin_preserves_members]

-- final proof
lemma searchTree_del_searchTree (t: Tree23 α) (x: α) (h: complete t):
    searchTree t → searchTree (deleteTree (del x t h)) := by
  intro hsT
  induction t with
  | nil => grind[searchTree, deleteTree, del]
  | node2 l a r l_ih r_ih =>
      obtain ⟨ hl, hr, hl', hr' ⟩ := hsT
      specialize l_ih (by grind[complete]) hl'
      specialize r_ih (by grind[complete]) hr'
      unfold del
      split
      · grind[setTree, deleteTree, searchTree]
      · split
        · expose_names;
          apply searchTree_node21_searchTree
          · assumption
          · assumption
          · intro x_1 hx
            have (y : α ) : y ∈ setTree (deleteTree (del x l (by grind))) → y ∈ setTree l := by
              grind[del_preserves_members]
            grind
          · assumption
        · split
          · expose_names
            apply searchTree_node22_searchTree
            · grind[deleteTree_splitMin_preserves_searchTree_2]
            · assumption
            · grind[deleteTree_splitMin_preserves_searchTree_1]
            · intro x' hx
              have h1 : (r.splitMin (by grind[complete]) (by grind[complete])).1 ∈ r.setTree := by grind[setTree, splitMin_preserves_members]
              grind
          · expose_names;
            apply searchTree_node22_searchTree
            · assumption
            · assumption
            · intro x_1 hx
              have (y : α ) : y ∈ setTree (deleteTree (del x r (by grind))) → y ∈ setTree r := by
                grind[del_preserves_members]
              grind
            · assumption
  | node3 l a m b r l_ih m_ih r_ih =>
      obtain ⟨ hab, hl, hma, hmb, hr, hl', hm', hr' ⟩ := hsT
      specialize l_ih (by grind[complete]) hl'
      specialize m_ih (by grind[complete]) hm'
      specialize r_ih (by grind[complete]) hr'
      unfold del
      split
      · split
        · grind[setTree, deleteTree, searchTree]
        · split
          · grind[setTree, deleteTree, searchTree]
          · grind[setTree, deleteTree, searchTree]
      · split
        · grind[searchTree_node31_searchTree, del_preserves_members]
        · split
          · apply searchTree_node32_searchTree
            · grind[deleteTree_splitMin_preserves_searchTree_2]
            · assumption
            · assumption
            · have : (m.splitMin (by grind) (by grind[complete])).1 ∈ m.setTree := by
                grind[splitMin_preserves_members, setTree, searchTree]
              grind[searchTree, setTree]
            · grind[deleteTree_splitMin_preserves_searchTree_1]
            · grind[splitMin_preserves_members, setTree, searchTree]
            · assumption
            · have : (m.splitMin (by grind) (by grind[complete])).1 ∈ m.setTree := by
                grind[splitMin_preserves_members, setTree, searchTree]
              grind[searchTree, setTree]
          · split
            · grind[searchTree_node32_searchTree, del_preserves_members]
            · split
              · apply searchTree_node33_searchTree
                · grind[deleteTree_splitMin_preserves_searchTree_2]
                · assumption
                · assumption
                · have : (r.splitMin (by grind) (by grind[complete])).1 ∈ r.setTree := by
                    grind[splitMin_preserves_members, setTree, searchTree]
                  grind[searchTree, setTree]
                · grind[deleteTree_splitMin_preserves_searchTree_1]
                · assumption
                · have : (r.splitMin (by grind) (by grind[complete])).1 ∈ r.setTree := by
                    grind[splitMin_preserves_members, setTree, searchTree]
                  grind[searchTree, setTree]
                · assumption
              · grind[searchTree_node33_searchTree, del_preserves_members]
