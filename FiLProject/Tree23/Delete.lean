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

@[grind]
def deleteTree : DeleteUp α → Tree23 α
| DeleteUp.eq t => t
| DeleteUp.underflow t => t

@[grind]
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

@[grind]
def node22 : (t: Tree23 α) → α → DeleteUp α → t ≠ nil → DeleteUp α
| t₁, a, DeleteUp.eq t₂, _ => DeleteUp.eq (Tree23.node2 t₁ a t₂)
| l, a, DeleteUp.underflow t_r, h =>
    match l with
    | nil => (by grind)
    | node2 t₁ b t₂ =>
      DeleteUp.underflow (Tree23.node3 t₁ b t₂ a t_r)
    | node3 t₁ b t₂ c t₃ =>
      DeleteUp.eq (Tree23.node2 (Tree23.node2 t₁ b t₂) c (Tree23.node2 t₃ a t_r))

@[grind]
def node31 : DeleteUp α → α → (t₁ : Tree23 α) → α → (t₂ : Tree23 α) → t₁ ≠ nil → t₂ ≠ nil → DeleteUp α
| DeleteUp.eq t₁, a, t₂, b, t₃, _, _ => DeleteUp.eq (Tree23.node3 t₁ a t₂ b t₃)
| DeleteUp.underflow t₁, a, t_m, c, r, _, _ =>
    match t_m with
    | nil => (by grind)
    | node2 t₂ b t₃ => DeleteUp.eq (Tree23.node2 (Tree23.node3 t₁ a t₂ b t₃) c r)
    | node3 t₂ b t₃ c_inner t₄ => DeleteUp.eq (node3 (node2 t₁ a t₂) b (node2 t₃ c_inner t₄) c r)

@[grind]
def node32 : (t₁ : Tree23 α) → α → DeleteUp α → α → (t₂ : Tree23 α) →  t₁ ≠ nil → t₂ ≠ nil → DeleteUp α
| t₁, a, DeleteUp.eq t₂, b, t₃, _, _ =>  DeleteUp.eq (node3 t₁ a t₂ b t₃)
| t₁, a, DeleteUp.underflow t₂, b, t_r, _, _ =>
    match t_r with
    | nil => (by grind)
    | node2 t₃ c t₄ => DeleteUp.eq (node2 t₁ a (node3 t₂ b t₃ c t₄))
    | node3 t₃ c t₄ d t₅ => DeleteUp.eq (node3 t₁ a (node2 t₂ b t₃) c (node2 t₄ d t₅))

@[grind]
def node33 : (t₁ : Tree23 α) → α → (t₂ : Tree23 α) → α → DeleteUp α →  t₁ ≠ nil → t₂ ≠ nil → DeleteUp α
| t₁, a, t₂, b, DeleteUp.eq t₃, _, _ => DeleteUp.eq (node3 t₁ a t₂ b t₃)
| t₁, a, t_m, c, DeleteUp.underflow t_u, _, _ =>
    match t_m with
    | nil => (by grind)
    | node2 t₂ b t₃ => DeleteUp.eq (node2 t₁ a (node3 t₂ b t₃ c t_u))
    | node3 t₂ b t₃ c_inner t₄ => DeleteUp.eq (node3 t₁ a (node2 t₂ b t₃) c_inner (node2 t₄ c t_u))

@[grind]
def splitMin : (t : Tree23 α) → complete t → t ≠ nil → α × DeleteUp α
| nil, _, h => by grind
| node2 l a r, hc, _ =>
  if h: l = nil then
    (a, DeleteUp.underflow nil)
  else
    -- extract the smallest element merge reduced left side with right side
    -- ah, that is why this is called splitMin ...
    let (x, l') := splitMin l (by grind  ) (by assumption)
    have hr : r ≠ nil := by grind
    (x, node21 l' a r (by assumption))
| node3 l a m b r, _, _ =>
  if h: l = nil then
    (a, DeleteUp.eq (node2 nil b nil))
  else
    let (x, l') := splitMin l (by grind  ) (by assumption)
    have hr : r ≠ nil := by grind
    have hm : m ≠ nil := by grind
    (x, node31 l' a m b r (by assumption) (by assumption))

@[grind]
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
    have h2 : r ≠ nil := by grind

    if (x < a) then
      -- recursion on left subtree and handle underflow logic via node21
      node21 (del x l (by grind  )) a r (by assumption)
    else if (x = a) then
      let (a0, r0) := splitMin r (by grind  ) (by assumption)
      node22 l a0 r0 (by assumption)
    else
      -- recursion on right subtree and handle underflow logic via node22
      node22 l a (del x r (by grind  )) (by assumption)
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
    have hr : r ≠ nil := by grind
    have hm : m ≠ nil := by grind

    if (x < a) then
      node31 (del x l (by grind  )) a m b r (by assumption) (by assumption)
    else if (x = a) then
      let (a', m') := splitMin m (by grind  ) (by assumption)
      node32 l a' m' b r (by assumption) (by assumption)
    else
      if (x < b) then
        node32 l a (del x m (by grind  )) b r (by assumption) (by assumption)
      else if (x = b) then
        let (b', r') := splitMin r (by grind  ) (by assumption)
        node33 l a m b' r' (by assumption) (by assumption)
      else
        node33 l a m b (del x r (by grind  )) (by assumption) (by assumption)

def delete (x : α) (t : Tree23 α) (hc : complete t) : Tree23 α :=
  deleteTree (del x t hc)

@[grind]
def deleteHeight : DeleteUp α → ℕ
| DeleteUp.eq t => height t
| DeleteUp.underflow t => height t + 1


omit [LinearOrder α] in
lemma completeness_preservation_deleteTree_node21 (a : α) (r : Tree23 α) (l' : DeleteUp α)
  (hr : complete r) (hl' : complete (deleteTree l'))
  (hheight : height r = deleteHeight l' ) (hrn : r ≠ nil) :
    complete (deleteTree (node21 l' a r hrn)) := by
  induction l' with
  | eq l => grind
  | underflow l =>
    unfold node21
    grind

omit [LinearOrder α] in
lemma completeness_preservation_deleteTree_node22 (a : α) (l : Tree23 α) (r' : DeleteUp α)
  (hl : complete l) (hr' : complete (deleteTree r'))
  (hheight : height l = deleteHeight r' ) (hln : l ≠ nil) :
    complete (deleteTree (node22 l a r' hln)) := by
  induction r' with
  | eq r => grind
  | underflow r =>
    unfold node22
    grind

omit [LinearOrder α] in
lemma completeness_preservation_deleteTree_node31 (a b : α) (m r : Tree23 α) (l' : DeleteUp α)
  (hm : complete m) (hr : complete r) (hl' : complete (deleteTree l'))
  (hhrl' : height r = deleteHeight l') (hhmr : height m = height r) (hrn : r ≠ nil) (hmn : m ≠ nil):
    complete (deleteTree (node31 l' a m b r hmn hrn)) := by
  induction l' with
  | eq l => grind
  | underflow l =>
    unfold node31
    grind

omit [LinearOrder α] in
lemma completeness_preservation_deleteTree_node32 (a b : α) (l r : Tree23 α) (m' : DeleteUp α)
  (hl : complete l) (hr : complete r) (hm' : complete (deleteTree m'))
  (hhrm' : height r = deleteHeight m') (hhlr : height l = height r) (hln : l ≠ nil) (hrn : r ≠ nil):
    complete (deleteTree (node32 l a m' b r hln hrn)) := by
  induction m' with
  | eq m => grind
  | underflow m =>
    unfold node32
    grind

omit [LinearOrder α] in
lemma completeness_preservation_deleteTree_node33 (a b : α) (l m : Tree23 α) (r' : DeleteUp α)
  (hl : complete l) (hm : complete m) (hr' : complete (deleteTree r'))
  (hhlr' : height l = deleteHeight r') (hhlm : height l = height m) (hln : l ≠ nil) (hmn : m  ≠ nil):
    complete (deleteTree (node33 l a m b r' hln hmn)) := by
  induction r' with
  | eq r => grind
  | underflow r =>
    unfold node33
    grind

omit [LinearOrder α] in
lemma max_height_node21 (a : α) (r : Tree23 α)  (l' : DeleteUp α) (h : 0 < height r):
    deleteHeight (node21 l' a r (by grind)) = max (deleteHeight l') (height r) + 1 := by
  unfold deleteHeight
  cases l' with
  | eq l => grind
  | underflow t =>
    simp[node21]
    grind

omit [LinearOrder α] in
lemma max_height_node22 (a : α) (l : Tree23 α)  (r' : DeleteUp α) (h : 0 < height l):
    deleteHeight (node22 l a r' (by grind)) = max (deleteHeight r') (height l) + 1 := by
  unfold deleteHeight
  cases r' with
  | eq l => grind
  | underflow t =>
    simp[node22]
    grind

omit [LinearOrder α] in
lemma max_height_node31 (a b : α) (m r : Tree23 α) (l' : DeleteUp α) (hr : 0 < height r) (hm : 0 < height m) :
    deleteHeight (node31 l' a m b r (by grind) (by grind)) = max (deleteHeight l') (max (height m) (height r)) + 1 := by
  unfold deleteHeight
  cases l' with
  | eq t => grind
  | underflow t =>
    simp[node31]
    grind

omit [LinearOrder α] in
lemma max_height_node32 (a b : α) (l r : Tree23 α) (m' : DeleteUp α) (hl : 0 < height l) (hr : 0 < height r) :
    deleteHeight (node32 l a m' b r (by grind) (by grind)) = max (deleteHeight m') (max (height l) (height r)) + 1 := by
  unfold deleteHeight
  cases m' with
  | eq t => grind
  | underflow t =>
    simp[node32]
    grind

omit [LinearOrder α] in
lemma max_height_node33 (a b : α) (l m : Tree23 α) (r' : DeleteUp α) (hl : 0 < height l) (hm : 0 < height m) :
    deleteHeight (node33 l a m b r' (by grind) (by grind)) = max (deleteHeight r') (max (height l) (height m)) + 1 := by
  unfold deleteHeight
  cases r' with
  | eq t => grind
  | underflow t =>
    simp[node33]
    cases m <;> grind

lemma splitMin_height_complete (t : Tree23 α )
  (hct: complete t) (hht : 0 < height t) :
    deleteHeight (splitMin t hct (by grind)).2 = height t := by
  induction t with
  | nil => grind
  | node2 l a r l_ih r_ih =>
    by_cases h : l = nil
    · grind
    · grind[max_height_node21]
  | node3 l a m b r l_ih m_ih r_ih =>
    by_cases h : l = nil
    · grind
    · grind[ max_height_node31]

lemma splitMin_complete (t : Tree23 α)
  (hct : complete t) (hht : 0 < height t) :
    complete (deleteTree (splitMin t hct (by grind)).2) := by
  induction t with
  | nil => grind
  | node2 l a r l_ih r_ih =>
      by_cases h : l = nil
      · grind
      · grind[completeness_preservation_deleteTree_node21, splitMin_height_complete]
  | node3 l a m a r l_ih m_ih r_ih =>
      by_cases h : l = nil
      · grind
      · grind[completeness_preservation_deleteTree_node31,splitMin_height_complete]

lemma complete_deleteHeight (t : Tree23 α) (x : α) (h : complete t):
    deleteHeight (del x t (by assumption)) = height t := by
  induction t with
  | nil => grind[del]
  | node2 l a r l_ih r_ih =>
    unfold del
    split
    · grind
    · split
      · grind[max_height_node21]
      · split
        · rw[max_height_node22]
          have hr: r ≠ nil := by grind[height]
          have : deleteHeight (splitMin r (by grind  ) hr).2 = height r := by
              rw[splitMin_height_complete]
              grind
          repeat grind
        · grind[max_height_node22]
  | node3 l a m b r l_ih m_ih r_ih =>
    unfold del
    split
    · grind
    · split
      · grind[max_height_node31]
      · split
        · rw[max_height_node32]
          have hm : m ≠ nil := by grind
          have : deleteHeight (splitMin m (by grind) hm).2 = height m := by
            rw[splitMin_height_complete]
            grind
          repeat grind
        · split
          · grind[max_height_node32]
          · split
            · rw[max_height_node33]
              have hr: r ≠ nil := by grind
              have : deleteHeight (splitMin r (by grind  ) hr).2 = height r := by
                rw[splitMin_height_complete]
                grind
              repeat grind
            · grind[max_height_node33]


lemma complete_complete_del (t : Tree23 α) (x : α) (h : complete t):
    complete (deleteTree (del x t h)) := by
  induction t with
  | nil => grind
  | node2 l a r l_ih r_ih =>
      grind[completeness_preservation_deleteTree_node21, completeness_preservation_deleteTree_node22, complete_deleteHeight, splitMin_height_complete, splitMin_complete]
  | node3 l a m b r l_ih m_ih r_ih =>
      grind[completeness_preservation_deleteTree_node31, completeness_preservation_deleteTree_node32, completeness_preservation_deleteTree_node33, complete_deleteHeight, splitMin_height_complete, splitMin_complete]

lemma delete_completeness_preservation (t : Tree23 α) (x : α) (h : complete t):
    complete (delete x t h) := by
    grind[complete_complete_del, delete]




-- searchTree property

-- first prove a helper
omit [LinearOrder α] in
@[grind]
lemma node21_preserves_members
  (l_up : DeleteUp α)
  (a el: α)
  (l r : Tree23 α)
  (hr : r ≠ nil)
  (hx : ∀ x: α, x ∈ setTree (deleteTree l_up) → x ∈ setTree l):
    el ∈ setTree (deleteTree (node21 l_up a r hr)) → el ∈ setTree (node2 l a r) := by
  cases leq : l_up
  · grind
  · simp[node21]
    cases r with
    | nil => grind
    | node2 l a r =>
      simp[deleteTree] -- grind needs simp here
      grind
    | node3 l a m b r => grind



omit [LinearOrder α] in
@[grind]
lemma node22_preserves_members
  (r_up : DeleteUp α)
  (a el: α)
  (l r : Tree23 α)
  (hl : l ≠ nil)
  (hx : ∀ x: α, x ∈ setTree (deleteTree r_up) → x ∈ setTree r):
    el ∈ setTree (deleteTree (node22 l a r_up hl)) → el ∈ setTree (node2 l a r) := by
  cases req : r_up
  · grind
  · simp[node22]
    cases l <;> grind

omit [LinearOrder α] in
@[grind]
lemma node31_preserves_members
  (l_up : DeleteUp α)
  (a b el: α)
  (l m r : Tree23 α)
  (hm : m ≠ nil)
  (hr : r ≠ nil)
  (hx : ∀ x: α, x ∈ setTree (deleteTree l_up) → x ∈ setTree l):
    el ∈ setTree (deleteTree (node31 l_up a m b r hm hr)) → el ∈ setTree (node3 l a m b r) := by
  cases leq: l_up
  · simp[deleteTree, node31] --grind needs simp here
    specialize hx el
    grind
  · simp[node31]
    cases m <;> simp [deleteTree] <;> grind

omit [LinearOrder α] in
@[grind]
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
    grind
  · cases r <;> simp [setTree, node32] <;> grind


omit [LinearOrder α] in
@[grind]
lemma node33_preserves_members
  (r_up : DeleteUp α)
  (a b el: α)
  (l m r : Tree23 α)
  (hl : l ≠ nil)
  (hm : m ≠ nil)
  (hx : ∀ x: α, x ∈ setTree (deleteTree r_up) → x ∈ setTree r):
    el ∈ setTree (deleteTree (node33 l a m b r_up hl hm)) → el ∈ setTree (node3 l a m b r) := by
  cases req: r_up
  · simp[deleteTree, node33] -- grind needs simp here
    grind
  · simp[node33]
    cases m <;> grind

@[grind]
lemma splitMin_preserves_members
  (t: Tree23 α)
  (htc : complete t)
  (htn : t ≠ nil)
  (el : α):
    el ∈ {(splitMin t htc htn).1} ∪ setTree (deleteTree (splitMin t htc htn).2) → el ∈ setTree t := by
  induction t generalizing el <;> grind --grind actually needs generalizing


@[grind]
lemma del_preserves_members (x : α ) (t : Tree23 α) (ht : complete t) (y : α ):
    y ∈ setTree (deleteTree (del x t ht)) → y ∈ setTree t := by
  intro h
  induction t generalizing y with
  | nil => grind
  | node2 l a r l_ih r_ih =>
    unfold del at h
    split at h
    · grind
    · split at h
      · cases del_eq : (del x l (by grind : complete l))
        · grind
        · simp [del_eq, node21] at h
          cases r <;> grind
      · split at h
        · have : y ∈ setTree (deleteTree (node22
                                            l
                                            (splitMin r (by grind) (by grind)).1
                                            (splitMin r (by grind) (by grind)).2
                                            (by grind))) := by
            grind
          have: y ∈ setTree (node2 l (splitMin r (by grind) (by grind)).1 r) := by
            grind
          grind
        · grind
  | node3 l a m b r l_ih m_ih r_ih =>
    unfold del at h
    split at h
    · split at h <;> grind
    · split at h
      · grind
      · split at h
        · have : y ∈ setTree (deleteTree (node32
                                            l
                                            (splitMin m (by grind) (by grind)).1
                                            (splitMin m (by grind) (by grind)).2
                                            b r
                                            (by grind) (by grind))) := by
            grind
          have: y ∈ setTree (node3 l (splitMin m (by grind) (by grind)).1 m b r) := by
            grind
          grind
        · split at h
          · grind
          · split at h
            · have : y ∈ setTree (deleteTree (node33
                                                l a m
                                                (splitMin r (by grind) (by grind)).1
                                                (splitMin r (by grind) (by grind)).2
                                                (by grind) (by grind))) := by
                grind
              have: y ∈ setTree (node3 l a m (splitMin r (by grind) (by grind)).1 r) := by
                grind
              grind
            · grind

-- main part of search tree preserveration
@[grind! .]
lemma searchTree_node21_searchTree (l' : DeleteUp α) (r : Tree23 α) (a : α) (h1: searchTree (deleteTree l')) (h2: searchTree r) (h3: ∀ x ∈ setTree (deleteTree l'), x < a) (h4: ∀ x ∈ setTree r, a < x) (hrn : r ≠ nil):
  searchTree (deleteTree (node21 l' a r hrn)) := by
  induction l' with
  | eq l' => grind
  | underflow l' =>
    simp[node21]
    cases r with
    | nil => grind
    | node2 m b r => grind
    | node3 l a' m b r =>
      have : a < a' := by grind
      grind

@[grind! .]
lemma searchTree_node22_searchTree (r': DeleteUp α) (l : Tree23 α) (a : α) (h1: searchTree (deleteTree r')) (h2: searchTree l) (h3: ∀ x ∈ setTree (deleteTree r'), a < x) (h4: ∀ x ∈ setTree l, x < a) (hln : l ≠ nil):
  searchTree (deleteTree (node22 l a r' hln)) := by
  induction r' with
  | eq r' => grind
  | underflow r' =>
    simp[node22]
    cases l with
    | nil => grind
    | node2 l a r => grind
    | node3 l a' m b r =>
      have : a > b := by grind
      grind

@[grind! .]
lemma searchTree_node31_searchTree (l' : DeleteUp α) (m : Tree23 α) (r : Tree23 α) (a : α) (b : α) (hsl': searchTree (deleteTree l')) (hsm: searchTree m) (hsr: searchTree r) (hab : a < b) (hl's: ∀ x ∈ setTree (deleteTree l'), x < a) (hms: ∀ x ∈ setTree m, a < x) (hmb: ∀ x ∈ setTree m, x < b) (hrs: ∀ x ∈ setTree r, b < x) (hmn : m ≠ nil) (hrn : r ≠ nil) :
    searchTree (deleteTree (node31 l' a m b r hmn hrn)) := by
  induction l' with
  | eq l' => grind
  | underflow l' =>
    cases m <;> grind

@[grind! .]
lemma searchTree_node32_searchTree (m' : DeleteUp α) (l : Tree23 α) (r : Tree23 α) (a : α) (b : α) (hsm': searchTree (deleteTree m')) (hsl: searchTree l) (hsr: searchTree r) (hab : a < b) (hm's :  ∀ x ∈ setTree (deleteTree m'), a < x) (hm'b : ∀ x ∈ setTree (deleteTree m'), x < b) (hrs: ∀ x ∈ setTree r, b < x) (hls: ∀ x ∈ setTree l, x < a) (hln : l ≠ nil) (hrn : r ≠ nil) :
    searchTree (deleteTree (node32 l a m' b r hln hrn)) := by
  induction m' with
  | eq m' => grind
  | underflow m' =>
    simp[node32]
    cases r with
    | nil => grind
    | node2 l a r => grind
    | node3 rl ra rm rb r =>
      have : ra ∈ (rl.node3 ra rm rb r).setTree := by
          grind
      grind

@[grind! .]
lemma searchTree_node33_searchTree (r' : DeleteUp α) (l : Tree23 α) (m : Tree23 α) (a : α) (b : α) (hsr': searchTree (deleteTree r')) (hsl: searchTree l) (hsm: searchTree m) (hab : a < b) (hr's: ∀ x ∈ setTree (deleteTree r'), b < x) (hms: ∀ x ∈ setTree m, a < x) (hmb: ∀ x ∈ setTree m, x < b) (hls: ∀ x ∈ setTree l, x < a) (hln : l ≠ nil) (hmn : m ≠ nil) :
    searchTree (deleteTree (node33 l a m b r' hln hmn)) := by
  induction r' with
  | eq r' => grind
  | underflow r' =>
    cases m <;> grind


@[grind! .]
lemma deleteTree_splitMin_preserves_searchTree_2 (t : Tree23 α) (hc : complete t) (hn : t ≠ nil) (hs : searchTree t) :
    (deleteTree (t.splitMin hc hn).2).searchTree := by
  induction t with
  | nil => grind
  | node2 l a r l_ih r_ih =>
    unfold splitMin
    split
    · grind
    · expose_names
      specialize l_ih (by grind) h (by grind)
      apply searchTree_node21_searchTree <;> grind
  | node3 l a m b r l_ih m_ih r_ih =>
    unfold splitMin
    split
    · grind
    · expose_names
      specialize l_ih (by grind) h (by grind)
      apply searchTree_node31_searchTree <;> grind

@[grind! .]
lemma deleteTree_splitMin_preserves_searchTree_1  (t : Tree23 α) (hc : complete t) (hn : t ≠ nil) (hs : searchTree t) :
     ∀ x ∈ (deleteTree (t.splitMin hc hn).2).setTree, (t.splitMin hc hn).1 < x := by
  induction t with
  | nil => grind
  | node2 l a r l_ih r_ih =>
    simp[splitMin]
    split
    · grind
    · expose_names
      simp
      intro x hx
      apply node21_preserves_members (l := (deleteTree ((l.splitMin (by grind) h).2)) ) at hx
      · simp at hx
        obtain h1 | h2 := hx
        · obtain h2 | h3 := h1 <;> grind
        · have : (l.splitMin (by grind) h).1 ∈ l.setTree := by
            grind
          grind
      · grind
  | node3 l a m b r l_ih m_ih r_ih =>
    simp[splitMin]
    split
    · grind
    · expose_names
      simp
      intro x hx
      apply node31_preserves_members (l := (deleteTree ((l.splitMin (by grind) h).2)) ) at hx
      · unfold setTree at hx
        simp at hx
        have : (l.splitMin (by grind) h).1 ∈ l.setTree := by
              grind
        grind
      · grind

-- final proof
lemma searchTree_del_searchTree (t: Tree23 α) (x: α) (h: complete t):
    searchTree t → searchTree (deleteTree (del x t h)) := by
  intro hsT
  induction t with
  | nil => grind
  | node2 l a r l_ih r_ih =>
      simp[del]
      split
      · grind
      · have (y : α ) : y ∈ setTree (deleteTree (del x l (by grind))) → y ∈ setTree l := by grind
        have h1 : (r.splitMin (by grind  ) (by grind  )).1 ∈ r.setTree := by grind
        have (y : α ) : y ∈ setTree (deleteTree (del x r (by grind))) → y ∈ setTree r := by grind
        grind
  | node3 l a m b r l_ih m_ih r_ih =>
      simp[del]
      split
      · grind
      · have : (m.splitMin (by grind) (by grind  )).1 ∈ m.setTree := by grind
        have : (r.splitMin (by grind) (by grind  )).1 ∈ r.setTree := by grind
        grind
