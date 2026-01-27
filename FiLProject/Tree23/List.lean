import FiLProject.Tree23.Basic

inductive Tree23s (α : Type u)
| T (t : Tree23 α)
| TTs (t : Tree23 α) (a : α) (ts : Tree23s α)
deriving DecidableEq

namespace Tree23s
open Tree23

universe u

variable {α : Type u}

def len :  Tree23s α → ℕ
| T _ => 1
| TTs _ _ ts => len ts + 1

def trees : Tree23s α → Set (Tree23 α)
| T t => {t}
| TTs t _ ts => {t} ∪ trees ts

def inorder2 : Tree23s α → List α
| T t => inorder t
| TTs t a ts => inorder t ++ [a] ++ inorder2 ts

def join_adj (t1 : Tree23 α) (a : α) (ts : Tree23s α) : Tree23s α :=
  match ts with
  | T t2 => T (node2 t1 a t2)
  | TTs t2 b ts =>
    match ts with
    | T t3 => T (node3 t1 a t2 b t3)
    | TTs t3 c ts => TTs (node2 t1 a t2) b (join_adj t3 c ts)

def not_T : Tree23s α → Bool
| T _ => false
| TTs _ _ _ => true


lemma join_adj_leq_len (t3 : Tree23 α) (t1 : Tree23 α) (c : α) (a : α) (ts : Tree23s α) :
    (join_adj t3 c ts).len ≤ (join_adj t1 a (TTs t3 c ts)).len :=
  by
    induction ts generalizing t3 c with
    | T t => grind[join_adj, len]
    | TTs t4 d ts' ih =>
      cases ts' with
      | T t => grind[join_adj, len]
      | TTs t5 e ts'' =>
        unfold join_adj
        simp[len]
        unfold join_adj at ih
        simp at ih

        exact join_adj_leq_len t5 t4 e d ts''




lemma join_adj_decreases_len (t1 : Tree23 α) (a : α) (ts : Tree23s α)  :
    len (join_adj t1 a ts) < len (TTs t1 a ts) :=
  by
    induction ts with
    | T _ => grind[join_adj, len]
    | TTs t2 b ts' ih =>
        simp [len] at *
        cases ts' with
        | T t => grind[len, join_adj]
        | TTs t3 c ts'' =>
          simp [len] at *
          unfold join_adj
          simp
          simp [len] at *
          have : (join_adj t3 c ts'').len ≤ (join_adj t1 a (TTs t3 c ts'')).len := by
            exact join_adj_leq_len t1 t3 a c ts''
          omega



def join_all : Tree23s α → Tree23 α
| T t => t
| TTs t a ts => join_all (join_adj t a ts)
termination_by x => len x
decreasing_by
  induction ts generalizing t a with
  | T _ => grind[join_adj, len]
  | TTs t2 b ts' ih =>
    specialize ih t2 b
    have : (TTs t a (TTs t2 b ts')).len = (TTs t2 b ts').len + 1 := by grind[len]
    rw[this]


    unfold len

    let ts := (TTs t2 b ts')
    cases h :(join_adj t a ts) with
    | T t => grind
    | TTs rt ra rts =>
      -- simp
      -- apply lt_trans
      -- have : ts = rts := by sorry
      --rw[ih] at h
      sorry




def join_adj2 : (ts : Tree23s α) → not_T ts = true → Tree23s α
| TTs t1 a (T t2), _ => T (node2 t1 a t2)
| TTs t1 a (TTs t2 b (T t3)), _ => T (node3 t1 a t2 b t3)
| TTs t1 a (TTs t2 b (TTs t3 c ts)), _ =>
    TTs (node2 t1 a t2) b (join_adj2 (TTs t3 c ts) rfl)

theorem join_adj2_decreases_length (ts : Tree23s α) (h : not_T ts = true) :
  len (join_adj2 ts h) < len ts := by
  match ts, h with
  | TTs t1 a (T t2), _ =>
    simp [join_adj2, len]
  | TTs t1 a (TTs t2 b (T t3)), _ =>
    simp [join_adj2, len]
  | TTs t1 a (TTs t2 b (TTs t3 c ts)), h =>
    simp [join_adj2, len]
    have IH := join_adj2_decreases_length (TTs t3 c ts) rfl
    have len_fact : len (TTs t3 c ts) = len ts + 1 := by simp [len]
    omega

def join_all2 : Tree23s α → Tree23 α
| T t => t
| TTs t a ts => join_all2 (join_adj2 (TTs t a ts) rfl)
termination_by x => len x
decreasing_by
  apply join_adj2_decreases_length
