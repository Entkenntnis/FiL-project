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
    cases ts with
    | T t => grind[join_adj, len]
    | TTs t4 d ts' =>
      cases ts' with
      | T t => grind[join_adj, len]
      | TTs t5 e ts'' =>
        unfold join_adj
        simp[len]
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
            exact join_adj_leq_len t3 t1 c a ts''
          omega


def join_all : Tree23s α → Tree23 α
| T t => t
| TTs t a ts => join_all (join_adj t a ts)
termination_by x => len x
decreasing_by
  exact join_adj_decreases_len t a ts
