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

def join_all : Tree23s α → Tree23 α
| T t => t
| TTs t a ts => join_all (join_adj t a ts)

def not_T : Tree23s α → Bool
| T _ => False
| TTs _ _ _ => True
