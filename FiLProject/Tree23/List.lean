
import FiLProject.Tree23.Complete

inductive Tree23s (α : Type u)
| T (t : Tree23 α)
| TTs (t : Tree23 α) (a : α) (ts : Tree23s α)
deriving DecidableEq

namespace Tree23s
open Tree23

universe u

variable {α : Type u}

@[grind]
def len :  Tree23s α → ℕ
| T _ => 1
| TTs _ _ ts => len ts + 1

@[grind, simp]
def trees : Tree23s α → Set (Tree23 α)
| T t => {t}
| TTs t _ ts => {t} ∪ trees ts

@[grind]
def inorder2 : Tree23s α → List α
| T t => inorder t
| TTs t a ts => inorder t ++ [a] ++ inorder2 ts

@[grind]
def join_adj (t1 : Tree23 α) (a : α) (ts : Tree23s α) : Tree23s α :=
  match ts with
  | T t2 => T (node2 t1 a t2)
  | TTs t2 b ts =>
    match ts with
    | T t3 => T (node3 t1 a t2 b t3)
    | TTs t3 c ts => TTs (node2 t1 a t2) b (join_adj t3 c ts)

@[grind! .]
lemma join_adj_leq_len (t3 : Tree23 α) (t1 : Tree23 α) (c : α) (a : α) (ts : Tree23s α) :
    (join_adj t3 c ts).len ≤ (join_adj t1 a (TTs t3 c ts)).len := by
  induction t3, c, ts using join_adj.induct generalizing t1 a <;> grind

@[grind! .]
lemma join_adj_decreases_len (t1 : Tree23 α) (a : α) (ts : Tree23s α):
    len (join_adj t1 a ts) < len (TTs t1 a ts) := by
  induction t1, a, ts using join_adj.induct <;> grind

@[grind! .]
lemma join_adj_decreases_len_by_half (t1 : Tree23 α) (a : α) (ts : Tree23s α):
    len (join_adj t1 a ts) ≤ len (TTs t1 a ts) / 2 := by
  induction t1, a, ts using join_adj.induct <;> grind

@[grind]
def join_all : Tree23s α → Tree23 α
| T t => t
| TTs t a ts => join_all (join_adj t a ts)
termination_by x => len x
decreasing_by grind

def not_T : Tree23s α → Bool
| T _ => false
| TTs _ _ _ => true

@[grind]
def leaves : List α → Tree23s α
| List.nil => T nil
| List.cons a as => TTs nil a (leaves as)

@[grind]
def tree23_of_list (as : List α) : Tree23 α :=
  join_all (leaves as)

@[grind! .]
lemma list_correctness_1 (t1 : Tree23 α) (a: α) (ts: Tree23s α):
    inorder2 (join_adj t1 a ts) = inorder2 (TTs t1 a ts) := by
  induction t1, a, ts using join_adj.induct <;> grind

lemma list_correctness_2 (ts: Tree23s α):
    inorder (join_all ts) = inorder2 ts := by
  induction ts using join_all.induct <;> grind

lemma list_correctness_3 (as : List α):
    inorder (tree23_of_list as) = as := by
  -- explicit reuse of previous lemma
  unfold tree23_of_list
  rw[list_correctness_2]
  induction as <;> grind

lemma list_completeness_1 (t1 : Tree23 α) (a : α) (ts : Tree23s α ) (n : ℕ) :
    (∀ t ∈ trees (TTs t1 a ts), complete t ∧ height t = n) →
    (∀ t ∈ trees (join_adj t1 a ts), complete t ∧ height t = n + 1) := by
  -- simp is necessary
  induction t1, a, ts using join_adj.induct  <;> simp at * <;> grind

lemma list_completeness_2 (n : ℕ):
    (ts : Tree23s α ) → (∀ t ∈ trees ts, complete t ∧ height t = n) →
    complete (join_all ts) := by
  intro ts h
  cases ts with
  | T t2 => grind
  | TTs t2 b ts' =>
    cases ts' with
    | T t3 => grind
    | TTs t3 c ts'' =>
      -- recursive application with slightly more complex argument
      have := list_completeness_2 (n + 1) (join_adj t2 b (TTs t3 c ts''))
               (fun t a => list_completeness_1 t2 b (TTs t3 c ts'') n h t a)
      grind
termination_by ts => len ts
decreasing_by grind


lemma list_completeness_3 (as : List α):
    ∀ t ∈ (trees (leaves as)), complete t ∧ height t = 0 := by
  induction as <;> grind

lemma list_completeness_4 (as : List α):
    complete (tree23_of_list as) := by
  -- grind can't find pattern for list_completeness_2, so manually apply here
  apply list_completeness_2 0
  grind[list_completeness_3]

@[grind]
def T_join_adj (_ : Tree23 α) (_ : α) (ts : Tree23s α) : ℕ :=
  match ts with
  | T _ => 1
  | TTs _ _ ts' =>
    match ts' with
    | T _ => 1
    | TTs t a ts => T_join_adj t a ts + 1

@[grind]
def T_join_all: Tree23s α → ℕ
| T _ => 1
| TTs t a ts => (T_join_adj t a ts) + T_join_all (join_adj t a ts) + 1
termination_by ts => len ts
decreasing_by grind

@[grind]
def T_leaves: List α → ℕ
| [] => 1
| List.cons _ xs => T_leaves xs + 1

@[grind]
def T_tree23_of_list (as : List α): ℕ :=
  T_leaves as + T_join_all (leaves as)

@[grind! .]
lemma tree23_of_list_running_time_1 (t : Tree23 α) (a : α) (ts: Tree23s α):
    T_join_adj t a ts ≤ len (TTs t a ts) / 2 := by
  induction t, a, ts using join_adj.induct <;> grind

lemma helper_nat_rel (n : ℕ) (h : n ≥ 1):
    n / 2 + n + 1 ≤ 2 * n := by
  induction n <;> grind

@[grind! .]
lemma tree23_of_list_running_time_2:
    (ts: Tree23s α) → T_join_all ts ≤ 2 * len ts := by
  intro ts
  induction ts using join_all.induct <;> grind

@[grind! .]
lemma tree23_of_list_running_time_3 (as : List α):
    T_leaves as ≤ as.length + 1 := by
  induction as <;> grind

@[grind! .]
lemma tree23_of_list_running_time_4 (as : List α):
    len (leaves as) = as.length + 1:= by
  induction as <;> grind

lemma tree23_of_list_running_time:
    (as : List α) → T_tree23_of_list as ≤ 3 * as.length + 3 := by
  grind
