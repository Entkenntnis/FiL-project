
import FiLProject.Tree23.Complete

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

def not_T : Tree23s α → Bool
| T _ => false
| TTs _ _ _ => true

def leaves : List α → Tree23s α
| List.nil => T nil
| List.cons a as => TTs nil a (leaves as)

def tree23_of_list (as : List α) : Tree23 α :=
  join_all (leaves as)

lemma list_correctness_1 (t1 : Tree23 α) (a: α) (ts: Tree23s α):
    inorder2 (join_adj t1 a ts) = inorder2 (TTs t1 a ts) := by
  cases ts with
  | T t =>
    grind[join_adj, inorder2, inorder]
  | TTs t2 b ts' =>
    cases ts' with
    | T t => grind[join_adj, inorder2, inorder]
    | TTs t3 c ts =>
      simp[join_adj]
      unfold inorder2
      have : (join_adj t3 c ts).inorder2 = (TTs t3 c ts).inorder2 := by exact list_correctness_1 t3 c ts
      rw [this]
      grind[inorder, inorder2]

lemma list_correctness_2:
    (ts: Tree23s α) → inorder (join_all ts) = inorder2 ts := by
  intro ts
  cases ts with
  | T t => grind[inorder, join_all, inorder2]
  | TTs t a ts =>
    unfold join_all
    have : (TTs t a ts).inorder2 = inorder2 (join_adj t a ts) := by exact Eq.symm (list_correctness_1 t a ts)
    rw[this]
    exact list_correctness_2 (join_adj t a ts)
termination_by x => len x
decreasing_by
  exact join_adj_decreases_len t a ts

lemma list_correctness_3 (as : List α):
    inorder (tree23_of_list as) = as := by
  unfold tree23_of_list
  rw[list_correctness_2]
  induction as with
  | nil => rfl
  | cons a as ih => grind[leaves, inorder2, inorder]


lemma list_completeness_1 (t1 : Tree23 α) (a : α) (ts : Tree23s α ) (n : ℕ) :
    (∀ t ∈ trees (TTs t1 a ts), complete t ∧ height t = n) →
    (∀ t ∈ trees (join_adj t1 a ts), complete t ∧ height t = n + 1) := by
  intro h t ht
  cases ts with
  | T t2 =>
    simp [join_adj, trees] at ht
    rw [ht]
    have ht1 : complete t1 ∧ height t1 = n := by
      apply h
      simp [trees]
    have ht2 : complete t2 ∧ height t2 = n := by
      apply h
      simp [trees]
    grind[complete]
  | TTs t2 b ts' =>
    cases ts' with
    | T t3 =>
      simp [join_adj, trees] at ht
      rw [ht]
      have ht1 : complete t1 ∧ height t1 = n := by
        apply h; simp [trees]
      have ht2 : complete t2 ∧ height t2 = n := by
        apply h; simp [trees]
      have ht3 : complete t3 ∧ height t3 = n := by
        apply h; simp [trees]
      grind[complete]
    | TTs t3 c ts'' =>
      simp [join_adj, trees] at ht
      cases ht with
      | inl heq =>
        rw [heq]
        have ht1 : complete t1 ∧ height t1 = n := by
          apply h; simp [trees]
        have ht2 : complete t2 ∧ height t2 = n := by
          apply h; simp [trees]
        grind[complete]
      | inr hmem =>
        have h' : ∀ t ∈ trees (TTs t3 c ts''), complete t ∧ height t = n := by
          intro t' ht'
          apply h
          simp [trees] at ht' ⊢
          grind
        have ih := list_completeness_1 t3 c ts'' n h'
        exact ih t hmem


lemma list_completeness_2 (ts : Tree23s α ) (n : ℕ) :
    (ts : Tree23s α ) → (∀ t ∈ trees ts, complete t ∧ height t = n) →
    complete (join_all ts) := by
  intro ts h
  induction ts with
  | T t2 =>
    simp [join_all]
    have ht2 : complete t2 ∧ height t2 = n := by
      apply h
      simp [trees]
    exact ht2.1
  | TTs t2 b ts' ih =>
    induction ts' with
    | T t3 =>
      simp[join_all, join_adj]
      have ht2 : complete t2 ∧ height t2 = n := by
        apply h
        simp [trees]
      have ht3 : complete t3 ∧ height t3 = n := by
        apply h
        simp [trees]
      grind
    | TTs t3 c ts'' ih2 =>
      have h1 : ∀ t ∈ trees (join_adj t2 b (TTs t3 c ts'')), complete t ∧ height t = n + 1 :=
        by exact list_completeness_1 t2 b (TTs t3 c ts'') n h
      simp[join_all]
      have oih := list_completeness_2 (join_adj t2 b (TTs t3 c ts'')) (n + 1)
      grind
termination_by x => len x
decreasing_by
  expose_names

  --exact join_adj_decreases_len t a (join_adj t2 b (TTs t3 c ts''))
