import tactic.basic
import tactic.linarith
import utils


inductive Untyped
| utrue
| ufalse
| uzero
| usucc : Untyped → Untyped
| uite : Untyped → Untyped → Untyped → Untyped
| upred : Untyped → Untyped
| uiszero : Untyped → Untyped

open Untyped

@[simp]
def consts : Untyped → list Untyped
| utrue := [utrue]
| ufalse := [ufalse]
| uzero := [uzero]
| (usucc n) := consts n
| (uite c t e) := (consts c) ++ ((consts t) ++ (consts e))
| (upred p) := consts p
| (uiszero v) := consts v

@[simp]
def size : Untyped → ℕ
| utrue := 1
| ufalse := 1
| uzero := 1
| (usucc n) := size n + 1
| (uite c t e) := ((size c + size t) + size e) + 1
| (upred p) := size p + 1
| (uiszero v) := size v + 1

@[simp]
def depth : Untyped → ℕ
| utrue := 1
| ufalse := 1
| uzero := 1
| (usucc n) := depth n + 1
| (uite c t e) := max (depth c) (max (depth t) (depth e)) + 1
| (upred p) := depth p + 1
| (uiszero v) := depth v + 1

theorem consts_finite :
  ∀u, ∃n, (consts u).length = n
  := begin
  intro u,
  induction u with n n_ih a b c a_ih b_ih c_ih,
  {
    existsi 1,
    simp,
  },
  {
    existsi 1,
    simp,
  },
  {
    existsi 1,
    simp,
  },
  {
    existsi (consts n).length,
    simp,
  },
  {
    exact exists_eq',
  },
  {
    exact u_ih,
  },
  {
    existsi (consts u_a).length,
    simp,
  }
end


theorem consts_le_size: 
    ∀t, (consts t).length ≤ size t
  := begin
  intro t,
  induction t,
  any_goals { simp },
  {
    exact le_add_right t_ih
  },
  {
    apply nat.le_succ_of_le,
    simp,
    apply smaller_than3 t_ih_a t_ih_a_1 t_ih_a_2,
  },
  {
    exact le_add_right t_ih,
  },
  {
    exact le_add_right t_ih,
  }
end

theorem untyped_depth_induction
  (p : Untyped → Prop)
  (h1 : ∀s r, depth r < depth s → p r → p s)
  : ∀s2, (p s2) := begin
  intro s2,
  specialize h1 s2,
  apply h1,
  sorry,
  sorry,
  sorry,
  -- induction s2,
end
