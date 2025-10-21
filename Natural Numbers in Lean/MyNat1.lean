-- import Mathlib.Data.Nat.GCD.Basic
-- import MIL.Common

import Mathlib.Tactic

set_option linter.unusedVariables false

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

--------------
-- Definitions

def iterate : (MyNat → MyNat) → MyNat → MyNat → MyNat
  | f, zero, n => n
  | f, succ m, n => f (iterate f m n)

def add : MyNat → MyNat → MyNat
  | m, n => iterate succ n m

-- sum f 3 = (f 0) + (f 1) + (f 2)
def sum : (MyNat → MyNat) → MyNat → MyNat
  | f, zero => zero
  | f, succ n => add (sum f n) (f n)

def mul : MyNat → MyNat → MyNat
  | m, n => iterate (fun x => add x m) n zero

def one : MyNat := succ zero

def two : MyNat := succ one

def three : MyNat := succ two

def prod : (MyNat → MyNat) → MyNat → MyNat
  | f, zero => one
  | f, succ x => mul (prod f x) (f x)

def pred : MyNat → MyNat
  | zero => zero
  | succ x => x

def sub : MyNat → MyNat → MyNat
  | m, n => iterate pred n m

inductive le' : MyNat → MyNat → Prop
  | refl (m : MyNat) : le' m m
  | step (m n : MyNat) (h : le' m n) : le' m n.succ

def le (x y : MyNat) : Prop := ∃ z, y = x.add z

def lt (x y : MyNat) : Prop := ∃ z : MyNat, y = x.add z.succ

def ge (x y : MyNat) : Prop := y.le x

def gt (x y : MyNat) : Prop := y.lt x

def tri : MyNat → MyNat
  | n => sum (fun x => x.succ) n

def fact : MyNat → MyNat
  | n => prod (fun x => x.succ) n

def pow : MyNat → MyNat → MyNat
  | m, n => iterate (fun x => x.mul m) n one

def div (a b : MyNat) : Prop := ∃ c, a.mul c = b

def increasing_local (f : MyNat → MyNat) :
Prop := ∀ n : MyNat, (f n).lt (f n.succ)

def increasing (f : MyNat → MyNat) :
Prop := ∀ m n : MyNat, m.lt n → (f m).lt (f n)

def nondecreasing_local (f : MyNat → MyNat) :
Prop := ∀ n : MyNat, (f n).le (f n.succ)

def nondecreasing (f : MyNat → MyNat) :
Prop := ∀ m n : MyNat, m.le n → (f m).le (f n)

def min (P : MyNat → Prop) (m : MyNat) : Prop :=
P m ∧ ∀ n : MyNat, P n → m.le n

def satisfiable (P : MyNat → Prop) : Prop :=
∃ m, P m

--------------------------------------
-- Theorems: successor and basic logic

theorem ne {a b : MyNat} :  ¬a = b ↔ a ≠ b := by
  simp

theorem zero_ne_succ {a : MyNat} : zero ≠ a.succ := nofun

theorem succ_ne_zero {a : MyNat} : a.succ ≠ zero := nofun

theorem succ_inj {a b : MyNat} :
a.succ = b.succ ↔ a = b := by
  constructor
  · intro h
    exact succ.inj h
  intro h
  rw [h]

theorem self_ne_succ {a : MyNat} :
a ≠ a.succ := by
  induction' a with a ha
  · exact zero_ne_succ
  intro h
  rw [succ_inj] at h
  contradiction

theorem succ_ne_self {n : MyNat} : n.succ ≠ n := by
  symm; exact self_ne_succ

theorem zero_ne_one : zero ≠ one := by
  rw [one]
  exact zero_ne_succ

theorem one_ne_zero : one ≠ zero := by
  symm; exact zero_ne_one

theorem zero_ne_two : zero ≠ two := by
  rw [two]; exact zero_ne_succ

theorem two_ne_zero : two ≠ zero := by
  symm; exact zero_ne_two

theorem one_ne_two : one ≠ two := by
  rw [one, two]
  intro h
  rw [succ_inj] at h
  exact zero_ne_one h

theorem two_ne_one : two ≠ one := by
  symm; exact one_ne_two

---------------------
-- Theorems: addition

theorem add_zero {a : MyNat} :
a.add zero = a := by
  rw [add, iterate]

theorem add_succ {a b : MyNat} :
a.add b.succ = (a.add b).succ := by
  rw [add, iterate, succ_inj, ← add]


theorem add_assoc {a b c : MyNat} :
(a.add b).add c = a.add (b.add c) := by
  induction' c with c hc
  · rw [add_zero, add_zero]
  rw [add_succ, hc, add_succ, add_succ]

theorem zero_add {a : MyNat} : zero.add a = a := by
  induction' a with a ha
  · rw [add_zero]
  rw [add_succ, ha]

theorem succ_add {a b : MyNat} :
a.succ.add b = (a.add b).succ := by
  induction' b with b hn
  · rw [add_zero, add_zero]
  rw [add_succ, hn, add_succ]

theorem add_comm {a b : MyNat} :
a.add b = b.add a := by
  induction' b with b hb
  · rw [add_zero, zero_add]
  rw [add_succ, hb, succ_add]

theorem add_left_cancel {a b c : MyNat} :
a.add b = a.add c ↔ b = c := by
  constructor
  · intro h
    induction' a with a ha
    · rw [zero_add, zero_add] at h
      exact h
    rw [succ_add, succ_add, succ_inj] at h
    exact ha h
  intro h
  rw [h]

theorem add_right_cancel {a b c : MyNat} :
a.add c = b.add c ↔ a = b := by
  constructor
  · intro h
    rw [add_comm, add_comm (a := b), add_left_cancel] at h
    exact h
  intro h
  rw [h]

theorem add_one {a : MyNat} :
a.add one = a.succ := by
  rw [one, add_succ, add_zero]

theorem one_add {n : MyNat} :
one.add n = n.succ := by
  rw [add_comm]; exact add_one

theorem add_eq_zero {m n : MyNat} :
m.add n = zero ↔ m = zero ∧ n = zero := by
  constructor
  intro h
  induction' n with n hn
  rw [add_zero] at h
  exact ⟨h, rfl⟩
  rw [add_succ] at h
  have := succ_ne_zero h
  contradiction
  intro h
  rcases h with ⟨h1, h2⟩
  rw [h1, h2, add_zero]

theorem zero_eq_add {m n : MyNat} :
zero = m.add n ↔ m = zero ∧ n = zero := by
  constructor
  · intro h
    symm at h
    exact add_eq_zero.1 h
  intro h
  rw [h.1, h.2, add_zero]

theorem add_eq_left {m n : MyNat} :
m.add n = m ↔ n = zero := by
  constructor
  · intro eq1
    nth_rewrite 2 [← add_zero (a := m)] at eq1
    rw [add_left_cancel] at eq1
    exact eq1
  intro eq1
  rw [eq1, add_zero]

theorem add_eq_right {m n : MyNat} :
m.add n = n ↔ m = zero := by
  rw [add_comm]
  exact add_eq_left

theorem one_add_one : one.add one = two := by
  rw [add_one, ← two]

------------------------
-- Theorems: predecessor

theorem ne_zero_eq_succ {a : MyNat} :
a ≠ zero ↔ a = a.pred.succ := by
  constructor
  · intro h
    induction' a with a ha
    · contradiction
    rw [pred]
  intro h1 h2
  rw [h2, pred] at h1
  exact zero_ne_succ h1

theorem pred_eq_zero {a : MyNat} :
a.pred = zero ↔ a = zero ∨ a = one := by
  constructor
  · intro h
    by_cases eq : a = zero
    · left
      exact eq
    right
    rw [one]
    induction' a with a ha
    · contradiction
    rw [pred] at h
    rw [h]
  intro h
  rcases h with h | h
  · rw [h, pred]
  rw [h, one, pred]

------------------------
-- Theorems: subtraction

theorem sub_zero {a : MyNat} :
a.sub zero = a := by
  rw [sub, iterate]

theorem sub_succ {a b : MyNat} :
a.sub b.succ = (a.sub b).pred := by
  rw [sub, iterate, sub]

theorem succ_sub_succ {a b : MyNat} :
a.succ.sub b.succ = a.sub b := by
  induction' b with b hb
  · rw [sub_succ, sub_zero, sub_zero, pred]
  rw [sub_succ, hb, sub_succ]

theorem sub_self {a : MyNat} :
a.sub a = zero := by
  induction' a with a ha
  · rw [sub_zero]
  rw [succ_sub_succ, ha]

theorem zero_sub {a : MyNat} : zero.sub a = zero := by
  induction' a with a ha
  · rw [sub_zero]
  rw [sub_succ, ha, pred]

theorem sub_eq_one_aux1 {a : MyNat} :
a.succ.sub a = one := by
  induction' a with a ha
  · rw [sub_zero, one]
  rw [succ_sub_succ]
  exact ha

theorem sub_eq_one_aux2 {a : MyNat} :
∀ (b : MyNat), a.sub b = one ↔ a = b.succ := by
  induction' a with a ha
  · intro b
    rw [zero_sub, one]
    simp
  intro b
  by_cases bz : b = zero
  · rw [bz, one, sub_zero]
  rw [ne, ne_zero_eq_succ] at bz
  constructor
  · intro h
    rw [bz, succ_sub_succ, ha b.pred] at h
    rw [← bz] at h
    rw [h]
  intro h
  rw [succ_inj] at h
  rw [h]
  induction' b with b hb
  · rw [sub_zero, one]
  rw [succ_sub_succ]
  exact sub_eq_one_aux1

theorem sub_eq_one {a b : MyNat} :
a.sub b = one ↔ a = b.succ := by
  exact sub_eq_one_aux2 b

theorem succ_sub_self {a : MyNat} : a.succ.sub a = one := by
  rw [sub_eq_one]

theorem add_sub_cancel_right {a b : MyNat} :
(a.add b).sub b = a := by
  induction' b with b hb
  · rw [sub_zero, add_zero]
  rw [add_succ, succ_sub_succ]
  exact hb

theorem add_sub_cancel_left {a b : MyNat} :
(a.add b).sub a = b := by
  rw [add_comm]
  exact add_sub_cancel_right

theorem sub_eq_zero_of_sub_ne_zero {a b : MyNat}
(h : a.sub b ≠ zero) : b.sub a = zero := by
  induction' a with a ha
  · rw [zero_sub] at h
    contradiction
  by_cases eq1 : a = b
  · rw [eq1, sub_succ, sub_self, pred]
  rw [sub_succ]
  have eq2 : a.sub b ≠ zero := by
    contrapose! h
    have bz : b ≠ zero := by
      intro bz
      rw [bz, sub_zero] at h
      rw [h, bz] at eq1
      contradiction
    rw [ne_zero_eq_succ] at bz
    rw [bz, succ_sub_succ]
    rw [bz, sub_succ, pred_eq_zero] at h
    rcases h with h | h
    · exact h
    rw [sub_eq_one] at h
    rw [← bz] at h
    contradiction
  rw [ha eq2, pred]

theorem pred_sub {m n : MyNat} :
m.pred.sub n = (m.sub n).pred := by
  by_cases mz : m = zero
  · rw [mz, pred, zero_sub, pred]
  rw [ne, ne_zero_eq_succ] at mz
  rw [← sub_succ]
  nth_rewrite 2 [mz]
  rw [succ_sub_succ]

theorem sub_sub_eq_sub_add {a b c : MyNat} :
(a.sub b).sub c = a.sub (b.add c) := by
  induction' c with c hc
  · rw [sub_zero, add_zero]
  rw [sub_succ, hc, add_succ, sub_succ]

theorem add_imp_sub_left {a b c : MyNat}
(h : a.add b = c) : b = c.sub a := by
  rw [← h, add_sub_cancel_left]

theorem add_imp_sub_right {a b c : MyNat}
(h : a.add b = c) : a = c.sub b := by
  rw [← h, add_sub_cancel_right]

theorem add_sub {a b : MyNat} :
(a.add (b.sub a) = a) ∨ (a.add (b.sub a) = b) := by
  by_cases eq1 : b.sub a = zero
  · left
    rw [eq1, add_zero]
  right
  induction' a with a ha
  · rw [zero_add, sub_zero]
  have eq2 : ¬b.sub a = zero := by
    contrapose! eq1
    rw [sub_succ, eq1, pred]
  have eq3 := ha eq2
  rw [succ_add, sub_succ, ← add_succ]
  rw [ne, ne_zero_eq_succ] at eq2
  rw [← eq2]
  exact eq3

---------------------------
-- Theorems: multiplication

theorem mul_zero {a : MyNat} : a.mul zero = zero := by
  rw [mul, iterate]

theorem mul_succ {a b : MyNat} :
a.mul b.succ = (a.mul b).add a := by
  rw [mul, iterate, mul]

theorem zero_mul {a : MyNat} : zero.mul a = zero := by
  induction' a with a ha
  · exact mul_zero
  rw [mul_succ, ha, add_zero]

theorem succ_mul {a b : MyNat} :
a.succ.mul b = (a.mul b).add b := by
  induction' b with b hb
  · rw [mul_zero, mul_zero, add_zero]
  rw [mul_succ, hb, mul_succ, add_succ, add_succ,
      add_assoc, add_comm (a := b), ← add_assoc]

theorem mul_one {a : MyNat} : a.mul one = a := by
  rw [one, mul_succ, mul_zero, zero_add]

theorem one_mul {a : MyNat} : one.mul a = a := by
  rw [one, succ_mul, zero_mul, zero_add]

theorem add_mul {a b c : MyNat} :
(a.add b).mul c = (a.mul c).add (b.mul c) := by
  induction' c with c hc
  · rw [mul_zero, mul_zero, mul_zero, add_zero]
  rw [mul_succ, hc, mul_succ, mul_succ,
      add_comm, add_comm (a := a.mul c) (b := a),
      add_comm (a := b.mul c), ← add_assoc (b := b),
      add_assoc (c := b), add_comm (a := a.mul c) (b := b),
      add_assoc, add_assoc, add_assoc]

theorem mul_add {a b c : MyNat} :
a.mul (b.add c) = (a.mul b).add (a.mul c) := by
  induction' c with c hc
  · rw [add_zero, mul_zero, add_zero]
  rw [add_succ, mul_succ, hc, mul_succ, add_assoc]

theorem mul_assoc {a b c : MyNat} :
(a.mul b).mul c = a.mul (b.mul c) := by
  induction' c with c hc
  · rw [mul_zero, mul_zero, mul_zero]
  rw [mul_succ, hc, mul_succ, mul_add]

theorem mul_comm {a b : MyNat} : a.mul b = b.mul a := by
  induction' b with b hb
  · rw [mul_zero, zero_mul]
  rw [mul_succ, hb, succ_mul]

theorem mul_eq_zero {m n : MyNat} :
m.mul n = zero ↔ m = zero ∨ n = zero := by
  constructor
  intro h
  by_cases nz : n = zero
  right
  exact nz
  rw [ne, ne_zero_eq_succ] at nz
  left
  rw [nz, mul_succ] at h
  rw [add_eq_zero] at h
  exact h.2
  intro h
  rcases h with h | h
  rw [h, zero_mul]
  rw [h, mul_zero]

theorem mul_eq_one_aux {m n : MyNat} :
m.mul n = one → m = one := by
  intro eq1
  by_cases eq2 : n = zero
  · rw [eq2, mul_zero, one] at eq1
    have := zero_ne_succ eq1
    contradiction
  by_cases eq3 : m = zero
  · rw [eq3, zero_mul, one] at eq1
    have := zero_ne_succ eq1
    contradiction
  rw [ne, ne_zero_eq_succ] at eq2
  rw [ne, ne_zero_eq_succ] at eq3
  rw [eq2, eq3, one, mul_succ, succ_mul, add_succ, succ_inj,
      add_eq_zero] at eq1
  rw [eq1.2] at eq3
  rw [eq3, one]

theorem mul_eq_one {m n : MyNat} :
m.mul n = one ↔ m = one ∧ n = one := by
  constructor
  intro h
  have := mul_eq_one_aux h
  constructor
  exact this
  rw [this, one_mul] at h
  exact h
  intro h
  rw [h.1, h.2, mul_one]

theorem mul_pred {m n : MyNat} :
m.mul n.pred = (m.mul n).sub m := by
  by_cases eq1 : n = zero
  · rw [eq1, pred, mul_zero, zero_sub]
  rw [ne, ne_zero_eq_succ] at eq1
  nth_rewrite 2 [eq1]
  rw [mul_succ, add_sub_cancel_right]

theorem mul_sub {a b c : MyNat} :
a.mul (b.sub c) = (a.mul b).sub (a.mul c) := by
  induction' c with c hc
  · rw [sub_zero, mul_zero, sub_zero]
  rw [sub_succ, mul_pred, hc, mul_succ, sub_sub_eq_sub_add]

theorem sub_mul {a b c : MyNat} :
(a.sub b).mul c = (a.mul c).sub (b.mul c) := by
  rw [mul_comm, mul_sub, mul_comm, mul_comm (a := c)]

---------------------
-- Theorems: ordering

theorem le_self {n : MyNat} : n.le n := by
  use zero
  rw [add_zero]

theorem add_imp_lt {m n c : MyNat} :
c ≠ zero → m.add c = n → m.lt n := by
  intro h1 h2
  rw [ne_zero_eq_succ] at h1
  use c.pred
  rw [← h1]
  symm
  exact h2

theorem lt_iff_succ_le {m n : MyNat} :
m.lt n ↔ m.succ.le n := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    use c
    rw [succ_add, ← add_succ]
    exact h
  intro h
  rcases h with ⟨c, hc⟩
  use c
  rw [add_succ, ← succ_add]
  exact hc

theorem lt_imp_le {m n : MyNat} :
m.lt n → m.le n := by
  intro eq1
  rw [lt] at eq1
  rcases eq1 with ⟨c, eq1⟩
  use c.succ

theorem lt_succ_self {n : MyNat} :
n.lt n.succ := by
  use zero
  rw [add_succ, add_zero]

theorem le_succ {n : MyNat} : n.le n.succ := by
  exact lt_imp_le (lt_succ_self (n := n))

theorem zero_le {a : MyNat} : zero.le a := by
  use a
  rw [zero_add]

theorem le_zero {a : MyNat} : a.le zero ↔ a = zero := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    symm at h
    rw [add_eq_zero] at h
    exact h.1
  intro h
  rw [h]
  exact zero_le

theorem succ_le_succ {a b : MyNat} :
a.succ.le b.succ ↔ a.le b := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    use c
    rw [succ_add, succ_inj] at h
    exact h
  intro h
  rcases h with ⟨c, h⟩
  use c
  rw [h, succ_add]

theorem le_one {n : MyNat} :
n.le one ↔ n = zero ∨ n = one := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    cases c
    rw [add_zero] at h
    right
    symm; exact h
    case succ c =>
      rw [add_succ, one, succ_inj, zero_eq_add] at h
      left
      exact h.1
  intro h
  rcases h with h | h
  · use one
    rw [h, zero_add]
  rw [h]
  exact le_self

theorem lt_one {n : MyNat} :
n.lt one ↔ n = zero := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    rw [one, add_succ, succ_inj, zero_eq_add] at h
    exact h.1
  intro h
  rw [h]
  use zero
  rw [zero_add, ← one]

theorem one_le {n : MyNat} :
one.le n ↔ n ≠ zero := by
  constructor
  · intro h
    intro h'
    rw [h', le_zero] at h
    exact one_ne_zero h
  intro h
  rw [ne_zero_eq_succ] at h
  rw [one, h, succ_le_succ]
  exact zero_le

theorem not_succ_le_self {n : MyNat} : ¬ n.succ.le n := by
  intro h
  rcases h with ⟨c, h⟩
  symm at h
  rw [succ_add, ← add_succ, add_eq_left] at h
  exact succ_ne_zero h

theorem le_antisymm {a b : MyNat} (ab : a.le b) (ba : b.le a) :
a = b := by
  rcases ab with ⟨c, ab⟩
  rcases ba with ⟨d, ba⟩
  rw [ba, add_assoc] at ab
  nth_rewrite 2 [← add_zero (a := b)] at ab
  symm at ab
  rw [add_zero, add_eq_left, add_eq_zero] at ab
  rw [ab.1, add_zero] at ba
  rw [ba]

theorem le_of_succ_le {a b : MyNat} (h : a.succ.le b) : a.le b := by
  rcases h with ⟨c, h⟩
  use c.succ
  rw [add_succ]
  rw [succ_add] at h
  exact h

theorem le_trans {a b c : MyNat} (hab : a.le b) (hbc : b.le c) :
a.le c := by
  rcases hab with ⟨m, hab⟩
  rcases hbc with ⟨n, hbc⟩
  use m.add n
  rw [← add_assoc, ← hab]
  exact hbc

theorem not_lt_self {n : MyNat} : ¬ n.lt n := by
  intro h
  rcases h with ⟨c, h⟩
  symm at h
  rw [add_eq_left] at h
  exact succ_ne_zero h

theorem succ_lt_succ {m n : MyNat} :
m.succ.lt n.succ ↔ m.lt n := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    rw [add_succ, succ_inj, succ_add, ← add_succ] at h
    use c
  intro h
  rcases h with ⟨c, h⟩
  use c
  rw [succ_add, h]

theorem le_iff_lt_or_eq {m n : MyNat} :
m.le n ↔ m.lt n ∨ m = n := by
  constructor
  · intro eq1
    rcases eq1 with ⟨c, eq1⟩
    cases c
    case zero =>
      rw [add_zero] at eq1
      right; symm; exact eq1
    case succ c =>
      left; use c
  intro eq1
  rcases eq1 with eq1 | eq1
  · exact lt_imp_le eq1
  rw [eq1]; exact le_self

theorem lt_of_le_of_lt {a b c : MyNat}
(eq1 : a.le b) (eq2 : b.lt c) :
a.lt c := by
  rcases eq1 with ⟨m, eq1⟩
  rcases eq2 with ⟨n, eq2⟩
  use m.add n
  rw [← add_succ, ← add_assoc, ← eq1]
  exact eq2

theorem lt_of_lt_of_le {a b c : MyNat}
(eq1 : a.lt b) (eq2 : b.le c) :
a.lt c := by
  rcases eq1 with ⟨m, eq1⟩
  rcases eq2 with ⟨n, eq2⟩
  use m.add n
  rw [← succ_add, ← add_assoc, ← eq1]
  exact eq2

theorem le_or_gt {m n : MyNat} : m.le n ∨ m.gt n := by
  induction' n with n hn
  · cases m
    case zero =>
      left; exact le_self
    case succ m =>
      right
      use m
      rw [zero_add]
  rcases hn with ⟨c, hn⟩ | ⟨c, hn⟩
  · left
    use c.succ
    rw [add_succ, hn]
  cases c
  case zero =>
    left
    rw [add_succ, add_zero] at hn
    rw [hn]; exact le_self
  case succ c =>
    right
    rw [hn, gt, add_succ, succ_lt_succ]
    use c

theorem le_iff_not_gt {m n : MyNat} : m.le n ↔ ¬m.gt n := by
  constructor
  · intro eq1 eq2
    rw [gt] at eq2
    have eq3 := lt_of_le_of_lt eq1 eq2
    exact not_lt_self eq3
  intro eq1
  have eq2 := le_or_gt (m := m) (n := n)
  rcases eq2 with eq2 | eq2
  · exact eq2
  contradiction

theorem lt_iff_not_ge {m n : MyNat} : m.lt n ↔ ¬ m.ge n := by
  have eq1 := le_iff_not_gt (m := m.succ) (n := n)
  rw [lt_iff_succ_le, ge]
  rw [gt, lt_iff_succ_le, succ_le_succ] at eq1
  exact eq1

theorem lt_or_ge {m n : MyNat} : m.lt n ∨ m.ge n := by
  have eq1 := le_or_gt (m := m.succ) (n := n)
  rw [lt_iff_not_ge]
  tauto

theorem lt_trichotomy {m n : MyNat} :
m.lt n ∨ m = n ∨ (n.lt m) := by
  rcases le_or_gt (m := m) (n := n) with eq1 | eq1
  · rw [le_iff_lt_or_eq] at eq1
    rw [← or_assoc]; left
    exact eq1
  rw [gt] at eq1
  right; right; exact eq1

theorem lt_trans {a b c : MyNat} (eq1 : a.lt b) (eq2 : b.lt c) :
a.lt c := by
  rcases eq1 with ⟨m, eq1⟩
  rcases eq2 with ⟨n, eq2⟩
  use m.succ.add n
  rw [add_succ, ← add_assoc, ← eq1, ← add_succ, eq2]

theorem lt_imp_not_lt {m n : MyNat} :
m.lt n → ¬ n.lt m := by
  intro h1 h2
  exact not_lt_self (lt_trans h1 h2)

theorem lt_iff_le_and_ne {m n : MyNat} :
m.lt n ↔ m.le n ∧ m ≠ n := by
  constructor
  · intro eq1
    constructor
    · exact lt_imp_le eq1
    intro eq2
    rw [eq2] at eq1
    exact not_lt_self eq1
  intro h
  rcases h with ⟨⟨c, h1⟩, h2⟩
  cases c
  case zero =>
    rw [add_zero] at h1
    symm at h1
    contradiction
  case succ c =>
    use c

theorem zero_lt_succ {n : MyNat} : zero.lt n.succ := by
  use n
  rw [zero_add]

theorem zero_lt_one : zero.lt one := by
  use zero
  rw [zero_add, ← one]

theorem one_lt_two : one.lt two := by
  use zero
  rw [← one]
  exact one_add_one

theorem zero_lt_two : zero.lt two := by
  exact lt_trans zero_lt_one one_lt_two

theorem sub_eq_zero_iff_le {a b : MyNat} :
a.sub b = zero ↔ a.le b := by
  constructor
  · intro eq1
    have eq2 := lt_trichotomy (m := a) (n := b)
    rcases eq2 with eq2 | eq2 | eq2
    · exact lt_imp_le eq2
    · rw [eq2]
      exact le_self
    rcases eq2 with ⟨c, eq2⟩
    rw [eq2, add_sub_cancel_left] at eq1
    have eq3 := succ_ne_zero (a := c)
    contradiction
  intro eq1
  rcases eq1 with ⟨c, eq1⟩
  rw [eq1, ← sub_sub_eq_sub_add, sub_self, zero_sub]

theorem succ_sub {a b : MyNat} :
a.le b ↔ b.succ.sub a = (b.sub a).succ := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    rw [h, ← add_succ, add_sub_cancel_left,
        add_sub_cancel_left]
  intro h
  rcases le_or_gt (m := a) (n := b) with h2 | h2
  · exact h2
  rw [gt] at h2
  rw [lt_iff_succ_le, ← sub_eq_zero_iff_le] at h2
  rw [h2] at h
  exfalso; exact zero_ne_succ h

theorem add_le_add_right_cancel {a b c : MyNat} :
(a.add c).le (b.add c) ↔ a.le b := by
  induction' c with c hc
  rw [add_zero, add_zero]
  rw [add_succ, add_succ, succ_le_succ]
  exact hc

theorem add_le_add_left_cancel {a b c : MyNat} :
(a.add b).le (a.add c) ↔ b.le c := by
  rw [add_comm, add_comm (b := c), add_le_add_right_cancel]

theorem add_lt_add_right_cancel {a b c : MyNat} :
(a.add c).lt (b.add c) ↔ a.lt b := by
  constructor
  · intro h
    rcases h with ⟨d, h⟩
    use d
    rw [add_assoc, add_comm (a := c), ← add_assoc,
        add_right_cancel] at h
    exact h
  intro h
  rcases h with ⟨d, h⟩
  use d
  rw [h, add_succ, add_succ, succ_add, add_assoc,
      add_comm (a := d), add_assoc]

theorem add_lt_add_left_cancel {a b c : MyNat} :
(a.add b).lt (a.add c) ↔ b.lt c := by
  rw [add_comm, add_comm (a := a)]
  exact add_lt_add_right_cancel

theorem le_mul {m n : MyNat} :
m.le (m.mul n.succ) := by
  rw [mul_succ]
  nth_rewrite 1 [← zero_add (a := m)]
  rw [add_le_add_right_cancel]
  exact zero_le

theorem le_iff_lt_succ {m n : MyNat} :
m.le n ↔ m.lt n.succ := by
  rw [lt_iff_succ_le, succ_le_succ]

theorem add_sub_le_right {a b c : MyNat} (h : c.le b) :
(a.add b).sub c = a.add (b.sub c) := by
  induction' c with c hc
  · rw [sub_zero, sub_zero]
  have h2 := h
  rcases h with ⟨d, h⟩
  rw [succ_add, ← add_succ] at h
  have eq1 : c.le b := by
    use d.succ
  have eq2 := hc eq1
  rw [sub_succ, eq2, sub_succ]
  have eq3 : b.sub c ≠ zero := by
    rw [le_iff_lt_succ, succ_lt_succ, lt] at h2
    rcases h2 with ⟨h2, h3⟩
    contrapose! h3
    rw [h, add_sub_cancel_left] at h3
    have := succ_ne_zero (a := d)
    contradiction
  rw [ne_zero_eq_succ] at eq3
  rw [eq3, add_succ, pred, pred]

theorem add_le_add {a b c d : MyNat} :
a.le c → b.le d → (a.add b).le (c.add d) := by
  intro ac bd
  rcases ac with ⟨m, ac⟩
  rcases bd with ⟨n, bd⟩
  use m.add n
  rw [add_comm (a := m), add_assoc, ← add_assoc (a := b), ← bd,
      add_comm (a := d), ← add_assoc, ← ac]

theorem mul_le_mul {a b c d : MyNat} :
a.le c → b.le d → (a.mul b).le (c.mul d) := by
  intro ac bd
  rcases ac with ⟨m, ac⟩
  rcases bd with ⟨n, bd⟩
  rw [ac, bd, mul_add, add_mul, add_mul, add_assoc]
  use (m.mul b).add ((a.mul n).add (m.mul n))

theorem mul_lt_mul {a b c d : MyNat} :
a ≠ zero → b ≠ zero → a.le c → b.lt d → (a.mul b).lt (c.mul d) := by
  intro az bz ac bd
  rcases ac with ⟨m, hm⟩
  rcases bd with ⟨n ,hn⟩
  set N : MyNat := n.succ
  rw [hn, hm, add_mul, mul_add, add_assoc]
  nth_rewrite 1 [← add_zero (a := a.mul b)]
  rw [add_lt_add_left_cancel, lt_iff_le_and_ne]
  constructor
  · exact zero_le
  intro h
  symm at h
  rw [add_eq_zero] at h
  rcases h with ⟨h1, _⟩
  rw [mul_eq_zero] at h1
  rcases h1 with h | h
  · exact az h
  exact succ_ne_zero h

theorem sub_ne_zero_iff_gt {m n : MyNat} :
m.sub n ≠ zero ↔ m.gt n := by
  constructor
  · intro eq1
    rw [gt]
    use ((m.sub n).pred)
    rw [ne_zero_eq_succ] at eq1
    rw [← eq1]
    rcases add_sub (a := n) (b := m) with eq2 | eq2
    · cases n
      case zero =>
        rw [zero_add, sub_zero] at eq2
        rw [eq2, zero_add, sub_zero]
      case succ n =>
        rw [sub_succ, succ_add, succ_inj, add_eq_left] at eq2
        rw [sub_succ, eq2, pred] at eq1
        exfalso
        exact zero_ne_succ eq1
    exact eq2.symm
  intro eq1 eq2
  rcases eq1 with ⟨c, eq1⟩
  rw [eq1, add_sub_cancel_left] at eq2
  exact succ_ne_zero eq2

theorem mul_right_increasing {m n : MyNat}
(hm : m ≠ zero) (hn : two.le n) :
m.lt (m.mul n) := by
  cases m
  case zero => contradiction
  case succ m =>
  clear hm
  rcases hn with ⟨c, hc⟩
  use m.add (m.succ.mul c)
  rw [succ_mul, hc, succ_add, succ_mul, add_succ, mul_add,
      two, succ_add, one_add, mul_succ, mul_one, add_succ, add_succ,
      succ_inj, succ_inj, add_assoc, add_assoc]

theorem mul_left_increasing {m n : MyNat}
(hm : two.le m) (hn : n ≠ zero) :
n.lt (m.mul n) := by
  have := mul_right_increasing (m := n) (n := m) hn hm
  rw [mul_comm]
  exact this

theorem mul_le_mul_left_cancel {a b c : MyNat} (eq1 : one.le a) :
(a.mul b).le (a.mul c) ↔ b.le c := by
  constructor
  · intro eq2
    rcases eq1 with ⟨d, eq1⟩
    rcases eq2 with ⟨m, eq2⟩
    rw [le_iff_not_gt]
    intro eq3
    rcases eq3 with ⟨n, eq3⟩
    rw [eq3, add_succ, mul_succ, mul_add, add_assoc,
        add_assoc] at eq2
    nth_rewrite 2 [← add_zero (a := a.mul c)] at eq2
    symm at eq2
    rw [add_zero, add_eq_left, add_eq_zero] at eq2
    have eq4 := eq2.2
    rw [add_eq_zero] at eq4
    symm at eq1
    rw [eq4.1, add_eq_zero] at eq1
    have eq5 := symm eq1.1
    exact zero_ne_one eq5
  intro eq2
  rcases eq2 with ⟨d, eq2⟩
  rw [eq2, mul_add]
  use a.mul d

-----------------------
-- Theorems: increasing functions

theorem inc_local_to_global {f : MyNat → MyNat} :
increasing_local f ↔ increasing f := by
  constructor
  · intro h m n hmn
    rcases hmn with ⟨c, hmn⟩
    induction c generalizing n with
    | zero =>
      rw [add_succ] at hmn
      rw [hmn]
      exact h m
    | succ c hc =>
      cases n
      case zero =>
        rw [add_succ] at hmn
        exfalso; exact zero_ne_succ hmn
      case succ n =>
      rw [add_succ, succ_inj] at hmn
      have h2 := hc n hmn
      exact lt_trans h2 (h n)
  intro h n
  exact h n n.succ lt_succ_self

theorem nd_local_to_global {f : MyNat → MyNat} :
nondecreasing_local f ↔ nondecreasing f := by
  constructor
  · intro h1 m n h2
    rcases h2 with ⟨c, h2⟩
    rw [← h2]; clear h2
    induction c with
    | zero =>
      rw [add_zero]
      exact le_self
    | succ c h2 =>
    rw [add_succ]
    exact le_trans h2 (h1 (m.add c))
  intro h m
  exact h m m.succ (lt_imp_le (lt_succ_self))

theorem inc_imp_nd {f : MyNat → MyNat} :
increasing f → nondecreasing f := by
  rw [← inc_local_to_global, ← nd_local_to_global]
  intro h1 n
  apply lt_imp_le
  exact h1 n

theorem inc_preserves_order {f : MyNat → MyNat} { m n : MyNat}
(h : increasing f) : (f m).lt (f n) ↔ m.lt n := by
  constructor
  · intro eq1
    rcases lt_or_ge (m := m) (n := n) with eq2 | eq2
    · exact eq2
    rw [ge] at eq2
    have eq3 := inc_imp_nd h
    have eq4 := eq3 n m eq2
    rw [le_iff_not_gt, gt] at eq4
    contradiction
  exact h m n

theorem increasing_inj {f : MyNat → MyNat} {m n : MyNat}
(h : increasing f) : f m = f n ↔ m = n := by
  constructor
  · intro eq1
    rcases lt_trichotomy (m := m) (n := n) with eq2 | eq2 | eq2
    · have eq3 := h m n eq2
      rw [lt_iff_le_and_ne] at eq3
      exfalso; exact eq3.2 eq1
    · exact eq2
    have eq3 := h n m eq2
    rw [lt_iff_le_and_ne] at eq3
    symm at eq1
    exfalso; exact eq3.2 eq1
  intro eq2
  rw [eq2]

theorem inc_of_inc_comp_inc {f g : MyNat → MyNat} :
increasing f → increasing g → increasing (fun x => f ( g x)) := by
  intro hf hg m n hmn
  simp
  exact hf (g m) (g n) (hg m n hmn)

theorem nd_of_nd_comp_nd {f g : MyNat → MyNat} :
nondecreasing f → nondecreasing g →
nondecreasing (fun x => f (g x)) := by
  intro hf hg m n hmn
  simp
  exact hf (g m) (g n) (hg m n hmn)

----------------------
-- Theorems: summation

theorem sum_extract_first {n : MyNat} {f : MyNat → MyNat} :
sum f n.succ = add (sum (fun x => f (x.succ)) n) (f zero) := by
  induction' n with n hn
  · rw [sum, zero_add, sum, sum, zero_add]
  rw [sum, hn, add_assoc, sum, add_assoc, add_comm (a := f zero)]

theorem sum_le_n {f g : MyNat → MyNat} {n : MyNat} :
  (∀ m : MyNat, (m.lt n → f m = g m)) → sum f n = sum g n := by
    induction' n with n hn
    · intro hm
      rw [sum, sum]
    intro hm
    rw [sum, sum]
    have eq1 := hm n
    have eq2 := lt_succ_self (n := n)
    rw [eq1 eq2, add_right_cancel]
    apply hn
    intro m eq3
    have eq4 := hm m
    exact eq4 (lt_trans eq3 eq2)

theorem sum_reverse_aux1 {f : MyNat → MyNat} {n : MyNat} :
sum (fun x => f (n.sub x).pred.succ) n =
sum (fun x => f (n.succ.sub x).pred) n := by
  set F1 : MyNat → MyNat := fun x => f (n.sub x).pred.succ with F1_def
  set F2 : MyNat → MyNat := fun x => f (n.succ.sub x).pred with F2_def
  have eq1 : ∀ m : MyNat, (m.lt n → F1 m = F2 m) := by
    intro m hm
    rw [F1_def, F2_def]
    simp
    have : (n.sub m).pred.succ = (n.succ.sub m).pred := by
      rcases hm with ⟨c, hm⟩
      rw [← hm, add_sub_cancel_left,
          pred, ← add_succ, add_sub_cancel_left, pred]
    rw [this]
  exact sum_le_n eq1

theorem sum_reverse_aux2 {n : MyNat} :
∀ f : MyNat → MyNat, sum f n = sum (fun x => f ((n.sub x).pred)) n := by
  induction' n with n hn
  · intro f
    rw [sum, sum]
  intro f
  rw [sum_extract_first, sum]
  have eq1 : f (n.succ.sub n).pred = f zero := by
    rw [← sub_succ, succ_sub_succ, sub_self]
  rw [eq1, add_right_cancel]
  rw [hn]
  exact sum_reverse_aux1

theorem sum_reverse {f : MyNat → MyNat} {n : MyNat} :
sum f n = sum (fun x => f ((n.sub x).pred)) n := by
  exact sum_reverse_aux2 f

theorem sq_eq_sum_odd {n : MyNat} :
sum (fun x => (x.add x).add one) n = n.mul n := by
  induction' n with n hn
  · rw [sum, mul_zero]
  rw [sum, hn, one, add_succ, add_zero, add_succ,
      mul_succ, succ_mul, add_succ, add_assoc]

theorem add_sum {f g : MyNat → MyNat} {n : MyNat} :
(sum f n).add (sum g n) = sum (fun x => (f x).add (g x) ) n := by
  induction' n with n hn
  · rw [sum, sum, sum, add_zero]
  rw [sum, sum, sum, add_assoc, ← add_assoc (a := f n),
      add_comm (a := f n), ← add_assoc, ← add_assoc, hn,
      ← add_assoc]

theorem num_mul_sum {f : MyNat → MyNat} {m n : MyNat} :
m.mul (sum f n) = sum (fun x => (m.mul (f x))) n := by
  induction' n with n hn
  · rw [sum, sum, mul_zero]
  rw [sum, sum, mul_add, hn]

theorem sum_const_eq_mul {m n : MyNat} :
sum (fun x => m) n = m.mul n := by
  induction' n with n hn
  · rw [sum, mul_zero]
  rw [sum, hn, mul_succ]

theorem sum_one {n : MyNat} :
sum (fun x => one) n = n := by
  have := sum_const_eq_mul (m := one) (n := n)
  rw [one_mul] at this
  exact this

theorem fun_eq_sum_sub_sum {f : MyNat → MyNat} {n : MyNat} :
f n = (sum f n.succ).sub (sum f n) := by
  rw [sum, add_sub_cancel_left]

theorem telescope {f : MyNat → MyNat} {n : MyNat}
(h : nondecreasing f) :
 (f n).sub (f zero) = sum (fun x => (f x.succ).sub (f x)) n := by
  induction' n with n hn
  · rw [sum, sub_self]
  rw [sum, ← hn]
  clear hn
  have h' := nd_local_to_global.2 h
  rcases h zero n zero_le with ⟨c, hc⟩
  rw [← add_imp_sub_left hc]
  rcases h' n with ⟨d, hd⟩
  rw [← add_imp_sub_left hd]
  rw [← hc, add_assoc] at hd
  rw [add_imp_sub_left hd]

theorem tri_sub_tri {n : MyNat} :
(tri n).sub (tri n.pred) = n := by
  cases n
  case zero =>
    rw [pred, sub_self]
  case succ n =>
  rw [tri, sum, ← tri, pred, add_sub_cancel_left]

theorem sum_le {f g : MyNat → MyNat} {n : MyNat}
(h : ∀ m : MyNat, m.lt n → (g m).le (f m)) :
(sum g n).le (sum f n) := by
  have eq1 : ∀ (m : MyNat), m.lt n → f m = ((g m).add ((f m).sub (g m))) := by
    intro m eq1
    have eq2 := h m eq1
    rcases eq2 with ⟨c, eq2⟩
    nth_rewrite 2 [← eq2]
    rw [add_sub_cancel_left, eq2]
  have eq2 := sum_le_n eq1
  rw [← add_sum] at eq2
  use sum (fun m => (f m).sub (g m)) n
  rw [← eq2]

theorem sum_sub_sum {f g : MyNat → MyNat} {n : MyNat} :
(∀ m : MyNat, m.lt n → (g m).le (f m)) → (sum f n).sub (sum g n) =
sum (fun x => (f x).sub (g x)) n := by
  intro h
  have eq1 : ∀ (m : MyNat), m.lt n → f m = ((g m).add ((f m).sub (g m))) := by
    intro m eq1
    have eq2 := h m eq1
    rcases eq2 with ⟨c, eq2⟩
    nth_rewrite 2 [← eq2]
    rw [add_sub_cancel_left, eq2]
  have eq2 := sum_le_n eq1
  rw [← add_sum] at eq2
  rw [eq2, add_sub_cancel_left]

theorem sum_eq_sum {f g : MyNat → MyNat} {n : MyNat} :
(∀ x, x.lt n → f x = g x) → sum f n = sum g n := by
  induction' n with n hn
  · intro _
    rw [sum, sum]
  intro h
  have eq1 : ∀ (x : MyNat), x.lt n → f x = g x := by
    intro x hx
    have := lt_trans hx lt_succ_self
    exact h x this
  rw [sum, sum]
  rw [hn eq1]
  rw [h n (lt_succ_self (n := n))]

theorem tri_inc : increasing tri := by
  rw [← inc_local_to_global]
  intro n
  nth_rewrite 2 [tri]
  rw [sum, ← tri]
  nth_rewrite 1 [← add_zero (a := n.tri)]
  rw [add_lt_add_left_cancel]
  exact zero_lt_succ

--------------------
-- Theorems : powers

theorem pow_zero {n : MyNat} :
n.pow zero = one := by
  rw [pow, iterate]

theorem pow_succ {m n : MyNat} :
m.pow n.succ = (m.pow n).mul m := by
  rw [pow, iterate, pow]

theorem pow_succ_left {m n : MyNat} :
m.pow n.succ = m.mul (m.pow n) := by
  rw [mul_comm, pow_succ]

theorem zero_pow {n : MyNat} :
zero.pow n.succ = zero := by
  rw [pow_succ, mul_zero]

theorem one_pow {n : MyNat} :
one.pow n = one := by
  induction' n with n hn
  · rw [pow_zero]
  rw [pow_succ, mul_one, hn]

theorem pow_one {n : MyNat} :
n.pow one = n := by
  rw [one, pow_succ, pow_zero, one_mul]

theorem pow_two {n : MyNat} :
n.pow two = n.mul n := by
  rw [two, pow_succ, pow_one]

theorem pow_eq_zero {m n : MyNat} :
m.pow n = zero → m = zero := by
  intro eq1
  contrapose eq1
  induction' n with n eq2
  rw [pow_zero, one]
  exact succ_ne_zero
  contrapose! eq2
  rw [pow_succ, mul_eq_zero] at eq2
  rcases eq2 with eq2 | eq2
  exact eq2
  contradiction

theorem pow_eq_one {m n : MyNat} (eq1 : two.le m) :
m.pow n = one ↔ n = zero := by
  constructor
  · intro eq2
    by_cases eq3 : n = zero
    exact eq3
    rw [ne, ne_zero_eq_succ] at eq3
    rw [eq3, pow_succ, mul_eq_one] at eq2
    rw [eq2.2, two, one, succ_le_succ, le_zero] at eq1
    have eq4 := succ_ne_zero (a := zero)
    contradiction
  intro eq2
  rw [eq2, pow_zero]

theorem one_le_pow {m n : MyNat} (eq1 : m ≠ zero) :
one.le (m.pow n) := by
  rw [le_iff_not_gt]
  contrapose! eq1
  rw [gt, lt_one] at eq1
  exact pow_eq_zero eq1

theorem pow_add {a b c : MyNat} :
a.pow (b.add c) = (a.pow b).mul (a.pow c) := by
  induction' c with c hc
  · rw [add_zero, pow_zero, mul_one]
  rw [add_succ, pow_succ, hc, pow_succ, mul_assoc]

theorem tri_add_tri {n : MyNat} :
(tri n).add (tri n.pred) = n.pow two := by
  cases n
  · case zero =>
    rw [tri, sum, pred, tri, sum, two, pow_succ, add_zero, mul_zero]
  case succ n =>
  rw [pred]
  have rv := sum_reverse (f := fun x => x.succ) (n := n.succ)
  rw [← tri] at rv
  set f : MyNat → MyNat :=
  fun x => (n.succ.sub x).pred.succ with f_def
  set g : MyNat → MyNat :=
  fun x => (n.succ.sub x) with g_def
  have fg: ∀ x, x.lt n.succ → f x = g x := by
    intro x hx
    rw [f_def, g_def]; simp
    rw [lt_iff_succ_le, succ_le_succ] at hx
    rcases hx with ⟨c, hx⟩
    rw [← hx, ← add_succ, add_sub_cancel_left, pred]
  have  eq1 := sum_eq_sum fg
  rw [eq1] at rv
  rw [rv, sum, add_assoc, add_comm (a := g n), ← add_assoc,
      tri, add_sum]
  have eq2 : g n = one := by
    rw [g_def]; simp
    rw [succ_sub_self]
  rw [eq2]
  set g2 : MyNat → MyNat := fun x => (g x).add x.succ with g2_def
  set g3 : MyNat → MyNat := fun x => n.succ.succ with g3_def
  have eq3 : ∀ x, x.lt n → g2 x = g3 x := by
    intro x hx
    rw [g3_def, g2_def, g_def]; simp
    rcases hx with ⟨c, hx⟩
    rw [← hx, ← add_succ, add_sub_cancel_left, add_succ,
        succ_add, succ_add, add_succ, add_succ, add_comm]
  rw [sum_eq_sum eq3, g3_def, sum_const_eq_mul, succ_mul,
      succ_mul, two, pow_succ, pow_one, mul_succ, succ_mul,
      add_succ, add_one]

theorem pow_right_increasing {a b c : MyNat}
(ha : two.le a) (hbc : b.lt c) : (a.pow b).lt (a.pow c) := by
  set f : MyNat → MyNat := fun x => a.pow x with f_def
  have f_inc : increasing_local f := by
    intro x
    rw [f_def]; simp
    rw [pow_succ]
    have : a.pow x ≠ zero := by
      intro h
      have := pow_eq_zero h
      rw [this, le_zero] at ha
      exact two_ne_zero ha
    exact mul_right_increasing (m := a.pow x) (n := a) this ha
  rw [inc_local_to_global] at f_inc
  have := f_inc b c hbc
  rw [f_def] at this
  simp at this
  exact this

theorem pow_as_prod {m n : MyNat} :
m.pow n = prod (fun x => m) n := by
  induction' n with n hb
  · rw [pow_zero, prod]
  rw [pow, iterate, ← pow, hb, prod]

theorem pow_left_increasing_aux {f : MyNat → MyNat} {c : MyNat}
(f_def : f = fun x => x.pow c.succ) :
increasing_local f := by
  induction c generalizing f with
  | zero =>
    intro n
    rw [f_def]; simp
    rw [← one, pow_one, pow_one]
    exact lt_succ_self
  | succ c hc =>
  intro n
  rw [f_def]; simp
  rw [pow_succ]
  nth_rewrite 2 [pow_succ]
  set g : MyNat → MyNat := fun x => x.pow c.succ with g_def
  have hg := hc g_def
  have eq1 := hg n
  rw [g_def] at eq1
  simp at eq1
  by_cases nz : n = zero
  · rw [nz, mul_zero, ← one, one_pow, mul_one]
    exact zero_lt_one
  apply mul_lt_mul
  · intro h
    exact nz (pow_eq_zero h)
  · exact nz
  · exact lt_imp_le eq1
  exact lt_succ_self

theorem pow_left_increasing {a b c : MyNat}
(cz : c ≠ zero) : (a.pow c).lt (b.pow c) ↔ a.lt b := by
  rw [ne_zero_eq_succ] at cz
  set d : MyNat := c.pred with d_def
  set f : MyNat → MyNat := fun x => x.pow d.succ with f_def
  have f_inc := pow_left_increasing_aux f_def
  rw [inc_local_to_global] at f_inc
  have eq := inc_preserves_order (f := f) (m := a) (n := b) f_inc
  rw [f_def] at eq; simp at eq
  rw [cz]; exact eq

theorem mul_pow {a b c : MyNat} :
(a.mul b).pow c = (a.pow c).mul (b.pow c) := by
  induction' c with c hc
  · rw [pow_zero, pow_zero, pow_zero, mul_one]
  rw [pow_succ, hc, pow_succ, pow_succ, mul_assoc, mul_assoc,
      ← mul_assoc (a := a) (b := b.pow c),
      mul_comm (a := a) (b := b.pow c), mul_assoc]

theorem pow_sub_pow {a b c : MyNat} :
(a.pow c).sub (b.pow c) = (a.sub b).mul
(sum (fun x => (a.pow x).mul (b.pow (c.pred.sub x))) c) := by
  cases c
  case zero =>
    rw [pow_zero, pow_zero, sub_self, sum, mul_zero]
  case succ c =>
  rw [pred]
  rcases lt_or_ge (m := a) (n := b) with h | h
  · have h2 := pow_left_increasing
               (a := a) (b := b) (c := c.succ) succ_ne_zero
    have h3 := h2.2 h
    have h4 := lt_imp_le h3
    rw [← sub_eq_zero_iff_le] at h4
    have h5 := lt_imp_le h
    rw [← sub_eq_zero_iff_le] at h5
    rw [h4, h5, zero_mul]
  rw [ge] at h
  set f : MyNat → MyNat :=
    fun x => (a.pow x).mul (b.pow (c.succ.sub x)) with f_def
  have eq1 : a.pow c.succ = f (c.succ) := by
    rw [f_def]; simp
    rw [sub_self, pow_zero, mul_one]
  have eq2 : b.pow c.succ = f zero := by
    rw [f_def]; simp
    rw [pow_zero, one_mul, sub_zero]
  have f_nd : nondecreasing_local f := by
    intro n
    rw [f_def]; simp
    rcases le_or_gt (m := n) (n := c) with eq3 | eq3
    · rcases eq3 with ⟨d, eq3⟩
      have eq4 := add_imp_sub_left eq3
      rw [succ_sub_succ]
      have eq5 : c.succ.sub n = d.succ := by
        rw [← eq3, ← add_succ, add_sub_cancel_left]
      rw [← eq4, eq5]
      rw [pow_succ, pow_succ]
      cases n
      case zero =>
        rw [pow_zero, one_mul, one_mul, mul_comm]
        apply mul_le_mul
        · exact h
        exact le_self
      case succ n =>
      rw [pow_succ, mul_assoc, mul_assoc, mul_assoc,
          mul_comm (a := a) (b := b.pow d),
          ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      apply mul_le_mul
      · exact le_self
      exact h
    rw [gt, lt_iff_succ_le, ← sub_eq_zero_iff_le] at eq3
    rw [sub_succ, eq3, pred, pow_zero, mul_one, mul_one, pow_succ]
    have nz : n ≠ zero := by
      intro eq4
      rw [eq4, sub_zero] at eq3
      exact succ_ne_zero eq3
    cases a
    case zero =>
      rw [ne_zero_eq_succ] at nz
      rw [mul_zero, nz, pow_succ, mul_zero]
      exact le_self
    case succ a =>
    set A : MyNat := a.succ with A_def
    nth_rewrite 1 [← mul_one (a := A.pow n)]
    apply mul_le_mul
    · exact le_self
    rw [A_def, one, succ_le_succ]
    exact zero_le
  rw [nd_local_to_global] at f_nd
  have tele := telescope (f := f) (n := c.succ) f_nd
  set g : MyNat → MyNat := fun x => (f x.succ).sub (f x) with g_def
  set G : MyNat → MyNat := fun x =>
    (a.sub b).mul ((a.pow x).mul (b.pow (c.sub x))) with G_def
  have eq3 : ∀ x, x.lt c.succ →
  g x = G x := by
    intro x eq3
    rw [← le_iff_lt_succ] at eq3
    rw [G_def]; simp
    rw [sub_mul, ← mul_assoc, ← pow_succ_left, ← mul_assoc,
        mul_comm (b := a.pow x), mul_assoc, ← pow_succ_left]
    rw [g_def, f_def]; simp
    rw [succ_sub_succ]
    rw [succ_sub.1 eq3]
  have eq4 := sum_eq_sum eq3
  rw [eq4, G_def, ← num_mul_sum] at tele
  have fc : f c.succ = a.pow c.succ := by
    rw [f_def]; simp
    rw [sub_self, pow_zero, mul_one]
  have f0 : f zero = b.pow c.succ := by
    rw [f_def]; simp
    rw [pow_zero, one_mul, sub_zero]
  rw [← f0, ← fc]
  exact tele

theorem sq_sub_sq {m n : MyNat} :
(m.pow two).sub (n.pow two) = (m.sub n).mul (m.add n) := by
  rw [pow_sub_pow (a := m) (b := n) (c := two)]
  rw [two, sum, pred, sub_self, pow_zero, mul_one, pow_one]
  nth_rewrite 2 [one]
  rw [sum, sub_zero, pow_one, pow_zero, one_mul, sum,
      zero_add, add_comm]

theorem sum_cb_eq_tri_sq {n : MyNat} :
sum (fun x => x.succ.pow three) n = n.tri.pow two := by
  have eq1 : ∀ x : MyNat,
  x.pow three = (x.tri.pow two).sub ((x.pred.tri).pow two) := by
    intro x
    calc
      x.pow three = x.mul (x.pow two) := by
        rw [three, pow_succ_left]
      _ = (x.tri.sub x.pred.tri).mul (x.tri.add x.pred.tri) := by
        rw [tri_sub_tri, tri_add_tri]
      _ = (x.tri.pow two).sub ((x.pred.tri).pow two) := by
        symm
        exact sq_sub_sq (m := x.tri) (n := x.pred.tri)
  set sq : MyNat → MyNat := fun x => x.pow two with sq_def
  have sq_inc : increasing sq := by
    intro a b h
    rw [sq_def]; simp
    rw [pow_left_increasing (a := a) (b := b) (c := two)
      two_ne_zero]
    exact h
  set f : MyNat → MyNat := fun x => sq (tri x) with f_def
  have f_inc := inc_of_inc_comp_inc sq_inc tri_inc
  rw [← f_def] at f_inc
  have f_nd := inc_imp_nd (f := f) f_inc
  have tele := telescope (f := f) (n := n) f_nd
  have fn : f n = n.tri.pow two := by
    rw [f_def]
  have f0 : f zero = zero := by
    rw [f_def]; simp
    rw [tri, sum, sq_def]; simp
    rw [two, zero_pow]
  rw [fn, f0, sub_zero] at tele
  set g : MyNat → MyNat := fun x => (f x.succ).sub (f x) with g_def
  have hg : g = fun x : MyNat => x.succ.pow three := by
    ext x
    rw [g_def, f_def, sq_def]; simp; symm
    have := eq1 x.succ
    rw [pred] at this
    exact this
  rw [hg] at tele
  symm
  exact tele

-------------------------
-- Theorems: divisibility

theorem div_zero {n : MyNat} :
n.div zero := by
  use zero
  rw [mul_zero]

theorem zero_div {n : MyNat} :
zero.div n ↔ n = zero := by
  constructor
  · intro h
    contrapose h
    intro h2
    rw [ne, ne_zero_eq_succ] at h
    rw [h] at h2
    rcases h2 with ⟨c, hc⟩
    rw [zero_mul] at hc
    exact zero_ne_succ hc
  intro h
  rw [h]
  use zero
  rw [zero_mul]

theorem div_one {n : MyNat} :
n.div one ↔ n = one := by
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    rw [mul_eq_one] at h
    exact h.1
  intro h
  use one
  rw [h, mul_one]

theorem floor_div {m n : MyNat} (mz : m ≠ zero) :
∃ c : MyNat, (m.mul c).le n ∧ n.lt (m.mul c.succ) := by
  have mz1 := mz
  have mz2 := mz
  clear mz
  rw [ne_zero_eq_succ] at mz2
  induction' n with n eq1
  · use zero
    constructor
    · rw [mul_zero]
      exact zero_le
    rw [mul_succ, mul_zero, zero_add, lt_iff_succ_le, mz2,
        succ_le_succ]
    exact zero_le
  rcases eq1 with ⟨c, eq1, eq2⟩
  rcases eq1 with ⟨d, eq1⟩
  by_cases eq4 : d = m.pred
  rw [eq4] at eq1
  use c.succ
  constructor
  · rw [mul_succ]
    nth_rewrite 2 [mz2]
    rw [add_succ, eq1]
    exact le_self
  · rw [mul_succ]
    nth_rewrite 2 [mz2]
    rw [add_succ, succ_lt_succ, lt_iff_succ_le, mul_succ,
        add_assoc, add_comm (a := m), ← add_assoc]
    nth_rewrite 3 [mz2]
    rw [add_succ, succ_le_succ, eq1]
    use m.pred
  use c
  constructor
  · use d.succ
    rw [add_succ, eq1]
  rw [mul_succ]
  nth_rewrite 2 [mz2]
  rw [add_succ, succ_lt_succ]
  rw [lt_iff_not_ge]
  contrapose! eq4
  rw [ge, ← eq1, add_le_add_left_cancel] at eq4
  rw [← eq1, mul_succ, add_lt_add_left_cancel,
      lt_iff_succ_le] at eq2
  rw [← succ_le_succ, ← mz2] at eq4
  have eq5 := le_antisymm eq4 eq2
  rw [eq5, pred]

--------------------------
-- Theorems: well ordering

theorem induction_from {P : MyNat → Prop} {n : MyNat} :
(P n) → (∀ m, n.le m → P m → P m.succ) → (∀ m, n.le m → P m) := by
  intro hp hm
  have : ∀ c, P (n.add c) := by
    intro c
    induction' c with c hc
    · rw [add_zero]; exact hp
    have eq1 : n.le (n.add c) := by
      use c
    have eq2 := hm (n.add c) eq1 hc
    rw [add_succ]; exact eq2
  intro m hmn
  rcases hmn with ⟨c, hc⟩
  rw [← hc]
  exact this c

theorem zero_is_min {P : MyNat → Prop} :
P zero ↔ min P zero := by
  constructor
  · intro h
    constructor
    exact h
    intro n hn
    exact zero_le
  intro h
  rcases h with ⟨h, _⟩
  exact h

lemma well_order_aux {P : MyNat → Prop} :
(∀ m : MyNat, ¬ min P m) → (∀ m n : MyNat, n.le m → ¬ P n) := by
  intro h1 m n h2
  induction' m with m hm generalizing n
  · rw [le_zero] at h2
    rw [h2]
    have h3 := h1 zero
    contrapose! h3
    rw [zero_is_min (P := P)] at h3
    exact h3
  have h3 := h1 n
  contrapose! h3
  constructor
  · exact h3
  intro k hk1
  rw [le_iff_not_gt]
  intro hk2
  rw [gt] at hk2
  have hk3 := lt_of_lt_of_le hk2 h2
  rw [lt_iff_succ_le, succ_le_succ] at hk3
  exact hm k hk3 hk1

theorem well_order {P : MyNat → Prop} :
satisfiable P ↔ ∃ m, min P m := by
  constructor
  · intro h
    contrapose h
    push_neg at h
    rw [satisfiable]
    push_neg
    have h2 := well_order_aux h
    intro m
    exact h2 m m le_self
  intro h
  rcases h with ⟨m, ⟨h1, _⟩⟩
  use m

end MyNat
