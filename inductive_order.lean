import Mathlib.Tactic

set_option linter.unusedVariables false

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

--------------
-- Definitions

inductive le : MyNat → MyNat → Prop
  | refl (m : MyNat) : le m m
  | step (m n : MyNat) (h : le m n) : le m n.succ

def pred : MyNat → MyNat
  | zero => zero
  | succ n => n

def add : MyNat → MyNat → MyNat
  | m, zero => m
  | m, succ n => succ (add m n)

def lt (m n : MyNat) : Prop := m.succ.le n

def ge (m n : MyNat) : Prop := n.le m

def gt (m n : MyNat) : Prop := n.lt m

def one : MyNat := succ zero

def two : MyNat := succ one

--------------------------------------
-- Theorems: successor and basic logic

theorem ne {a b : MyNat} :  ¬a = b ↔ a ≠ b := by
  rw []

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


-----------
-- Theorems



theorem le_refl {n : MyNat} : n.le n := le.refl n

theorem le_step {m n : MyNat} : m.le n → m.le n.succ := le.step m n

theorem le_succ {n : MyNat} : n.le n.succ := by
  apply le_step
  exact le_refl

theorem le_trans {a b c : MyNat} (h1 : a.le b) (h2 : b.le c) :
a.le c := by
  induction h2 with
  | refl =>
    exact h1
  | step c hab hac =>
    apply le_step
    exact hac

theorem lt_imp_le {m n : MyNat} :
m.lt n → m.le n := by
  intro h
  rw [lt] at h
  exact le_trans le_succ h

theorem zero_le {n : MyNat} : zero.le n := by
  induction' n with n hn
  exact le_refl
  exact le_step hn

theorem succ_le {m n : MyNat} : m.succ.le n → m.le n :=
  le_trans (le_step (le_refl (n := m)))

theorem not_succ_le_zero {n : MyNat} : ¬ n.succ.le zero := nofun

theorem le_zero {n : MyNat} : n.le zero ↔ n = zero := by
  constructor
  · intro h
    induction' n with n hn
    rfl
    exfalso; exact not_succ_le_zero h
  intro h; rw [h]; exact le_refl

theorem le_succ_iff {m n : MyNat} :
m.le n.succ ↔ m = n.succ ∨ m.le n := by
  constructor
  · have eq1 :
∀ a : MyNat, a = n.succ → m.le a → m = n.succ ∨ m.le n := by
      intro a ha h
      induction h with
      | refl =>
        left; exact ha
      | step a hm hn =>
        right
        rw [succ_inj] at ha
        rw [ha] at hm; exact hm
    exact eq1 n.succ rfl
  intro h
  rcases h with h | h
  · rw [h]; exact le.refl n.succ
  exact le.step m n h

theorem succ_le_succ_aux1 {m n : MyNat} :
m.succ.le n.succ → m.le n := by
  rw [le_succ_iff]
  intro h
  rcases h with h | h
  · rw [succ_inj] at h
    rw [h]; exact le_refl
  exact le_trans le_succ h

theorem succ_le_succ_aux2 {m n : MyNat} :
m.le n → m.succ.le n.succ := by
  intro h
  induction' n with n hn
  · rw [le_zero] at h
    rw [h]; exact le_refl
  rw [le_succ_iff (m := m) (n := n)] at h
  rcases h with h | h
  · rw [h]; exact le_refl
  have h2 := hn h
  exact le_trans h2 le_succ

theorem succ_le_succ {m n : MyNat} :
 m.succ.le n.succ ↔ m.le n := by
  exact ⟨succ_le_succ_aux1, succ_le_succ_aux2⟩

theorem one_le {n : MyNat} :
one.le n ↔ n ≠ zero := by
  rw [one]
  cases n
  case zero =>
    constructor
    · intro h; exfalso; exact not_succ_le_zero h
    intro h; contradiction
  case succ n =>
    constructor
    · intro h1 h2
      exact succ_ne_zero h2
    intro h
    rw [succ_le_succ]
    exact zero_le

theorem le_one {n : MyNat} :
n.le one ↔ n = zero ∨ n = one := by
  cases n
  case zero =>
    constructor
    · intro; left; rfl
    intro h
    rcases h with h | h
    · exact zero_le
    exfalso; exact zero_ne_one h
  case succ n =>
    constructor
    · intro h
      right
      rw [one, succ_inj]
      rw [one, succ_le_succ, le_zero] at h
      exact h
    intro h
    rcases h with h | h
    · exfalso; exact succ_ne_zero h
    rw [one, succ_inj] at h
    rw [h, ← one]
    exact le_refl

theorem not_succ_le_self (n : MyNat) : ¬ n.succ.le n := by
  induction' n with n hn
  · exact not_succ_le_zero
  contrapose! hn
  rw [succ_le_succ] at hn
  exact hn

theorem le_antisymm {m n : MyNat} (hmn : m.le n) (hnm : n.le m) :
m = n := by
  induction hmn with
  | refl =>
    rfl
  | step n h1 h2 =>
    have h3 := le_trans hnm h1
    exfalso; exact not_succ_le_self (n := n) h3

theorem le_iff_not_gt {m n : MyNat} :
m.le n ↔ ¬ m.gt n := by
  constructor
  · induction' m with m hm
    · intro h1
      exact not_succ_le_zero
    intro h1 h2
    rw [gt, lt, succ_le_succ] at h2
    have h3 := le_trans h1 h2
    exact not_succ_le_self (n := m) h3
  intro h
  rw [gt, lt] at h
  induction' m with m hm generalizing n
  · exact zero_le
  · rw [succ_le_succ] at h
    have eq1 := hm (n := n.pred)
    cases n
    case zero =>
      exfalso; exact h zero_le
    case succ n =>
      rw [pred] at eq1
      rw [succ_le_succ]
      exact eq1 h

theorem le_or_gt {m n : MyNat} :
m.le n ∨ m.gt n := by
  rw [le_iff_not_gt]
  tauto

theorem lt_or_ge {m n : MyNat} :
m.lt n ∨ m.ge n := by
  rw [← gt, ge]
  symm
  exact le_or_gt

theorem le_iff_eq_or_lt {m n : MyNat} :
m.le n ↔ m = n ∨ m.lt n := by
  constructor
  · intro h
    have h2 := lt_or_ge (m := m) (n := n)
    rcases h2 with h2 | h2
    · right; exact h2
    rw [ge] at h2
    left; exact le_antisymm h h2
  intro h
  rcases h with h | h
  · rw [h]; exact le_refl
  exact lt_imp_le h

theorem lt_trichotomy {m n : MyNat} :
m.lt n ∨ m = n ∨ n.lt m := by
  have h := lt_or_ge (m := m) (n := n)
  rcases h with h | h
  · left; exact h
  rw [ge, le_iff_eq_or_lt] at h
  right;
  rcases h with h | h
  · left; symm; exact h
  right; exact h

theorem le_iff_add {m n : MyNat} :
m.le n ↔ ∃ c, m.add c = n := by
  constructor
  · intro h
    induction h with
    | refl =>
      use zero
      rw [add]
    | step n h1 h2 =>
      rcases h2 with ⟨c, h2⟩
      use succ c
      rw [add, h2]
  intro h
  rcases h with ⟨c, h⟩
  induction' c with c hc generalizing n
  · rw [add] at h
    rw [h]; exact le_refl
  have h2 := hc (n := n.pred)
  cases n
  case zero =>
    rw [add] at h
    exfalso; exact succ_ne_zero h
  case succ n =>
    rw [pred] at h2
    rw [add, succ_inj] at h
    exact le_trans (h2 h) le_succ
