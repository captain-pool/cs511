import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p


-- mcbeth 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
  a = 2 * 3 + 5 := by rw [h1,h2]
  _ = 11 := by ring

-- mcbeth 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
  x = (x + 4) - 4 := by ring
  _ = 2 - 4 := by rw[h1]
  _ = -2 := by ring

--mcbeth 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
  a = (a - 5 * b) + 5 * b := by ring
  _ = 4 + 5 * b := by rw[h1]
  _ = 4 + 5 * b + 10 - 10 := by ring
  _ = 4 + 5 * b + 5 * 2 - 10 := by ring
  _ = -6 + 5 * (b + 2) := by ring
  _ = -6 + 5 * 3 := by rw[h2]
  _= 9 := by ring


-- lec slide 2 page 21
theorem slide2_page21 {p q r : Prop} (h: p ∧ q → r) : p → (q → r) := by
intro hp
intro hq
have hpq: p ∧ q := by apply And.intro hp hq
apply h hpq

theorem slide2_page23 {p q r : Prop} (h: p → ( q → r )) : ( p → q ) → ( p → r ) := by
  intro hpq
  intro hp
  have hq : q := by apply hpq hp
  apply h hp hq

theorem slide2_page24 {p q r : Prop} (h1: (p∧¬q)→ r) (h2: ¬r) (h3: p) : q := by
  have hnnq: ¬¬q := by
    intro hnq
    have hpnq : p ∧ ¬q := by apply And.intro h3 hnq
    have hr : r := by apply h1 hpnq
    contradiction
  apply notnotE hnnq