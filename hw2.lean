import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

theorem five_a {p q : Prop} : (¬p ∧ ¬q)  → ¬(p ∨ q) := by
intro h
have h_contr: p ∨ q → ⊥ := by
{
  intro hpq
  obtain ⟨hnp, hnq⟩ := h
  have p_bot: p → ⊥ := by
  {
    intro hp
    show False; apply hnp hp
  }
  have q_bot: q → ⊥ := by {
    intro hq
    show False; apply hnq hq
  }
  apply Or.elim hpq p_bot q_bot
}
apply h_contr


theorem five_b {p q : Prop} : ¬ p ∨ ¬ q → ¬(p ∧ q) := by
intro h
have h1: ¬ p → ¬(p∧q) := by
{
  intro hnp

  have npq: ¬ (p ∧ q) := by {
    intro hpq
    obtain ⟨hp, hq⟩ := hpq
    show False; apply hnp hp
  }
  apply npq
}
have h2: ¬ q → ¬(p∧q) := by
{
  intro hnq
  have npq: ¬ (p ∧ q) := by {
    intro hpq
    obtain ⟨hp, hq⟩ := hpq
    show False; apply hnq hq
  }
  apply npq
}
apply Or.elim h h1 h2



  theorem six_a {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := by
  calc
    x = x + 3 - 3 := by ring
    _ ≥ 2 * y - 3 := by rel [h1]
    _ ≥ 2 * 1 - 3 := by rel [h2]
    _ = -1 := by numbers

theorem six_b {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = (a + (a + 2 * b)) / 2:= by ring
    _ ≥  (a + 4) / 2 := by rel [h2]
    _ ≥ (3 + 4) / 2 := by rel [h1]
    _ ≥ 3 := by numbers

theorem six_c {x : ℤ} (h1 : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x
      = x * ((x - 4)^2 - 14) := by ring
    _ ≥ 9 * ((9 - 4)^2 - 14) := by rel [h1]
    _ ≥ 3 := by numbers