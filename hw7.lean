import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use



-- Prob 4a
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n ^ 2 ≥ 2 ^ 2 := by rel [hn] 
      _ > 2 := by numbers


-- Prob 4b
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro hl
    by_cases hr : P ∧ ¬Q
    · apply hr
    · rw [not_and_or] at hr
      rw [not_not] at hr
      have h' : P → Q := by
        intro hp
        cases hr with
        | inl l => contradiction
        | inr r => apply r
      contradiction
  · intro hr
    obtain ⟨hp, _⟩ := hr
    intro h'
    have hq : Q := by apply h' hp
    contradiction

-- Prob 5a
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  intro h
  use k
  constructor
  · apply hk
  · constructor
    · apply hk1
    · apply hkp

-- Prob 5b
example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have h : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro h
    have hprime := prime_test hp2 h
    contradiction
  push_neg at h
  apply h