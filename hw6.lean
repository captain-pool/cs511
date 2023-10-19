import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

--4a
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intro hxP
    obtain ⟨x, hxP⟩ := hxP
    use x
    obtain h_left_right := h x
    rw [h_left_right] at hxP
    apply hxP
  . intro hxQ
    obtain ⟨x, hxQ⟩ := hxQ
    use x
    obtain h_left_right := h x
    rw[←h_left_right] at hxQ
    apply hxQ

--4b
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intro h_exy  
    obtain ⟨x, h_ey⟩ := h_exy
    obtain ⟨y, h_e⟩ := h_ey
    use y
    use x
    apply h_e
  . intro h_eyx  
    obtain ⟨y, h_ex⟩ := h_eyx
    obtain ⟨x, h_e⟩ := h_ex
    use x
    use y
    apply h_e

--4c
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  . intro hPxy
    intro y
    intro x
    apply hPxy x y
  . intro h
    intro y
    intro x
    apply  h x y

--4d
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intro h
    obtain ⟨heP, hQ⟩ := h
    obtain ⟨x, hP⟩ := heP 
    use x
    constructor
    apply hP
    apply hQ

  . intro h
    obtain ⟨x, hPxQ⟩ := h
    constructor
    use x
    apply And.left hPxQ
    apply And.right hPxQ

--5a
def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

theorem superpowered_one : Superpowered 1 := by
 intro n
 conv => ring_nf
 apply prime_two



lemma tribalanced_zero : Tribalanced 0 := by
 intro n
 simp
 numbers

theorem not_two_tribalanced : ¬ Tribalanced 2 := by
  intro h
  have tltt := h 3
  numbers at tltt

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h1 : Tribalanced 1
  · use 1
    constructor
    apply h1
    numbers
    apply not_two_tribalanced
  · use 0
    constructor
    apply tribalanced_zero
    numbers
    apply h1


--5b
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  . apply superpowered_one
  . intro h
    have h_4294967297_prime : Prime ((1+1) ^ (1+1) ^ 5 + 1) := h 5
    conv at h_4294967297_prime => numbers
    have h_4294967297_not_prime : ¬ Prime 4294967297 := by
      apply not_prime 641 6700417
      numbers
      numbers
      numbers
    contradiction

