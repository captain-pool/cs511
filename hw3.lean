import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- 4a
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt2' : 0 < x * (-t) := by calc
        0 < -x * t := by addarith[hxt]
        _ = x * -t := by ring
    have hx' : 0 ≤ x := by addarith [hx]
    cancel x at hxt2'
    have t': t < 0 := by addarith[hxt2']
    apply ne_of_lt
    apply t'

-- 4b
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

-- 4c
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2 
  constructor
  . calc
    p = (p + p) / 2 := by ring
    _ < (p + q) / 2 := by addarith[h]
  . calc
    (p + q) / 2 < (q + q) / 2 := by addarith[h]
    _ = q := by ring



-- 5(a)
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have H := le_or_gt x 0
  obtain hxle0 | hxgt0 := H
  · use x - 1
    have hneg : -x ≥ 0 := by addarith[hxle0]
    calc
      (x - 1) ^ 2 = x^2 -2 * x + 1 := by ring
      _ = (-x) ^ 2 - 2 * x + 1 := by ring
      _ ≥ (0) ^ 2 - 2 * x + 1 := by rel [hneg]
      _ = 2 * (-x) + 1 := by ring 
      _ ≥ 2 * 0 + 1 := by rel[hneg]
      _ = 1 := by ring
      _ > x := by addarith[hxle0]
  · use x + 1
    calc
      (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by ring
      _ ≥ (0) ^ 2 + 2 * x + 1 := by rel [hxgt0] 
      _ = 2 * x + 1 := by ring
      _ > 2 * x := by extra 
      _ = x + x := by ring
      _ ≥ 0 + x := by rel [hxgt0]
      _ = x := by ring 

 
-- 5(b)
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hx⟩ := h
  intro ht
  rw [ht] at hx
  apply ne_of_lt hx
  ring

-- 5(c)
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  obtain hale2 | hagt2 := le_or_gt a 2
  . apply ne_of_lt
    calc
      m = 2 * a := by rw[ha]
      _ ≤ 2 * 2 := by rel[hale2]
      _ < 5 := by ring

  . apply ne_of_gt
    have hage3: a ≥ 3 := by addarith[hagt2]
    calc
      m = 2 * a := by rw[ha]
      _ ≥ 2 * 3 := by rel[hage3]
      _ > 5 := by ring