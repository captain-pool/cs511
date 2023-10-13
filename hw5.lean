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

-- 4a

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h
    constructor
    · use 9 * a
      rw [ha]
      ring
    · use 7 * a
      rw [ha]
      ring
  · intro h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    use (4 * b - 3 * a)
    calc
      n = 28 * n - 27 * n := by ring
      _ = 28 * (9 * b) - 27 * n := by rw [hb]
      _ = 28 * (9 * b) - 27 * (7 * a) := by rw [ha]
      _ = 63 * (4 * b - 3 * a) := by ring

-- 4b
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  . intro h
    obtain hle0 | hgt0 := le_or_gt k 0
    · left 
      simp at hle0
      apply hle0
    · right 
      obtain hle1 | hgt1 := le_or_gt k 1
      · left
        have hgt1 : k ≥ 1 := by addarith [hgt0] 
        apply le_antisymm hle1 hgt1 
      · right
        have hgt2 : k ≥ 2 := by addarith [hgt1] 
        have hlt3:  k ^ 2 < 3 ^ 2
        {
          calc
            k ^ 2 ≤ 6 := by rel[h]
            _ < 6 + 3 := by extra
            _ = 3 ^ 2 := by numbers
        }
        cancel 2 at hlt3
        addarith[hgt2, hlt3]
  . intro h
    obtain h0 | h12 := h
    . calc
      k ^ 2 = k * k := by ring
      _ = 0 * k := by rw[h0]
      _ ≤ 0 := by ring
      _ ≤ 6 := by addarith 
    . obtain h1 | h2 := h12
      . calc
        k ^ 2 = k * k := by ring
        _ = 1 * 1 := by rw[h1]
        _ ≤ 1 := by ring
        _ ≤ 6 := by addarith 
      . calc
        k ^ 2 = k * k := by ring
        _ = 2 * 2 := by rw[h2]
        _ ≤ 4 := by ring
        _ ≤ 6 := by addarith 



-- 5a



-- 5b
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  . addarith
  . intro y hy
    calc
      y = ((4*y - 3) + 3) / 4 := by ring
      _ = (9 + 3) / 4 := by rw[hy]
      _ = 3 := by ring

-- 5c
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  · simp
  · simp
    intro n
    intro hn
    have hge0 : n ≥ 0 := by extra
    have hle0 := by apply hn 0
    apply le_antisymm hle0 hge0

-- 6a
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp
  intro m hmp
  have hplt0 : 0 < p := by extra
  have hmge1 : m ≥ 1  := Nat.pos_of_dvd_of_pos hmp hplt0
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le hmge1
  · left
    addarith [hm]
  . 
    have hmgep : m ≤ p := Nat.le_of_dvd hplt0 hmp
    obtain hpem | hpgm : m = p ∨ m < p := eq_or_lt_of_le hmgep
    . right
      apply hpem
    . have h2 : ¬m ∣ p := by 
      {
        apply H m
        apply hm_left 
        apply hpgm
      }
      contradiction



-- 6b
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain hale2 | hagt2 := le_or_gt a 2
  . obtain hble1 | hbgt1 := le_or_gt b 1
    . 
      have hc: c ^ 2 < 3 ^ 2 := by  
      {
        calc 
          c ^ 2 = a ^ 2 + b ^ 2 := by rw[h_pyth]
          _ ≤  2 ^ 2 + 1 ^ 2 := by rel[hale2, hble1]
          _ = 4 + 1 := by ring
          _ < 5 + 4 := by extra
          _ = 3 ^ 2 := by ring
      } 
      have hc': c < 3 := by cancel 2 at hc
      interval_cases a
      . interval_cases b 
        . interval_cases c 
          . contradiction 
          . contradiction 
      . interval_cases b 
        . interval_cases c 
          . contradiction 
          . contradiction
    . have hbc: b ^ 2 < c ^ 2 := by  
      {
        calc 
          b ^ 2 <  b ^ 2 + a ^ 2 := by extra
          _ = c ^ 2 := by addarith[h_pyth]
      }
      have hbltc: b < c := by cancel 2 at hbc
      have hbge2: b ≥ 2 := by addarith[hbgt1]
      have hbc': c ≥ b + 1 := by addarith[hbltc]
      have hbcsq : c ^ 2 < (b + 1) ^ 2 := by 
      {
        calc
          c ^ 2 = a ^ 2 + b ^ 2 := by rw[h_pyth]
          _ ≤ 2 ^ 2 + b ^ 2 := by rel[hale2]
          _ = b ^ 2 + 2 * 2 := by ring 
          _ ≤ b ^ 2 + 2 * b := by rel[hbge2]
          _ < b ^ 2 + 2 * b + 1 := by extra
          _ = (b + 1) ^ 2 := by ring
      } 
      have : ¬ (c ≥ b + 1) := by 
      { 
        cancel 2 at hbcsq
        addarith[hbcsq]
      }
      contradiction
  . apply hagt2


-- 6c
  example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  have ha := le_or_lt y x
  cases ha with
  | inl h_ylex => apply h_ylex
  | inr h_ygtx =>
    have h_contr_1 : x ^ n < y ^ n := by rel [h_ygtx]
    have h_contr_2 := not_le_of_lt h_contr_1
    contradiction

-- 6d
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨hp, hdiv⟩ := h
  obtain h | h := lt_or_eq_of_le hp
  · right
    have h_not_even : ¬Nat.Even p := by
      intro h_even 
      obtain ⟨a, ha⟩ := h_even
      have h2 : 2∣p := by 
        use a
        rw [ha]
      obtain h_cont|h_cont := hdiv 2 h2
      . contradiction
      . rw [h_cont] at h
        have h_cont': 0 < 0 := by addarith[h]
        contradiction
    obtain h_is_even | h_p_is_odd := Nat.even_or_odd p
    . contradiction
    . apply h_p_is_odd
  · left
    rw[h]