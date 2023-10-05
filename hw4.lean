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
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r


--4a
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 2 * (7 * k + 1) + 1 := by ring 


--4b
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + 3 * b + a + 1
  calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + 3 * b + a + 1) + 1 := by ring

--4c
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even, Odd] at *
  obtain ⟨k,hk⟩ := hn
  use 2*k^2 + 2*k - 3
  calc
    n^2 + 2*n - 5 = (k+k)^2 + 2*(k+k) - 5 := by rw [hk]
    _ = 2 * (2*k^2 + 2*k - 3) + 1 := by ring

--4d
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  dsimp [Even] at *
  obtain hbc | hbc := Int.even_or_odd (b - c)
  . right
    right
    obtain ⟨x, hbc⟩ := hbc
    use x
    calc
      b - c = 2 * x := by rw[hbc]
      _ = x + x := by ring 
  . obtain hac | hac := Int.even_or_odd (a + c)
    . right
      left
      obtain ⟨x, hac⟩ := hac
      use x
      calc
        a + c = 2 * x := by rw[hac]
        _ = x + x := by ring
    . left
      obtain ⟨x, hac⟩ := hac
      obtain ⟨y, hbc⟩ := hbc
      use (x - y - c)
      calc
        a - b = (a + c) - (b - c) - 2 * c := by ring
        _ = (2 * x + 1) - (b - c) - 2 * c := by rw[hac]
        _ = (2 * x + 1) - (2 * y + 1) - 2 * c := by rw[hbc]
        _ = 2 * x - 2 * y - 2 * c := by ring
        _ = 2 * (x - y - c) := by ring
        _ = (x - y - c) + (x -y -c) := by ring



-- 5a
  example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  obtain ha | ha := h ((a+b)/2)
  . calc
      b =  2 * ( (a + b) / 2 ) - a := by ring
      _ ≥ 2 * a - a := by rel [ha]
      _ = a := by ring
  . calc
      a =  2 * ( (a + b) / 2 ) - b := by ring
      _ ≤  2 * b - b := by rel [ha]
      _ = b := by ring


-- 5b
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  dsimp
  use -3
  intro x y h
  have hl := calc
    (x+y)^2 ≤ (x+y)^2 + (x-y)^2 := by extra
    _ = 2 * (x^2 + y^2) := by ring
    _ ≤ 2 * 4 := by rel [h]
    _ ≤ 3 ^ 2 := by numbers
  have hr : (0:ℝ) ≤ 3 := by numbers
  exact And.left (abs_le_of_sq_le_sq' hl hr)


-- 5c
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  obtain ⟨x, hx⟩ := hn 3 (by numbers) (by numbers)
  obtain ⟨y, hy⟩ := hn 5 (by numbers) (by numbers)
  use 2*x - 3*y
  calc
    n = 10*n - 9*n := by ring
    _ = 10*(3*x) - 9*(5*y) :=  by nth_rw 1 [hx]; rw[hy]
    _ = 15*(2*x - 3*y) := by ring

--5d
example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 7
  intro x hx
  calc
    x ^ 3 + 3 * x  = x * ( x ^ 2  + 3 ) := by ring
    _ ≥ 7 * ( x ^ 2  + 3 ) := by rel[hx]
    _ = 7 * x ^ 2 + 21 := by ring  
    _ = 7 * x ^ 2 + 12 + 9 := by ring
    _ ≥ 7 * x ^ 2 + 12 := by extra

--6a
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have h1 : (x + 3) * (x - 2) = 0 := by
      calc
        (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
        _ = 0 := by rw [h]
    have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
    cases h2 with
    | inl left => 
      left
      calc
        x = x + 3 - 3 := by ring
        _ = 0 - 3 := by rw [left]
        _ = -3 := by numbers
    | inr right =>
      right
      calc
        x = x - 2 + 2 := by ring
        _ = 0 + 2 := by rw [right]
        _ = 2 := by numbers
  · intro h4
    cases h4 with
    | inl left =>
      calc
        x ^ 2 + x - 6 = (-3) ^ 2 + (-3) - 6 := by rw [left]
        _ = 0 := by numbers
    | inr right =>
      calc
        x ^ 2 + x - 6 = 2 ^ 2 + 2 - 6 := by rw [right]
        _ = 0 := by numbers


--6b 
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h1
    have hsq : (2 * a - 5) ^ 2 ≤ 1 ^ 2 := by
      calc
        (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
        _ ≤ 4 * (-1) + 5 := by rel [h1]
        _ = 1 ^ 2 := by numbers
    have hasq : (-1 ≤ 2 * a - 5) ∧ (2 * a - 5 ≤ 1) := by
      apply abs_le_of_sq_le_sq' hsq
      numbers
    obtain ⟨hn1, h1⟩ := hasq
    have h2 : 2 * 2 ≤ 2 * a := by addarith [hn1]
    cancel 2 at h2
    have h3 : 2 * 3 ≥ 2 * a := by addarith [h1]
    cancel 2 at h3
    have hc := le_or_succ_le a 2
    cases hc with
    | inl left =>
      left
      apply le_antisymm left h2
    | inr right =>
      right
      apply le_antisymm h3 right
  · intro hc2
    cases hc2 with
    | inl left =>
      extra
    | inr right =>
      extra