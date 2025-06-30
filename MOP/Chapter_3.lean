-- Codings in Chapter 3

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Basic

#check Even
-- Making a definition in Lean
-- def Odd (a : ℤ) : Prop := ∃ k : ℤ, a = 2 * k + 1
-- def Even (a : ℤ) : Prop := ∃ k, a = 2 * k

example : Odd (7:ℤ) := by
  dsimp [Odd]
  use 3
  norm_num


example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  norm_num

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 14 * k + 7 - 4 := by ring
    _ = 14 * k + 3 := by ring
    _ = 14 * k + 2 + 1 := by ring
    _ = 2 * (7 * k + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + 3 * b + 1
  calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 4 * a * b + 2 * (a + b) + 1 + 4 * b + 2 := by ring
    _ = 4 * a * b + 2 * a + 6 * b + 3 := by ring
    _ = 2 * a * (2 * b + 1) + 2 * (3 * b + 1) + 1 := by ring
    _ = 2 * (2 * a * b + a + 3 * b + 1) + 1 := by ring

-- Some problems occurred for Even (). Using self-defined isEven () instead.
example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨a, ha⟩ := hm
  use 3 * a - 1
  exact calc
    3 * m - 5 = 3 * (2 * a + 1) - 5 := by rw [ha]
    _ = 6 * a - 2 := by ring
    _ = 2 * (3 * a - 1) := by ring
    _ = 3 * a - 1 + (3 * a - 1) := by ring

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    rw [hx]; ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    rw [hx]; ring

-- 3.1 Exercises
example : Odd (-9 : ℤ) := by
  dsimp [Odd]
  use -5
  norm_num

example : Even (26 : ℤ) := by
  dsimp [Even]
  use 13
  norm_num

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨x, hx⟩ := hm
  obtain ⟨y, hy⟩ := hn
  use y + x
  rw [hy, hx]
  ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨x, hx⟩ := hp
  obtain ⟨y, hy⟩ := hq
  use x - y - 2
  rw [hx, hy]
  ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use 3 * x + y - 1
  rw [hx, hy]
  ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨x, hx⟩ := hr
  obtain ⟨y, hy⟩ := hs
  use 3 * x - 5 * y - 1
  rw [hx, hy]
  ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨a, ha⟩ := hx
  use 4 * a ^ 3 + 6 * a ^ 2 + 3 * a
  rw [ha]
  ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨x, hx⟩ := hn
  use 2 * x ^ 2 - x
  rw [hx]
  ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨x, hx⟩ := ha
  use 2 * x ^ 2 + 4 * x - 1
  rw [hx]
  ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨x, hx⟩ := hp
  use 2 * x ^ 2 + 5 * x - 1
  rw [hx]
  ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + b
  rw [ha, hb]
  ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain hn1 | hn2 := Int.even_or_odd n
  -- Case 1: n is even
  . obtain ⟨x, hx1⟩ := hn1
    -- Now we need to prove that 3 * (2*x)^2 + 3 * (2*x) - 1 is odd
    use 6 * x ^ 2 + 3 * x - 1
    rw [hx1]
    ring
  -- Case 2: n is odd
  . obtain ⟨x, hx2⟩ := hn2
    -- Now we need to prove that 3 * (2*x + 1)^2 + 3 * (2*x + 1) - 1 is odd
    use 6 * x ^ 2 + 9 * x + 2
    rw [hx2]
    ring

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  dsimp [Odd]
  by_cases h : Odd n
  · use n
    exact ⟨le_rfl, h⟩
  · -- h : ¬Odd n ⇒ Even n
    have : Even n := by
      obtain he | ho := Int.even_or_odd n
      · exact he
      · contradiction
    obtain ⟨k, hk⟩ := this
    use n + 1
    constructor
    · linarith
    · use k
      rw [hk]
      ring

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain h₁ | h₁ := Int.even_or_odd (a - b)
  · exact Or.inl h₁
  obtain h₂ | h₂ := Int.even_or_odd (a + c)
  · exact Or.inr (Or.inl h₂)
  obtain h₃ | h₃ := Int.even_or_odd (b - c)
  · exact Or.inr (Or.inr h₃)

  obtain ⟨k1, hk1⟩ := h₁
  obtain ⟨k2, hk2⟩ := h₂
  obtain ⟨k3, hk3⟩ := h₃

  have : 2 * a = (a - b) + (a + c) + (b - c) := by ring
  rw [hk1, hk2, hk3] at this

  let k := k1 + k2 + k3
  have odd2a : Odd (2 * a) := ⟨k, by rw [this]; ring⟩

  exact Int.not_odd_even _ odd2a


-- 3.2
example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8

example : (-2 : ℤ) ∣ 6 := by
  dsimp [(· ∣ ·)]
  use -3
  norm_num

example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring

example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  sorry

example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  sorry

open Int

lemma Int.not_dvd_of_exists_lt_and_lt (a b : ℤ)
    (h : ∃ q : ℤ, b * q < a ∧ a < b * (q + 1)) :
    ¬ b ∣ a := by
  sorry

example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · norm_num -- show `5 * 2 < 12`
  · norm_num -- show `12 < 5 * (2 + 1)`

-- This part is incomplete by the time uploaded.
example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have hpos : 0 < a * k := by rw [hk]; exact hb
  have ha : 0 < a ∨ a = 0 := Nat.lt_or_eq_of_le (Nat.zero_le a)
  cases ha with
  | inl ha =>
    have hk1 : 1 ≤ k := Nat.le_of_mul_le_mul_left (by linarith [hpos]) ha
    calc
      a = a * 1 := by ring
      _ ≤ a * k := Nat.mul_le_mul_left a hk1
      _ = b := by rw [hk]
  | inr ha =>
    rw [ha, zero_mul] at hk
    rw [hk] at hb
    exact (Nat.lt_irrefl 0 hb).elim
