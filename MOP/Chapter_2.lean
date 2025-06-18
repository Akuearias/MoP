-- Here are proofs mentioned in Chapter 2.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Basic

open Int
-- addarith -> linarith
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by linarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring

-- numbers -> norm_num
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1]
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by norm_num
  linarith [h3]


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by linarith [h1] -- justify with one tactic
  have h4 : r ≤ 3 - s := by linarith [h2] -- justify with one tactic
  calc
    r = (r + r) / 2 := by ring -- justify with one tactic
    _ ≤ (3 - s + (3 + s)) / 2 := by rel [h3, h4] -- justify with one tactic
    _ = 3 := by ring -- justify with one tactic

-- cancel is no longer available in Lean 4. We need to modify the sample code thoroughly,
-- like the one below.
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  -- We know t is non-zero because t ≥ 1.
  have h3 : t ≠ 0 := by linarith

  -- Start with the given equation
  have h_eq_tt : t * t = 3 * t := by
    rw [pow_two t] at h1
    exact h1

  -- Now, divide both sides by t (which we know is non-zero)
  have h4 : t = 3 := by
    -- Apply the division to both sides.
    -- This uses the fact that if a*c = b*c and c ≠ 0, then a = b.
    apply (mul_left_inj' h3).mp -- `mul_left_inj'` is the lemma we need for cancellation
    exact h_eq_tt

  -- Now that we have t = 3, we can prove t ≥ 2
  rw [h4]
  norm_num

example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 : a ^ 2 ≥ 1 :=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 0 + 1 := by nlinarith -- b^2 >= 0 is a basic property, nlinarith can handle this
    _ = 1 := by ring
  -- Now we have a^2 >= 1 and a >= 0. We want to show a >= 1.
  -- nlinarith can usually combine these.
  nlinarith [h3, h2]

example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have h1 : x ≤ -1 := by linarith [hx]
  calc
    y ≥ 3 - 2 * x := by linarith [hy]
    _ ≥ 3 + 2 := by linarith [h1]
    _ ≥ 5 := by norm_num
    _ > 3 := by norm_num

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : 0 ≤ b + a := by linarith [h1]
  have h4 : 0 ≤ b - a := by linarith [h2]
  have h5 : 0 ≤ (b + a) * (b - a) := by exact mul_nonneg h3 h4
  calc
    a ^ 2 ≤ a ^ 2 + (b + a) * (b - a) := by linarith [h5]
    _ = a ^ 2 + b ^ 2 - a ^ 2 := by ring
    _ = b ^ 2 := by ring

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h1 : 0 ≤ b - a := by linarith [h]
  have h2 : ((b - a) * ((b - a) ^ 2 + 3 * (b + a) ^ 2)) / 4 ≥ 0 := by
    have h_inner_nonneg : 0 ≤ (b - a) ^ 2 + 3 * (b + a) ^ 2 := by
      apply add_nonneg
      apply pow_two_nonneg
      apply mul_nonneg
      norm_num
      apply pow_two_nonneg
    apply div_nonneg
    apply mul_nonneg h1 h_inner_nonneg
    norm_num
  calc
    a ^ 3 ≤ a ^ 3 + ((b - a) * ((b - a) ^ 2 + 3 * (b + a) ^ 2)) / 4 := by linarith [h2]
    _ = b ^ 3 := by ring

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 : x ^ 2 - 4 = 0 := by linarith [h1]
  have h4 : (x + 2) * (x - 2) = 0 := by
   rw [← h3]
   ring_nf
  have h5 : x + 2 ≠ 0 := by linarith [h2]
  have h6 : x * (x + 2) = 2 * (x + 2) := by
    calc
      x * (x + 2) = x ^ 2 + 2 * x := by ring
      _ = 4 + 2 * x := by rw [← h1]
      _ = 2 * (x + 2) := by ring

  exact mul_right_cancel₀ h5 h6

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1 : n ^ 2 - 4 * n + 4 = 0 := by linarith [hn]
  have h2 : n ^ 2 - 4 * n + 4 = (n - 2) ^ 2 := by ring

  have h3 : (n - 2) ^ 2 = 0 := by
    calc
      (n - 2) ^ 2 = n ^ 2 - 4 * n + 4 := by exact h2.symm
      _ = 0 := by exact h1

  have h4 : n - 2 = 0 := by
    exact sq_eq_zero_iff.mp h3

  exact eq_of_sub_eq_zero h4

example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have h3 : 0 < x := by linarith [h2]
  have h4 : y = 1 / x := by
    field_simp [h3.ne']
    rw [← h]
    ring
  rw [h4]

  apply le_of_mul_le_mul_right _ h3
  calc
    (1 / x) * x = 1 := by
      field_simp [ne_of_gt h3]
    _ ≤ 1 * x := by
      rw [one_mul]
      exact h2

-- numbers -> nlinarith
example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by nlinarith

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  calc
    y ^ 2 + 1 ≥ 0 + 1 := by
      apply add_le_add_right
      exact sq_nonneg y
    _ = 1 := by norm_num
    _ > 0 := by norm_num

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  · calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by nlinarith
      _ = 0 := h1
  · exact sq_nonneg a

example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  have h1 : m = 4 := by linarith [hm]
  calc
    3 * m = 3 * 4 := by rw [h1]
    _ = 12 := by ring
    _ ≠ 6 := by nlinarith

example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  have h3 : s ≤ -2 := by linarith [h1]
  have h4 : s ≥ -2 := by linarith [h2]
  calc
    s = -2 := by linarith [h3, h4]

example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

lemma le_or_succ_le (a b : ℕ) : a ≤ b ∨ b + 1 ≤ a :=
  match le_or_gt a b with
  | Or.inl hab => Or.inl hab
  | Or.inr hba =>
      have : b + 1 ≤ a := Nat.succ_le_of_lt hba
      Or.inr (Nat.succ_le_of_lt hba)

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by nlinarith
  apply ne_of_gt
  calc
    n ^ 2 ≥ 2 ^ 2 := by rel [hn]
    _ = 4 := by nlinarith
    _ > 2 := by nlinarith

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by nlinarith


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  cases h2 with
  | inl h => exact Or.inl (eq_of_sub_eq_zero h)
  | inr h => exact Or.inr (eq_of_sub_eq_zero h)

-- The code below is buggy.

/- example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := int_le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by linarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]
-/

example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring

theorem abs_le_of_sq_le_sq_2 {x y : ℚ} (h1 : x ^ 2 ≤ y ^ 2) (h2 : 0 ≤ y) :
    -y ≤ x ∧ x ≤ y :=
  abs_le.mp (abs_le_of_sq_le_sq h1 h2)

example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3 := by
    apply abs_le_of_sq_le_sq_2
    · calc
        p ^ 2 ≤ 9 := by linarith [hp]
        _ = 3 ^ 2 := by linarith
    · exact by linarith
  exact le_trans (by linarith) hp'.left

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by linarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · linarith [h2]

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by linarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by linarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb

example {a b : ℝ} (h : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have ha : a ^ 2 = 0 := by
    apply le_antisymm
    · calc
        a ^ 2 ≤ a ^ 2 + b ^ 2 := by linarith [sq_nonneg b]
        _ = 0 := h
    · exact sq_nonneg a
  have hb : b ^ 2 = 0 := by
    apply le_antisymm
    · calc
        b ^ 2 ≤ a ^ 2 + b ^ 2 := by linarith [sq_nonneg a]
        _ = 0 := h
    · exact sq_nonneg b
  exact ⟨sq_eq_zero_iff.mp ha, sq_eq_zero_iff.mp hb⟩

example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * a + b = a + a + b := by ring
    _ ≤ 1 + 3 := by linarith [h1, h2]
    _ ≤ 4 := by linarith

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc
   2 * r = r + s + r - s := by ring
   _ ≤ 1 + 5 := by linarith [h1, h2]
   _ ≤ 6 := by linarith

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  calc
    m ≤ n - 5 := by linarith [h2]
    _ ≤ 8 - 5 := by linarith [h1]
    _ ≤ 3 := by linarith

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have h1 : p ≥ 7 := by linarith [hp]
  constructor
  · calc
      p ^ 2 = p * p := by ring
      _ ≥ 7 * 7 := by
        apply mul_le_mul
        . exact h1.le
        . exact h1.le
        . norm_num
        . exact le_trans (by norm_num : (0 : ℤ) ≤ 7) h1.le
      _ ≥ 49 := by linarith
  · exact h1

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  apply And.intro
  have h1 : a ≥ 6 := by linarith [h]
  exact h1
  calc
    3 * a ≥ 3 * 6 := by linarith
    _ ≥ 18 := by linarith
    _ ≥ 10 := by linarith

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have h3 : x + 2 * y = (x + y) + y := by ring
  rw [h3] at h2
  rw [h1] at h2
  have h4 : y = 2 := by
    calc
      y = y + 5 - 5 := by ring
      _ = (5 + y) - 5 := by ring
      _ = 7 - 5 := by rw [h2]
      _ = 2 := by linarith

  have h5 : x = 3 := by
    have dummy : x + 2 = 5 := by
      rw [h4] at h1
      exact h1
    calc
      x = x + 2 - 2 := by ring
      _ = (x + 2) - 2 := by ring
      _ = 5 - 2 := by rw [dummy]
      _ = 3 := by linarith

  exact ⟨h5, h4⟩

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) : a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
    have h3 : a * (b - 1) = 0 := by
      calc
        a * (b - 1) = a * b - a * 1 := by rw [mul_sub]
        _ = a - a := by rw [mul_one, h1]
        _ = 0 := by rw [sub_self]
    have h4 : b * (a - 1) = 0 := by
      calc
        b * (a - 1) = b * a - b * 1 := by rw [mul_sub]
        _ = a * b - b * 1 := by rw [mul_comm b a]
        _ = a * b - b := by linarith
        _ = b - b := by rw [h2]
        _ = 0 := by rw [sub_self]
    cases eq_zero_or_eq_zero_of_mul_eq_zero h3 with
    | inl ha => -- a = 0
      left
      constructor
      · exact ha
      · rw [ha, zero_mul] at h2
        rw [eq_comm] at h2
        exact h2
    | inr hb => -- b - 1 = 0, so b = 1
      cases eq_zero_or_eq_zero_of_mul_eq_zero h4 with
      | inl hb' => -- b = 0
        have : b = 1 := by rw [sub_eq_zero] at hb; exact hb
        rw [hb'] at this
        have contra : (0 : ℝ) = (1 : ℝ) := this
        apply absurd contra zero_ne_one
      | inr ha => -- a - 1 = 0, so a = 1
        right
        constructor
        · rw [sub_eq_zero] at ha; exact ha
        · rw [sub_eq_zero] at hb; exact hb

-- 2.5
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by
      have : b ^ 2 ≥ 0 := sq_nonneg b
      linarith

example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h

  have H := le_or_gt x 0
  obtain hx_le_0 | hx_gt_0 := H

  -- Case 1: x ≤ 0
  case inl =>
    have hx_lt_0 : x < 0 := by
      by_cases x_eq_0 : x = 0
      · rw [x_eq_0] at hxt
        simp at hxt -- hxt becomes `0 < 0`, which is `False`.
        -- Goal is solved automatically by Lean.
      · -- If x is not 0, and we know x ≤ 0, then x must be < 0.
        exact lt_of_le_of_ne hx_le_0 x_eq_0

    -- Goal: t > 0
    -- Proof by contradiction: Assume ¬(t > 0) i.e., t ≤ 0 and derive a contradiction.
    have t_pos : t > 0 := by
      by_contra h_not_t_gt_0 -- h_not_t_gt_0 : ¬ (t > 0)
      -- Convert `¬ (t > 0)` to `t ≤ 0` for `lt_of_le_of_ne`.
      have ht_le_0 : t ≤ 0 := le_of_not_gt h_not_t_gt_0

      -- Subcase: t = 0
      by_cases t_eq_0 : t = 0
      · rw [t_eq_0] at hxt
        simp at hxt -- `x * 0 < 0` simplifies to `0 < 0`.
        -- Goal is solved automatically.
      · -- Subcase: t < 0 (since t ≤ 0 and t ≠ 0)
        have ht_lt_0 : t < 0 := lt_of_le_of_ne ht_le_0 t_eq_0
        -- We now have `hx_lt_0 : x < 0` and `ht_lt_0 : t < 0`.
        -- The product of two negative numbers is positive.
        have x_mul_t_pos : 0 < x * t := mul_pos_of_neg_of_neg hx_lt_0 ht_lt_0
        -- We have `x_mul_t_pos : 0 < x * t` and `hxt : x * t < 0`. This is a contradiction.
        linarith [x_mul_t_pos, hxt]

    -- Since `t > 0`, it means `t` cannot be `0`.
    exact ne_of_gt t_pos

  -- Case 2: x > 0
  case inr =>
    -- Goal: t < 0
    -- Proof by contradiction: Assume ¬(t < 0) i.e., t ≥ 0 and derive a contradiction.
    have t_neg : t < 0 := by
      by_contra h_not_t_lt_0 -- h_not_t_lt_0 : ¬ (t < 0)
      -- Convert `¬ (t < 0)` to `t ≥ 0` for `lt_of_le_of_ne'`.
      have ht_ge_0 : t ≥ 0 := (not_lt.mp h_not_t_lt_0)

      -- Subcase: t = 0
      by_cases t_eq_0 : t = 0
      · rw [t_eq_0] at hxt
        simp at hxt -- `x * 0 < 0` simplifies to `0 < 0`.
        -- Goal is solved automatically.
      · -- Subcase: t > 0 (since t ≥ 0 and t ≠ 0)
        have ht_gt_0 : t > 0 := lt_of_le_of_ne' ht_ge_0 t_eq_0
        -- We now have `hx_gt_0 : x > 0` and `ht_gt_0 : t > 0`.
        -- The product of two positive numbers is positive.
        have x_mul_t_pos : 0 < x * t := mul_pos hx_gt_0 ht_gt_0
        -- We have `x_mul_t_pos : 0 < x * t` and `hxt : x * t < 0`. This is a contradiction.
        linarith [x_mul_t_pos, hxt]

    -- Since `t < 0`, it means `t` cannot be `0`.
    exact ne_of_lt t_neg

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  norm_num

example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  norm_num

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  norm_num

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  . calc
      p = (p + p) / 2 := by simp
      _ < (p + q) / 2 := by linarith
  . calc
      (p + q) / 2 < (q + q) / 2 := by linarith
      _ = q := by simp

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  norm_num
  constructor
  norm_num
  constructor
  norm_num
  norm_num

-- 2.5 Exercises
example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  norm_num

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6, 7
  norm_num

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  norm_num
  norm_num

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  norm_num

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  intro ht_eq_1

  have h_cases : t - 1 ≤ 0 ∨ t - 1 > 0 := le_or_gt (t - 1) 0

  cases h_cases
  case inl h_le_zero_case =>

    obtain ⟨a, ha⟩ := h
    rw [ht_eq_1] at ha
    linarith

  case inr h_gt_zero_case =>
    linarith

-- Exercise 7 has problems when coding. There may be requirements for fixing the issue of Lean.

--example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  --intro hm

  --cases' h with a ha

  --rw [hm] at ha

  --have h_2_dvd_2a : 2 ∣ (2 * a) := by
  --  exact dvd_mul_right 2 a

  --have h_mod_2_zero : (2 * a) % 2 = 0 := by
  --  rw [Int.emod_eq_zero_iff_dvd]
  --  exact h_2_dvd_2a

-- Exercise 8 has problems, requiring time for figuring out how to use Lean 4 to solve it.
example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  let s := (a + b + c) / 2
  let x := s - a
  let y := s - b
  let z := s - c
  use x, y, z
  constructor
  · -- x ≥ 0
    have : x = (b + c - a) / 2 := by
      unfold x s
      field_simp
      linarith
    rw [this]
    have : b + c - a ≥ 0 := by linarith [ha]
    exact div_nonneg this (by norm_num)
  constructor
  · -- y ≥ 0
    have : y = (a + c - b) / 2 := by
      unfold y s
      field_simp
      linarith
    rw [this]
    have : a + c - b ≥ 0 := by linarith [hb]
    exact div_nonneg this (by norm_num)
  constructor
  · -- z ≥ 0
    have : z = (a + b - c) / 2 := by
      unfold z s
      field_simp
      linarith
    rw [this]
    have : a + b - c ≥ 0 := by linarith [hc]
    exact div_nonneg this (by norm_num)
  constructor
  · -- a = y + z
    have : y + z = a := by
      unfold y z s
      field_simp
      linarith
    rw [this]
  constructor
  · -- b = x + z
    have : x + z = b := by
      unfold x z s
      field_simp
      linarith
    rw [this]
  · -- c = x + y
    have : x + y = c := by
      unfold x y s
      field_simp
      linarith
    rw [this]
