-- Here are proofs mentioned in Chapter 1.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic


-- Example 1.2.1
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
    calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring

-- Example 1.2.2
example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
    calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * s := by rw [h2]
    _ = -1 - 2 * 3 := by rw [h1]
    _ = -7 := by ring

-- Example 1.2.3
example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) : (2 * a * n + b * m) ^ 2 = 2 :=
    calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw [h1, h2]
    _ = 2 := by ring

-- Example 1.2.4
example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) : d * (a * f - b * e) = 0 :=
    calc
    d * (a * f - b * e) = a * d * f - d * b * e := by ring
    _ = (b * c) * f - d * b * e := by rw [h1]
    _ = b * (c * f) - d * b * e := by ring
    _ = b * (d * e) - d * b * e := by rw [h2]
    _ = 0 := by ring

-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
    calc
    a = 2 * b + 5 := h1
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring

-- Example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
    calc
    x = 2 - 4 := by linarith [h1]
    _ = -2 := by ring

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
    calc
    a = 4 + 5 * b := by linarith [h1]
    _ = 4 + 5 * 1 := by linarith [h2]
    _ = 9 := by ring

-- Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
    calc
    w = (4 - 1) / 3 := by linarith [h1]
    _ = 1 := by ring

-- Example 1.3.5
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
    calc
    x = 2 * x + 3 := by linarith [h1]
    _ = x := by rw [h1]
    _ = -3 := by linarith

-- Example 1.3.6
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  have h3 : y = 2 * x - 4 := by linarith [h1]
  have h4 : y = x + 1 := by linarith [h2]
  calc
    x = 2 * x - 5 := by linarith [h3, h4]
    _ = x := by linarith
    _ = 5 := by linarith

-- Example 1.3.7
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
    calc
    u = 4 - 2 * v := by linarith [h1]
    _ = 6 + 2 * v := by linarith [h2]
    _ = (4 + 6) / 2 := by linarith
    _ = 5 := by ring

-- Example 1.3.8
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
   calc
   x = 4 - y := by linarith [h1]
   _ = (4 + 3 * y) / 5 := by linarith [h2]
   _ = 2 := by linarith

-- Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
  a ^ 2 - a + 3 = ((a - 3) ^ 2 + 6 * a - 9) - a + 3 := by linarith [h1]
  _ = (a - 3) ^ 2 + 5 * a - 6 := by linarith
  _ = (a - 3) ^ 2 + 5 * ((a - 3) + 3) - 6 := by linarith
  _ = (a - 3) ^ 2 + 5 * (a - 3) + 9 := by linarith
  _ = (2 * b) ^ 2 + 5 * (2 * b) + 9 := by rw [h1]
  _ = 4 * b ^ 2 + 10 * b + 9 := by linarith

-- Example 1.3.10
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
  z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = (z ^ 2 - z + 1) * (z ^ 2 - 2) + 3 := by linarith
  _ = (z ^ 2 - z + 1) * 0 + 3 := by rw [h1]
  _ = 3 := by linarith

/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/


example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
  y = 4 * 3 - 3 := by linarith [h1]
  _ = 9 := by linarith

example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
  a = 0 + b := by linarith [h]
  _ = b := by linarith

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
  x = 5 + 3 * y := by linarith [h1]
  _ = 5 + 3 * 3 := by rw [h2]
  _ = 14 := by ring

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  calc
  p = 1 + 2 * q := by linarith [h1]
  _ = -2 / 2 := by linarith [h2]
  _ = -1 := by ring


example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  calc
  x = 3 - 2 * y := by linarith [h2]
  _ = 3 - 2 * 2 := by linarith [h1]
  _ = -1 := by ring

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  calc
  p = 1 - 4 * q := by linarith [h1]
  _ = 1 - 4 * 3 := by linarith [h2]
  _ = -11 := by ring

example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  calc
  a = 7 - 3 * c - 2 * b := by linarith [h1]
  _ = 4 - 2 * b := by linarith [h3]
  _ = 4 - 2 * 1 := by linarith [h2]
  _ = 2 := by ring

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  calc
  u = (3 - v) / 4 := by linarith [h1]
  _ = (3 - 2) / 4 := by rw [h2]
  _ = 1 / 4 := by ring

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 :=
  calc
  c = 4 * c - 3 * c := by ring
  _ = -2 - 1 := by linarith [h1]
  _ = -3 := by ring


example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
  calc
  p = (5 * p - 3 * p) / 2 := by ring
  _ = (1 + 3) / 2 := by linarith [h1]
  _ = 2 := by ring

example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 :=
  calc
  x = 1 - y := by linarith [h2]
  _ = 1 - (4 - 2 * x) := by linarith [h1]
  _ = 3 := by linarith

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 :=
  calc
  a = 1 + b := by linarith [h2]
  _ = 1 + (4 - a) / 2 := by linarith [h1]
  _ = 2 := by linarith

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  calc
  u ^ 2 + 3 * u + 1 = (u + 1) ^ 2 + u := by ring
  _ = v ^ 2 + u := by rw [h1]
  _ = v ^ 2 + (v - 1) := by linarith [h1]
  _ = v ^ 2 + v - 1 := by ring

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  have h : t ^ 2 = 4 := by linarith [ht]
  calc
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2
      = (t ^ 2) ^ 2 + 3 * t * t ^ 2 - 3 * t ^ 2 - 2 * t - 2 := by ring
  _ = 4 ^ 2 + 3 * t * 4 - 3 * 4 - 2 * t - 2 := by rw [h]
  _ = 16 + 12 * t - 12 - 2 * t - 2 := by ring
  _ = 10 * t + 2 := by ring


example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  have hx : x = 2 := by linarith [h1]
  have hxy : y * x = 2 * x := by linarith [h2]
  have x_ne : x ≠ 0 := by rw [hx]; norm_num

  calc
    y = (y * x) / x := (eq_div_iff_mul_eq x_ne).mpr rfl
    _ = (2 * x) / x := by rw [hxy]
    _ = 2 := by rw [hx]; field_simp

example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  calc
  p ^ 2 + q ^ 2 + r ^ 2 = (p + q + r) ^ 2 - (2 * p * q + 2 * q * r + 2 * p * r) := by ring
  _ = 0 ^ 2 - (2 * p * q + 2 * q * r + 2 * p * r) := by rw [h1]
  _ = 0 - 4 := by linarith [h2]
  _ = -4 := by linarith


/-! # Section 1.4: Proving inequalities -/


-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by norm_num

-- Example 1.4.2
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by linarith [h1]
    _ = 3 := by ring

-- Example 1.4.3
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  calc
  x + y ≤ x + (x + 5) := by rel [h1]
  _ ≤ 2 * (-2) + 5 := by linarith [h2]
  _ ≤ 1 := by norm_num
  _ < 2 := by norm_num


-- Example 1.4.4
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by rel [h4, h5]
    _ ≤ A * B + A * B + A * v := by rel [h8, h9]
    _ ≤ A * B + A * B + 1 * v := by rel [h2]
    _ ≤ A * B + A * B + B * v := by rel [h3]
    _ < A * B + A * B + B * A := by rel [h9]
    _ = 3 * A * B := by ring

-- Example 1.4.5
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by ring
    _ ≥ 10 * t - 3 * t - 17 := by rel [ht]
    _ = 7 * t - 17 := by ring
    _ ≥ 7 * 10 - 17 := by rel [ht]
    _ ≥ 5 := by norm_num

-- Example 1.4.6
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc
  n ^ 2 = n * n := by ring
  _ ≥ 5 * n := by rel [hn]
  _ = 4 * n + n := by ring
  _ = 2 * n + 2 * n + n := by ring
  _ ≥ 2 * n + 2 * 5 + 5 := by rel [hn]
  _ = 2 * n + 15 := by ring
  _ > 2 * n + 11 := by norm_num


-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
  calc
    n ≤ m ^ 2 + n := by
      apply Int.le_add_of_nonneg_left
      exact sq_nonneg m
    _ ≤ 2 := by rel [h]


-- Example 1.4.8
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by
      apply le_add_of_nonneg_right
      exact sq_nonneg (x - y)
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 1 := by rel [h]
    _ < 3 := by norm_num

-- Example 1.4.9
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by
      apply le_add_of_nonneg_left
      linarith [sq_nonneg a, sq_nonneg b]
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _ ≤ 2 * (8 * b) + 8 * a + a := by rel [h3]
    _ = 7 * b + 9 * (a + b) := by ring
    _ ≤ 7 * b + 9 * 8 := by rel[h3]
    _ = 7 * b + 72 := by ring

-- Example 1.4.10
example {a b c : ℝ} :
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 :=
  calc
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)
      ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2
          + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2
          + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) := by
          linarith [sq_nonneg (a ^ 2 * (b ^ 2 - c ^ 2)), sq_nonneg (b ^ 4 - c ^ 4),
                 sq_nonneg (a ^ 2 * b * c - b ^ 2 * c ^ 2)]
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by ring


/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/


example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
  x = x + 3 - 3 := by ring
  _ ≥ 2 * y - 3 := by rel [h1]
  _ ≥ 2 * 1 - 3 := by rel [h2]
  _ ≥ -1 := by norm_num



example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
  a + b = (2 * a + 2 * b) / 2 := by ring
  _ ≥ (4 + a) / 2 := by linarith [h2]
  _ ≥ (4 + 3) / 2 := by rel [h1]
  _ ≥ 7 / 2 := by norm_num
  _ ≥ 3 := by norm_num

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
  x ^ 3 - 8 * x ^ 2 + 2 * x = x * (x ^ 2 - 8 * x + 16) - 14 * x := by ring
  _ = x * ((x - 4) ^ 2 - 14) := by ring
  _ ≥ 9 * ((9 - 4) ^ 2 - 14) := by rel [hx]
  _ ≥ 99 := by norm_num
  _ ≥ 3 := by norm_num


-- Unsolved exercise. With problems.
example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  sorry


example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  calc
  n ^ 2 - 2 * n + 3 = n ^ 2 - 2 * n + 1 + 2 := by ring
  _ = (n - 1) ^ 2 + 2 := by ring
  _ ≥ (5 - 1) ^ 2 + 2 := by rel [h1]
  _ = 18 := by norm_num
  _ > 14 := by norm_num

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  calc
  x ^ 2 - 2 * x = x ^ 2 - 2 * x + 1 - 1 := by ring
  _ = (x - 1) ^ 2 - 1 := by ring
  _ ≥ -1 := by linarith [sq_nonneg (x - 1)]

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  calc
  a ^ 2 + b ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 + 2 * a * b := by ring
  _ = (a - b) ^ 2 + 2 * a * b := by ring
  _ ≥ 2 * a * b := by linarith [sq_nonneg (a - b)]

/-! # Section 1.5: A shortcut -/

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by linarith

example {a b : ℤ} (ha : a - 2 * b = 1) : a = 2 * b + 1 := by linarith

example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 :=
  calc
    x + y ^ 2 = x - 7 := by linarith
    _ = -5 := by linarith


example {s t : ℝ} (h : t = 4 - s * t) : t + s * t > 0 := by linarith

example {m n : ℝ} (h1 : m ≤ 8 - n) : 10 > m + n := by linarith


-- Check that `addarith` can't verify this deduction!
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by linarith

-- Changes:
-- numbers -> norm_num
-- addarith [<Hypothesis>] -> linarith
