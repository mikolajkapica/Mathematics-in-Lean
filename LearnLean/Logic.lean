import Mathlib

example (a b c : ℕ) : a * b * c = (b * c) * a := by
  rw [mul_assoc]
  rw [mul_comm]


variable (a b c : ℝ)

#check mul_comm a b


-- Using calc
example (a b c : ℕ) : a * b * c = (b * c) * a :=
calc
  a * b * c = a * (b * c) := by rw [mul_assoc]
  _ = (b * c) * a := by rw [mul_comm]


theorem myt1 : ∀ (a b c : ℕ), a * b * c = (b * c) * a := by
  intro a b c
  calc
    a * b * c = a * (b * c) := by rw [mul_assoc]
    _ = (b * c) * a := by rw [mul_comm]

theorem myt2 : ∀ (a b c : ℕ), a * b * c = (b * c) * a := by
  intro a b c
  rw [mul_assoc, mul_comm]














-- #check ∀ x : ℝ, 0 ≤ x → |x| = x

-- theorem my_lemma4:
--   ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
--   intro x y ε epos ele1 xlte ylte
--   calc
--     |x * y| = |x| * |y| := by rw [abs_mul]
--     _ ≤ |x| * ε := sorry
--     _ < 1 * ε := sorry
--     _ = ε := sorry
