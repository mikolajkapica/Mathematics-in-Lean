import Mathlib



example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  . apply h₀
  . apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := le_trans h₀ h₁

variable (a b c d e : ℝ)
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_of_lt_of_le h₁
  apply le_trans h₂
  apply le_of_lt h₃

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by linarith

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith




-- example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
--   linarith [exp_le_exp.mpr h']


example : 0 ≤ a ^ 2 := by
  exact sq_nonneg a



-- example (h : a ≤ b) : c - exp b ≤ c - exp a := by
--   exact Real.instDistribLatticeReal.proof_1 (c - sorryAx ℝ true)

theorem qneq: 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith


example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_le']
  constructor
  . calc
    a * b = (2 * a * b) / 2 := by ring
    _ ≤ (a ^ 2 + b ^ 2) / 2 := by linarith [qneq a b]
  . calc
    -(a * b) = (2 * (-a) * b) / 2 := by ring
    _ ≤ ((-a) ^ 2 + b ^ 2) / 2 := by linarith [qneq (-a) b]
    _ = (a ^ 2 + b ^ 2) / 2 := by simp [sq a]
