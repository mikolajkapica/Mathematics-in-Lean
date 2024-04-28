import Mathlib

example : |x| = |-x| := by
  cases le_total 0 x with
  | inl h => rw [abs_of_nonneg h, abs_of_nonpos (neg_nonpos.mpr h), neg_neg]
  | inr h => rw [abs_of_nonpos h, abs_of_nonneg (neg_nonneg.mpr h)]
