import Mathlib

-- theorem le_of_lt
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * ε := mul_le_mul (le_refl |x|) (le_of_lt ylt) (abs_nonneg y) (abs_nonneg x)
    _ < 1 * ε := mul_lt_mul_of_pos_right (lt_of_lt_of_le xlt ele1) epos
    _ = ε := one_mul ε



def f (x : ℕ) : ℝ := 1 + 1/(x+1)

def FnUb (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

example : FnUb f (3 : ℝ) := by
  have h1 : ∀ x, 1 ≤ (x + 1) := by
    intro x
    apply le_add_of_nonneg_right
    apply zero_le
  intro x
  simp [f]
