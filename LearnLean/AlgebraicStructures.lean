import Mathlib

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

theorem MY_neg_add_cancel_left (a b : R) : -a + a + b = b := by
  rw [add_left_neg]
  rw [add_comm]
  rw [add_zero]


theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc]
  rw [add_right_neg]
  rw [add_zero]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_add (a : R) : 0 + a = a := by rw [add_comm, add_zero]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul]
    rw [zero_add]
    rw [add_zero (0 * a)]
  rw [add_left_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h: a + b = 0) : -a = b := by
  rw [← zero_add a, ← add_left_neg b, add_assoc, add_comm b, h, add_zero, neg_neg]

theorem eq_neq_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← neg_eq_of_add_eq_zero h]
  rw [neg_neg]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : -(-a) = a := by
  rw [neg_eq_of_add_eq_zero]
  rw [add_left_neg]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

-- theorem self_sub (a : R) : a - a = 0 := by
--   rw [sub_eq_add_neg]
--   rw [add_right_neg a]

-- theorem self_sub (a : R) : a - a = 0 :=

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two]
  rw [add_mul]
  rw [one_mul]

end MyRing

namespace Groups
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
      rw [mul_assoc, ← mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv]
  rw [← h, ← mul_assoc, mul_left_inv, one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← mul_left_inv a, ← mul_assoc, mul_right_inv, one_mul]


theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← mul_one a⁻¹, ← mul_right_inv (a * b), ← mul_assoc, ← mul_assoc, ← mul_assoc, mul_assoc b⁻¹, mul_left_inv, mul_assoc b⁻¹, one_mul, mul_left_inv, one_mul]


end Groups
