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

theorem neg_neg (a : R) : -(-a) = a := by
  rw [neg_eq_of_add_eq_zero]
  rw [add_left_neg]



end MyRing
