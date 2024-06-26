import Mathlib

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply and.intro
  exact hp
  apply and.intro
  exact hq
  exact hp
