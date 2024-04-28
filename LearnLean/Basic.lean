import Init.Data.Nat
import Init.Data.Bool
import Mathlib.Data.Real.Basic

#check Nat.succ 5


/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false


#check Nat × Nat → Nat


def add (x y : Nat) : Nat := x + y

#eval add 5 5


#check id
#check @id
#check @id Nat 5


#check And
#check Not

variable (p q r : Prop)
#check p ∧ q

#check p ∨ q

variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p


variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h


variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
    show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
    show p ∧ q from And.intro (And.right h) (And.left h))

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
    show p ∧ (q ∧ r) from And.intro (And.left (And.left h)) (And.intro (And.right (And.left h)) (And.right h)))
    (fun h : p ∧ (q ∧ r) =>
    show (p ∧ q) ∧ r from And.intro (And.intro (And.left h) (And.left (And.right h))) (And.right (And.right h)))
