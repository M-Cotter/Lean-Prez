import Mathlib

#print "Hello world! I (the screen on the right) am the Lean InfoView"

-- I am a comment. I am Green.

/- This is a comment that takes up multiple lines.
  We can write Latex symbols in Lean, some of the most used ones are

  \N = ℕ, \Z = ℤ, \to = →, \mapsto = ↦

  write backslash and then guess what the name might be then hit space
  (usually symbols have many aliases).
-/

-- Check the type of three (it is a natural number).
#check 3

-- However, three can also be an integer.
#check (3 : ℤ)

-- Or even a real number!
#check (3 : ℝ)

-- Check the type of a string.
#check "hello world!"

-- Check the type of the natural numbers themselves. (it is `Type`)
#check ℕ

-- Avoid Russel's paradox
#check Type
#check Type 1
#check Type 2

-- We can define a synonym for three.
def MyThree := (3 : ℕ)

#check MyThree

-- Functions
def AddThree (x : ℕ) : ℕ := x + 3

-- This is alternative, more traditional, functional notation
def NewAddThree : ℕ → ℕ := fun (x : ℕ) ↦ x + 3

#check NewAddThree

#check Nat.add

#check Nat.add 3
