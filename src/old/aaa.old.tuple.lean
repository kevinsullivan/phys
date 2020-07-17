import data.real.basic

/-
We represent he type of n-tuples over a field, K, as
instances of Lean 3 vectors. These are just tuples and
not really vectors as the name suggests. We thus note
a mis-naming of "vector" in Lean. It's "tuple" in math. 
-/ 
def tuple (K : Type) [discrete_field K] (n : ℕ) := vector K n 

example : tuple ℝ 4 := subtype.mk [1,0,0,0] rfl
