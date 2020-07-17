import data.vector
import data.real.basic


/-
The type of n-tuples over a field, K.
Note: Mis-naming: "vector" in Lean is "tuple" in math. 
-/ 
def n_tuple (K : Type) [field K] (n : ℕ) := vector K n 

example : n_tuple ℝ 4 := subtype.mk [1,0,0,0] rfl

