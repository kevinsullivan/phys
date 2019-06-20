axiom S : Type

/-mutual inductive X, Y
with X : Type 
    | mk : Π (s : S), Y → X
with Y : Type 
    | mk' : Π (s : S), list X  → Y


mutual inductive A, B
with A : S → Type 
    | mk : Π (s : S), B s → A s
with B : S → Type 
    | mk' : Π (s : S), A s → B s
-/

namespace ex1
universe u
mutual inductive affine_point, affine_vector, affine_frame (α : Type u)
with affine_point : Type u
| mk : α → affine_frame → affine_point
with affine_vector : Type u
| mk : α → affine_frame → affine_vector
with affine_frame : Type u
| mk : (list affine_point) → affine_frame
end ex1

namespace ex2
universe u
axiom space : Type (u+1)
mutual inductive affine_point, affine_vector, affine_frame (α : space)
with affine_point : Type (u+1)
| mk : affine_frame → affine_point
with affine_vector : Type (u+1)
| mk : affine_frame → affine_vector
with affine_frame : Type (u+1)
| mk : affine_point → (list affine_vector) → affine_frame
end ex2

/-
mutual inductive P, Q (s : Type)
with P : Type 
    | mk : s → Q s → P s
with Q : Type 
    | mk' : Π (s : S), list (P s) → Q s

#print P
-/
   
