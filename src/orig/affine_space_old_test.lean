import .affine_space

set_option pp.implicit true
set_option pp.notation false
#print vector_has_add
axioms 
    (K : Type) 
    (f : discrete_field K) 
    (n : ℕ) 
    (z : has_zero (fin n)) 
    (s : K) 
    (v1 v2 : @affine_vector n z K f)
#check (@vector_vector_add n z K f v1 v2)
#check (@scalar_vector_mult n z K f s v1)

-- test overloading
#check v1 + v2

