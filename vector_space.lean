namespace vector_space

section

variable vector : Type
variable field : Type
variable scalar : Type

variable scalar_scalar_mult : scalar → scalar → scalar 
local notation a * b := scalar_scalar_mult a b

variable vector_vector_add : vector → vector → vector
local notation v1 + v2 := vector_vector_add v1 v2

variable scalar_vector_mult : scalar → vector → vector
local notation α # v := scalar_vector_mult α v

-- testing
variables v1 v2 v3: vector
variables α β : scalar
#check (α # v1)
#check (v1 + v2)
#check (α * β)


-- Associativity of addition	u + (v + w) = (u + v) + w
theorem assoc_vector_vector_add : 
    ∀ (v1 v2 v3 : vector), v1 + v2 + v3 = (v1 + v2) + v3 :=
sorry


-- Commutativity of addition	u + v = v + u
theorem comm_vector_vector_add : 
    ∀ (v1 v2 : vector), v1 + v2 = v2 + v1 :=
sorry

/-
Identity element of addition	
There exists an element 0 ∈ V, called the zero vector, 
such that v + 0 = v for all v ∈ V.
-/ 

variable zero_vector : vector

theorem identity_vector_vector_add : 
    ∀ v, v + zero_vector = v :=
sorry


/-
Inverse elements of addition
For every v ∈ V, there exists an element −v ∈ V, 
called the additive inverse of v, such that v + (−v) = 0.
-/

theorem inverse_vector_vector_add : ∀ v, ∃ negv, negv + v = zero_vector


/-
Compatibility of scalar multiplication with field multiplication	
a(bv) = (ab)v [nb 2]
-/
theorem compat_scalar_mult_field_mult : 
    ∀ a b : scalar, ∀ v : vector,
    (a # (b # v)) = ((a * b) # v) :=
sorry

/-
Identity element of scalar multiplication	1v = v, where 1 denotes the multiplicative identity in F.
-/

variable one_scalar : scalar

theorem one_scalar_vector_mult : ∀ v, (one_scalar # v) = v :=
sorry


/-Distributivity of scalar multiplication with respect to vector addition  	a(u + v) = au + av
Distributivity of scalar multiplication with respect to field addition	(a + b)v = av + bv
-/


end 
end vector_space