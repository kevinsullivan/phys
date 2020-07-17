/-
A vector space takes in two types, k and M, where k is a field
and M is an additive commutative group. The vector space is
constructed as a module with k being a set of scalars and
M being a set of vectors.

Code:
abbreviation vector_space (k : Type u) (M : Type v) [field k] [add_comm_group M] :=
module k M
-/




/-
An additive commutative group is an abelian group that has an
addition operation equipped with an identity element
and additive inverses.


@[class]
structure add_comm_group :
Type u → Type u
add : G → G → G
add_assoc : ∀ (a b c_1 : G), a + b + c_1 = a + (b + c_1)
zero : G
zero_add : ∀ (a : G), 0 + a = a
add_zero : ∀ (a : G), a + 0 = a
neg : G → G
add_left_neg : ∀ (a : G), -a + a = 0
add_comm : ∀ (a b : G), a + b = b + a

-/

/-
A field is a set of elements with a commutative addition operation,
equipped with additive inverses, as well as a commutative
multiplication operation, also equipped with multiplicative 
inverses. Both also have an identity element and satisfy
the distributive properties.



@[class]
structure field :
Type u → Type u
add : α → α → α
add_assoc : ∀ (a b c_1 : α), a + b + c_1 = a + (b + c_1)
zero : α
zero_add : ∀ (a : α), 0 + a = a
add_zero : ∀ (a : α), a + 0 = a
neg : α → α
add_left_neg : ∀ (a : α), -a + a = 0
add_comm : ∀ (a b : α), a + b = b + a
mul : α → α → α
mul_assoc : ∀ (a b c_1 : α), a * b * c_1 = a * (b * c_1)
one : α
one_mul : ∀ (a : α), 1 * a = a
mul_one : ∀ (a : α), a * 1 = a
left_distrib : ∀ (a b c_1 : α), a * (b + c_1) = a * b + a * c_1
right_distrib : ∀ (a b c_1 : α), (a + b) * c_1 = a * c_1 + b * c_1
mul_comm : ∀ (a b : α), a * b = b * a
inv : α → α
zero_ne_one : 0 ≠ 1
mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1
inv_zero : 0⁻¹ = 0
-/



/-
A module has a ring of scalars R, and a group M (similar to a
vector space, but the set of scalars is a ring, not a field).
It extends semimodule R M.


class module (R : Type u) (M : Type v) [ring R] [add_comm_group M] extends semimodule R M
end prio
-/


/-
A ring is an set of elements with a commutative addition 
operation that has additive inverses and an identity element. It
also has a second binary operation, multiplication, which
is associative and has an identity element. The distributive
properties must also be obeyed.


@[class]
structure ring :
Type u → Type u
add : α → α → α
add_assoc : ∀ (a b c_1 : α), a + b + c_1 = a + (b + c_1)
zero : α
zero_add : ∀ (a : α), 0 + a = a
add_zero : ∀ (a : α), a + 0 = a
neg : α → α
add_left_neg : ∀ (a : α), -a + a = 0
add_comm : ∀ (a b : α), a + b = b + a
mul : α → α → α
mul_assoc : ∀ (a b c_1 : α), a * b * c_1 = a * (b * c_1)
one : α
one_mul : ∀ (a : α), 1 * a = a
mul_one : ∀ (a : α), a * 1 = a
left_distrib : ∀ (a b c_1 : α), a * (b + c_1) = a * b + a * c_1
right_distrib : ∀ (a b c_1 : α), (a + b) * c_1 = a * c_1 + b * c_1

-/


/-
A semimodule takes in a semiring R, and an additive, commutative
monoid M, and extends distrib_mul_action R M. 


class semimodule (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] extends distrib_mul_action R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : M, (0 : R) • x = 0)
end prio
-/


/-
a semiring is a group of elements with an abelian addition
operation with an identity element, and an associative
multiplication operation with an identity element (no requirement
for inverses or commutative multiplication)



@[class]
structure semiring :
Type u → Type u
add : α → α → α
add_assoc : ∀ (a b c_1 : α), a + b + c_1 = a + (b + c_1)
zero : α
zero_add : ∀ (a : α), 0 + a = a
add_zero : ∀ (a : α), a + 0 = a
add_comm : ∀ (a b : α), a + b = b + a
mul : α → α → α
mul_assoc : ∀ (a b c_1 : α), a * b * c_1 = a * (b * c_1)
one : α
one_mul : ∀ (a : α), 1 * a = a
mul_one : ∀ (a : α), a * 1 = a
left_distrib : ∀ (a b c_1 : α), a * (b + c_1) = a * b + a * c_1
right_distrib : ∀ (a b c_1 : α), (a + b) * c_1 = a * c_1 + b * c_1
zero_mul : ∀ (a : α), 0 * a = 0
mul_zero : ∀ (a : α), a * 0 = 0

-/



/-
an additive commutative monoid is a set of elements
with a commutative addition operation and an identity element.

@[class]
structure add_comm_monoid :
Type u → Type u
add : M → M → M
add_assoc : ∀ (a b c_1 : M), a + b + c_1 = a + (b + c_1)
zero : M
zero_add : ∀ (a : M), 0 + a = a
add_zero : ∀ (a : M), a + 0 = a
add_comm : ∀ (a b : M), a + b = b + a

-/



/-
distrib_mul_action requires that scalar multiplication 
exists and obeys the distributive property.


@[class]
structure distrib_mul_action (α : Type u) (β : Type v)  :
Type (max u v)
to_mul_action : mul_action α β
smul_add : ∀ (r : α) (x y : β), r • (x + y) = r • x + r • y
smul_zero : ∀ (r : α), r • 0 = 0


-/

/-
a multiplication action requires that 
scalars and scalar multiplication exist


@[class]
structure mul_action (α : Type u) (β : Type v)  :
Type (max u v)
to_has_scalar : has_scalar α β
one_smul : ∀ (b : β), 1 • b = b
mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

-/

/-
has_scalar means that scalar multiplication is defined.
@[class]
structure has_scalar :
Type u → Type v → Type (max u v)
smul : α → γ → γ
Typeclass f

-/