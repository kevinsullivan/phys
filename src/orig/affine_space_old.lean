import algebra.module
import data.vector
import .torsor

-- for testing
import data.real.basic
set_option pp.notation false


-- UNDERLYING REPRESENTATION

universe u

/-
First, we need to build up a concept of vector spaces
where vectors are tuples over a field, K. We start by
defining a polymorphic tuple type.

Background: the "vector" type in the Lean standard library
is a type whose values are really just tuples. We define
a "tuple" type polymorphic as the type of tuples of length
n over values of a type, K.
-/
def tuple 
    (n : ℕ) 
    (K : Type u) := 
        vector K n 

/-
With K a discrete field with zero and one values,
we define a function to return tuples of length n
over K with all elements equal to the field's zero
element. 
-/
def mk_zero_tuple :
    ∀ (n : ℕ) 
    (K : Type u) 
    [f : discrete_field K] 
    [z : has_zero K],
        vector K n 
| 0 K f z := vector.nil
| (nat.succ n') K f z := vector.cons (z.zero) (@mk_zero_tuple n' K f z)

-- testing
def aReal3ZeroTuple : tuple 3 ℝ := 
    subtype.mk [0,0,0] rfl
def aReal4ZeroTuple : tuple 4 ℝ := 
    subtype.mk [0,0,0,0] rfl


/-
Now we're going to represent vectors in an affine space
of dimension n over a field K as (n+1)-tuples with the
first element equal to the zero for K; and we'll represent
points in  such an affine space as (n+1) tuples with first
element equal to the one for K. Here we provide functions
for manufacturing such (n+1) tuples given n-tuples of values
over K.
-/

def affine_vector_tuple 
    (n : ℕ) [has_zero (fin n)] 
    (K: Type u) [f: discrete_field K] [zf : has_zero K]  := 
        { c : tuple (nat.succ n) K // c.nth 0 = zf.zero }

def affine_point_tuple 
    (n : ℕ)  [has_zero (fin n)] 
    (K: Type u) [discrete_field K] [of : has_one K] := 
{ t : tuple (nat.succ n) K // t.nth 0 = of.one }

/-
Here are functions for manufacturing n-d affine_vector_tuple
and affine_point_tuple objects given n-tuples of coordinates.
These functions add the required zero or one first element and
type-check as returning elements of the preceding (sub)types.
These functions implement a kind of information hiding, in that
users of these functions need only provide and think about the
three affine coordinates, and not the fourth dimension one that
we use to distingish points from vectors.
-/

def mk_affine_vector_tuple :        -- add vector of coords argument
    ∀ {n : ℕ} [nz: has_zero (fin n)]
    {K : Type u} [f : discrete_field K] [z : has_zero K]
    (c: tuple n K),
    @affine_vector_tuple n nz K f z
| n nz K f z c := 
    ⟨ vector.cons z.zero c, by simp ⟩ 

def mk_affine_point_tuple :        -- add vector of coords argument
    ∀ {n : ℕ} [nz : has_zero (fin n)]
    {K : Type u} [f : discrete_field K] [o : has_one K]
    (c: tuple n K),
    @affine_point_tuple n nz K f o
| n nz K f o c := ⟨ vector.cons o.one c, by simp ⟩

def get_affine_vector_tuple_coords 
    {n : ℕ} [has_zero (fin n)] 
    {K: Type} [f: discrete_field K] [zf : has_zero K]
    (t : affine_vector_tuple n K) : tuple n K:= 
match t with
⟨ c, pf ⟩ := c.tail
end

def get_affine_point_tuple_coords 
    {n : ℕ} [has_zero (fin n)] 
    {K: Type} [f: discrete_field K] [zf : has_zero K]
    (t : affine_point_tuple n K) : tuple n K:= 
match t with
⟨ c, pf ⟩ := c.tail
end

/-
Here are a few examples. In the first, we see that 
to create an affine 3-d vector, we have to provide 
a 4-tuple, namely one with the property that the
discriminator element is set to 0. Having done so,
we can then recover the array of three coordinates.
-/
def anAffine3Vector : affine_vector_tuple 3 ℝ := 
subtype.mk aReal4ZeroTuple rfl

#check get_affine_vector_tuple_coords anAffine3Vector

/-
Better, and what we intend, is, instead, that to 
create an affine 3-d point or vector, one provides 
a 3-tuple, rather that a 4-tuple, the rest being 
hidden implementation details.
-/
def aVector3Tuple : affine_vector_tuple 3 ℝ :=    -- non-computable
mk_affine_vector_tuple aReal3ZeroTuple
def aPoint3Tuple : affine_point_tuple 3 ℝ :=    -- non-computable
mk_affine_point_tuple aReal3ZeroTuple
#check aVector3Tuple
#check aPoint3Tuple

def mk_affine_zero_vector_tuple
    (n : ℕ) [z :has_zero (fin n)] 
    (K: Type u) [f: discrete_field K]  
    : affine_vector_tuple n K :=
mk_affine_vector_tuple (mk_zero_tuple n K)

-- testing
#check mk_affine_zero_vector_tuple 3 ℝ 

def mk_affine_zero_point_tuple
    (n : ℕ) [has_zero (fin n)] 
    (K: Type u) [discrete_field K]  
    : affine_point_tuple n K :=
mk_affine_point_tuple (mk_zero_tuple n K)

-- THE MAIN DATA TYPES: space, point, vector, frame

/-
We define a type of spaces. A space has a name, a
positive dimension, and a field (which in turn has
both zero and one elements).
-/

structure space : Type 1 :=
mk ::
(name : string)
(dim : ℕ) 
[posDim : has_zero (fin dim)]
(K: Type) 
[fieldK : discrete_field K]
[zero : has_zero K]
[one : has_one K]

-- testing

def time : space :=         -- non-computable
    space.mk "time" 1 ℝ 

/-
We define affine point, vector, and frame types.
The space to which each such object belongs is a
part of its type. The definitions are mutually
recursive, because point and a vector are defined
partly in terms of a frame (in terms of which its
coordinates are interpreted), and a frame in turn
is defined by a point (its origin) and a tuple of
vectors (comprising a basis for its vector space).
-/

mutual inductive affine_point, affine_vector, affine_frame
with affine_point : space → Type 1
    | mk :  
        Π { s : space }, 
        affine_frame s → 
        @affine_point_tuple s.dim s.posDim s.K s.fieldK s.one → affine_point s
    | mk_std : 
        Π { s : space },         -- std point, (1, 0, 0, ..., 0) wrt std_frame
        affine_point s
with affine_vector : space → Type 1
    | mk : 
        Π {s : space}, 
        affine_frame s → 
        @affine_vector_tuple s.dim s.posDim s.K s.fieldK s.zero → affine_vector s
    | mk_std : 
        Π { s : space },        -- std vector(0, 0, 0, ..., 0) wrt std_frame
        (fin s.dim) → affine_vector s
with affine_frame : space → Type 1
    | mk : Π { s : space }, affine_point s → affine_vector s → affine_frame s -- stub
    | mk_std : Π { s : space },  affine_frame s  -- std frame

-- testing

def aFrame : affine_frame time :=  -- non-computable
affine_frame.mk_std

def aVector : affine_vector time :=
affine_vector.mk 
    aFrame 
    (@mk_affine_zero_vector_tuple time.dim time.posDim time.K time.fieldK)

def aPoint : affine_point time :=
affine_point.mk aFrame (@mk_affine_zero_point_tuple time.dim time.posDim time.K time.fieldK)

def mk_std_vector {s : space } :=
    @mk_affine_zero_vector_tuple s.dim s.posDim s.K s.fieldK

def mk_vector (s : space ) (f : affine_frame s) (c : tuple s.dim s.K) :=
    @affine_vector.mk 

-- test

def aVector' : affine_vector time := @mk_vector time (affine_frame.mk_std) (mk_affine_zero_vector_tuple time.dim time.K) := _
_

/-
Basic projection functions
-/

def mk_std_frame { s : space } : affine_frame s :=
sorry

def get_frame { s : space } (p: affine_point s) : affine_frame s :=
match p with
| affine_point.mk_std := mk_std_frame
| affine_point.mk f t := f
end

def get_coords { s : space } (p: affine_point s) : affine_frame s :=
match p with
| affine_point.mk_std := mk_std_frame
| affine_point.mk f t := f
end

-- CORRESPONDING OPERATIONS AND NOTATIONS

-- scalar vector multiplication
def scalar_vector_mult:
    ∀ {s : space }, s.K → affine_vector s → affine_vector s
| s K v := 
    match v with
        | affine_vector.mk_std d := 
            @affine_vector.mk 
                s
                affine_frame.mk_std 
                (@mk_affine_zero_vector_tuple s.dim s.posDim s.K s.fieldK)
        | affine_vector.mk frame tuple := 
            affine_vector.mk frame tuple
    end

/-
n nz K f z
-/


instance  vector_has_scalar_mult 
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K] : 
    has_scalar K (affine_vector_tuple n K) := 
⟨ scalar_vector_mult ⟩ 

-- vector negation

def vector_neg
   {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K]
    (v : affine_vector_tuple n K) : 
    affine_vector_tuple n K :=
begin
sorry
end

instance  vector_has_neg
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K] : 
    has_neg (affine_vector_tuple n K) := 
⟨ vector_neg ⟩ 


-- vector vector addition
def vector_vector_add 
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K]
    (v1 : affine_vector_tuple n K) 
    (v2 : affine_vector_tuple n K) : 
    affine_vector_tuple n K :=
begin
sorry
end

instance  vector_has_add
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K] : 
    has_add (affine_vector_tuple n K) := 
⟨ vector_vector_add ⟩ 


-- point point subtraction
def point_point_sub
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K]
    (p2 : affine_point_tuple n K) 
    (p1 : affine_point_tuple n K) : 
    affine_vector_tuple n K :=
begin
sorry
end

-- Can't use std lib's has_sub: wrong signature
-- We'll have to define our own notation instead
infix -        := point_point_sub


-- zero vector
def vector_zero
    (n : ℕ) [has_zero (fin n)] 
    (K: Type u) [discrete_field K] [has_zero K] : 
    affine_vector_tuple n K :=
begin
sorry
end

instance  vector_has_zero
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K]
    (v : affine_vector_tuple n K) : 
    has_zero (affine_vector_tuple n K) := 
⟨ vector_zero n K⟩ 

-- zero point
def point_zero
    (n : ℕ) [has_zero (fin n)] 
    (K: Type u) [discrete_field K] [has_zero K] : 
    affine_point_tuple n K :=
begin
sorry
end

instance point_inhabited 
    (n : ℕ) [has_zero (fin n)] 
    (K: Type u) [discrete_field K] [has_zero K] :
    inhabited (affine_point_tuple n K) :=
⟨ point_zero n K⟩ 


-- PROPERTIES

lemma scalar_mult_left_one 
    {n : ℕ} [has_zero (fin n)] 
    {K : Type u} [discrete_field K]
    (x : affine_vector_tuple n K) : 
    (has_one.one K) • x = x := 
begin
--rw monoid.one_mul,
sorry
end

lemma scalar_mult_left_zero
    {n : ℕ} [has_zero (fin n)] 
    {K : Type u} [discrete_field K]
    (x : affine_vector_tuple n K) : 
    (has_zero.zero K) • x = (vector_zero n K) := 
begin
sorry
end

theorem scal_times_sum_dist  
    (n : ℕ) [has_zero (fin n)] 
    (K : Type u) [discrete_field K] 
    (r : K) 
    (x y : affine_vector_tuple n K) :
    r • (x + y) = r • x + r • y := 
begin
sorry
end


theorem sum_times_scal_dist 
    (n : ℕ) [has_zero (fin n)]
    (K : Type u) [discrete_field K]  
    (r s : K) 
    (x : affine_vector_tuple n K) :
    (r + s) • x = r • x + s • x := 
begin
sorry
end


theorem scal_prod_times_dist 
    (n : ℕ) [has_zero (fin n)] 
    (K : Type u) [discrete_field K] 
    (r s : K) (x : affine_vector_tuple n K): 
    (r * s) • x = r • s • x :=
begin
sorry
end


/-
class add_semigroup (α : Type u) extends has_add α :=
(add_assoc : ∀ a b c : α, a + b + c = a + (b + c))
-/
instance vector_add_semigroup
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K] : 
    add_semigroup (affine_vector_tuple n K) := 
begin
sorry
end

/-
class add_monoid (α : Type u) extends add_semigroup α, has_zero α :=
(zero_add : ∀ a : α, 0 + a = a) (add_zero : ∀ a : α, a + 0 = a)
-/
instance vector_add_monoid
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K] : 
    add_monoid (affine_vector_tuple n K) := 
begin
sorry
end

/-
class add_comm_monoid (α : Type u) extends add_monoid α, add_comm_semigroup α
-/
instance vector_add_comm_monoid 
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K] : 
    add_comm_monoid (affine_vector_tuple n K) := 
begin
sorry
end

/-
class add_group (α : Type u) extends add_monoid α, has_neg α :=
(add_left_neg : ∀ a : α, -a + a = 0)
-/
instance vector_add_group 
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K] : 
    add_group (affine_vector_tuple n K) := 
begin
sorry
end

instance vector_add_comm_group 
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K] : 
    add_comm_group (affine_vector_tuple n K) := 
begin
sorry
end


/-
A semimodule is a generalization of vector spaces to a scalar semiring.
It consists of a scalar semiring `α` and an additive monoid of "vectors" `β`,
connected by a "scalar multiplication" operation `r • x : β`
(where `r : α` and `x : β`) with some natural associativity and
distributivity axioms similar to those on a ring. 

class semimodule (α : Type u) (β : Type v) [semiring α]
  [add_comm_monoid β] extends has_scalar α β 
-/
instance affine_semimodule 
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K] : 
    semimodule K (affine_vector_tuple n K) := 
begin
sorry
end


/-
A module is a generalization of vector spaces to a scalar ring.
It consists of a scalar ring `α` and an additive group of "vectors" `β`,
connected by a "scalar multiplication" operation `r • x : β`
(where `r : α` and `x : β`) with some natural associativity and
distributivity axioms similar to those on a ring. 

class module (α : Type u) (β : Type v) [ring α] [add_comm_group β] extends semimodule α β
-/

instance affine_module 
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K] : 
    module K (affine_vector_tuple n K) := 
begin
sorry
end

/-
A vector space is the same as a module, except the scalar ring is actually
a field. (This adds commutativity of the multiplication and existence of inverses.)
This is the traditional generalization of spaces like `ℝ^n`, which have a natural
addition operation and a way to multiply them by real numbers, but no multiplication
operation between vectors. 

class vector_space (α : Type u) (β : Type v) [discrete_field α] [add_comm_group β] extends module α β
-/

instance affine_vector_space 
    {n : ℕ} [has_zero (fin n)] 
    {K: Type u} [discrete_field K] : 
    vector_space K (affine_vector_tuple n K) := 
begin
sorry
end


-- PROPERTIES

/-
We will define an affine space as a torsor over a vector space.
Here we define the concept of a torsor. The basic idea is that 
if you subtract two points in a torsor, you get a vector, and if
you add a vector to a point, you get a new point: the given one
translated by the vector, if you want to think geometrically.
-/

class torsor 
    (G : Type u) [add_group G]
    (X : Type u) [inhabited X] :=
(add : G → X → X)
(sub : X → X → G)
(left_zero : ∀ (x : X), add 0 x = x)
(add_assoc : ∀ (g1 g2 : G) (x : X), add (g1 + g2) x = add g1 (add g2 x))
(add_sub: ∀ (x y : X), add (sub x y) y = x)
(sub_add: ∀ (x : X) (g : G), sub (add g x) x = g)


/-
class affine_space  
    (n : ℕ) [has_zero (fin n)]
    (K: Type)  [discrete_field K] extends
    torsor (affine_vector n K) (affine_point n K) 
-/
