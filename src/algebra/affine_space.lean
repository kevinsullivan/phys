import algebra.module
import data.vector
import data.rat -- testing


universe u

/-
TUPLES of length n over a field, K. Don't add
implicit typeclass parameters here, as it will 
cause the mutual inductive type below not to be
accepted.
-/
def tuple 
    (d : ℕ) 
    (K : Type u) : 
    Type u := 
vector K d

def tuple_tuple_add
    {d : ℕ} 
    {K : Type u} 
    [a : has_add K]
    (t1 t2 : tuple d K) :
    tuple d K :=
match t1, t2 with
| subtype.mk [] pf, _  := subtype.mk [] pf
| (subtype.mk l1 pf1), (subtype.mk l2 pf2) := 
    subtype.mk (list.zip_with a.add l1 l2) sorry
end

def scalar_tuple_mult
    {d : ℕ} 
    {K : Type u} 
    [m : has_mul K]
    (a : K)
    (t : tuple d K) :
        vector K d := 
subtype.mk 
    (list.map (λ c, a * c) t.val) 
    (by simp; exact t.property)


def tuple_neg
    {d : ℕ} 
    {K : Type u} 
    [n : has_neg K]
    (t : tuple d K) :
        vector K d := 
subtype.mk (list.map n.neg t.val) sorry

def mk_tuple_zero :
    Π
    (d : ℕ) 
    (K : Type u)  
    [z : has_zero K],
        vector K d 
| 0 K z := vector.nil
| (nat.succ n') K z := vector.cons (z.zero) (@mk_tuple_zero n' K z)

-- A few routines to construct standard basis vector tuples
def mk_indicator_tuple_helper :
    Π
    (d : ℕ) 
    (K : Type u) 
    [z : has_zero K]
    [o : has_one K]
    (i : ℕ)
    (b : bool),
        (list K)
| 0 K z o i b := list.nil
| (nat.succ n') K f o i b := 
    if (i = 0 ∧ b = ff) 
    then (list.append [o.one] (@mk_indicator_tuple_helper n' 
        K f o (i-1) true))
    else (list.append [o.one] (@mk_indicator_tuple_helper n' 
        K f o (i-1) b))

lemma mk_indicator_tuple_helper_length :
    ∀ 
    (d : ℕ) 
    (K : Type u) 
    [z : has_zero K]
    [o : has_one K]
    (i : ℕ)
    (b : bool),
    list.length (@mk_indicator_tuple_helper d K z o i b) = d :=
begin
intros,
induction d, 
simp [mk_indicator_tuple_helper],
simp [mk_indicator_tuple_helper],
sorry,
end

def mk_indicator_tuple
    (d : ℕ) 
    (K : Type u) 
    [z : has_zero K]
    [o : has_one K]
    (i : fin d) :
        vector K d :=
subtype.mk 
    (@mk_indicator_tuple_helper d K z o i.val false)
    (by apply mk_indicator_tuple_helper_length)

/-
SPACES over a field.

We define a type, space. We will use values of 
this type to identify a given affine space and 
characterize its key attributes: its dimension,
the field over in terms of which scalars and 
coordinate tuples are defined, and its English
name. Names allow us to distinguish spaces with
the same field and dimensionality but different
interpretations. 

We use typeclass lookup to recover a proof
that the given type, K, is a field (if it is 
and if it has an instance defined), and, in
this case, its zero and one elements. Doing
this here allows us to infer all of these 
values from given dim and K parameters in 
the subsequence definition of affine points,
vectors, and frames, just below. 
-/
structure space
(dim : ℕ) 
(K: Type) 
[isField : discrete_field K] : 
Type :=
mk :: (name : string)

/-
A mutual inductive definition of affine point, 
vector, and frame types. A point in an affine space 
is given coordinates in terms of a frame. A vector 
can be given coordinates in the same way. A frame, 
in turn, has a point, its origin, and a sequence of 
vectors, constituting a basis for the vector space. 
We are not yet specifying or enforcing the linear 
independence of the vectors. The points and vectors 
that make up a frame, being points and vectors, in 
turn have coordinates expressed in terms of some 
(possible other) frame. The recursion bottoms out 
with at a standard frame with a standard origin and 
standard basis vectors. This structure naturally 
supports situation where you have chains of changes 
in basis/coordinate-systems. This kind of situation 
arises frequently in domains like computer graphics 
and robotics.
-/
mutual inductive affine_point, affine_vector, affine_frame 
    { d : ℕ } 
    { K: Type }
    { f : discrete_field K }
--    { z : has_zero K }
--    { o : has_one K }
    (s : space d K)
with affine_point : Type 1
| mk_std : affine_point
| mk : affine_frame → tuple d K → affine_point
with affine_vector : Type 1
| mk_std : affine_vector
| mk : affine_frame → tuple d K → affine_vector
with affine_frame : Type 1
| mk_std : affine_frame
| mk : affine_point → (list affine_vector) → affine_frame

/-
TBD: Need a better representation of vector space basis than
(list affine_vector). At a minimum the length has to be d and
the vectors have to be linearly independent.
-/

/-
TBD: Need representation of affine transformations, also to be
represented in the form of d-tuples of affine vectors.
-/

/-
Basic projection functions
-/

def mk_std_frame 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    (s : space d K) :=
affine_frame.mk_std s

def get_point_frame 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} (
    p: affine_point s) : affine_frame s :=
match p with
| affine_point.mk_std s := mk_std_frame s
| affine_point.mk f t := f
end

def get_vector_frame 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} (
    v: affine_vector s) : affine_frame s :=
match v with
| affine_vector.mk_std s := mk_std_frame s
| affine_vector.mk f t := f
end

def get_point_coords
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} (
    p: affine_point s) : tuple d K :=
match p with
| affine_point.mk_std s := mk_tuple_zero d K
| affine_point.mk f t := t
end

def get_vector_coords
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} (
    v: affine_vector s) : tuple d K :=
match v with
| affine_vector.mk_std s := mk_tuple_zero d K
| affine_vector.mk f t := t
end

def get_frame_origin
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} (
    f: affine_frame s) : affine_point s :=
match f with
| affine_frame.mk_std s := affine_point.mk_std s
| affine_frame.mk origin basis := origin
end

-- Derived constructor functions

def mk_std_basis_vector 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    (s : @space d K f) -- why
    (i : fin d) : affine_vector s :=
affine_vector.mk 
    (affine_frame.mk_std s) 
    (mk_indicator_tuple d K i)

def mk_std_basis
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    (s : space d K) : 
        list (affine_vector s) := sorry
/-
Todo above: Synthesize d-length list of basis
vector_d_i and a proof of linear indepedence.
-/

def get_frame_basis
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} (
    f: affine_frame s) : list (affine_vector s) :=
match f with
| affine_frame.mk_std s := mk_std_basis s
| affine_frame.mk origin basis := basis
end 

-- VECTOR OPERATIONS

-- scalar vector multiplication
def scalar_vector_mult
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} 
    (a : K)
    (v : affine_vector s) : 
    affine_vector s := 
match v with
    | affine_vector.mk_std d := 
        affine_vector.mk 
            (affine_frame.mk_std s)
            (scalar_tuple_mult 
                a 
                (get_vector_coords 
                    (affine_vector.mk_std s)
                )
            )
    | affine_vector.mk frame tuple := 
        affine_vector.mk 
            (get_vector_frame v)
            (scalar_tuple_mult 
                a 
                (get_vector_coords v)
            )
end

instance  vector_has_scalar_mult 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} : 
    has_scalar K (affine_vector s) := 
⟨ scalar_vector_mult ⟩ 

-- vector vector addition
def vector_vector_add 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} 
    (a : K)
    (v1 v2 : affine_vector s) :
    -- (compat : get_vector_frame v1 = get_vector_frame v2)
    affine_vector s :=
match v1, v2 with
| v, affine_vector.mk_std s := v
| affine_vector.mk_std s, v := v
| (affine_vector.mk f1 t1), (affine_vector.mk f2 t2) := 
    affine_vector.mk 
        (get_vector_frame v1)
        (tuple_tuple_add 
            (get_vector_coords v1) 
            (get_vector_coords v2)
        ) 
end

#check vector_vector_add

instance vector_has_add
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} 
    (a : K) :
    has_add (affine_vector s) := 
⟨ @vector_vector_add d K f s a⟩ 

def vector_neg 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} 
    (v : affine_vector s) :
    affine_vector s :=
affine_vector.mk 
    (get_vector_frame v)
    (tuple_neg (get_vector_coords v))

instance vector_has_neg
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} 
    (v : affine_vector s) : 
    has_neg (affine_vector s) := 
⟨ vector_neg ⟩ 

-- zero vector
def vector_zero
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    (s : space d K) : 
    affine_vector s :=
affine_vector.mk 
    (mk_std_frame s)
    (mk_tuple_zero d K)

instance  vector_has_zero
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} : 
    has_zero (affine_vector s) := 
⟨ vector_zero s ⟩  

-- PROPERTIES

set_option pp.notation false

lemma scalar_mult_left_one 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    [o : has_one K] 
    (s : space d K) 
    (v : affine_vector s) : 
    o.one • v = v :=            -- can't write 1 here
begin
simp [has_scalar.smul],
induction d,
cases v,
simp [scalar_vector_mult],
end

lemma scalar_mult_left_zero
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    [z : has_zero K] 
    (s : space d K) 
    (v : affine_vector s) : 
    z.zero • v = (vector_zero s) := 
begin
sorry
end

theorem scal_times_sum_dist  
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K}
    [h: has_add (affine_vector s)]
    {r : K}
    {v1 v2 : affine_vector s} :
    r • (v1 + v2) = r • v1 + r • v2 := 
begin
sorry
end


theorem sum_times_scal_dist 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K}
    [has_scalar K (affine_vector s)]
    [has_add (affine_vector s)]
    (a b : K) 
    (v : affine_vector s) :
    (a + b) • v = a • v + b • v := 
begin
sorry
end


theorem scal_prod_times_dist 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K}
    [has_scalar K (affine_vector s)]
    [has_add (affine_vector s)]
    (v : affine_vector s)
    (a b : K) : 
    (a * b) • v = a • b • v :=
begin
sorry
end


/-
class add_semigroup (α : Type u) extends has_add α :=
(add_assoc : ∀ a b c : α, a + b + c = a + (b + c))
-/
instance vector_add_semigroup
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K}
    (a b : K) 
    (v : affine_vector s) :
    add_semigroup (affine_vector s) := 
begin
sorry
end

/-
class add_monoid (α : Type u) extends add_semigroup α, has_zero α :=
(zero_add : ∀ a : α, 0 + a = a) (add_zero : ∀ a : α, a + 0 = a)
-/
instance vector_add_monoid
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} :
    add_monoid (affine_vector s) := 
begin
sorry
end

/-
class add_comm_monoid (α : Type u) extends add_monoid α, add_comm_semigroup α
-/
instance vector_add_comm_monoid 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} :
    add_comm_monoid (affine_vector s) := 
begin
sorry
end

/-
class add_group (α : Type u) extends add_monoid α, has_neg α :=
(add_left_neg : ∀ a : α, -a + a = 0)
-/
instance vector_add_group 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} :
    add_group (affine_vector s) := 
begin
sorry
end

instance vector_add_comm_group 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} :
    add_comm_group (affine_vector s) := 
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
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} :
    semimodule K (affine_vector s) := 
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
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} :
    module K (affine_vector s) := 
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

set_option class.instance_max_depth 64

instance affine_vector_space 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} :
    vector_space K (affine_vector s) :=  
begin
sorry
end


-- SAVED POINT STUFF

-- point point subtraction
def point_point_sub
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K}
    (p1 p2 : affine_point s) : 
    affine_vector s:=
begin
sorry
end

-- Can't use std lib's has_sub: wrong signature
-- We'll have to define our own notation instead
infix -        := point_point_sub


instance point_inhabited 
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K} :
    inhabited (affine_point s) := 
⟨ affine_point.mk_std s ⟩ 

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


class affine_space  
    {d : ℕ}
    {K: Type} 
    [f : discrete_field K] 
    {s : space d K}
    extends
    torsor (affine_vector s) (affine_point s)