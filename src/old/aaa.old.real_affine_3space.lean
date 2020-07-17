import data.matrix
import data.rat
import data.real.basic
import algebra.pi_instances

-- See https://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.vector.html
-- See https://hal.inria.fr/inria-00377431/document
-- See! http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.652.3183&rep=rep1&type=pdf



/-
Given a group, G, we represent a G-torsor as a tuple (X, m, α, λ, ι, τ, ν), where 
m : G × X → X is the action, and the remaining components represent the associativity
property, the left unit property, the proof that X is a set, the proof that G acts
freely and transitively on X, and the proof that X is nonempty.
-/

class torsor 
    (G : Type) [add_group G]
    (X : Type) [inhabited X] :=
(add : G → X → X)
(sub : X → X → G)
(left_zero : ∀ (x : X), add 0 x = x)
(add_assoc : ∀ (g1 g2 : G) (x : X), add (g1 + g2) x = add g1 (add g2 x))
(add_sub: ∀ (x y : X), add (sub x y) y = x)
(sub_add: ∀ (x : X) (g : G), sub (add g x) x = g)

class affine_space    
    (K: Type)  [discrete_field K]    --discrete_field in Lean is math's "field"
    (V : Type) [add_comm_group V] [vector_space K V] 
    (P : Type) [inhabited P]
extends torsor V P 

/-
The type of n-tuples over a field, K.
Note: Mis-naming: "vector" in Lean is "tuple" in math. 
-/ 
def tuple (K : Type) [discrete_field K] (n : ℕ) := vector K n 
example : tuple ℝ 4 := subtype.mk [1,0,0,0] rfl
def pt_origin_tuple_ℝ_4 : tuple ℝ 4 := subtype.mk [1,0,0,0] rfl
def vec_origin_tuple_ℝ_4 : tuple ℝ 4 := subtype.mk [0,0,0,0] rfl
/-
We're going to represent objects in affine 3-space as
real 4-tuples. We'll represent vectors as 4-tuples where
the first element is zero, and points as 4-tuples where
the first element is one.

KEVIN: This seems overly concrete. Rethink?
-/

def vector3 (K: Type) [discrete_field K]  := { t : tuple K 4 // t.nth 0 = 0 }
def point3 (K: Type) [discrete_field K] := { t : tuple K 4 // t.nth 0 = 1 }

def vector3ℝ := vector3 ℝ 
def point3ℝ := point3 ℝ 
/-
Previous lookahead showed that we should now establish the following properties.
-/
-- what is zero?
-- what is one?

instance  scal_N_vec3: has_scalar ℕ (vector3ℝ) := sorry
--axiom scal_N_vec3' : has_scalar ℕ (vector3ℝ)
instance scal_R_vec3_R: has_scalar ℝ (vector3ℝ) := sorry
axiom v3_left_one : ∀ (x : vector3ℝ), 1 • x = x 
instance : has_zero (vector3ℝ) := sorry
axiom left_zero : ∀ (x : vector3ℝ), 0 • x = 0
instance : has_scalar ℝ ℕ := sorry
axiom right_zero : ∀ (r : ℝ), r • 0 = 0
axiom what_name : has_scalar ℝ (vector3ℝ)
instance : has_add (vector3ℝ) := sorry
axiom scal_times_sum_dist : ∀ (r : ℝ) (x y : vector3ℝ), r • (x + y) = r • x + r • y
axiom sum_times_scal_dist : ∀ (r s : ℝ) (x : vector3ℝ), (r + s) • x = r • x + s • x
axiom scal_prod_times_dist : ∀ (r s : ℝ) (x : vector3ℝ), (r * s) • x = r • s • x
instance : has_neg (vector3ℝ) := sorry

-- And these
axiom v3_add_inv : ∀ (a : vector3ℝ), -a + a = 0
axiom v3_add_comm : ∀ (a b : vector3ℝ), a + b = b + a
axiom v3_add : vector3ℝ → vector3ℝ → vector3ℝ -- right interpretation?
axiom v3_add_assoc : ∀ (a b c : vector3ℝ), a + b + c = a + (b + c)
axiom v3_exists : vector3ℝ
axiom v3_left_zero : ∀ (a : vector3ℝ), 0 + a = a
axiom v3_right_zero : ∀ (a : vector3ℝ), a + 0 = a
axiom v3_neg : vector3 ℝ → vector3ℝ -- right interpretation?

/-
Let's now formalize real affine 3-space.
-/

example : point3ℝ := subtype.mk pt_origin_tuple_ℝ_4 rfl
def point3_std_origin : point3ℝ := subtype.mk pt_origin_tuple_ℝ_4 rfl

instance point3_inhabited : inhabited (point3ℝ) :=
    inhabited.mk point3_std_origin

instance : add_comm_group (vector3ℝ)  :=
begin
apply add_comm_group.mk,
exact v3_add_inv,
exact v3_add_comm,
exact v3_add_assoc,
exact v3_left_zero,
exact v3_right_zero,
end

instance : vector_space ℝ (vector3ℝ) :=
begin
apply vector_space.mk _ _,
apply module.mk _ _,
apply semimodule.mk,
exact scal_times_sum_dist,
exact sum_times_scal_dist,
exact scal_prod_times_dist,
sorry
-- 1/3
--exact v3_left_one,
--doesn't work
end

instance : affine_space ℝ (vector3ℝ) (point3ℝ) :=
begin
-- this is what we want to build
sorry
end

axioms v1 v2 : vector3ℝ 
axioms p1 p2 : point3ℝ 

#check v1 + v2
#check 3 • v1
#check p2 - p1
#check p1 + v1

def p3 : point3ℝ := subtype.mk pt_origin_tuple_ℝ_4 rfl
def v3 : vector3ℝ := subtype.mk vec_origin_tuple_ℝ_4 rfl
