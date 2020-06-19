import algebra.module
import .n_K_tuple
--import .affine_space


/-
We will represent vectors in an affine n-space over K 
as n+1 dimensional tuples over K with 0'th entries
equal to 0. With element-wise tuple addition and scalar
multiplication, we will prove that these objects form a
vector space.
-/
def affine_n_K_vector 
    (n : ℕ) [has_zero (fin n)] 
    (K: Type) [discrete_field K]  := 
{ t : n_K_tuple K (n + 1) // t.nth 0 = 0 }

/-
We will represent points n an affine n-space over K 
as n+1 dimensional tuples over K with 0'th entries
equal to 1. With element-wise tuple addition and scalar
multiplication, we will prove that these objects form a
torsor, with differences between them giving rise to
vectors as defined just above.
-/
def affine_n_K_point 
    (n : ℕ)  [has_zero (fin n)] 
    (K: Type) [discrete_field K] := 
{ t : n_K_tuple K (n + 1) // t.nth 0 = 1 }

/-
Clearly this won't work, as the length here is 4 in particular

def affine_n_K_point_origin_tuple (n : ℕ) (K: Type) [discrete_field K] : n_K_tuple K n := 
        subtype.mk [1,0,0,0] rfl

def affine_n_K_vector_zero_tuple (n : ℕ) (K: Type) [discrete_field K] : n_K_tuple K n := 
        subtype.mk [0,0,0,0] rfl

--def pt_origin_tuple_ℝ_4 : n_K_tuple ℝ 4 := 
--        subtype.mk [1,0,0,0] rfl

--def vec_origin_tuple_ℝ_4 : n_K_tuple ℝ 4 := 
--        subtype.mk [0,0,0,0] rfl
-/

/-
Previous lookahead showed that we should now establish the following properties.
-/
-- what is zero?
-- what is one?

-- has_salar comes from module.lean

instance  scal_N_vec_n: has_scalar ℕ (affine_n_K_vector) := sorry
--axiom scal_N_vec3' : has_scalar ℕ (affine_three_K_vectorℝ)
instance scal_R_vec_n: has_scalar ℝ (affine_n_K_vector) := sorry

/-
PROPERTIES HOLD

That right there is where the conflict/problem is.
-/

axiom v3_left_one : ∀ (n : ℕ) (K : Type) [discrete_field K] (x : affine_n_K_vector n K), 1 • x = x 

instance : ∀ (n : ℕ) (K : Type) [discrete_field K], has_zero (affine_n_K_vector) := sorry

/-
Stopped here. Is it impossible to prove these constraints hold
in the general case, without specifying a particular n and/or K?
-/


axiom left_zero : ∀ (n : ℕ) (K : Type) [discrete_field K] (x : affine_n_K_vector n K), 0 • x = 0

/-
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)
infixr ` • `:73 := has_scalar.smul
-/
instance : has_scalar ℝ ℕ := sorry

axiom right_zero : 
    ∀ (n : ℕ) (K : Type) [discrete_field K] (r : K), 
        r • 0 = 0 -- error, inferring 0 of type ℕ

axiom what_name_for_this : 
    ∀ (n : ℕ) (K : Type) [discrete_field K], 
        has_scalar K (affine_n_K_vector n K)
            -- := <element-wise mult by given K>

-- undefined here due to error above
axiom affine_vector_has_add : 
    ∀ (n : ℕ) (K : Type) [discrete_field K], 
        has_add (affine_n_K_vector n K) 


axiom scal_times_sum_dist : 
    ∀ (n : ℕ) (K : Type) [discrete_field K], 
        ∀ (r : K) (x y : affine_n_K_vector n K), 
            r • (x + y) = r • x + r • y


axiom sum_times_scal_dist : 
    ∀ (n : ℕ) (K : Type) [discrete_field K], 
        ∀ (r s : K) (x : affine_n_K_vector n K), 
            (r + s) • x = r • x + s • x


axiom scal_prod_times_dist : 
    ∀ (n : ℕ) (K : Type) [discrete_field K], 
        ∀ (r s : K) (x : affine_n_K_vector n K), 
            (r * s) • x = r • s • x

-- OOPS, this isn't right. Instances are concrete
-- Move this to later, where K=ℝ and n=4.
axiom has_negatives : 
    ∀ (n : ℕ) (K : Type) [discrete_field K],
        has_neg (affine_n_K_vector n K) 


/-
instance  scal_N_vec3: has_scalar ℕ (affine_three_K_vectorℝ) := sorry
--axiom scal_N_vec3' : has_scalar ℕ (affine_three_K_vectorℝ)
instance scal_R_vec3_R: has_scalar ℝ (affine_three_K_vectorℝ) := sorry
axiom v3_left_one : ∀ (x : affine_three_K_vectorℝ), 1 • x = x 
instance : has_zero (affine_three_K_vectorℝ) := sorry
axiom left_zero : ∀ (x : affine_three_K_vectorℝ), 0 • x = 0
instance : has_scalar ℝ ℕ := sorry
axiom right_zero : ∀ (r : ℝ), r • 0 = 0
axiom what_name : has_scalar ℝ (affine_three_K_vectorℝ)
instance : has_add (affine_three_K_vectorℝ) := sorry
axiom scal_times_sum_dist : ∀ (r : ℝ) (x y : affine_three_K_vectorℝ), r • (x + y) = r • x + r • y
axiom sum_times_scal_dist : ∀ (r s : ℝ) (x : affine_three_K_vectorℝ), (r + s) • x = r • x + s • x
axiom scal_prod_times_dist : ∀ (r s : ℝ) (x : affine_three_K_vectorℝ), (r * s) • x = r • s • x
instance : has_neg (affine_three_K_vectorℝ) := sorry
-/


-- And these
axiom v3_add_inv : ∀ (a : affine_three_K_vectorℝ), -a + a = 0
axiom v3_add_comm : ∀ (a b : affine_three_K_vectorℝ), a + b = b + a
axiom v3_add : affine_three_K_vectorℝ → affine_three_K_vectorℝ → affine_three_K_vectorℝ -- right interpretation?
axiom v3_add_assoc : ∀ (a b c : affine_three_K_vectorℝ), a + b + c = a + (b + c)
axiom v3_exists : affine_three_K_vectorℝ
axiom v3_left_zero : ∀ (a : affine_three_K_vectorℝ), 0 + a = a
axiom v3_right_zero : ∀ (a : affine_three_K_vectorℝ), a + 0 = a
axiom v3_neg : affine_three_K_vector ℝ → affine_three_K_vectorℝ 


/-
axiom v3_add_inv : ∀ (a : affine_three_K_vectorℝ), -a + a = 0
axiom v3_add_comm : ∀ (a b : affine_three_K_vectorℝ), a + b = b + a
axiom v3_add : affine_three_K_vectorℝ → affine_three_K_vectorℝ → affine_three_K_vectorℝ -- right interpretation?
axiom v3_add_assoc : ∀ (a b c : affine_three_K_vectorℝ), a + b + c = a + (b + c)
axiom v3_exists : affine_three_K_vectorℝ
axiom v3_left_zero : ∀ (a : affine_three_K_vectorℝ), 0 + a = a
axiom v3_right_zero : ∀ (a : affine_three_K_vectorℝ), a + 0 = a
axiom v3_neg : affine_three_K_vector ℝ → affine_three_K_vectorℝ -- right interpretation?
-/

/-
Let's now formalize real affine 3-space.
-/

example : point3ℝ := subtype.mk pt_origin_tuple_ℝ_4 rfl
def point3_std_origin : point3ℝ := subtype.mk pt_origin_tuple_ℝ_4 rfl

instance point3_inhabited : inhabited (point3ℝ) :=
    inhabited.mk point3_std_origin

instance : add_comm_group (affine_three_K_vectorℝ)  :=
begin
apply add_comm_group.mk,
exact v3_add_inv,
exact v3_add_comm,
exact v3_add_assoc,
exact v3_left_zero,
exact v3_right_zero,
end

instance : vector_space ℝ (affine_three_K_vectorℝ) :=
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

instance : affine_space ℝ (affine_three_K_vectorℝ) (point3ℝ) :=
begin
-- this is what we want to build
sorry
end

axioms v1 v2 : affine_three_K_vectorℝ 
axioms p1 p2 : point3ℝ 

#check v1 + v2
#check 3 • v1
#check p2 - p1
#check p1 + v1

def p3 : point3ℝ := subtype.mk pt_origin_tuple_ℝ_4 rfl
def v3 : affine_three_K_vectorℝ := subtype.mk vec_origin_tuple_ℝ_4 rfl
