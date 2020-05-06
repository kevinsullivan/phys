/-
SCALAR_EXPR := (SCALAR_EXPR) | SCALAR_EXPR + SCALAR_EXPR | SCALAR_EXPR * SCALAR_EXPR | SCALAR_VAR | SCALAR_LITERAL
-/
namespace peirce
def scalar := ℕ

structure scalar_var : Type :=
mk :: (index : ℕ)

def scalar_interp := scalar_var → scalar

def init_scalar_interp := λ (s : scalar_var), 0

inductive scalar_expression : Type 
| scalar_lit : ℕ → scalar_expression
| scalar_paren : scalar_expression → scalar_expression
| scalar_mul : scalar_expression → scalar_expression → scalar_expression
| scalar_add : scalar_expression → scalar_expression → scalar_expression
| scalar_var : scalar_var → scalar_expression

open scalar_expression

def scalar_eval : scalar_expression → scalar_interp → scalar
| (scalar_lit n) i :=  n
| (scalar_paren e) i :=  scalar_eval e i
| (scalar_mul e1 e2) i := nat.mul (scalar_eval e1 i) (scalar_eval e2 i)
| (scalar_add e1 e2) i := nat.add (scalar_eval e1 i) (scalar_eval e2 i)
| (scalar_expression.scalar_var v) i := i v







/-
    VEC_EXPR := (VEC_EXPR) | VEC_EXPR + VEC_EXPR | VEC_EXPR * SCALAR_EXPR | VEC_VAR | VEC_LITERAL
-/
--TODO: refactor vector_space and vectors so that they are mutually inducted.
structure vector_space : Type :=
mk :: (index : ℕ)



structure vector_variable (sp : vector_space) : Type :=
mk :: (index : ℕ)

structure vector (sp : vector_space) : Type :=
mk :: (x y z : ℕ)



def vector_interp (sp : vector_space) := vector_variable sp → vector sp




inductive vector_vector_space_transformation : Type

inductive vector_vector_space_transformation_expressions : Type

inductive vector_expression (sp: vector_space) : Type 
| vector_literal : @vector sp → vector_expression
| scalar_vector_mul : scalar_expression → vector_expression → vector_expression
| vector_paren : vector_expression → vector_expression 
| vector_add : vector_expression → vector_expression → vector_expression
| vector_var : vector_variable sp → vector_expression

open vector_expression




def vector_eval (sp : vector_space) : vector_expression sp → vector_interp sp → scalar_interp → vector sp
| (vector_literal v) i_v i_s :=  v
| (scalar_vector_mul s v) i_v i_s :=
        let interp_v := (vector_eval v i_v i_s) in
        let interp_s := scalar_eval s i_s in
        (@vector.mk sp
            (interp_v.x * interp_s)
            (interp_v.y * interp_s)
            (interp_v.z * interp_s)
        )
| (vector_paren v) i_v i_s := vector_eval v i_v i_s
| (vector_add e1 e2) i_v i_s := 
        let interp_v1 := vector_eval e1 i_v i_s in
        let interp_v2 := vector_eval e2 i_v i_s in
        (@vector.mk sp
            (interp_v1.x + interp_v2.x)
            (interp_v1.y + interp_v2.y)
            (interp_v1.z + interp_v2.z)
        )
| (vector_var v) i_v i_s := i_v v

-- Example code below
-- Note: You need to define vectors, vector variable interpreters, and vector expressions
--       with a vector vector_space argument


structure transform (input output: vector_space): Type :=
mk :: (one two three : vector output)
--EVERYTHING IS BASED ON COLUMN VECTORS


def matrix_mul_cols {sp1 sp2 : vector_space} (v1 v2 v3 : vector sp2) (v4 : vector sp1) : 
    (vector sp2) := 
        vector.mk sp2 
            (v1.x*v4.x+v2.x*v4.y+v3.x*v4.z) 
            (v1.y*v4.x+v2.y*v4.y+v3.y*v4.z) 
            (v1.z*v4.x+v2.z*v4.y+v3.z*v4.z) 

def transform_apply {sp1 sp2 : vector_space} (t : transform sp1 sp2) (inputvec : vector sp1) : 
    vector sp2 := 
        matrix_mul_cols t.one t.two t.three inputvec

def transform_compose {sp1 sp2 sp3: vector_space} (t1 : transform sp1 sp2) (t2 : transform sp2 sp3) : 
    transform sp1 sp3 := 
        transform.mk sp1 
            (matrix_mul_cols t2.one t2.two t2.three t1.one) 
            (matrix_mul_cols t2.one t2.two t2.three t1.two)
            (matrix_mul_cols t2.one t2.two t2.three t1.three)
       
--def res2 : vector _ := 
    --( transform_apply ( t2 : transform _ _)  ( v2 : vector _ ) : vector _ )




end peirce