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

def e1 : scalar_expression := scalar_lit 3
def e2 : scalar_expression := scalar_paren e1
def e3 := scalar_add e1 e2
def e4 := scalar_mul e1 e2

def scalar_eval : scalar_expression → scalar_interp → scalar
| (scalar_lit n) i :=  n
| (scalar_paren e) i :=  scalar_eval e i
| (scalar_mul e1 e2) i := nat.mul (scalar_eval e1 i) (scalar_eval e2 i)
| (scalar_add e1 e2) i := nat.add (scalar_eval e1 i) (scalar_eval e2 i)
| (scalar_var v) i := i v

#reduce scalar_eval (scalar_lit 3) init_scalar_interp

/-
    VEC_EXPR := (VEC_EXPR) | VEC_EXPR + VEC_EXPR | VEC_EXPR * SCALAR_EXPR | VEC_VAR | VEC_LITERAL
-/

structure vector_space : Type :=
mk :: (index : ℕ)

def bar_vector_space := vector_space.mk 0
def foo_vector_space := vector_space.mk 1

structure vector_variable (sp : vector_space) : Type :=
mk :: (index : ℕ)

structure vector (sp : vector_space) : Type :=
mk :: (x y z : ℕ)

#check vector.mk

def vector_interp (sp : vector_space) := vector_variable sp → vector sp
def init_vector_interp : vector_interp bar_vector_space := λ v : vector_variable bar_vector_space, @vector.mk bar_vector_space 0 0 0

def v1 := @vector.mk bar_vector_space 1 2 3
def v2 := @vector.mk bar_vector_space 1 6 2
def v3 := @vector.mk bar_vector_space 0 1 3
def v4 := @vector.mk bar_vector_space 1 2 4

#reduce v1 

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

def ve1 : vector_expression bar_vector_space := (vector_literal v1)
def ve2 : vector_expression bar_vector_space := vector_add (vector_literal v2) (ve1)
def vv0 : vector_variable bar_vector_space := vector_variable.mk _ 0
def vv1 : vector_variable foo_vector_space := vector_variable.mk _ 1
def vv0_e : vector_expression bar_vector_space := vector_paren (vector_var vv0)

def vv1_e : vector_expression bar_vector_space := scalar_vector_mul (scalar_lit 3) (vector_var vv1)  -- Type error expected
-- This line will fail to typecheck because vv1 was defined with vector_space foo_vector_space,
-- rather than expected bar_vector_space

def vv2_e : vector_expression _ := vector_add (vector_var vv0) (vector_var vv0) 
-- Type inference working as expected

def vve_e : vector_expression _ := vector_add (vector_var vv0) (vector_var vv1) -- Type error expected
-- Additional example with error + type inference


def v_interp : vector_interp bar_vector_space := λ v : vector_variable bar_vector_space,
        match v.index with,
            0 := vector.mk _ 1 1 1,
            1 := vector.mk _ 2 2 2,
            _ := vector.mk _ 0 0 0
        end

#reduce vector_eval bar_vector_space (ve2) init_vector_interp init_scalar_interp
#reduce vector_eval bar_vector_space (vector_add vv0_e vv1_e) v_interp init_scalar_interp

structure transform (inp outp: vector_space): Type

def transform_apply {sp1 sp2 : vector_space} (t : transform sp1 sp2) (inputvec : vector sp1) : 
    vector sp2 := 
        vector.mk sp2 0 0 0
        --todo: make transformations take in 3 vectors (col and row)
def transform_compose {sp1 sp2 sp3: vector_space} (t1 : transform sp1 sp2) (t2 : transform sp2 sp3) : 
    transform sp1 sp3 := 
        transform.mk sp1 sp3
        --Make transformation take in 3 vectors ('Yanni')
def t1 := transform.mk foo_vector_space bar_vector_space
def t2 := transform.mk bar_vector_space foo_vector_space
#check transform_apply t1 v1 --type error expected
#check transform_apply t2 v1
#check transform_apply t1 (transform_apply t2 v1)
def res2 : vector _ := 
    ( transform_apply ( t2 : transform _ _)  ( v2 : vector _ ) : vector _ )

def vvv1 := @vector.mk bar_vector_space 1 2 3
def vvv2 := @vector.mk foo_vector_space 1 6 2



def vvv3 := vector_add (vector_literal vvv1) (vector_literal (transform_apply t1 ( vvv2)))
end peirce