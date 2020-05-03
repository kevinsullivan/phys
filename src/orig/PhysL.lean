/-
SCALAR_EXPR := (SCALAR_EXPR) | SCALAR_EXPR + SCALAR_EXPR | SCALAR_EXPR * SCALAR_EXPR | SCALAR_VAR | SCALAR_LITERAL
-/

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

structure space : Type :=
mk :: (index : ℕ)

def bar_space := space.mk 0
def foo_space := space.mk 1

structure vector_variable (sp : space) : Type :=
mk :: (index : ℕ)

structure phys_vector (sp : space) : Type :=
mk :: (x y z : ℕ)

#check phys_vector.mk

def vector_interp (sp : space) := vector_variable sp → phys_vector sp
def init_vector_interp : vector_interp bar_space := λ v : vector_variable bar_space, @phys_vector.mk bar_space 0 0 0

def v1 := @phys_vector.mk bar_space 1 2 3
def v2 := @phys_vector.mk bar_space 1 6 2
def v3 := @phys_vector.mk bar_space 0 1 3
def v4 := @phys_vector.mk bar_space 1 2 4

#reduce v1

inductive vector_space_transformation : Type

inductive vector_space_transformation_expressions : Type

inductive vector_expression (sp: space) : Type 
| vector_literal : @phys_vector sp → vector_expression
| scalar_vector_mul : scalar_expression → vector_expression → vector_expression
| vector_paren : vector_expression → vector_expression 
| vector_mul : vector_expression → vector_expression → vector_expression
| vector_add : vector_expression → vector_expression → vector_expression
| vector_var : vector_variable sp → vector_expression

open vector_expression

def vector_eval (sp : space) : vector_expression sp → vector_interp sp → scalar_interp → phys_vector sp
| (vector_literal v) i_v i_s :=  v
| (scalar_vector_mul s v) i_v i_s :=
        let interp_v := (vector_eval v i_v i_s) in
        let interp_s := scalar_eval s i_s in
        (@phys_vector.mk sp
            (interp_v.x * interp_s)
            (interp_v.y * interp_s)
            (interp_v.z * interp_s)
        )
| (vector_paren v) i_v i_s := vector_eval v i_v i_s
| (vector_mul e1 e2) iv is := phys_vector.mk _ 0 0 0 -- stub
| (vector_add e1 e2) i_v i_s := 
        let interp_v1 := vector_eval e1 i_v i_s in
        let interp_v2 := vector_eval e2 i_v i_s in
        (@phys_vector.mk sp
            (interp_v1.x + interp_v2.x)
            (interp_v1.y + interp_v2.y)
            (interp_v1.z + interp_v2.z)
        )
| (vector_var v) i_v i_s := i_v v

-- Example code below
-- Note: You need to define vectors, vector variable interpreters, and vector expressions
--       with a vector space argument

def ve1 : vector_expression bar_space := (vector_literal v1)
def ve2 : vector_expression bar_space := vector_add (vector_literal v2) (ve1)
def vv0 : vector_variable bar_space := vector_variable.mk _ 0
def vv1 : vector_variable foo_space := vector_variable.mk _ 1
def vv0_e : vector_expression bar_space := vector_paren (vector_var vv0)

def vv1_e : vector_expression bar_space := scalar_vector_mul (scalar_lit 3) (vector_var vv1)  -- Type error expected
-- This line will fail to typecheck because vv1 was defined with space foo_space,
-- rather than expected bar_space

def vv2_e : vector_expression _ := vector_add (vector_var vv0) (vector_var vv0) 
-- Type inference working as expected

def vve_e : vector_expression _ := vector_add (vector_var vv0) (vector_var vv1) -- Type error expected
-- Additional example with error + type inference


def v_interp : vector_interp bar_space := λ v : vector_variable bar_space,
        match v.index with,
            0 := phys_vector.mk _ 1 1 1,
            1 := phys_vector.mk _ 2 2 2,
            _ := phys_vector.mk _ 0 0 0
        end

#reduce vector_eval bar_space (ve2) init_vector_interp init_scalar_interp
#reduce vector_eval bar_space (vector_add vv0_e vv1_e) v_interp init_scalar_interp

structure transform (inp outp: space): Type

def transform_apply {sp1 sp2 : space} (t : transform sp1 sp2) (inputvec : phys_vector sp1) : 
    phys_vector sp2 := 
        phys_vector.mk sp2 0 0 0

def t1 := transform.mk foo_space bar_space
def t2 := transform.mk bar_space foo_space
#check transform_apply t1 v1 --type error expected
#check transform_apply t2 v1
#check transform_apply t1 (transform_apply t2 v1)
def res2 : phys_vector _ := 
    ( transform_apply ( t2 : transform _ _)  ( v2 : phys_vector _ ) : phys_vector _ )