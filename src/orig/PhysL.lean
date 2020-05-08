/-
SCALAR_EXPR := (SCALAR_EXPR) | SCALAR_EXPR + SCALAR_EXPR | SCALAR_EXPR * SCALAR_EXPR | SCALAR_VAR | SCALAR_LITERAL
-/
namespace peirce
def scalar := ℕ

structure scalar_variable : Type :=
mk :: (index : ℕ)

def scalar_interp := scalar_variable → scalar

def init_scalar_interp := λ (s : scalar_variable), 0

inductive scalar_expression : Type 
| scalar_lit : ℕ → scalar_expression
| scalar_paren : scalar_expression → scalar_expression
| scalar_mul : scalar_expression → scalar_expression → scalar_expression
| scalar_add : scalar_expression → scalar_expression → scalar_expression
| scalar_var : scalar_variable → scalar_expression

open scalar_expression

def scalar_eval : scalar_expression → scalar_interp → scalar
| (scalar_lit n) i :=  n
| (scalar_paren e) i :=  scalar_eval e i
| (scalar_mul e1 e2) i := nat.mul (scalar_eval e1 i) (scalar_eval e2 i)
| (scalar_add e1 e2) i := nat.add (scalar_eval e1 i) (scalar_eval e2 i)
| (scalar_var v) i := i v


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

def mk_vector_interp (sp : vector_space ) : vector_interp sp := λ (v : vector_variable sp), @vector.mk sp 0 0 0


inductive vector_expression (sp: vector_space) : Type 
| vector_literal : @vector sp → vector_expression
| scalar_vector_mul : scalar_expression → vector_expression → vector_expression
| vector_paren : vector_expression → vector_expression 
| vector_add : vector_expression → vector_expression → vector_expression
| vector_var : vector_variable sp → vector_expression

open vector_expression

--Vec v(1, 1, 1);



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

--EVERYTHING IS BASED ON COLUMN VECTORS
/-
note: output vector space is implied, 
doesn't need to be explicitly stated
-/

/-
TRANSFORM_EXPR := (TRANSFORM_EXPR) | TRANSFORM_COMPOSITION | TRANSFORM_VAR | TRANSFORM_LITERAL
-/


structure transform (input output: vector_space): Type :=
mk :: (one two three : vector_expression output)

inductive transform_variable (input output : vector_space) :  Type
| mk : ℕ → transform_variable

def transform_interp (sp1 sp2 : vector_space) := transform_variable sp1 sp2 → transform sp1 sp2

def mk_transform_interp (sp1 sp2 : vector_space ) : transform_interp sp1 sp2 := λ (t : transform_variable sp1 sp2), @transform.mk sp1 sp2 (vector_literal (@vector.mk sp2 0 0 0)) (vector_literal (@vector.mk sp2 0 0 0))  (vector_literal (@vector.mk sp2 0 0 0)) 

inductive transform_expression (sp1 sp2 : vector_space)
| transform_literal : (transform sp1 sp2) → transform_expression
| transform_var : transform_variable sp1 sp2→ transform_expression
| transform_paren : transform_expression → transform_expression

open transform_expression

def transform_eval (sp1 sp2 : vector_space) : transform_expression sp1 sp2 → transform_interp sp1 sp2 → transform sp1 sp2
| (transform_literal t1) i := t1
| (transform_var v) i := i v
| (transform_paren t1) i := transform_eval t1 i

            
def matrix_mul_cols {sp1 sp2 : vector_space} (v1 v2 v3 : vector sp2) (v4 : vector sp1) : 
    (vector sp2) := 
        @vector.mk sp2 
            (v1.x*v4.x+v2.x*v4.y+v3.x*v4.z) 
            (v1.y*v4.x+v2.y*v4.y+v3.y*v4.z) 
            (v1.z*v4.x+v2.z*v4.y+v3.z*v4.z) 

def transform_apply {sp1 sp2 : vector_space} (t : transform_expression sp1 sp2) (inputvec : vector_expression sp1) : 
    vector_expression sp2 := 
        vector_expression.vector_literal
            (matrix_mul_cols 
                (vector_eval sp2 (transform_eval sp1 sp2 t (mk_transform_interp sp1 sp2)).one (mk_vector_interp sp2) init_scalar_interp)
                (vector_eval sp2 (transform_eval sp1 sp2 t (mk_transform_interp sp1 sp2)).two (mk_vector_interp sp2) init_scalar_interp)
                (vector_eval sp2 (transform_eval sp1 sp2 t (mk_transform_interp sp1 sp2)).three (mk_vector_interp sp2) init_scalar_interp)
                (vector_eval sp1 inputvec (mk_vector_interp sp1) init_scalar_interp))

def transform_compose {sp1 sp2 sp3: vector_space} (t1 : transform_expression sp2 sp1) (t2 : transform_expression sp3 sp2) : 
    transform_expression sp3 sp1 := 
        transform_expression.transform_literal
            (@transform.mk sp3 sp1
                ((transform_apply t1 (transform_eval sp3 sp2 t2 (mk_transform_interp sp3 sp2)).one))
                ((transform_apply t1 (transform_eval sp3 sp2 t2 (mk_transform_interp sp3 sp2)).two))
                ((transform_apply t1 (transform_eval sp3 sp2 t2 (mk_transform_interp sp3 sp2)).three)))
            --(matrix_mul_cols t2.one t2.two t2.three t1.one) 
            --(matrix_mul_cols t2.one t2.two t2.three t1.two)
            --(matrix_mul_cols t2.one t2.two t2.three t1.three)



structure bool_var : Type :=
mk :: (index : ℕ)

inductive boolean_expression
| lit (b : bool)
| var (v : bool_var)
| and (e1 e2 : boolean_expression)

inductive scalar_cmd : Type
| SKIP : scalar_cmd
| assmt : scalar_variable → scalar_expression → scalar_cmd
| ite : boolean_expression → scalar_cmd →  scalar_cmd → scalar_cmd
| while : boolean_expression → scalar_cmd → scalar_cmd → scalar_cmd

inductive vector_cmd : Type
| SKIP : vector_cmd
| assmt : ∀ sp : vector_space, vector_variable sp → vector_expression sp → vector_cmd
| ite : boolean_expression → vector_cmd → vector_cmd → vector_cmd
| while : boolean_expression → vector_cmd → vector_cmd

inductive transform_cmd : Type
| SKIP : transform_cmd
| assmt : ∀ sp1 sp2 : vector_space, transform_variable sp1 sp2 → transform_expression sp1 sp2 → transform_cmd
| ite : boolean_expression → transform_cmd → transform_cmd → transform_cmd
| while : boolean_expression → transform_cmd → transform_cmd

end peirce