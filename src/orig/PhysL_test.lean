import .PhysL
open peirce

open peirce.scalar_expression
open peirce.vector_expression
open peirce.transform_expression


def bar := vector_space.mk 0
def foo := vector_space.mk 1


-- Test scalar_expression constructors
def e1 : scalar_expression := scalar_lit 3
def e2 : scalar_expression := scalar_paren e1
def e3 := scalar_add e1 e2
def e4 := scalar_mul e1 e2

-- Test scalar_eval
#reduce scalar_eval (scalar_lit 3) init_scalar_interp


-- Test vector constructor
#check vector.mk

def init_vector_interp : vector_interp bar := λ v : vector_variable bar, @vector.mk bar 0 0 0

def v1 := @vector.mk bar 1 2 3
#eval v1

--def v2 : vector bar := @vector.mk bar 1 6 2
def v3 := @vector.mk bar 0 1 3
def v4 := @vector.mk bar 1 2 4

#reduce v1


-- Test vector_experssion constructors and vector_eval
-- Example code below
-- Note: You need to define vectors, vector variable interpreters, and vector expressions
--       with a vector vector_space argument

def ve1 : vector_expression bar := (vector_literal v1)
def vv0 : vector_variable bar := @vector_variable.mk _ 0
def vv1 : vector_variable foo := @vector_variable.mk _ 1
def vv0_e : vector_expression bar := vector_paren (vector_var vv0)

def v_var : vector_variable bar := @vector_variable.mk bar 1
def v : vector_expression bar := vector_var v_var
#check v == @vector_literal bar (@vector.mk bar 1 1 1)

-- .... 



def vv1_e : vector_expression bar := scalar_vector_mul (scalar_lit 3) (vector_var vv1)  -- Type error expected
-- This line will fail to typecheck because vv1 was defined with vector_space foo,
-- rather than expected bar

def vv2_e : vector_expression _ := vector_add (vector_var vv0) (vector_var vv0) 
-- Type inference working as expected

def vve_e : vector_expression _ := vector_add (vector_var vv0) (vector_var vv1) -- Type error expected
-- Additional example with error + type inference


def v_interp : vector_interp bar := λ v : vector_variable bar,
        match v.index with,
            0 := @vector.mk _ 1 1 1,
            1 := @vector.mk _ 2 2 2,
            _ := @vector.mk _ 0 0 0
        end

#reduce vector_eval v init_vector_interp init_scalar_interp
#reduce vector_eval (vector_add vv0_e vv1_e) v_interp init_scalar_interp

--Linear transformation tests
/-
t1 : foo → bar
Matrix of transformation:
    [ 1 1 1 ]
    [ 0 1 1 ]
    [ 0 0 1 ]

-/
def t1 := @transform.mk foo bar
    (vector_literal (@vector.mk bar 1 0 0)) (vector_literal (@vector.mk bar 1 1 0)) (vector_literal (@vector.mk bar 1 1 1))

/-
t2 : bar → foo
    Matrix of Transformation:
    [ 2 0 0 ]
    [ 0 2 0 ]
    [ 0 0 2 ]
-/
def t2 := @transform.mk bar foo 
    (vector_literal (@vector.mk foo 2 0 0)) (vector_literal (@vector.mk foo 0 2 0)) (vector_literal (@vector.mk foo 0 0 2))

#check t1
#check v1
#check transform_apply (transform_literal t1) (vector_literal v1) --type error expected
#check t2
#check transform_apply (transform_literal t2) (vector_literal v1)
#check transform_apply (transform_literal t1) (transform_apply (transform_literal t2) (vector_literal v1))

#check t1
#check t2
--t1 composed with t2: foo → foo
#check transform_compose (transform_literal t1) (transform_literal t2) 

/-
t3 : foo → foo
    Matrix of Transformation:
    [ 2 0 0 ]   [ 1 1 1 ]    [ 2 2 2 ]
    [ 0 2 0 ] * [ 0 1 1 ] =  [ 0 2 2 ] 
    [ 0 0 2 ]   [ 0 0 1 ]    [ 0 0 2 ]
       M_T1   *   M_T2    =   M_T3
-/
def t3 := transform_compose (transform_literal t1) (transform_literal t2)
#eval (vector_eval (transform_eval t3 mk_transform_interp).one mk_vector_interp init_scalar_interp).x
#eval (vector_eval (transform_eval t3 mk_transform_interp).one mk_vector_interp init_scalar_interp).y
#eval (vector_eval (transform_eval t3 mk_transform_interp).one mk_vector_interp init_scalar_interp).z
#eval (vector_eval (transform_eval t3 mk_transform_interp).two mk_vector_interp init_scalar_interp).x
#eval (vector_eval (transform_eval t3 mk_transform_interp).two mk_vector_interp init_scalar_interp).y
#eval (vector_eval (transform_eval t3 mk_transform_interp).two mk_vector_interp init_scalar_interp).z
#eval (vector_eval (transform_eval t3 mk_transform_interp).three mk_vector_interp init_scalar_interp).x
#eval (vector_eval (transform_eval t3 mk_transform_interp).three mk_vector_interp init_scalar_interp).y
#eval (vector_eval (transform_eval t3 mk_transform_interp).three mk_vector_interp init_scalar_interp).z
def vvv1 := @vector.mk bar 1 2 3
def vvv2 := @vector.mk foo 1 6 2

def vvv3 := vector_add (vector_literal vvv1) (transform_apply (transform_literal t1) (vector_literal vvv2))



-- BELOW HERE IS OUTPUT COPIED FROM RESULTS OF PEIRCE, WITH GEOM VECTOR_SPACE CTRL+H'D IN

def time : peirce.vector_space := peirce.vector_space.mk 4
def geom : peirce.vector_space := peirce.vector_space.mk 5

def flt_var : peirce.scalar_variable := peirce.scalar_variable.mk  1
def flt : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt_var ( ( peirce.scalar_expression.scalar_lit 0 : peirce.scalar_expression ) )

def flt2_var : peirce.scalar_variable := peirce.scalar_variable.mk  2
def flt2 : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt2_var ( ( peirce.scalar_expression.scalar_lit 0 : peirce.scalar_expression ) )

def flt3_var : peirce.scalar_variable := peirce.scalar_variable.mk  3
def flt3 : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt3_var ( ( peirce.scalar_expression.scalar_var flt2_var : peirce.scalar_expression  )  )

def flt4_var : peirce.scalar_variable := peirce.scalar_variable.mk  4
def flt4 : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt4_var ( ( peirce.scalar_expression.scalar_mul ( peirce.scalar_expression.scalar_var flt3_var : peirce.scalar_expression  )  ( peirce.scalar_expression.scalar_var flt3_var : peirce.scalar_expression  )  : peirce.scalar_expression )  )

def r2o2_var : peirce.scalar_variable := peirce.scalar_variable.mk  5
def r2o2 : peirce.scalar_cmd := peirce.scalar_cmd.assmt r2o2_var ( ( peirce.scalar_expression.scalar_lit 0 : peirce.scalar_expression ) )

def v1_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 6
def v12 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v1_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def v2_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 7
def v2 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v2_var ( ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  )

def r11_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 8
def r11 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r11_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def r12_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 9
def r12 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r12_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def r13_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 10
def r13 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r13_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def res1_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 11
def res1 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res1_var ( ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  )

def vvv_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 12
def vvv : peirce.vector_cmd := @peirce.vector_cmd.assmt geom vvv_var ( ( @peirce.vector_expression.vector_add geom ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom v2_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def v3_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 13
def v32 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v3_var ( ( @peirce.vector_expression.scalar_vector_mul geom ( peirce.scalar_expression.scalar_var flt2_var : peirce.scalar_expression  )  ( @peirce.vector_expression.vector_var geom v2_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def v4_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 14
def v42 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v4_var ( ( @peirce.vector_expression.vector_paren geom ( @peirce.vector_expression.vector_add geom ( @peirce.vector_expression.vector_var geom v3_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_add geom ( @peirce.vector_expression.vector_var geom v2_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom v2_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) : peirce.vector_expression geom ) : peirce.vector_expression geom )  )

def r21_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 15
def r21 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r21_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def r22_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 16
def r22 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r22_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def r23_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 17
def r23 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r23_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def s11_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 18
def s11 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom s11_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def s12_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 19
def s12 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom s12_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def s13_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 20
def s13 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom s13_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def sh1_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 21
def sh1 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom sh1_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def sh2_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 22
def sh2 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom sh2_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def sh3_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 23
def sh3 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom sh3_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def p1_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 24
def p1 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom p1_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def p2_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 25
def p2 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom p2_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def p3_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 26
def p3 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom p3_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def c1_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 27
def c1 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom c1_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def c2_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 28
def c2 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom c2_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def c3_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 29
def c3 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom c3_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )


def rotation1_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 33
def rotation1 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotation1_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom r11_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom r12_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom r13_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def rotation2_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 34
def rotation2 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotation2_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom r21_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom r22_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom r23_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def scale1_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 35
def scale1 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom scale1_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom s11_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom s12_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom s13_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def sheer1_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 36
def sheer1 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom sheer1_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom sh1_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom sh2_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom sh3_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def projection_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 37
def projection : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom projection_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom p1_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom p2_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom p3_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def double_rotate_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 38
def double_rotate : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom double_rotate_var ( ( peirce.transform_compose ( @peirce.transform_expression.transform_var geom geom rotation1_var : peirce.transform_expression geom geom )  ( @peirce.transform_expression.transform_var geom geom rotation2_var : peirce.transform_expression geom geom )  : peirce.transform_expression geom geom )  )

def rotate_and_scale_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 39
def rotate_and_scale : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotate_and_scale_var ( ( peirce.transform_compose ( @peirce.transform_expression.transform_var geom geom double_rotate_var : peirce.transform_expression geom geom )  ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  : peirce.transform_expression geom geom )  )

def cob1_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 40
def cob1 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom cob1_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom c1_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom c2_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom c3_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def v2_41 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v2_var ( ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  )

def res1_42 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res1_var ( ( peirce.transform_apply ( @peirce.transform_expression.transform_var geom geom rotation1_var : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def v2_43 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v2_var ( ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  )

def v4_44 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v4_var ( ( @peirce.vector_expression.scalar_vector_mul geom ( peirce.scalar_expression.scalar_var flt3_var : peirce.scalar_expression  )  ( @peirce.vector_expression.vector_add geom ( @peirce.vector_expression.vector_var geom v4_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom v4_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) : peirce.vector_expression geom ) )

def flt_51 : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt_var ( ( peirce.scalar_expression.scalar_lit 0 : peirce.scalar_expression ) )

def flt3_52 : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt3_var ( ( peirce.scalar_expression.scalar_paren ( peirce.scalar_expression.scalar_var flt2_var : peirce.scalar_expression  )  : peirce.scalar_expression )   )

def rotate_and_scale_53 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotate_and_scale_var ( ( peirce.transform_compose ( @peirce.transform_expression.transform_var geom geom double_rotate_var : peirce.transform_expression geom geom )  ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  : peirce.transform_expression geom geom )  )

def rotate_and_scale_54 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotate_and_scale_var ( ( peirce.transform_compose ( @peirce.transform_expression.transform_var geom geom double_rotate_var : peirce.transform_expression geom geom )  ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  : peirce.transform_expression geom geom )  )

def rotate_and_scale_55 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotate_and_scale_var ( ( @peirce.transform_expression.transform_var geom geom cob1_var : peirce.transform_expression geom geom )  )