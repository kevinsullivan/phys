import .PhysL
open peirce

open peirce.scalar_expression

-- Test scalar_expression constructors
def e1 : scalar_expression := scalar_lit 3
def e2 : scalar_expression := scalar_paren e1
def e3 := scalar_add e1 e2
def e4 := scalar_mul e1 e2

-- Test scalar_eval
#reduce scalar_eval (scalar_lit 3) init_scalar_interp

-- Test vector_space constructor
def bar_vector_space := vector_space.mk 0
def foo_vector_space := vector_space.mk 1

-- Test vector constructor
#check vector.mk

def init_vector_interp : vector_interp bar_vector_space := λ v : vector_variable bar_vector_space, @vector.mk bar_vector_space 0 0 0

def v1 := @vector.mk bar_vector_space 1 2 3
#eval v1

--def v2 : vector bar_vector_space := @vector.mk bar_vector_space 1 6 2
def v3 := @vector.mk bar_vector_space 0 1 3
def v4 := @vector.mk bar_vector_space 1 2 4

#reduce v1


-- Test vector_experssion constructors and vector_eval
-- Example code below
-- Note: You need to define vectors, vector variable interpreters, and vector expressions
--       with a vector vector_space argument
open peirce.vector_expression

def ve1 : vector_expression bar_vector_space := (vector_literal v1)
def ve2 : vector_expression bar_vector_space := vector_add (vector_literal v2) (ve1)
def vv0 : vector_variable bar_vector_space := @vector_variable.mk _ 0
def vv1 : vector_variable foo_vector_space := @vector_variable.mk _ 1
def vv0_e : vector_expression bar_vector_space := vector_paren (vector_var vv0)

--Vec v[geom] = Vec(1, 0, 0)[time];

-- ... Vector_Def has a (VecIdent, Vector_Expr)

/-
Suppose you have "def v1 := ..."
Suppose you encounter, in C++, this expression: "v2 = v1"
Unparse this as "def v2 := v1"
-/

/-
    Vec v2;
    v2 = v1;

    -- 

    def v2 := v1



-- 

    (1) declares v2 to be a Vec-valued variable

    def v2_var : vector_variable <some space> := vector_variable.mk ...
    


    (2) it binds this variable to a decl ref expr on the right

    |-DeclStmt 0x55ecd1141fb0 <line:14:3, col:14>
    | `-VarDecl 0x55ecd1141c50 <col:3, col:12> col:7 used v2 'Vec' cinit
    |   `-CXXConstructExpr 0x55ecd1141f78 <col:12> 'Vec' 'void (const Vec &) noexcept'
    |     `-ImplicitCastExpr 0x55ecd1141cd8 <col:12> 'const Vec' lvalue <NoOp>
    |       `-DeclRefExpr 0x55ecd1141cb0 <col:12> 'Vec' lvalue Var 0x55ecd1140838 'v1' 'Vec'
    OLD:
    def v2 : peirce.vec geom  := (v1) : peirce.vec time /*!!!*/
    NEW:
    def v2_var : vector_variable geom 1


    ...
    def v2_var : vector_variable.mk geom 
    def v2 := v1

    v2 = v1;
    |-CXXOperatorCallExpr 0x55ecd1142610 <line:15:3, col:8> 'Vec' lvalue
    | |-ImplicitCastExpr 0x55ecd11425f8 <col:6> 'Vec &(*)(const Vec &) noexcept' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55ecd1142228 <col:6> 'Vec &(const Vec &) noexcept' lvalue CXXMethod 0x55ecd1142048 'operator=' 'Vec &(const Vec &) noexcept'
    | |-DeclRefExpr 0x55ecd1141fc8 <col:3> 'Vec' lvalue Var 0x55ecd1141c50 'v2' 'Vec'
    | `-ImplicitCastExpr 0x55ecd11421d8 <col:8> 'const Vec' lvalue <NoOp>
    |   `-DeclRefExpr 0x55ecd1141ff0 <col:8> 'Vec' lvalue Var 0x55ecd1140838 'v1' 'Vec'
    `-ReturnStmt 0x55ecd1142678 <line:112:3, col:10>

    #check 
-/


-- v2 = v;

def v_var : vector_variable bar_vector_space := @vector_variable.mk bar_vector_space 1
def v : vector_expression bar_vector_space := vector_var v_var
#check v == @vector_literal bar_vector_space (@vector.mk bar_vector_space 1 1 1)

-- .... 


def v2_var : vector_variable bar_vector_space := @vector_variable.mk bar_vector_space 2
def v2 : vector_expression bar_vector_space := vector_var v2_var
#check v2 == @vector_literal bar_vector_space (@vector.mk bar_vector_space 1 1 1)

#check v2 






def vv1_e : vector_expression bar_vector_space := scalar_vector_mul (scalar_lit 3) (vector_var vv1)  -- Type error expected
-- This line will fail to typecheck because vv1 was defined with vector_space foo_vector_space,
-- rather than expected bar_vector_space

def vv2_e : vector_expression _ := vector_add (vector_var vv0) (vector_var vv0) 
-- Type inference working as expected

def vve_e : vector_expression _ := vector_add (vector_var vv0) (vector_var vv1) -- Type error expected
-- Additional example with error + type inference


def v_interp : vector_interp bar_vector_space := λ v : vector_variable bar_vector_space,
        match v.index with,
            0 := @vector.mk _ 1 1 1,
            1 := @vector.mk _ 2 2 2,
            _ := @vector.mk _ 0 0 0
        end

#reduce vector_eval bar_vector_space (ve2) init_vector_interp init_scalar_interp
#reduce vector_eval bar_vector_space (vector_add vv0_e vv1_e) v_interp init_scalar_interp

--Linear transformation tests
/-
t1 : foo_vector_space → bar_vector_space
Matrix of transformation:
    [ 1 1 1 ]
    [ 0 1 1 ]
    [ 0 0 1 ]

-/
def t1 := @transform.mk foo_vector_space bar_vector_space
    (@vector.mk bar_vector_space 1 0 0) (@vector.mk bar_vector_space 1 1 0) (@vector.mk bar_vector_space 1 1 1) 

/-
t2 : bar_vector_space → foo_vector_space
    Matrix of Transformation:
    [ 2 0 0 ]
    [ 0 2 0 ]
    [ 0 0 2 ]
-/
def t2 := @transform.mk bar_vector_space foo_vector_space 
    (@vector.mk foo_vector_space 2 0 0) (@vector.mk foo_vector_space 0 2 0) (@vector.mk foo_vector_space 0 0 2) 

#check t1
#check v1
#check transform_apply t1 v1 --type error expected
#check t2
#check transform_apply t2 v1
#check transform_apply t1 (transform_apply t2 v1)

#check t1
#check t2
--t1 composed with t2: foo_vector_space → foo_vector_space
#check transform_compose t1 t2 

/-
t3 : foo_vector_space → foo_vector_space
    Matrix of Transformation:
    [ 2 0 0 ]   [ 1 1 1 ]    [ 2 2 2 ]
    [ 0 2 0 ] * [ 0 1 1 ] =  [ 0 2 2 ] 
    [ 0 0 2 ]   [ 0 0 1 ]    [ 0 0 2 ]
       M_T1   *   M_T2    =   M_T3
-/
def t3 := transform_compose t1 t2
#eval t3.one.x
#eval t3.one.y
#eval t3.one.z
#eval t3.two.x
#eval t3.two.y
#eval t3.two.z
#eval t3.three.x
#eval t3.three.y
#eval t3.three.z
def vvv1 := @vector.mk bar_vector_space 1 2 3
def vvv2 := @vector.mk foo_vector_space 1 6 2

def vvv3 := vector_add (vector_literal vvv1) (vector_literal (transform_apply t1 ( vvv2)))