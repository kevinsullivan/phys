import physDimension

import data.real.basic
import ..affine.aff_coord_space

noncomputable theory


abbreviation real_zero := (0 : ℝ)
abbreviation nat_zero := (0 : ℕ)
abbreviation rat_zero := (0 : ℚ)

/-
physicalDimension
time and distance are base types
can create derived types with the inverse and multiplication operations
-/
inductive physicalDimension : Type
| time
| distance
| inverse : (physicalDimension → physicalDimension)
| multiply : (physicalDimension → physicalDimension → physicalDimension)

--define velocity to be physical dimension of (distance / time)
def velocity : physicalDimension :=
    physicalDimension.multiply physicalDimension.distance (physicalDimension.inverse physicalDimension.time)

--take affine_frame to be a type 
--since we want some notion of a frame attached to any points/vectors we define
axiom affine_frame : Type



/-
phys_space

can construct any physical space for a given dimension and physical dimension
i.e. 3D Geometric space (distance as its physical dimension)
    1D time space (time as its physical dimension)
-/
structure phys_space (d : physicalDimension) : Type :=
    mk ::  (dimension : ℕ) (std_frame : affine_frame)

--take std to be some affine frame
axiom std : affine_frame


structure GeometricPointStruct : Type :=
    mk :: (sp : phys_space physicalDimension.distance) (pt : aff_pt ℝ 3) (B : affine_frame)

structure TimePointStruct : Type :=
    mk :: (sp : phys_space physicalDimension.time) (pt : aff_pt ℝ 1) (B : affine_frame)



structure GeometricVector : Type :=
    mk :: (sp : phys_space physicalDimension.distance) (vec : aff_vec ℝ 3) (B : affine_frame)



/-
def GeomAdd : GeometricVector → GeometricVector → GeometricVector
| (GeometricVector.mk a x b) (GeometricVector.mk a y b) := GeometricVector.mk a (x+y) b
| _ _ := sorry --should throw an error

instance : has_add GeometricVector := ⟨GeomAdd⟩

-/


structure TimeVector : Type :=
    mk :: (sp : phys_space physicalDimension.time) (vec : aff_vec ℝ 1) (B : affine_frame)




structure VelocityVector : Type :=
    mk :: (sp : phys_space velocity) (vec : aff_vec ℝ 3) (B : affine_frame)


/-
Norm Function:
takes in some 1-dimensional Time vector and returns its magnitude (i.e. first element in the list)
-/
def magnitude : TimeVector → ℝ
| _ := 0


/-
Example function for creating GeometricPoint from 3 reals and a physical space
-/
def GeometricPoint (p : phys_space physicalDimension.distance) (x y z : ℝ) : GeometricPointStruct :=
    GeometricPointStruct.mk p (aff_pt.mk [1,x,y,z] rfl rfl) p.std_frame

def TimePoint (p : phys_space physicalDimension.time) (t : ℝ) : TimePointStruct :=
    TimePointStruct.mk p (aff_pt.mk [1, t] rfl rfl) p.std_frame

--def example_point := GeometricPoint geom3 1 1 1
--def example_time := TimePoint time 10




def EuclideanGeometry (name : string) (n : nat): phys_space physicalDimension.distance :=
    phys_space.mk n std

def ClassicalTime (name : string) : phys_space physicalDimension.time :=
    phys_space.mk 1 std

def ClassicalVelocity (name : string) (n : nat) : phys_space velocity :=
    phys_space.mk n std

/-
+REAL1_EXPR := 
	PAREN +REAL1_EXPR | ~A parenthesized expression evaluating to a real (floating point) value
	INV +REAL1_EXPR | ~Inverse of an expression evaluating to a real (floating point) value
	NEG +REAL1_EXPR | ~Negation of an expression evaluating to a real (floating point) value
	ADD +REAL1_EXPR +REAL1_EXPR | ~Addition of an expression evaluating to a real (floating point) value with an expression evaluating to a real (floating point) value 
	MUL +REAL1_EXPR +REAL1_EXPR | ~Multiplication of an  expression evaluating to a real (floating point) value
	REF +REAL1_VAR | ~A variable expression evaluating to a real (floating point) value
	=REAL1_LITERAL

+REAL3_EXPR := 
	PAREN +REAL3_EXPR |  ~A parenthesized expression evaluating to a tuple with 3 real (floating point) values
	ADD +REAL3_EXPR +REAL3_EXPR | ~Addition of an expression evaluating to a tuple with 3 real (floating point) values with an expression evaluating to a tuple with 3 real (floating point) values
	INV +REAL3_EXPR | ~Inverse of an expression evaluating to a tuple with 3 real (floating point) values
	NEG +REAL3_EXPR | ~Negation of an expression evaluating to a tuple with 3 real (floating point) values
	MUL +REAL3_EXPR +REAL1_EXPR | ~Multiplication of an expression evaluating to a tuple with 3 real (floating point) values with an expression evaluating to a real (floating point) value
	MUL +REALMATRIX_EXPR +REAL3_EXPR |  ~Multiplication of an expression evaluating to a real matrix with an expression evaluating to a tuple with 3 real (floating point) values
	REF +REAL3_VAR |  ~A variable expression evaluating to a tuple with 3 real (floating point) values
	=REAL3_LITERAL

+REAL4_EXPR :=
	PAREN +REAL4_EXPR | ~A parenthesized expression evaluating to a tuple with 4 real (floating point) values
	ADD +REAL4_EXPR +REAL4_EXPR |  ~Addition of an expression evaluating to a tuple with 4 real (floating point) values with an expression evaluating to a tuple with 3 real (floating point) values
	MUL +REAL4_EXPR +REAL1_EXPR | ~Multiplication of an expression evaluating to a tuple with 4 real (floating point) val ues with an expression evaluating to a real (floating point) value
	REF +REAL4_VAR | ~A variable expression evaluating to a tuple with 4 real (floating point) values
	=REAL4_LITERAL 

+REALMATRIX_EXPR :=
	PAREN +REALMATRIX_EXPR | ~A parenthesized expression evaluating to a matrix with real (floating point) entries
	MUL +REALMATRIX_EXPR +REALMATRIX_EXPR |   ~Multiplication of an expression evaluating to a real matrix with an expression evaluating to a matrix with real (floating point) entries
	REF_EXPR +REALMATRIX_VAR | ~A variable expression evaluating to a matrix with real (floating point) entries
	=REALMATRIX_LITERAL 


1REAL1_VAR := 
	IDENT ~An identifier storing a real (floating point)
1REAL3_VAR := 
	IDENT ~An identifier storing a tuple with 4 real (floating point) values
1REAL4_VAR := 
	IDENT ~An identifier storing a tuple with 4 real (floating point) values
1REALMATRIX_VAR := 
	IDENT ~An identifier storing a matrix with real (floating point) entries

    tf::vector3 myvedctor 
-/

structure RealScalarVar
| mk (n : ℕ)
structure GeometricScalarVar
| mk (n : ℕ) 
structure TimeScalarVar
| mk (n : ℕ) 
structure VelocityScalarVar
| mk (n : ℕ) 
structure Geometric3VectorVar
| mk (n : ℕ) 
structure TimeVectorVar
| mk (n : ℕ) 
structure VelocityVectorVar
| mk (n : ℕ) 
structure Geometric3PointVar
| mk (n : ℕ) 
structure TimePointVar
| mk (n : ℕ) 
structure VelocityPointVar
| mk (n : ℕ)


inductive RealScalarExpression
| RealLitScalar : ℝ → RealScalar Expression
| RealVarScalar : RealScalarVar → RealScalarExpression
| RealAddScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealSubScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealMulScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealDivScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealNegScalar : RealScalarExpression → RealScalarExpression
| RealInvScalar : RealScalarExpression → RealScalarExpression
| RealParenScalar : RealScalarExpression → RealScalarExpression
-- no? | GeometricZeroScalar
-- no? | GeometricOneScalar

inductive GeometricScalarExpression
| GeometricLitScalar : ℝ → GeometricScalarExpression
| GeometricVarScalar : GeometricScalarVar → GeometricScalarExpression
| GeometricAddScalarScalar : GeometricScalarExpression → GeometricScalarExpression → GeometricScalarExpression
| GeometricSubScalarScalar : GeometricScalarExpression → GeometricScalarExpression → GeometricScalarExpression
| GeometricMulScalarScalar : GeometricScalarExpression → GeometricScalarExpression → GeometricScalarExpression
| GeometricDivScalarScalar : GeometricScalarExpression → GeometricScalarExpression → GeometricScalarExpression
| GeometricNegScalar : GeometricScalarExpression → GeometricScalarExpression
| GeometricInvScalar : GeometricScalarExpression → GeometricScalarExpression
| GeometricParenScalar : GeometricScalarExpression → GeometricScalarExpression
| GeometricNormVector : GeometricVectorExpression → GeometricScalarExpression

inductive TimeScalarExpression
| TimeLitScalar : ℝ → TimeScalarExpression
| TimeVarScalar : TimeScalarVar → TimeScalarExpression
| TimeAddScalarScalar : TimeScalarExpression → TimeScalarExpression → TimeScalarExpression
| TimeSubScalarScalar : TimeScalarExpression → TimeScalarExpression → TimeScalarExpression
| TimeMulScalarScalar : TimeScalarExpression → TimeScalarExpression → TimeScalarExpression
| TimeDivScalarScalar : TimeScalarExpression → TimeScalarExpression → TimeScalarExpression
| TimeNegScalar : TimeScalarExpression → TimeScalarExpression
| TimeInvScalar : TimeScalarExpression → TimeScalarExpression
| TimeParenScalar : TimeScalarExpression → TimeScalarExpression

inductive VelocityScalarExpression
| VelocityLitScalar : ℝ → VelocityScalarExpression 
| VelocityVarScalar : VelocityScalarVar → VelocityScalarExpression
| VelocityAddScalarScalar : VelocityScalarExpression → VelocityScalarExpression → VelocityScalarExpression 
| VelocitySubScalarScalar : VelocityScalarExpression → VelocityScalarExpression → VelocityScalarExpression
| VelocityMulScalarScalar : VelocityScalarExpression → VelocityScalarExpression → VelocityScalarExpression
| VelocityDivScalarScalar : VelocityScalarExpression → VelocityScalarExpression → VelocityScalarExpression
| VelocityNegScalar : VelocityScalarExpression → VelocityScalarExpression
| VelocityInvScalar : VelocityScalarExpression → VelocityScalarExpression
| VelocityParenScalar : VelocityScalarExpression → VelocityScalarExpression

inductive Geometric3VectorExpression
| Geometric3LitVector : Geometric3Vector → Geometric3VectorExpression
| Geometric3VarVector : Geometric3VectorVar → Geometric3VectorExpression
| Geometric3AddVectorVector : Geometric3VectorExpression → Geometric3VectorExpression → Geometric3VectorExpression
| Geometric3NegVector : Geometric3VectorExpression → Geometric3VectorExpression
| Geometric3MulScalarVector : RealScalarExpression → Geometric3VectorExpression → Geometric3VectorExpression
| Geometric3MulVectorScalar : Geometric3VectorExpression → RealScalarExpression → Geometric3VectorExpression
| Geometric3SubPointPoint : Geometric3PointExpression → Geometric3PointExpression → Geometric3VectorExpression
| Geometric3ParenVector : Geometric3VectorExpression → Geometric3VectorExpression

inductive TimeVectorExpression
| TimeLitVector : TimeVector → TimeVectorExpression
| TimeVarVector : TimeVectorVar → TimeVectorExpression
| TimeAddVectorVector : TimeVectorExpression → TimeVectorExpression → TimeVectorExpression
| TimeNegVector : TimeVectorExpression → TimeVectorExpression
| TimeMulScalarVector : RealScalarExression → TimeVectorExpression → TimeVectorExpression
| TimeMulVectorScalar : TimeVectorExpression → RealScalarExpression → TimeVectorExpression 
| TimeSubPointPoint : TimePointExpression → TimePointExpression → TimeVectorExpression
| TimeParenVector : TimeVectorExpression → TimeVectorExpression

inductive VelocityVectorExpression
| VelocityLitVector : VelocityVector → VelocityVectorExpression
| VelocityVarVector : VelocityVectorVar → VelocityVectorExpression
| VelocityAddVectorVector : VelocityVectorExpression → VelocityVectorExpression → VelocityVectorExpression
--| VelocitySubVectorVector (pt: VelocityPoint) 
| VelocityNegVector : VelocityVectorExpression → VelocityVectorExpression
| VelocityMulScalarVector : RealScalarExpression → VelocityVectorExpression → VelocityVectorExpression
| VelocityMulVectorScalar : VelocityVectorExpression → RealScalarExpression → VelocityVectorExpression
| VelocitySubPointPoint : VelocityPointExpression → VelocityPointExpression → VelocityVectorExpression
| VelocityParenVector : VelocityVectorExpression  → VelocityVectorExpression
-- no? | VelocityZeroVector 

inductive Geometric3PointExpression
| Geometric3LitPoint : Geometric3Point → Geometric3PointExpression
| Geometric3SubVectorVector : Geometric3VectorExpression → Geometric3VectorExpression → Geometric3PointExpression
| Geometric3NegPoint : Geometric3PointExpression → Geometric3PointExpression
| Geometric3AddPointVector : Geometric3PointExpression → Geometric3VectorExpression → Geometric3PointExpression
| Geometric3AddVectorPoint : Geometric3VectorExpression → Geometric3PointExpression → Geometric3PointExpression
| Geometric3ScalarPoint : RealScalarExpression → Geometric3PointExpression → Geometric3PointExpression
| Geometric3PointScalar : Geometric3PointExpression RealScalarExpression → Geometric3PointExpression
| Geometric3ParenPoint : Geometric3PointExpression → Geometric3PointExpression

inductive TimePointExpression
| TimeLitPoint : TimePoint → TimePointExpression
| TimeSubVectorVector : TimeVectorExpression → TimeVectorExpression → TimePointExpression
| TimeNegPoint : TimePointExpression → TimePointExpression
| TimeAddPointVector : TimePointExpression → TimeVectorExpression → TimePointExpression
| TimeAddVectorPoint : TimeVectorExpression → TimePointExpression → TimePointExpression
| TimeScalarPoint : RealScalarExpression → TimePointExpression → TimePointExpression
| TimePointScalar : TimePointExpression → RealScalarExpression → TimePointExpression
| TimeParenPoint : TimePointExpression → TimePointExpression

inductive VelocityPointExpression
| VelocityLitPoint : VelocityPoint → VelocityPointExpresion
| VelocitySubVectorVector : VelocityVectorExpression → VelocityVectorExpression → VelocityPointExpresion
| VelocityNegPoint : VelocityPointExpression → VelocityPointExpression
| VelocityAddVectorPoint : VelocityVectorExpression → VelocityPointExpression → VelocityPointExpression
| VelocityScalarPoint : RealScalarExpression → VelocityPointExpression → VelocityPointExpression
| VelocityPointScalar : VelocityPointExpression → RealScalarExpression → VelocityPointExpression
| VelocityParenPoint : VelocityPointExpression → VelocityPointExpression


abbreviation RealScalarInterp := RealScalarVar → ℝ

abbreviation GeometricScalarInterp := GeometricScalarVar → ℝ
abbreviation TimeScalarInterp := TimeScalarVar → ℝ
abbreviation VelocityScalarInterp := VelocityScalarVar → ℝ

abbreviation Geometric3VectorInterp := GeometricVectorVar → ℝ
abbreviation TimeVectorInterp := TimeVectorVar → ℝ
abbreviation Velocity3VectorInterp := VelocityVectorVar → 

abbreviation Geometric3PointInterp := GeometricPointVar → GeometricPoint
abbreviation TimePointInterp := TimePointVar → TimePoint
abbreviation Velocity3PointInterp := VelocityPointVar → VelocityPoint


def DefaultRealScalarInterp : RealScalarInterp := λ scalar, real_zero
def DefaultGeometricScalarInterp : GeometricScalarInterp := λ scalar, real_zero
def DefaultTimeScalarInterp : TimeScalarInterp := λ scalar, real_zero
def DefaultVelocityScalarInterp : VelocityScalarInterp := λ scalar, real_zero
def DefaultGeometric3VectorInterp : GeometricScalarInterp := λ vector, default_geometric3_vector
def DefaultTimeVectorInterp : TimeVectorInterp := λ vector, default_time_vector
def DefaultVelocity3VectorInterp : VelocityVectorInterp := λ vector, default_velocity3_vector
def DefaultGeometric3PointInterp : Geometric3PointInterp := λ point, default_geometric3_point
def DefaultTimePointInterp : TimePointInterp := λ point, default_time_point
def DefaultVelocity3PointInterp : Velocity3 := λ point, default_velocity3_point


/-
important for static analysis!!

100 scalar variables

nontrivial : map them individually to a value that makes sense, can change at different points in  program

start of program : interp mapping 1

end of program : interp mapping n

default : map them all to 0

-/
/-
REAL PROGRAM : 100 variables

95 "UNKNOWN"
~ loose bound on "5" of them


CTRLH ℝ → ℚ 
-/