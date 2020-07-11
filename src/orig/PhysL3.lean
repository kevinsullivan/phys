import ..physics.physDimension

noncomputable theory



abbreviation real_zero := (0 : ℝ)
abbreviation nat_zero := (0 : ℕ)
abbreviation rat_zero := (0 : ℚ)
abbreviation Geometric3Vector_zero := Geometric3Vector.mk geom3 (aff_vec.mk [0,0,0,0] rfl rfl) std
abbreviation Velocity3Vector_zero := Velocity3Vector.mk vel (aff_vec.mk [0,0,0,0] rfl rfl) std 
abbreviation TimeVector_zero := TimeVector.mk time (aff_vec.mk [0,0] rfl rfl) std
abbreviation Geometric3Point_zero := Geometric3Point geom3 0 0 0
abbreviation Velocity3Point_zero := Velocity3PointStruct.mk vel (aff_pt.mk [1,0,0,0] rfl rfl) std 
abbreviation TimePoint_zero := TimePoint time 0

structure RealScalarVar : Type :=
	mk :: (n : ℕ)
structure GeometricScalarVar : Type :=
	mk :: (n : ℕ)
structure TimeScalarVar : Type :=
	mk :: (n : ℕ)
structure VelocityScalarVar : Type :=
	mk :: (n : ℕ)
structure Geometric3VectorVar : Type :=
	mk :: (n : ℕ)
structure TimeVectorVar : Type :=
	mk :: (n : ℕ)
structure Velocity3VectorVar : Type :=
	mk :: (n : ℕ)
structure Geometric3PointVar : Type :=
	mk :: (n : ℕ)
structure TimePointVar : Type :=
	mk :: (n : ℕ)
structure Velocity3PointVar : Type :=
	mk :: (n : ℕ)


mutual inductive RealScalarExpression, GeometricScalarExpression, 
	TimeScalarExpression, VelocityScalarExpression, Geometric3VectorExpression, 
	Velocity3VectorExpression, TimeVectorExpression, Geometric3PointExpression, 
	Velocity3PointExpression, TimePointExpression
with RealScalarExpression : Type
| RealLitScalar : ℝ → RealScalarExpression
| RealVarScalar : RealScalarVar → RealScalarExpression
| RealAddScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealSubScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealMulScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealDivScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealNegScalar : RealScalarExpression → RealScalarExpression
| RealInvScalar : RealScalarExpression → RealScalarExpression
| RealParenScalar : RealScalarExpression → RealScalarExpression
with GeometricScalarExpression : Type
| GeometricLitScalar : ℝ → GeometricScalarExpression
| GeometricVarScalar : GeometricScalarVar → GeometricScalarExpression
| GeometricAddScalarScalar : GeometricScalarExpression → GeometricScalarExpression → GeometricScalarExpression
| GeometricSubScalarScalar : GeometricScalarExpression → GeometricScalarExpression → GeometricScalarExpression
| GeometricMulScalarScalar : GeometricScalarExpression → GeometricScalarExpression → GeometricScalarExpression
| GeometricDivScalarScalar : GeometricScalarExpression → GeometricScalarExpression → GeometricScalarExpression
| GeometricNegScalar : GeometricScalarExpression → GeometricScalarExpression
| GeometricInvScalar : GeometricScalarExpression → GeometricScalarExpression
| GeometricParenScalar : GeometricScalarExpression → GeometricScalarExpression
| GeometricNormVector : Geometric3VectorExpression → GeometricScalarExpression
with TimeScalarExpression : Type
| TimeLitScalar : ℝ → TimeScalarExpression
| TimeVarScalar : TimeScalarVar → TimeScalarExpression
| TimeAddScalarScalar : TimeScalarExpression → TimeScalarExpression → TimeScalarExpression
| TimeSubScalarScalar : TimeScalarExpression → TimeScalarExpression → TimeScalarExpression
| TimeMulScalarScalar : TimeScalarExpression → TimeScalarExpression → TimeScalarExpression
| TimeDivScalarScalar : TimeScalarExpression → TimeScalarExpression → TimeScalarExpression
| TimeNegScalar : TimeScalarExpression → TimeScalarExpression
| TimeInvScalar : TimeScalarExpression → TimeScalarExpression
| TimeParenScalar : TimeScalarExpression → TimeScalarExpression
| TimeNormVector : TimeVectorExpression → TimeScalarExpression
with VelocityScalarExpression : Type
| VelocityLitScalar : ℝ → VelocityScalarExpression 
| VelocityVarScalar : VelocityScalarVar → VelocityScalarExpression
| VelocityAddScalarScalar : VelocityScalarExpression → VelocityScalarExpression → VelocityScalarExpression 
| VelocitySubScalarScalar : VelocityScalarExpression → VelocityScalarExpression → VelocityScalarExpression
| VelocityMulScalarScalar : VelocityScalarExpression → VelocityScalarExpression → VelocityScalarExpression
| VelocityDivScalarScalar : VelocityScalarExpression → VelocityScalarExpression → VelocityScalarExpression
| VelocityNegScalar : VelocityScalarExpression → VelocityScalarExpression
| VelocityInvScalar : VelocityScalarExpression → VelocityScalarExpression
| VelocityParenScalar : VelocityScalarExpression → VelocityScalarExpression
| VelocityNormVector : Velocity3VectorExpression → VelocityScalarExpression
with Geometric3VectorExpression : Type
| Geometric3LitVector : Geometric3Vector → Geometric3VectorExpression
| Geometric3VarVector : Geometric3VectorVar → Geometric3VectorExpression
| Geometric3AddVectorVector : Geometric3VectorExpression → Geometric3VectorExpression → Geometric3VectorExpression
| Geometric3NegVector : Geometric3VectorExpression → Geometric3VectorExpression
| Geometric3MulScalarVector : RealScalarExpression → Geometric3VectorExpression → Geometric3VectorExpression
| Geometric3MulVectorScalar : Geometric3VectorExpression → RealScalarExpression → Geometric3VectorExpression
| Geometric3SubPointPoint : Geometric3PointExpression → Geometric3PointExpression → Geometric3VectorExpression
| Geometric3ParenVector : Geometric3VectorExpression → Geometric3VectorExpression
with Velocity3VectorExpression : Type
| Velocity3LitVector : Velocity3Vector → Velocity3VectorExpression
| Velocity3VarVector : Velocity3VectorVar → Velocity3VectorExpression
| Velocity3AddVectorVector : Velocity3VectorExpression → Velocity3VectorExpression → Velocity3VectorExpression
| Velocity3NegVector : Velocity3VectorExpression → Velocity3VectorExpression
| Velocity3MulScalarVector : RealScalarExpression → Velocity3VectorExpression → Velocity3VectorExpression
| Velocity3MulVectorScalar : Velocity3VectorExpression → RealScalarExpression → Velocity3VectorExpression
| Velocity3SubPointPoint : Velocity3PointExpression → Velocity3PointExpression → Velocity3VectorExpression
| Velocity3ParenVector : Velocity3VectorExpression  → Velocity3VectorExpression
with TimeVectorExpression : Type
| TimeLitVector : TimeVector → TimeVectorExpression
| TimeVarVector : TimeVectorVar → TimeVectorExpression
| TimeAddVectorVector : TimeVectorExpression → TimeVectorExpression → TimeVectorExpression
| TimeNegVector : TimeVectorExpression → TimeVectorExpression
| TimeMulScalarVector : RealScalarExpression → TimeVectorExpression → TimeVectorExpression
| TimeMulVectorScalar : TimeVectorExpression → RealScalarExpression → TimeVectorExpression 
| TimeSubPointPoint : TimePointExpression → TimePointExpression → TimeVectorExpression
| TimeParenVector : TimeVectorExpression → TimeVectorExpression
with Geometric3PointExpression : Type
| Geometric3LitPoint : Geometric3PointStruct → Geometric3PointExpression
| Geometric3SubVectorVector : Geometric3VectorExpression → Geometric3VectorExpression → Geometric3PointExpression
| Geometric3NegPoint : Geometric3PointExpression → Geometric3PointExpression
| Geometric3AddPointVector : Geometric3PointExpression → Geometric3VectorExpression → Geometric3PointExpression
| Geometric3AddVectorPoint : Geometric3VectorExpression → Geometric3PointExpression → Geometric3PointExpression
| Geometric3ScalarPoint : RealScalarExpression → Geometric3PointExpression → Geometric3PointExpression
| Geometric3PointScalar : Geometric3PointExpression → RealScalarExpression → Geometric3PointExpression
| Geometric3ParenPoint : Geometric3PointExpression → Geometric3PointExpression
with Velocity3PointExpression : Type
| Velocity3LitPoint : Velocity3PointStruct → Velocity3PointExpression
| Velocity3SubVectorVector : Velocity3VectorExpression → Velocity3VectorExpression → Velocity3PointExpression
| Velocity3NegPoint : Velocity3PointExpression → Velocity3PointExpression
| Velocity3AddVectorPoint : Velocity3VectorExpression → Velocity3PointExpression → Velocity3PointExpression
| Velocity3AddPointVector : Velocity3PointExpression → Velocity3VectorExpression → Velocity3PointExpression
| Velocity3ScalarPoint : RealScalarExpression → Velocity3PointExpression → Velocity3PointExpression
| Velocity3PointScalar : Velocity3PointExpression → RealScalarExpression → Velocity3PointExpression
| Velocity3ParenPoint : Velocity3PointExpression → Velocity3PointExpression
with TimePointExpression : Type
| TimeLitPoint : TimePointStruct → TimePointExpression
| TimeSubVectorVector : TimeVectorExpression → TimeVectorExpression → TimePointExpression
| TimeNegPoint : TimePointExpression → TimePointExpression
| TimeAddPointVector : TimePointExpression → TimeVectorExpression → TimePointExpression
| TimeAddVectorPoint : TimeVectorExpression → TimePointExpression → TimePointExpression
| TimeScalarPoint : RealScalarExpression → TimePointExpression → TimePointExpression
| TimePointScalar : TimePointExpression → RealScalarExpression → TimePointExpression
| TimeParenPoint : TimePointExpression → TimePointExpression



/-
VARIABLE UNKNOWN

CASE 1: I PROVIDE A TYPE FOR VARIABLE -> REAL SCALAR VARIABLE X
RealScalarExpression.RealScalarVar 4 --{4}

CASE 2: I DONT PROVIDE A TYPE FOR VARIABLE
{}


-/


--RealScalarExpression Notations
notation {e} := RealScalarExpression.RealScalarVar e
notation e1 + e2 := RealScalarExpression.RealAddScalarScalar e1 e2
notation e1 - e2 := RealScalarExpression.RealSubScalarScalar e1 e2
notation e1 * e2 := RealScalarExpression.RealMulScalarScalar e1 e2
notation e1 / e2 := RealScalarExpression.RealDivScalarScalar e1 e2
notation -e := RealScalarExpression.RealNegScalar e
notation e⁻¹ := RealScalarExpression.RealInvScalar e
notation /e/ := RealScalarExpression.RealParenScalar e
--GeometricScalarExpression Notations
notation {e} := GeometricScalarExpression.GeometricVarScalar e
notation e1 + e2 := GeometricScalarExpression.GeometricAddScalarScalar e1 e2
notation e1 - e2 := GeometricScalarExpression.GeometricSubScalarScalar e1 e2
notation e1 * e2 := GeometricScalarExpression.GeometricMulScalarScalar e1 e2
notation e1 / e2 := GeometricScalarExpression.GeometricDivScalarScalar e1 e2
notation -e := GeometricScalarExpression.GeometricNegScalar e
notation e⁻¹ := GeometricScalarExpression.GeometricInvScalar e
notation /e/ := GeometricScalarExpression.GeometricParenScalar e
notation |e| := GeometricScalarExpression.GeometricNormVector e
--TimeScalarExpression Notations
notation {e} := TimeScalarExpression.TimeVarScalar  
notation e1 + e2 := TimeScalarExpression.TimeAddScalarScalar e1 e2
notation e1 - e2 := TimeScalarExpression.TimeSubScalarScalar e1 e2
notation e1 * e2 := TimeScalarExpression.TimeMulScalarScalar e1 e2
notation e1 / e2 := TimeScalarExpression.TimeDivScalarScalar e1 e2
notation -e := TimeScalarExpression.TimeNegScalar e
notation e¬⁻¹⁻¹ := TimeScalarExpression.TimeInvScalar e
notation /e/ := TimeScalarExpression.TimeParenScalar e
notation |e| := TimeScalarExpression.TimeNormVector e
--VelocityScalarExpression Notations
notation {e} := VelocityScalarExpression.VelocityVarScalar e
notation e1 + e2 := VelocityScalarExpression.VelocityAddScalarScalar e1 e2
notation e1 - e2 := VelocityScalarExpression.VelocitySubScalarScalar e1 e2
notation e1 * e2 := VelocityScalarExpression.VelocityMulScalarScalar e1 e2
notation e1 / e2 := VelocityScalarExpression.VelocityDivScalarScalar e1 e2
notation -e := VelocityScalarExpression.VelocityNegScalar e
notation e⁻¹ := VelocityScalarExpression.VelocityInvScalar e
notation /e/ := VelocityScalarExpression.VelocityParenScalar e
notation |e| := VelocityScalarExpression.VelocityNormVector e

--Gemoetric3Vector Notations
notation {e} := Geometric3VectorExpression.Geometric3VectorVar e
notation e1 + e2 := Geometric3VectorExpression.Geometric3AddVectorVector e1 e2
notation -e := Geometric3VectorExpression.Geometric3NegVector e
notation c * e := Geometric3VectorExpression.Geometric3MulScalarVector c e
notation e * c := Geometric3VectorExpression.Geometric3MulVectorScalar e c
notation e1 - e2 := Geometric3VectorExpression.Geometric3SubPointPoint e1 e2
notation /e/ := Geometric3VectorExpression.Geometric3ParenVector e

--Velocity3Vector Notations
notation {e} := Velocity3VectorExpression.Velocity3VectorVar e
notation e1 + e2 := Velocity3VectorExpression.Velocity3AddVectorVector e1 e2
notation -e := Velocity3VectorExpression.Velocity3NegVector e
notation c * e := Velocity3VectorExpression.Velocity3MulScalarVector c e
notation e * c := Velocity3VectorExpression.Velocity3MulVectorScalar e c
notation e1 - e2 := Velocity3VectorExpression.Velocity3SubPointPoint e1 e2
notation /e/ := Velocity3VectorExpression.Velocity3ParenVector e

--TimeVector Notations
notation {e} := TimeVectorExpression.TimeVectorVar e
notation e1 + e2 := TimeVectorExpression.TimeAddVectorVector e1 e2
notation -e := TimeVectorExpression.TimeNegVector e
notation c * e := TimeVectorExpression.TimeMulScalarVector c e
notation e * c := TimeVectorExpression.TimeMulVectorScalar e c
notation e1 - e2 := TimeVectorExpression.TimeSubPointPoint e1 e2
notation /e/ := TimeVectorExpression.TimeParenVector e


--Geometric3Point Notations
notation e1 - e2 := Geometric3PointExpression.Geometric3SubVectorVector e1 e2
notation -e := Geometric3PointExpression.Geometric3NegPoint e
notation e1 + e2 := Geometric3PointExpression.Geometric3AddVectorPoint e1 e2
notation e1 + e2 := Geometric3PointExpression.Geometric3AddPointVector e1 e2
notation c * e := Geometric3PointExpression.Geometric3ScalarPoint c e
notation e * c := Geometric3PointExpression.Geometric3PointScalar e c
notation /e/ := Geometric3PointExpression.Geometric3ParenPoint e

--Velocity3Point Notations
notation e1 - e2 := Velocity3PointExpression.Velocity3SubVectorVector e1 e2
notation -e := Velocity3PointExpression.Velocity3NegPoint e
notation e1 + e2 := Velocity3PointExpression.Velocity3AddVectorPoint e1 e2
notation e1 + e2 := Velocity3PointExpression.Velocity3AddPointVector e1 e2
notation c * e := Velocity3PointExpression.Velocity3ScalarPoint c e
notation e * c := Velocity3PointExpression.Velocity3PointScalar e c
notation /e/ := Velocity3PointExpression.Velocity3ParenPoint e

--TimePoint Notations
notation e1 + e2 := TimePointExpression.TimeAddPointVector e1 e2
notation e1 + e2 := TimePointExpression.TimeAddVectorPoint e1 e2
notation /e/ := TimePointExpression.TimeParenPoint e
notation e1 - e2 := TimePointExpression.TimeSubVectorVector e1 e2
notation -e := TimePointExpression.TimeNegPoint e
notation c * e := TimePointExpression.TimeScalarPoint c e
notation e * c := TimePointExpression.TimePointScalar e c









abbreviation RealScalarInterp := RealScalarVar → ℝ

abbreviation GeometricScalarInterp := GeometricScalarVar → ℝ
abbreviation TimeScalarInterp := TimeScalarVar → ℝ
abbreviation VelocityScalarInterp := VelocityScalarVar → ℝ

abbreviation Geometric3VectorInterp := Geometric3VectorVar → Geometric3Vector
abbreviation TimeVectorInterp := TimeVectorVar → TimeVector
abbreviation Velocity3VectorInterp := Velocity3VectorVar → Velocity3Vector

abbreviation Geometric3PointInterp := Geometric3PointVar → Geometric3PointStruct
abbreviation TimePointInterp := TimePointVar → TimePointStruct
abbreviation Velocity3PointInterp := Velocity3PointVar → Velocity3PointStruct


def DefaultRealScalarInterp : RealScalarInterp := λ scalar, real_zero
def DefaultGeometricScalarInterp : GeometricScalarInterp := λ scalar, real_zero
def DefaultTimeScalarInterp : TimeScalarInterp := λ scalar, real_zero
def DefaultVelocityScalarInterp : VelocityScalarInterp := λ scalar, real_zero
def DefaultGeometric3VectorInterp : Geometric3VectorInterp := λ vector, Geometric3Vector_zero
def DefaultTimeVectorInterp : TimeVectorInterp := λ vector, TimeVector_zero
def DefaultVelocity3VectorInterp : Velocity3VectorInterp := λ vector, Velocity3Vector_zero
def DefaultGeometric3PointInterp : Geometric3PointInterp := λ point, Geometric3Point_zero
def DefaultTimePointInterp : TimePointInterp := λ point, TimePoint_zero
def DefaultVelocity3PointInterp : Velocity3PointInterp := λ point, Velocity3Point_zero

def realScalarEval : RealScalarExpression → RealScalarInterp → ℝ 
| (RealScalarExpression.RealLitScalar r) i := r
| (RealScalarExpression.RealVarScalar v) i := i v
| (RealScalarExpression.RealAddScalarScalar e1 e2) i := (realScalarEval e1 i) + (realScalarEval e2 i)
| (RealScalarExpression.RealSubScalarScalar e1 e2) i := (realScalarEval e1 i) - (realScalarEval e2 i)
| (RealScalarExpression.RealMulScalarScalar e1 e2) i := (realScalarEval e1 i) * (realScalarEval e2 i)
| _ _ := 0 --dividing with reals causes "rec_fn_macro only allowed in meta definitions" error



def geometricScalarEval : GeometricScalarExpression → GeometricScalarInterp → ℝ 
| (GeometricScalarExpression.GeometricLitScalar r) i := r
| (GeometricScalarExpression.GeometricVarScalar v) i := i v
| (GeometricScalarExpression.GeometricAddScalarScalar e1 e2) i := (geometricScalarEval e1 i) + (geometricScalarEval e2 i)
| (GeometricScalarExpression.GeometricSubScalarScalar e1 e2) i := (geometricScalarEval e1 i) - (geometricScalarEval e2 i)
| (GeometricScalarExpression.GeometricMulScalarScalar e1 e2) i := (geometricScalarEval e1 i) * (geometricScalarEval e2 i)
| _ _ := 0 --same division error

def timeScalarEval : TimeScalarExpression → TimeScalarInterp → ℝ 
| (TimeScalarExpression.TimeLitScalar r) i := r
| (TimeScalarExpression.TimeVarScalar v) i := i v
| (TimeScalarExpression.TimeAddScalarScalar e1 e2) i := (timeScalarEval e1 i) + (timeScalarEval e2 i)
| (TimeScalarExpression.TimeSubScalarScalar e1 e2) i := (timeScalarEval e1 i) - (timeScalarEval e2 i)
| (TimeScalarExpression.TimeMulScalarScalar e1 e2) i := (timeScalarEval e1 i) * (timeScalarEval e2 i)
| _ _ := 0 --same division error

def velocityScalarEval : VelocityScalarExpression → VelocityScalarInterp → ℝ 
| (VelocityScalarExpression.VelocityLitScalar r) i := r
| (VelocityScalarExpression.VelocityVarScalar v) i := i v
| (VelocityScalarExpression.VelocityAddScalarScalar e1 e2) i := (velocityScalarEval e1 i) + (velocityScalarEval e2 i)
| (VelocityScalarExpression.VelocitySubScalarScalar e1 e2) i := (velocityScalarEval e1 i) - (velocityScalarEval e2 i)
| (VelocityScalarExpression.VelocityMulScalarScalar e1 e2) i := (velocityScalarEval e1 i) * (velocityScalarEval e2 i)
| _ _ := 0 --same division error



def geometric3VectorEval : Geometric3VectorExpression → Geometric3VectorInterp → Geometric3Vector
| (Geometric3VectorExpression.Geometric3LitVector vec) i := vec
| (Geometric3VectorExpression.Geometric3VarVector v) i := i v
| (Geometric3VectorExpression.Geometric3AddVectorVector v1 v2) i := Geometric3Vector_zero
| (Geometric3VectorExpression.Geometric3NegVector v) i := Geometric3Vector_zero
| (Geometric3VectorExpression.Geometric3MulScalarVector c v) i := Geometric3Vector_zero
| (Geometric3VectorExpression.Geometric3MulVectorScalar v c) i := Geometric3Vector_zero
| (Geometric3VectorExpression.Geometric3SubPointPoint p1 p2) i := Geometric3Vector_zero
| (Geometric3VectorExpression.Geometric3ParenVector v) i := Geometric3Vector_zero



def velocity3VectorEval : Velocity3VectorExpression → Velocity3VectorInterp → Velocity3Vector
| _ _ := Velocity3Vector_zero

def timeVectorEval : TimeVectorExpression → TimeVectorInterp → TimeVector
| _ _ := TimeVector_zero

def geometric3PointEval : Geometric3PointExpression → Geometric3PointInterp → Geometric3PointStruct
| _ _ := Geometric3Point_zero

def velocity3PointEval : Velocity3PointExpression → Velocity3PointInterp → Velocity3PointStruct
| _ _ := Velocity3Point_zero

def timePointEval : TimePointExpression → TimePointInterp → TimePointStruct
| _ _ := TimePoint_zero

/-
| (RealScalarExpression.RealLitScalar r) i := r
| (RealScalarExpression.RealVarScalar v) i := i v
| (RealScalarExpression.RealAddScalarScalar e1 e2) i := realScalarEval e1 i + realScalarEval e2 i
| (RealScalarExpression.RealSubScalarScalar e1 e2) i := realScalarEval e1 i - realScalarEval e2 i
| (RealScalarExpression.RealMulScalarScalar e1 e2) i := realScalarEval e1 i * realScalarEval e2 i
| (RealScalarExpression.RealDivScalarScalar e1 e2) i := realScalarEval e1 i / realScalarEval e2 i
| (RealScalarExpression.RealNegScalar e) i := -1 * realScalarEval e i
| (RealScalarExpression.RealInvScalar e) i := 1 / realScalarEval e i
| (RealScalarExpression.RealParenScalar e) i := realScalarEval e i
-/

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

