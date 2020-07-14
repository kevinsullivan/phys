import ..physics.physlib

noncomputable theory



abbreviation RealScalarDefault := (0 : ℝ)
--for peirce:
abbreviation GeometricScalarDefault := (0 : ℝ)
abbreviation TimeScalarDefault := (0 : ℝ)
abbreviation VelocityScalarDefault := (0 : ℝ)


abbreviation NatDefault := (0 : ℕ)
abbreviation RationalDefault := (0 : ℚ)




--7/14 why is aff_vec in this file? - needs to go
abbreviation Geometric3VectorDefault := Geometric3Vector.mk geom3 (aff_vec.mk [0,0,0,0] rfl rfl) affine_frame.std
abbreviation Velocity3VectorDefault := Velocity3Vector.mk vel (aff_vec.mk [0,0,0,0] rfl rfl) affine_frame.std 
abbreviation TimeVectorDefault := TimeVector.mk time (aff_vec.mk [0,0] rfl rfl) affine_frame.std
abbreviation Geometric3PointDefault := Geometric3Point geom3 0 0 0
--abbreviation Velocity3Point_zero := Velocity3PointStruct.mk vel (aff_pt.mk [1,0,0,0] rfl rfl) std 
abbreviation TimePointDefault := TimePoint time 0

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

notation !n := RealScalarVar.mk n
notation !n := GeometricScalarVar.mk n
notation !n := TimeScalarVar.mk n
notation !n := VelocityScalarVar.mk n
notation !n := Geometric3VectorVar.mk n
notation !n := TimeVectorVar.mk n
notation !n := Velocity3VectorVar.mk n
notation !n := Geometric3PointVar.mk n
notation !n := TimePointVar.mk n


--7/12 Andrew - NO, WE DONT WANT THIS!!!
--structure Velocity3PointVar : Type :=
--	mk :: (n : ℕ)


mutual inductive RealScalarExpression, GeometricScalarExpression, 
	TimeScalarExpression, VelocityScalarExpression, Geometric3VectorExpression, 
	Velocity3VectorExpression, TimeVectorExpression, Geometric3PointExpression, 
	/-Velocity3PointExpression,-/ TimePointExpression
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
/-with Velocity3PointExpression : Type
| Velocity3LitPoint : Velocity3PointStruct → Velocity3PointExpression
| Velocity3SubVectorVector : Velocity3VectorExpression → Velocity3VectorExpression → Velocity3PointExpression
| Velocity3NegPoint : Velocity3PointExpression → Velocity3PointExpression
| Velocity3AddVectorPoint : Velocity3VectorExpression → Velocity3PointExpression → Velocity3PointExpression
| Velocity3AddPointVector : Velocity3PointExpression → Velocity3VectorExpression → Velocity3PointExpression
| Velocity3ScalarPoint : RealScalarExpression → Velocity3PointExpression → Velocity3PointExpression
| Velocity3PointScalar : Velocity3PointExpression → RealScalarExpression → Velocity3PointExpression
| Velocity3ParenPoint : Velocity3PointExpression → Velocity3PointExpression-/
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
notation #e := RealScalarExpression.RealScalarVar e
notation e1 + e2 := RealScalarExpression.RealAddScalarScalar e1 e2
notation e1 - e2 := RealScalarExpression.RealSubScalarScalar e1 e2
notation e1 * e2 := RealScalarExpression.RealMulScalarScalar e1 e2
notation e1 / e2 := RealScalarExpression.RealDivScalarScalar e1 e2
notation -e := RealScalarExpression.RealNegScalar e
notation e⁻¹ := RealScalarExpression.RealInvScalar e
notation (e := RealScalarExpression.RealParenScalar e
notation %e := RealScalarExpression.RealScalarLiteral e

--GeometricScalarExpression Notations
notation #e := GeometricScalarExpression.GeometricVarScalar e
notation e1 + e2 := GeometricScalarExpression.GeometricAddScalarScalar e1 e2
notation e1 - e2 := GeometricScalarExpression.GeometricSubScalarScalar e1 e2
notation e1 * e2 := GeometricScalarExpression.GeometricMulScalarScalar e1 e2
notation e1 / e2 := GeometricScalarExpression.GeometricDivScalarScalar e1 e2
notation -e := GeometricScalarExpression.GeometricNegScalar e
notation e⁻¹ := GeometricScalarExpression.GeometricInvScalar e
notation (e := GeometricScalarExpression.GeometricParenScalar e
notation |e| := GeometricScalarExpression.GeometricNormVector e
notation =e := GeometricScalarExpression.GeometricScalarLiteral e


--def p : GeometricScalarExpression := %GeometricScalarDefault : GeometricScalarExpression

--TimeScalarExpression Notations
notation #e := TimeScalarExpression.TimeVarScalar  
notation e1 + e2 := TimeScalarExpression.TimeAddScalarScalar e1 e2
notation e1 - e2 := TimeScalarExpression.TimeSubScalarScalar e1 e2
notation e1 * e2 := TimeScalarExpression.TimeMulScalarScalar e1 e2
notation e1 / e2 := TimeScalarExpression.TimeDivScalarScalar e1 e2
notation -e := TimeScalarExpression.TimeNegScalar e
notation e¬⁻¹⁻¹ := TimeScalarExpression.TimeInvScalar e
notation (e := TimeScalarExpression.TimeParenScalar e
notation |e| := TimeScalarExpression.TimeNormVector e
notation %e := TimeScalarExpression.TimeScalarLiteral e
--VelocityScalarExpression Notations
notation #e := VelocityScalarExpression.VelocityVarScalar e
notation e1 + e2 := VelocityScalarExpression.VelocityAddScalarScalar e1 e2
notation e1 - e2 := VelocityScalarExpression.VelocitySubScalarScalar e1 e2
notation e1 * e2 := VelocityScalarExpression.VelocityMulScalarScalar e1 e2
notation e1 / e2 := VelocityScalarExpression.VelocityDivScalarScalar e1 e2
notation -e := VelocityScalarExpression.VelocityNegScalar e
notation e⁻¹ := VelocityScalarExpression.VelocityInvScalar e
notation (e := VelocityScalarExpression.VelocityParenScalar e
notation |e| := VelocityScalarExpression.VelocityNormVector e
notation %e := VelocityScalarExpression.VelocityScalarLiteral e

--Gemoetric3Vector Notations
notation #e := Geometric3VectorExpression.Geometric3VectorVar e
notation e1 + e2 := Geometric3VectorExpression.Geometric3AddVectorVector e1 e2
notation -e := Geometric3VectorExpression.Geometric3NegVector e
notation c * e := Geometric3VectorExpression.Geometric3MulScalarVector c e
notation e * c := Geometric3VectorExpression.Geometric3MulVectorScalar e c
notation e1 - e2 := Geometric3VectorExpression.Geometric3SubPointPoint e1 e2
notation (e := Geometric3VectorExpression.Geometric3ParenVector e
notation %e := Geometric3VectorExpression.Geometric3VectorLiteral e

--Velocity3Vector Notations
notation #e := Velocity3VectorExpression.Velocity3VectorVar e
notation e1 + e2 := Velocity3VectorExpression.Velocity3AddVectorVector e1 e2
notation -e := Velocity3VectorExpression.Velocity3NegVector e
notation c * e := Velocity3VectorExpression.Velocity3MulScalarVector c e
notation e * c := Velocity3VectorExpression.Velocity3MulVectorScalar e c
notation e1 - e2 := Velocity3VectorExpression.Velocity3SubPointPoint e1 e2
notation (e := Velocity3VectorExpression.Velocity3ParenVector e
notation %e := Velocity3VectorExpression.Velocity3VectorLiteral e

--TimeVector Notations
notation #e := TimeVectorExpression.TimeVectorVar e
notation e1 + e2 := TimeVectorExpression.TimeAddVectorVector e1 e2
notation -e := TimeVectorExpression.TimeNegVector e
notation c * e := TimeVectorExpression.TimeMulScalarVector c e
notation e * c := TimeVectorExpression.TimeMulVectorScalar e c
notation e1 - e2 := TimeVectorExpression.TimeSubPointPoint e1 e2
notation (e := TimeVectorExpression.TimeParenVector e
notation %e := TimeVectorExpression.TimeVectorLiteral e


--Geometric3Point Notations
notation #e := Geometric3PointExpression.Geometric3PointVar e
notation e1 - e2 := Geometric3PointExpression.Geometric3SubVectorVector e1 e2
notation -e := Geometric3PointExpression.Geometric3NegPoint e
notation e1 + e2 := Geometric3PointExpression.Geometric3AddVectorPoint e1 e2
notation e1 + e2 := Geometric3PointExpression.Geometric3AddPointVector e1 e2
notation c * e := Geometric3PointExpression.Geometric3ScalarPoint c e
notation e * c := Geometric3PointExpression.Geometric3PointScalar e c
notation (e := Geometric3PointExpression.Geometric3ParenPoint e
notation %e := Geometric3PointExpression.TimePointLiteral e

--Andrew : Remove this
--Velocity3Point Notations
/-notation e1 - e2 := Velocity3PointExpression.Velocity3SubVectorVector e1 e2
notation -e := Velocity3PointExpression.Velocity3NegPoint e
notation e1 + e2 := Velocity3PointExpression.Velocity3AddVectorPoint e1 e2
notation e1 + e2 := Velocity3PointExpression.Velocity3AddPointVector e1 e2
notation c * e := Velocity3PointExpression.Velocity3ScalarPoint c e
notation e * c := Velocity3PointExpression.Velocity3PointScalar e c
notation (e := Velocity3PointExpression.Velocity3ParenPoint e
-/
--TimePoint Notations
notation #e := TimePointExpression.TimePointVar e
notation e1 + e2 := TimePointExpression.TimeAddPointVector e1 e2
notation e1 + e2 := TimePointExpression.TimeAddVectorPoint e1 e2
notation (e := TimePointExpression.TimeParenPoint e
notation e1 - e2 := TimePointExpression.TimeSubVectorVector e1 e2
notation -e := TimePointExpression.TimeNegPoint e
notation c * e := TimePointExpression.TimeScalarPoint c e
notation e * c := TimePointExpression.TimePointScalar e c
notation %e := TimePointExpression.TimePointLiteral e









abbreviation RealScalarInterp := RealScalarVar → ℝ

abbreviation GeometricScalarInterp := GeometricScalarVar → ℝ
abbreviation TimeScalarInterp := TimeScalarVar → ℝ
abbreviation VelocityScalarInterp := VelocityScalarVar → ℝ

abbreviation Geometric3VectorInterp := Geometric3VectorVar → Geometric3Vector
abbreviation TimeVectorInterp := TimeVectorVar → TimeVector
abbreviation Velocity3VectorInterp := Velocity3VectorVar → Velocity3Vector

abbreviation Geometric3PointInterp := Geometric3PointVar → Geometric3PointStruct
abbreviation TimePointInterp := TimePointVar → TimePointStruct
--abbreviation Velocity3PointInterp := Velocity3PointVar → Velocity3PointStruct


def DefaultRealScalarInterp : RealScalarInterp := λ scalar, RealScalarDefault
def DefaultGeometricScalarInterp : GeometricScalarInterp := λ scalar, RealScalarDefault
def DefaultTimeScalarInterp : TimeScalarInterp := λ scalar, RealScalarDefault
def DefaultVelocityScalarInterp : VelocityScalarInterp := λ scalar, RealScalarDefault
def DefaultGeometric3VectorInterp : Geometric3VectorInterp := λ vector, Geometric3VectorDefault
def DefaultTimeVectorInterp : TimeVectorInterp := λ vector, TimeVectorDefault
def DefaultVelocity3VectorInterp : Velocity3VectorInterp := λ vector, Velocity3VectorDefault
def DefaultGeometric3PointInterp : Geometric3PointInterp := λ point, Geometric3PointDefault
def DefaultTimePointInterp : TimePointInterp := λ point, TimePointDefault
--def DefaultVelocity3PointInterp : Velocity3PointInterp := λ point, Velocity3Point_zero

inductive RealScalarCommand : Type
| Assignment : RealScalarVar → RealScalarExpression → RealScalarCommand

notation v = e := RealScalarCommand.Assignment v e

inductive GeometricScalarCommand : Type
| Assignment : GeometricScalarVar → GeometricScalarExpression → GeometricScalarCommand

notation v = e := GeometricScalarCommand.Assignment v e

inductive TimeScalarCommand : Type
| Assignment : TimeScalarVar → TimeScalarExpression → TimeScalarCommand

notation v = e := TimeScalarCommand.Assignment v e

inductive VelocityScalarCommand : Type
| Assignment : VelocityScalarVar → VelocityScalarExpression → VelocityScalarCommand

notation v = e := VelocityScalarCommand.Assignment v e

inductive Geometric3VectorCommand : Type
| Assignment : Geometric3VectorVar → Geometric3VectorExpression → Geometric3VectorCommand

notation v = e := Geometric3VectorCommand.Assignment v e

inductive TimeVectorCommand : Type
| Assignment : TimeVectorVar → TimeVectorExpression → TimeVectorCommand

notation v = e := TimeVectorCommand.Assignment v e

inductive Velocity3VectorCommand : Type
| Assignment : Velocity3VectorVar → Velocity3VectorExpression → Velocity3VectorCommand

notation v = e := Velocity3VectorCommand.Assignment v e

inductive Geometric3PointCommand : Type
| Assignment : Geometric3PointVar → Geometric3PointExpression → Geometric3PointCommand

notation v = e := Geometric3PointCommand.Assignment v e

inductive TimePointCommand : Type
| Assignment : TimePointVar → TimePointExpression → TimePointCommand

notation v = e := TimePointCommand.Assignment v e
/-
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

--def velocity3PointEval : Velocity3PointExpression → Velocity3PointInterp → Velocity3PointStruct
--| _ _ := Velocity3Point_zero

def timePointEval : TimePointExpression → TimePointInterp → TimePointStruct
| _ _ := TimePoint_zero
-/
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


--import .physlang


def worldGeometry := EuclideanGeometry  "worldGeometry" 3

def worldTime := ClassicalTime  "worldTime"  

def worldVelocity := ClassicalVelocity  "worldVelocity" 3



def REAL3_VAR_IDENT_tf_start_point : Geometric3PointVar  :=  !1


def REAL1.LITERAL.B.L105C36.E.L105C36 : _ :=  GeometricScalarExpression.GeometricLitScalar 1

def REAL1.LITERAL.B.L105C40.E.L105C40 : _ :=  %_ 

def REAL1.LITERAL.B.L105C44.E.L105C44 : GeometricScalarExpression  :=  %GeometricScalarDefault 
def REAL3.LITERAL.B.L105C26.E.L105C46 : _ := % (REAL1.EXPR.B.L105C36.E.L105C36)  (REAL1.EXPR_.B.L105C40.E.L105C40)  (REAL1.EXPR.B.L105C44.E.L105C44) 
def DECLARE.B.L104C5.E.L105C47 : _ := (REAL3.VAR.IDENT.tf.start.point) = (REAL3.EXPR_.B.L105C26.E.L105C46)


def REAL3.VAR.IDENT.tf.end.point : Geometric3PointVar  :=  !2


def REAL1.LITERAL.B.L107C34.E.L107C34 : _ :=  %_ 

def REAL1.LITERAL.B.L107C38.E.L107C39 : _ :=  %_ 

def REAL1.LITERAL.B.L107C42.E.L107C42 : _ :=  %_ 
def REAL3.LITERAL.B.L107C24.E.L107C44 : _ := % (REAL1.EXPR_.B.L107C34.E.L107C34)  (REAL1.EXPR_.B.L107C38.E.L107C39)  (REAL1.EXPR.B.L107C42.E.L107C42) 
def DECLARE.B.L106C5.E.L107C45 : _ := (REAL3.VAR.IDENT.tf.end.point) = (REAL3.EXPR_.B.L107C24.E.L107C44)


def REAL3_VAR_IDENT_tf_displacement : GeometricVectorVar  :=  !3


def REAL3.EXPR_tf_end_point.B.L109C35.E.L109C35 : _ := # (REAL3.VAR.IDENT.tf.end.point) 

def REAL3.EXPR_tf_start_point.B.L109C50.E.L109C50 : _ := # (REAL3.VAR.IDENT.tf.start.point) 
def REAL3.EXPR_.B.L109C35.E.L109C50 : _ := (REAL3.EXPR_tf_end_point.B.L109C35.E.L109C35) - (REAL3.EXPR_tf_start_point.B.L109C50.E.L109C50)
def DECLARE_.B.L109C5.E.L109C64 : _ := (REAL3.VAR.IDENT.tf.displacement) = (REAL3.EXPR_.B.L109C35.E.L109C50)

