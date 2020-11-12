import .....math.affine.real_affine_coordinate_space_lib
import ..metrology.dimension 
import ..metrology.measurement
import .....math.affine.algebra


noncomputable theory
open real_lib


structure classicalTime : Type :=
mk :: (sp : real_affine_coord_nspace 1 (real_affine_coord_nspace.get_standard 1)) (id : ℕ) -- id serves as unique ID for a given geometric space


def get_classicalTime (id : ℕ) : classicalTime :=
⟨real_affine_coord_nspace.mk_with_standard_frame 1, id⟩

noncomputable def classicalTimeAlgebra : classicalTime →  real_affine_coord_nspace 1 (real_affine_coord_nspace.get_standard 1)
| (classicalTime.mk sp n) := sp

open measurementSystem
inductive classicalTimeFrame : Type 
| standard (t : classicalTime) : classicalTimeFrame
| interpret (f : classicalTimeFrame) (m : MeasurementSystem) : classicalTimeFrame

def classicalTime.stdFrame (t : classicalTime) :=
    classicalTimeFrame.standard t

def classicalTime.interpretFrame (f : classicalTimeFrame) (m : MeasurementSystem) :=
    classicalTimeFrame.interpret f m


structure classicalTimeVector (t : classicalTime) :=
mk :: (id : ℕ) (val : real_affine_coord_nspace.point t.sp)

structure classicalTimePoint (t : classicalTime) : Type :=
mk :: (id : ℕ) (pt : real_affine_point 1)


def tm := get_classicalTime 1

#check tm

/--/
noncomputable def classicalTimeFrameAlgebra : classicalTimeFrame → Algebra
| (classicalTime.mk sp n) := sp
-/

/-
structure classicalTimeVector (t : classicalTime) :=
mk :: (id : ℕ) (vec : real_affine_vector 1)

variables sp1 : classicalTime
variables (v1 : classicalTimeVector sp1) (v2 : classicalTimeVector sp1)
variables (a : aff_vec_coord_tuple ℝ 1) (b : aff_vec_coord_tuple ℝ 1)
def tt : _ := a + b

def classicalTimeVectorAdd {t : classicalTime} 
    : classicalTimeVector t → classicalTimeVector t → classicalTimeVector t
| v1 v2 := classicalTimeVector.mk (0) (v1.vec + v2.vec)
instance ct_vec_add {sp : classicalTime} : has_add (classicalTimeVector sp) := ⟨classicalTimeVectorAdd⟩
def classicalTimeVectorSub {t : classicalTime}
    : classicalTimeVector t → classicalTimeVector t → classicalTimeVector t
| v1 v2 := classicalTimeVector.mk (0) (v1.vec - v2.vec)
instance ct_vec_sub {sp : classicalTime} : has_sub (classicalTimeVector sp) := ⟨classicalTimeVectorSub⟩
def classicalTimeVectorNeg {t : classicalTime}
    : classicalTimeVector t → classicalTimeVector t
| v1 := ⟨0,-v1.vec⟩
instance ct_vec_neg {sp : classicalTime} : has_neg (classicalTimeVector sp) := ⟨classicalTimeVectorNeg⟩

structure classicalTimePoint (t : classicalTime) : Type :=
mk :: (id : ℕ) (pt : real_affine_point 1)
-/

/-
structure classicalTimeCoordinateVector (s : classicalTime) extends classicalTimeVector s :=
(f : classicalTimeFrame s)--mk :: (id : ℕ) (val : vector ℝ 1) {s : classicalTime} (f : classicalTimeFrame s)


structure classicalTimeCoordinatePoint (s : classicalTime) extends classicalTimePoint s :=
(f : classicalTimeFrame s)--mk 
-/
/-
The Algebra type is simply a variant type for encapsulating different kinds
of algebras (e.g., affine space, monoid, or whatever). It's currently situated
in the real_affine_space file, but should be moved.
-/
/-
-/

-- provide standard world time object
def worldTime := getClassicalTime 0
#check worldTime

/-
noncomputable def classicalTimeAlgebra : classicalTime → real_affine.Algebra
| (classicalTime.mk n) := real_affine.Algebra.aff_space (real_affine.to_affine_space 1)
-/

/-
noncomputable def classicalTimeVectorAlgebra {t : classicalTime} : classicalTimeVector t → real_affine.Algebra
| (classicalTimeVector.mk _ v) := real_affine.Algebra.aff_vec_coord_tupletor (real_affine.to_affine_vector v)

noncomputable def classicalTimePointAlgebra {t : classicalTime} : classicalTimeVector t → real_affine.Algebra
| (classicalTimeVector.mk _ v) := real_affine.Algebra.aff_point (real_affine.to_affine_point v)

noncomputable def classicalTimeFrameHelper  {t : classicalTime} : classicalTimeFrame t → real_affine.real_affine_frame 1
| (@classicalTimeFrame.standard t m) := real_affine.to_standard_frame 1
| (@classicalTimeFrame.derived t f p v m) := real_affine.to_derived_frame 1 p.val 
    (λn : fin 1, (v n).val) (real_affine.to_coordinatized_affine_space 1 
    (classicalTimeFrameHelper f).1)

noncomputable def classicalTimeFrameAlgebra {t : classicalTime} : classicalTimeFrame t → real_affine.Algebra
| f := real_affine.Algebra.aff_frame (classicalTimeFrameHelper f)
noncomputable def classicalTimeCoordinateVectorAlgebra {t : classicalTime} : classicalTimeCoordinateVector t → real_affine.Algebra :=
    λ v, real_affine.Algebra.aff_vec_coord_tupletor (real_affine.to_affine_vector_with_frame v.val (real_affine.to_coordinatized_affine_space 1 (classicalTimeFrameHelper v.f).1))

noncomputable def classicalTimeCoordinatePointAlgebra {t : classicalTime} : classicalTimeCoordinatePoint t → real_affine.Algebra :=
    λ v, real_affine.Algebra.aff_point (real_affine.to_affine_point_with_frame v.val (real_affine.to_coordinatized_affine_space 1 (classicalTimeFrameHelper v.f).1))
-/

-- Kevin: add has_to_algebra typeclass

