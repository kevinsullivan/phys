import .....math.new_affine.real_affine_space
import ..metrology.dimension 
import ..metrology.measurement

structure classicalTime : Type :=
mk :: (name : ℕ) -- name serves as unique ID for a given geometric space


structure classicalTimeVector (t : classicalTime) : Type :=
mk :: (name : ℕ) (val : vector ℝ 1)

structure classicalTimePoint (t : classicalTime) : Type :=
mk :: (name : ℕ) (val : vector ℝ 1)

--inductive classicalTimeFrame : classicalTime → Type 
--| standard (t : classicalTime) : classicalTimeFrame t
--| derived (t : classicalTime) : classicalTimeFrame t

open measurementSystem

inductive classicalTimeFrame : classicalTime → Type 
| standard (t : classicalTime) (m : MeasurementSystem) : classicalTimeFrame t
| derived (t : classicalTime) : 
    classicalTimeFrame t → classicalTimePoint t → (fin 1 → classicalTimeVector t) → MeasurementSystem → classicalTimeFrame t

structure classicalTimeCoordinateVector (s : classicalTime) extends classicalTimeVector s :=
(f : classicalTimeFrame s)--mk :: (name : ℕ) (val : vector ℝ 1) {s : classicalTime} (f : classicalTimeFrame s)

structure classicalTimeCoordinatePoint (s : classicalTime) extends classicalTimePoint s :=
(f : classicalTimeFrame s)--mk 
-- provide standard world time object
def worldTime := classicalTime.mk 0 

noncomputable def classicalTimeAlgebra : classicalTime → real_affine.Algebra
| (classicalTime.mk n) := real_affine.Algebra.aff_space (real_affine.to_affine_space 1)

noncomputable def classicalTimeVectorAlgebra {t : classicalTime} : classicalTimeVector t → real_affine.Algebra
| (classicalTimeVector.mk _ v) := real_affine.Algebra.aff_vector (real_affine.to_affine_vector v)

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
    λ v, real_affine.Algebra.aff_vector (real_affine.to_affine_vector_with_frame v.val (real_affine.to_coordinatized_affine_space 1 (classicalTimeFrameHelper v.f).1))

noncomputable def classicalTimeCoordinatePointAlgebra {t : classicalTime} : classicalTimeCoordinatePoint t → real_affine.Algebra :=
    λ v, real_affine.Algebra.aff_point (real_affine.to_affine_point_with_frame v.val (real_affine.to_coordinatized_affine_space 1 (classicalTimeFrameHelper v.f).1))


-- Kevin: add has_to_algebra typeclass

