import .....math.new_affine.real_affine_space
import ..metrology.dimension 

structure classicalTime : Type :=
mk :: (name : ℕ) -- name serves as unique ID for a given geometric space

-- provide standard world time object
def worldTime := classicalTime.mk 0 

noncomputable def classicalTimeAlgebra : classicalTime → real_affine.Algebra
| (classicalTime.mk n) := real_affine.Algebra.aff_space (real_affine.to_affine 1)

-- Kevin: add has_to_algebra typeclass

