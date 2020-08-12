import .....math.affine.real_affine_space
import ..metrology.dimension 

-- name serves as unique ID for a given geometric space
structure classicalVelocity : Type :=
mk :: (name : ℕ) 


-- TODO: Fix algebra. It should be vector space, I think (or is there a torsor here?)
noncomputable def classicalVelocityAlgebra : classicalVelocity → Algebra
| (classicalVelocity.mk n) := Algebra.affine_space (to_affine 1)