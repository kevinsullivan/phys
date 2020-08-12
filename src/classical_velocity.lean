import .classical_geometry
import .classical_time

-- name serves as unique ID for a given geometric space
structure classicalVelocity : Type :=
mk :: (g : classicalGeometry) (t : classicalTime) 


-- TODO: Connect algebra of g to the algebra that is returned? Or is it already?
noncomputable def classicalVelocityAlgebra : classicalVelocity → Algebra
| (classicalVelocity.mk g t) := Algebra.vector_space (to_vector 1)