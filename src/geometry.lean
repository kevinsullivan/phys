import .....math.affine.real_affine_space
import ..metrology.dimension 

-- name serves as unique ID for a given geometric space
structure classicalGeometry : Type :=
mk :: (name : ℕ) (dim : ℕ ) 

noncomputable def classicalGeometryAlgebra : classicalGeometry → Algebra
| (classicalGeometry.mk n d) := Algebra.affine_space (to_affine d)