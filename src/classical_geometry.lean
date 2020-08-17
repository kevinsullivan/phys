import .....math.affine.real_affine_space
import ..metrology.dimension 

-- name serves as unique ID for a given geometric space
structure classicalGeometry : Type :=
mk :: (name : ℕ) (dim : ℕ ) 

-- provide standard 3D world object
def worldGeometry := classicalGeometry.mk 0 3

noncomputable def classicalGeometryAlgebra : classicalGeometry → Algebra
| (classicalGeometry.mk n d) := Algebra.affine_space (to_affine d)