import .....math.new_affine.real_affine_space
import ..metrology.dimension 

-- name serves as unique ID for a given geometric space
structure classicalGeometry : Type :=
mk :: (name : ℕ) (dim : ℕ ) 

-- provide standard 3D world object
def worldGeometry := classicalGeometry.mk 0 3

/-before:

noncomputable def classicalGeometryAlgebra : classicalGeometry → real_affine.Algebra
| (classicalGeometry.mk n d) := real_affine.Algebra.aff_space (real_affine.to_affine d)
plus "_space"
-/
noncomputable def classicalGeometryAlgebra : classicalGeometry → real_affine.Algebra
| (classicalGeometry.mk n d) := real_affine.Algebra.aff_space (real_affine.to_affine_space d)
