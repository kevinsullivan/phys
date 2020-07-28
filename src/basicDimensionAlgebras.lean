import data.real.basic
import ...math.affine.aff_coord_space

namespace basicDimension

-- Space or "BasicDimension"? Rethink name

inductive BasicDimension : Type
| length
| mass 
| time
| current
| temperature
| quantity
| intensity

open BasicDimension

-- tell me the algebraic structure of give basic dimension
def algebraOf : BasicDimension → Type
| length := affine_space (aff_pt ℝ 1) ℝ (aff_vec ℝ 1)
| mass := { m : ℝ // m >= 0}
| time := affine_space (aff_pt ℝ 1) ℝ (aff_vec ℝ 1)
| current := ℝ 
| temperature := { t : ℝ // t >= 0} -- absolute zero
| quantity := ℕ 
| intensity := { i : ℝ // i >= 0} 

#check affine_space (aff_pt ℝ 3) ℝ (aff_vec ℝ 3)
#print affine_space (aff_pt ℝ 3) ℝ (aff_vec ℝ 3)

end basicDimension