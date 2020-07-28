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
| length := affine_space (aff_pt ℝ 3) ℝ (aff_vec ℝ 3)
| mass := affine_space (aff_pt ℝ 3) ℝ (aff_vec ℝ 3)
| time := affine_space (aff_pt ℝ 1) ℝ (aff_vec ℝ 1)
| current := affine_space (aff_pt ℝ 3) ℝ (aff_vec ℝ 3)
| temperature := affine_space (aff_pt ℝ 1) ℝ (aff_vec ℝ 1)
| quantity := affine_space (aff_pt ℝ 3) ℝ (aff_vec ℝ 3)
| intensity := affine_space (aff_pt ℝ 3) ℝ (aff_vec ℝ 3)

#check affine_space (aff_pt ℝ 3) ℝ (aff_vec ℝ 3)

end basicDimension