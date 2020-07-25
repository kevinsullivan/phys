import data.real.basic
import ...math.affine.aff_coord_space

namespace space

inductive Space : Type
| length
| mass 
| time
| current
| temperature
| quantity
| intensity

def type : Space → Type
| length := affine_space ℝ 

end space