--import .....math.affine.aff_coord_space
import data.real.basic

namespace scalar

/-
Algebraic types of scalars for different physical dimensions.
Deprecated. Use basicDimScalarType.

TODO: Rethink use of abbreviation
-/
abbreviation length := ℝ 
abbreviation time := ℝ 
abbreviation mass := { r : ℝ // r >= 0}
abbreviation current := ℝ 
abbreviation temperature := { r : ℝ // r >= 0} -- how/where to say can't be equivalent to negative in Kelvin?  
abbreviation quantity := ℕ 
abbreviation intensity := {r : ℝ // r >= 0}    -- is this right?

-- Need proof that result isn't negative. Currently sorry. Turns into runtime check?
def add_mass : mass → mass → mass 
| m1 m2 := ⟨m1.1 + m2.1, _ ⟩

-- Need proof that result isn't negative. Currently sorry. Turns into runtime check?
def add_intensity : intensity → intensity → intensity 
| i1 i2 := ⟨i1.1 + i2.1, _ ⟩

-- Need proof that result isn't negative. Currently sorry. Turns into runtime check?
def add_temperature : temperature → temperature → temperature 
| i1 i2 := ⟨i1.1 + i2.1, _ ⟩

-- Need proof that result isn't negative. Currently sorry. Turns into runtime check?
def sub_mass : mass → mass → mass 
| m1 m2 := ⟨m1.1 - m2.1, _ ⟩

-- Need proof that result isn't negative. Currently sorry. Turns into runtime check?
def sub_intensity : intensity → intensity → intensity 
| i1 i2 := ⟨i1.1 - i2.1, _ ⟩

-- Need proof that result isn't negative. Currently sorry. Turns into runtime check?
def sub_temperature : temperature → temperature → temperature 
| i1 i2 := ⟨i1.1 - i2.1, _ ⟩

-- Need proof that result isn't negative. Currently sorry. Turns into runtime check?
def mul_mass : mass → mass → mass 
| m1 m2 := ⟨m1.1 * m2.1, _ ⟩

-- Need proof that result isn't negative. Currently sorry. Turns into runtime check?
def mul_intensity : intensity → intensity → intensity 
| i1 i2 := ⟨i1.1 * i2.1, _ ⟩

-- Need proof that result isn't negative. Currently sorry. Turns into runtime check?
def mul_temperature : temperature → temperature → temperature 
| i1 i2 := ⟨i1.1 * i2.1, _ ⟩


end scalar