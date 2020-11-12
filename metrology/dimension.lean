import data.real.basic

/-
Here we formalize the standard dimensional analysis concept of 
a physical dimension. 

A key to understanding this design is to see that we define two
types: BasicDimension and Dimension. BasicDimension represents
the set of basic dimension of the SI system only, while Dimension
represents the set of basic and derived dimensions. The function
basicDimToDim returns a Dimension value for each BasicDimension
value, injecting the set of basic dimensions into the set of 
basic and derived dimensions.  
-/ 



/-
First we enumerate the basic dimensions of the SI system.
-/

namespace dimension

-- Basic dimensions of the SI system 
inductive BasicDimension : Type
| length
| mass 
| time
| current
| temperature
| quantity
| intensity

/-
Next we associate a scalar type with each basic dimension.
-/

def basicDimScalarType : BasicDimension → Type 
| BasicDimension.length := ℝ 
| BasicDimension.time := ℝ 
| BasicDimension.mass := { r : ℝ // r >= 0}
| BasicDimension.current := ℝ 
| BasicDimension.temperature := { r : ℝ // r >= 0 } -- how/where to say can't be equivalent to negative in Kelvin?  
| BasicDimension.quantity := ℕ 
| BasicDimension.intensity := {r : ℝ // r >= 0}    -- is this right?

/-
Now we represent an arbitrary derived dimension as a 7-tuple of 
rational exponents corresponding to the basic dimensions. It's
well known that the algebraic structure of this set is that of 
an additive commutative (abelian) group. (Should be proved.)
For example, the dimension for velocity is <1,0,-1, 0, 0, 0, 0>.
ToDo: Is ℚ really the right type for these values? Do we need
fractional dimensions?
-/
structure Dimension  : Type :=
mk :: 
(length: ℚ)
(mass : ℚ)
(time : ℚ)
(current: ℚ)
(temperature : ℚ)
(quantity : ℚ)
(intensity: ℚ)

/-
Here is the injection of BasicDimension into Dimension.
-/
def basicDimToDim : BasicDimension → Dimension
| BasicDimension.length := Dimension.mk 1 0 0 0 0 0 0
| BasicDimension.mass := Dimension.mk 0 1 0 0 0 0 0
| BasicDimension.time := Dimension.mk 0 0 1 0 0 0 0
| BasicDimension.current := Dimension.mk 0 0 0 1 0 0 0
| BasicDimension.temperature := Dimension.mk 0 0 0 0 1 0 0
| BasicDimension.quantity := Dimension.mk 0 0 0 0 0 1 0
| BasicDimension.intensity := Dimension.mk 0 0 0 0 0 0 1

/-
Here now are  functions for computing derived dimensions. 
-/
-- Functions that compute derived dimensions
def mul : Dimension → Dimension → Dimension 
| (Dimension.mk l m t c p q i) (Dimension.mk l' m' t' c' p' q' i') := 
  Dimension.mk (l+l') (m+m') (t+t') (c+c') (p+p') (q+q') (i+i')

instance : has_mul Dimension := ⟨mul⟩

def inv : Dimension → Dimension 
| (Dimension.mk l m t c p q i) := (Dimension.mk (-l) (-m) (-t) (-c) (-p) (-q) (-i) ) 

def div : Dimension → Dimension → Dimension 
| q1 q2 := mul q1 (inv q2)

/-
Standard claim: the set of dimensions forms a multiplicative
abelian (commutative) group. But is this really true? If, for
example, quantity of material is measured as a natural number,
what quantity do you get when you take 1/2 of 3 particles? If
the notion is that particles are indivisible then this either
makes no sense, or the answer is 1 remainder 1, and what does
that mean? For now, we state the usual claim, but we think it
requires more thought.
-/
instance dimensionIsAbelianGroup : add_comm_group Dimension := sorry


-- tell me the algebraic structure of give basic dimension

/-
def algebraOf : BasicDimension → Type
| BasicDimension.length := ℝ --real_affine.Algebra--affine_space (aff_pt_coord_tuple ℝ 1) ℝ (aff_vec_coord_tuple ℝ 1)
| BasicDimension.mass := { m : ℝ // m >= 0}
| BasicDimension.time := ℝ--affine_space (aff_pt_coord_tuple ℝ 1) ℝ (aff_vec_coord_tuple ℝ 1)
| BasicDimension.current := ℝ 
| BasicDimension.temperature := { m : ℝ // m >= 0} -- exists absolute zero
| BasicDimension.quantity := ℕ 
| BasicDimension.intensity := { m : ℝ // m >= 0}
-/

def algebraOfDimension : Dimension → real_affine.Algebra
| (Dimension.mk l m t c p q i) := real_affine.Algebra.aff_space (real_affine.to_affine 1)

end dimension
