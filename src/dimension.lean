import .....math.affine.aff_coord_space
import data.real.basic

/-
Here we formalize the standard dimensional analysis concept of 
a physical dimension. We enumerate the basic dimensions of the 
SI system by name, then represent an arbitrary dimension as a
7-tuple of rational exponents corresponding to the enumerated
basic dimensions. It's well known that the algebraic structure
of this set is that of an additive commutative (abelian) group.

Next we define functions for computing derived dimensions. Then
we give standard physics names to a few derived dimensions. This
list can be greatly extended. 
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

def dimType : BasicDimension → Type 
| BasicDimension.length := ℝ 
| BasicDimension.time := ℝ 
| BasicDimension.mass := { r : ℝ // r >= 0}
| BasicDimension.current := ℝ 
| BasicDimension.temperature := { r : ℝ // r >= 0 } -- how/where to say can't be equivalent to negative in Kelvin?  
| BasicDimension.quantity := ℕ 
| BasicDimension.intensity := {r : ℝ // r >= 0}    -- is this right?

/-
Usual formalization of concept of dimension
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

-- Names for basic dimensions as dimensions
def basicDimToDim : BasicDimension → Dimension
| BasicDimension.length := Dimension.mk 1 0 0 0 0 0 0
| BasicDimension.mass := Dimension.mk 0 1 0 0 0 0 0
| BasicDimension.time := Dimension.mk 0 0 1 0 0 0 0
| BasicDimension.current := Dimension.mk 0 0 0 1 0 0 0
| BasicDimension.temperature := Dimension.mk 0 0 0 0 1 0 0
| BasicDimension.quantity := Dimension.mk 0 0 0 0 0 1 0
| BasicDimension.intensity := Dimension.mk 0 0 0 0 0 0 1

-- Functions that compute derived dimensions
def mul : Dimension → Dimension → Dimension 
| (Dimension.mk l m t c p q i) (Dimension.mk l' m' t' c' p' q' i') := 
  Dimension.mk (l+l') (m+m') (t+t') (c+c') (p+p') (q+q') (i+i')

def inv : Dimension → Dimension 
| (Dimension.mk l m t c p q i) := (Dimension.mk (-l) (-m) (-t) (-c) (-p) (-q) (-i) ) 

def div : Dimension → Dimension → Dimension 
| q1 q2 := mul q1 (inv q2)

-- It's an additive commutative group
instance dimensionIsAbelianGroup : add_comm_group Dimension := _

-- some dimensions

open BasicDimension

-- Names for basic dimensions as dimensions
def length := basicDimToDim length 
def mass := basicDimToDim mass 
def time := basicDimToDim time
def current := basicDimToDim current
def temperature := basicDimToDim temperature
def quantity := basicDimToDim quantity
def intensity := basicDimToDim intensity

-- And now some deried dimension
def area := mul length length
def volume := mul area length
def velocity := div length time
def acceleration := div velocity time
def density := div quantity volume
-- etc

-- tell me the algebraic structure of give basic dimension

def realAffine1Space := affine_space (aff_pt ℝ 1) ℝ (aff_vec ℝ 1)
def nonNegativeReals := { m : ℝ // m >= 0}

structure Algebra : Type 1 :=
mk :: 
(length: Type)
(mass : Type)
(time : Type)
(current: Type)
(temperature : Type)
(quantity : Type)
(intensity: Type)

def algebraOf : BasicDimension → Type
| BasicDimension.length := affine_space (aff_pt ℝ 1) ℝ (aff_vec ℝ 1)
| BasicDimension.mass := { m : ℝ // m >= 0}
| BasicDimension.time := affine_space (aff_pt ℝ 1) ℝ (aff_vec ℝ 1)
| BasicDimension.current := ℝ 
| BasicDimension.temperature := { m : ℝ // m >= 0} -- exists absolute zero
| BasicDimension.quantity := ℕ 
| BasicDimension.intensity := { m : ℝ // m >= 0}

def algebraOfDimension : Dimension → Type
| (Dimension.mk l m t c p q i) := affine_space (aff_pt ℝ 1) ℝ (aff_vec ℝ 1)


/-
Kevin: https://benjaminjurke.com/content/articles/2015/compile-time-numerical-unit-dimension-checking/
-/
end dimension
