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

-- It's an additive commutative group
instance DimensionIsAbelianGroup : add_comm_group Dimension := _

-- Names for basic dimensions as dimensions
def length := Dimension.mk 1 0 0 0 0 0 0
def mass := Dimension.mk 0 1 0 0 0 0 0
def time := Dimension.mk 0 0 1 0 0 0 0
def current := Dimension.mk 0 0 0 1 0 0 0
def temperature := Dimension.mk 0 0 0 0 1 0 0
def quantity := Dimension.mk 0 0 0 0 0 1 0
def intensity := Dimension.mk 0 0 0 0 0 0 1

-- Functions that compute derived dimensions
def mul : Dimension → Dimension → Dimension 
| (Dimension.mk l m t c p q i) (Dimension.mk l' m' t' c' p' q' i') := 
  Dimension.mk (l+l') (m+m') (t+t') (c+c') (p+p') (q+q') (i+i')

def inv : Dimension → Dimension 
| (Dimension.mk l m t c p q i) := (Dimension.mk (-l) (-m) (-t) (-c) (-p) (-q) (-i) ) 

def div : Dimension → Dimension → Dimension 
| q1 q2 := mul q1 (inv q2)

-- some derived dimensions
def area := mul length length
def volume := mul area length
def velocity := div length time
def acceleration := div velocity time
def density := div quantity volume
-- etc

-- tell me the algebraic structure of give basic dimension

def realAffine1Space := affine_space (aff_pt ℝ 1) ℝ (aff_vec ℝ 1)
def nonNegativeReals := { m : ℝ // m >= 0}

def algebraOf : BasicDimension → Type
| BasicDimension.length := realAffine1Space
| BasicDimension.mass := nonNegativeReals
| BasicDimension.time := realAffine1Space
| BasicDimension.current := ℝ 
| BasicDimension.temperature := nonNegativeReals -- exists absolute zero
| BasicDimension.quantity := ℕ 
| BasicDimension.intensity := nonNegativeReals

/-
Kevin: https://benjaminjurke.com/content/articles/2015/compile-time-numerical-unit-dimension-checking/
-/
end dimension
