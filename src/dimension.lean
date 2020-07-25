import .....math.affine.aff_coord_space
import data.real.basic

/-
Kevin: https://benjaminjurke.com/content/articles/2015/compile-time-numerical-unit-dimension-checking/
-/

/-
Restricting the exponents of dimensions to 
integers equates to assuming smooth rather
than, say, fractal spaces (I think. -Kevin).
-/
abbreviation dimType := ℚ 

structure PhysicalDimension  : Type :=
mk :: 
(length: dimType)
(mass : dimType)
(time : dimType)
(current: dimType)
(temperature : dimType)
(quantity : dimType)
(intensity: dimType)

def mul : 
    PhysicalDimension → PhysicalDimension → PhysicalDimension 
| (PhysicalDimension.mk l m t c p q i) 
  (PhysicalDimension.mk l' m' t' c' p' q' i') := 
  PhysicalDimension.mk (l+l') (m+m') (t+t') (c+c') (p+p') (q+q') (i+i')

def inv : 
    PhysicalDimension → PhysicalDimension 
| (PhysicalDimension.mk l m t c p q i) := (PhysicalDimension.mk (-l) (-m) (-t) (-c) (-p) (-q) (-i) ) 

def div : PhysicalDimension → PhysicalDimension → PhysicalDimension 
| q1 q2 := mul q1 (inv q2)

-- Basic dimensions
def length := PhysicalDimension.mk 1 0 0 0 0 0 0
def mass := PhysicalDimension.mk 0 1 0 0 0 0 0
def time := PhysicalDimension.mk 0 0 1 0 0 0 0
def current := PhysicalDimension.mk 0 0 0 1 0 0 0
def temperature := PhysicalDimension.mk 0 0 0 0 1 0 0
def quantity := PhysicalDimension.mk 0 0 0 0 0 1 0
def intensity := PhysicalDimension.mk 0 0 0 0 0 0 1

-- derived dimensions
def area := mul length length
def volume := mul area length
def velocity := div length time
def acceleration := div velocity time
-- etc