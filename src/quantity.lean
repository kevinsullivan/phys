import .measurement
import .dimension
import .scalar

namespace quantity

open measurementSystem
open dimension

/-
We express a physical quantity as a tuple of scalars, each
of a type consistent with its base dimension, relative to a
given (potentially derived) dimension and measurement system.
In this way, scalars are combined with units to yield quantities.
-/
structure Quantity (d : Dimension) (m : MeasurementSystem) : Type :=
mk :: 
(length : scalar.length)
(mass : scalar.mass)
(time : scalar.time)
(current : scalar.current)
(temperature : scalar.temperature)
(quantity : scalar.quantity)
(intensity : scalar.intensity) 

open scalar

-- Return quantity of one unit of basic dimension in given measurement system
def quantity (d : BasicDimension) (m : MeasurementSystem) (s : dimType d) : 
  Quantity (basicDimToDim d) m :=
match d with 
| BasicDimension.length :=        Quantity.mk s ⟨0, _⟩ 0 0 0 0 ⟨0, _⟩ 
| BasicDimension.mass  :=         Quantity.mk 0 s 0 0 0 0 ⟨0, _⟩
| BasicDimension.time  :=         Quantity.mk 0 ⟨0, _⟩ s 0 0 0 ⟨0, _⟩ 
| BasicDimension.current  :=      Quantity.mk 0 ⟨0, _⟩ 0 s 0 0 ⟨0, _⟩
| BasicDimension.temperature  :=  Quantity.mk 0 ⟨0, _⟩ 0 0 s 0 ⟨0, _⟩
| BasicDimension.quantity  :=     Quantity.mk 0 ⟨0, _⟩ 0 0 0 s ⟨0, _⟩
| BasicDimension.intensity :=     Quantity.mk 0 ⟨0, _⟩ 0 0 0 0 s
end 

-- Examples

def oneMeter := quantity BasicDimension.length si_measurement_system (1 : ℝ)
def twoSeconds := quantity BasicDimension.time si_measurement_system (2 : ℝ)
def threePounds := quantity BasicDimension.mass imperial_measurement_system ⟨(3 : ℝ), _ ⟩

open scalar
open dimension

/-
We can add quantities as long as they are in the same physical
dimensions and expressed with respect to the same measurement
systems. 

We note that we could build measurement system conversions in
here. We choose not to do so, leaving designers to make such
conversions explicit where needed.

Proofs will be required that we aren't violating any
algebraic invariants. For example, we mustn't subtract a large
mass from a small mass to obtain a negative mass, because mass
(in the ordinary physics we formalize) can't be negative. 
-/
def add 
    {d : Dimension} 
    {ms : MeasurementSystem} 
    (q1 q2 : Quantity d ms) : 
    Quantity d ms := 
  match q1 with 
    | Quantity.mk l m t c p q i :=
        match q2 with 
            | Quantity.mk l' m' t' c' p' q' i' :=
      Quantity.mk (l+l') (scalar.add_mass m m') (t+t') (c+c') (p+p') (q+q') (scalar.add_intensity i i')
    end
  end

def sub {d : Dimension} {ms : MeasurementSystem}  (q1 q2 : Quantity d ms) : 
    Quantity d ms := 
  match q1 with 
    | Quantity.mk l m t c p q i :=
        match q2 with 
            | Quantity.mk l' m' t' c' p' q' i' :=
      Quantity.mk (l-l') (scalar.sub_mass m m') (t-t') (c-c') (p-p') (q-q') (scalar.sub_intensity i i')
    end
  end

  /-
  We can multiple quantities as long as they are expressed with
  respect to the same measurement systems. Clearly they don't need
  to be in the same units, as we'd then be able to multiple, e.g.,
  quantities expressed in meters and in seconds, respectively.

  We note that we could build measurement system conversions in
  here. We choose not to do so, leaving designers to make such
  conversions explicit where needed.
  -/
  def mul 
    {ms : MeasurementSystem}
    {d1 d2 : Dimension} 
    (q1 : Quantity d1 ms) 
    (q2 : Quantity d2 ms) : Quantity (mul d1 d2) ms :=
  match q1 with 
    | Quantity.mk l m t c p q i :=
        match q2 with 
            | Quantity.mk l' m' t' c' p' q' i' :=
              Quantity.mk (l*l') (scalar.mul_mass m m') (t*t') (c*c') (p*p') (q*q') (scalar.mul_intensity i i')
        end
    end

  end quantity
