import .measurementSystem

open measurementSystem

/-
We express a physical quantity as a tuple of scalars, each
of a type consistent with its base dimension, relative to a
given (potentially derived) dimension and measurement system.
In this way, scalars are combined with units to yield quantities.
-/
structure PhysicalQuantity (d : PhysicalDimension) (m : MeasurementSystem) : Type :=
mk :: 
(length : scalar.length)
(mass : scalar.mass)
(time : scalar.time)
(current : scalar.current)
(temperature : scalar.temperature)
(quantity : scalar.quantity)
(intensity : scalar.intensity) 

/-
We can add quantities as long as they are in the same physical
dimensions and expressed with respect to the same measurement
systems. Proofs will be required that we aren't violating any
algebraic invariants. For example, we mustn't subtract a large
mass from a small mass to obtain a negative mass, because mass
(in the ordinary physics we formalize) can't be negative. 
-/
def PhysicalQuantityAdd 
    {d : PhysicalDimension} 
    {ms : MeasurementSystem} 
    (q1 q2 : PhysicalQuantity d ms) : 
    PhysicalQuantity d ms := 
  match q1 with 
    | PhysicalQuantity.mk l m t c p q i :=
        match q2 with 
            | PhysicalQuantity.mk l' m' t' c' p' q' i' :=
      PhysicalQuantity.mk (l+l') (scalar.add_mass m m') (t+t') (c+c') (p+p') (q+q') (scalar.add_intensity i i')
    end
  end

def PhysicalQuantitySubtract {d : PhysicalDimension} {ms : MeasurementSystem}  (q1 q2 : PhysicalQuantity d ms) : 
    PhysicalQuantity d ms := 
  match q1 with 
    | PhysicalQuantity.mk l m t c p q i :=
        match q2 with 
            | PhysicalQuantity.mk l' m' t' c' p' q' i' :=
      PhysicalQuantity.mk (l-l') (scalar.sub_mass m m') (t-t') (c-c') (p-p') (q-q') (scalar.sub_intensity i i')
    end
  end
