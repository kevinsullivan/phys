import .dimensions
import .unit

namespace measurementSystem

/-
We define a measurement system to be a 7-tuple
of units: one for length, one for mass, etc.
-/
structure MeasurementSystem : Type :=
mk ::
(length : unit.length)
(mass : unit.mass)
(time : unit.time)
(current : unit.current)
(temperature : unit.temperature)
(quantity : unit.quantity)
(intensity : unit.intensity) 

-- Examples

def si_measurement_system : MeasurementSystem :=
MeasurementSystem.mk 
unit.length.meter
unit.mass.kilogram
unit.time.second
unit.current.ampere
unit.temperature.kelvin
unit.quantity.mole
unit.intensity.candela

-- double check this and fix if necessary
def imperial_measurement_system : MeasurementSystem :=
MeasurementSystem.mk 
unit.length.foot
unit.mass.pound
unit.time.second
unit.current.ampere
unit.temperature.fahrenheit
unit.quantity.mole
unit.intensity.candela

def si_nanoseconds : MeasurementSystem :=
{
  time := unit.time.nanosecond
  ..si_measurement_system
}
/-
inductive length : Type 
| meter
| centimeter
| foot
inductive mass : Type
| kilogram 
| pound
inductive time : Type
| second
| millisecond
| nanosecond
inductive current : Type
| ampere
inductive temperature : Type
| kelvin
| fahrenheit
inductive quantity : Type
| mole
inductive intensity : Type
| candela 
-/

instance leneq 
  {l1 : unit.length}
  {l2 : unit.length}
  : decidable (l1=l2)
  := 
  begin
    cases l1,
    { 
      cases l2,
      {exact decidable.is_true rfl},
      {exact decidable.is_false (by contradiction)},
      {exact decidable.is_false (by contradiction)}
    },
    {
      cases l2,
      {exact decidable.is_false (by contradiction)},
      {exact decidable.is_true rfl},
      {exact decidable.is_false (by contradiction)}
    },
    {
      cases l2,
      {exact decidable.is_false (by contradiction)},
      {exact decidable.is_false (by contradiction)},
      {exact decidable.is_true rfl},
    },
  end

instance mass_eq
  {l1 : unit.mass}
  {l2 : unit.mass}
  : decidable (l1=l2)
  := 
  begin
    cases l1,
    { 
      cases l2,
      {exact decidable.is_true rfl},
      {exact decidable.is_false (by contradiction)}
    },
    {
      cases l2,
      {exact decidable.is_false (by contradiction)},
      {exact decidable.is_true rfl}
    }
  end

instance time_eq
  {l1 : unit.time}
  {l2 : unit.time}
  : decidable (l1=l2)
  := 
  begin
    cases l1,
    { 
      cases l2,
      {exact decidable.is_true rfl},
      {exact decidable.is_false (by contradiction)},
      {exact decidable.is_false (by contradiction)}
    },
    {
      cases l2,
      {exact decidable.is_false (by contradiction)},
      {exact decidable.is_true rfl},
      {exact decidable.is_false (by contradiction)}
    },
    {
      cases l2,
      {exact decidable.is_false (by contradiction)},
      {exact decidable.is_false (by contradiction)},
      {exact decidable.is_true rfl},
    },
  end

instance cur_eq
  {l1 : unit.current}
  {l2 : unit.current}
  : decidable (l1=l2)
  := 
  begin
    cases l1,
    { 
      cases l2,
      {exact decidable.is_true rfl},
    },
  end

instance temp_eq
  {l1 : unit.temperature}
  {l2 : unit.temperature}
  : decidable (l1=l2)
  := begin
    
    cases l1,
    { 
      cases l2,
      {exact decidable.is_true rfl},
      {exact decidable.is_false (by contradiction)}
    },
    {
      cases l2,
      {exact decidable.is_false (by contradiction)},
      {exact decidable.is_true rfl}
    }
  end

instance q_eq
  {l1 : unit.quantity}
  {l2 : unit.quantity}
  : decidable (l1=l2)
  := 
  begin
    cases l1,
    { 
      cases l2,
      {exact decidable.is_true rfl},
    },
  end

instance i_eq
  {l1 : unit.intensity}
  {l2 : unit.intensity}
  : decidable (l1=l2)
  := 
  begin
    cases l1,
    { 
      cases l2,
      {exact decidable.is_true rfl},
    },
  end


/-
(length : unit.length)
(mass : unit.mass)
(time : unit.time)
(current : unit.current)
(temperature : unit.temperature)
(quantity : unit.quantity)
(intensity : unit.intensity) 

-/
instance meq 
  {m1 : MeasurementSystem}
  {m2 : MeasurementSystem}
  : decidable (m1=m2)
  :=
  if leneq:m1.length = m2.length then
    if meq : m1.mass=m2.mass then
      if teq : m1.time = m2.time then
        if ceq : m1.current = m2.current then
          if tmpeq : m1.temperature = m2.temperature then
            if qeq : m1.quantity = m2.quantity then
              if ieq : m1.intensity = m2.intensity then
                begin
                  induction m1, induction m2,
                  simp *,
                  exact decidable.is_true (by cc)
                end
              else begin
              induction m1, induction m2,
              simp *,
              exact decidable.is_false (by contradiction)
            end
            else begin
              induction m1, induction m2,
              simp *,
              exact decidable.is_false (by contradiction)
            end
          else begin
            induction m1, induction m2,
            simp *,
            exact decidable.is_false (by contradiction)
          end
        else begin
            induction m1, induction m2,
            simp *,
            exact decidable.is_false (by contradiction)
          end
      else begin
            induction m1, induction m2,
            simp *,
            exact decidable.is_false (by contradiction)
          end
    else begin
        induction m1, induction m2,
        simp *,
        exact decidable.is_false (by contradiction)
      end
  else begin
      induction m1, induction m2,
      simp *,
      exact decidable.is_false (by contradiction)
    end


end measurementSystem