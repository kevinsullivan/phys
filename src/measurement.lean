import .dimension
import .unit
import .scalar

namespace measurementSystem

structure MeasurementSystem : Type :=
mk ::
(length : unit.length)
(mass : unit.mass)
(time : unit.time)
(current : unit.current)
(temperature : unit.temperature)
(quantity : unit.quantity)
(intensity : unit.intensity) 

end measurementSystem

open measurementSystem unit

def si_measurement_system : MeasurementSystem :=
MeasurementSystem.mk 
length.meter
mass.kilogram
time.second
current.ampere
temperature.kelvin
quantity.mole
intensity.candela

-- double check this and fix if necessary
def imperial_measurement_system : MeasurementSystem :=
MeasurementSystem.mk 
length.foot
mass.pound
time.second
current.ampere
temperature.fahrenheit
quantity.mole
intensity.candela
