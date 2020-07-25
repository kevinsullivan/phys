import .dimension
import .unit
import .scalar

namespace measurementSystem

structure MeasurementSystem : Type :=
(length : unit.length)
(mass : unit.mass)
(time : unit.time)
(current : unit.current)
(temperature : unit.temperature)
(quantity : unit.quantity)
(intensity : unit.intensity) 

end measurementSystem