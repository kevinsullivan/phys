import .physlib

-- in meters
def twoMeters : 
    PhysicalQuantity 
        length 
        (MeasurementSystem.mk lengthUnit.meter massUnit.kilogram timeUnit.second) := 
    PhysicalQuantity.mk 2 0 0

-- in centimeters
def twoMeters' : 
    PhysicalQuantity 
        length 
        (MeasurementSystem.mk lengthUnit.centimeter massUnit.kilogram timeUnit.second) := 
    PhysicalQuantity.mk 200 0 0

-- in meters
def threeMeters : 
    PhysicalQuantity 
        length 
        (MeasurementSystem.mk lengthUnit.meter massUnit.kilogram timeUnit.second) := 
    PhysicalQuantity.mk 3 0 0

-- Should work
def fiveMeters := 
    PhysicalQuantityAdd
        twoMeters
        threeMeters

-- should not work
def fiveMeters' := 
    PhysicalQuantityAdd
        twoMeters'
        threeMeters
