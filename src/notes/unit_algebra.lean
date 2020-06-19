variable biblio_item : Type

inductive quantity : Type
| length : quantity
| mass : quantity
| time : quantity
| amount : quantity
| current : quantity
| temperature : quantity
| intensity : quantity
| mult : quantity → quantity → quantity
| div : quantity → quantity → quantity

inductive munit
| meter : munit
| kilogram : munit
| second : munit
| ampere : munit
| kelvin : munit
| candela : munit
| mole : munit
| mult : munit → munit → munit
| div : munit → munit → munit

open munit
open quantity

def quantity_munit: quantity → munit
| length := meter
| mass := quantity
| time := quantity
| amount := quantity
| current := quantity
| temperature := quantity
| intensity := quantity
| mult := quantity → quantity → quantity
| div := quantity → quantity → quantity


structure quant_desc := mk ::
(name : string)     -- e.g., "length"
(symbol : string)   -- e.g., "L"
(unit : munit) -- e.g., meter

def foo : quantity → quant_desc
| quantity.length := quant_desc.mk "Length" "L" (munit.meter)
| quantity.mass := quant_desc.mk "Mass" "K" (munit.kilogram)
| quantity.time := quant_desc.mk "Time" "T" (munit.second)
| quantity.amount := quant_desc.mk "Amount" "N" (munit.mole)
| quantity.current := quant_desc.mk "Current" "A" (munit.ampere)
| quantity.temperature := quant_desc.mk "Temperature" "K" (munit.kelvin)
| quantity.intensity := quant_desc.mk "Intensity" "J" (munit.candela)
| (quantity.mult q1 q2) := quant_desc.mk "BLIP" "B" (munit.mult q1 q2 )
| (quantity.div q1 q2) := quant_desc.mk "BLIP" "B" (munit.div q1 q2 )

structure munit_desc := mk ::
(quant : quantity)   -- e.g., length
(name : string)      -- e.g., "meter"
(symbol : string)    -- e.g., "m"
(defn : string)      /- e.g.,  "The metre is the length of the 
                        path travelled by light in vacuum during 
                        a time interval of 1 / 299792458 of a 
                        \second."   -/
(std : biblio_item)         -- e.g., "17th CGPM (1983, Resolution 1, CR, 97)"


