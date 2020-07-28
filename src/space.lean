import .dimension .basicDimensionAlgebras

-- eval(Lit_Geom_Expr "world" 3)

-- a space is at least pair that combines 
-- a PhysicalDimension (7-tuple)
-- algebraic structure information
-- an indication of the physical phenomena being represented

-- separate notion of a measurement system on a space

namespace physicalSpace


structure PhysicalSpace : Type 1 :=
mk ::
(name : string)
(dim : PhysicalDimension)
(algebra : Type)

open basicDimension

def Geom1D : PhysicalSpace :=
⟨"geom1d", length, algebraOf basicDimension.BasicDimension.length⟩

end physicalSpace