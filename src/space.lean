import .dimension 
import ...math.affine.aff_coord_space


/-
DSL defines term something like this: (Lit_Geom_Expr "world" 3 si_system ...)

What are the semantics of this term? To what does the following evaluate?

    eval(Lit_Geom_Expr "world" 3 si_system ...) ----> something in phys

Intuition: It evaluates to a "space". Idea: Dimensions are spaces.

A space (phys) in turn is a physical concept with an algebraic structure (affine space)

For example, a 1D geometric space has the structure of an real affine 1 space. 

Another intuition: Spaces (qua dimensions) can be multiplied

For example, we can multiple 2 1-d geometric spaces to get a 2D space.
-/



-- a space is at least pair that combines 
-- a Dimension (7-tuple)
-- algebraic structure information
-- an indication of the physical phenomena being represented

-- separate notion of a measurement system on a space

namespace Space

open dimension

structure Space : Type 1 :=
mk ::
(name : string)
(dim : Dimension)
(algebra : Type)

def Geom3d : Space :=
⟨ "1dGeom", 1, _⟩ 

def Time : Space :=
⟨ "Time", 1, _⟩ 


end Space