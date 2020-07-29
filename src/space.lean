import .dimension 


/-
DSL defines term something like this: (Lit_Geom_Expr "world" 3)

What are the semantics of this term? To what does the following evaluate?

    eval(Lit_Geom_Expr "world" 3)

Intuition: It evaluates to a "space". Idea: Dimensions are spaces.

A space in turn is a physical concept with an algebraic structure.with

For example, a 1D geometric space has the structure of an real affine 1 space. 

Another intuition: Spaces (qua dimensions) can be multiplied.with

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


def Geom1D : Space :=
-- Space.mk ...
⟨"geom1d", length, algebraOf BasicDimension.length⟩

def Geom2D : Space :=
⟨ "geom2d", area, 

end Space