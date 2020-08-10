import .dimension 
import ...math.affine.real_affine_space


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





structure Space :=
mk ::
(name : string)
(dim : dimension.Dimension)
(algebra : Algebra)

namespace Space

open dimension dimension.BasicDimension

noncomputable def Geom1d : Space :=
⟨"1dGeom", length, Algebra.affine_space (to_affine 1)⟩ -- "Dimension" doesn't have "1," wrong type of dimension

noncomputable def Geom3d : Space :=
⟨"3dGeom", length * length * length, Algebra.affine_space (to_affine 3)⟩ -- "Dimension" doesn't have "1," wrong type of dimension

/- 
Would be nice to have the ability to reject inconsistent arguments, as in the following example.
noncomputable def bad : Space := ⟨"inconsistent", length, Algebra.affine_space (to_affine 5)⟩
-/

noncomputable def Time : Space :=
⟨"Time", time, Algebra.affine_space (to_affine 1)⟩ 


end Space