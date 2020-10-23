/-
The dimensions.lean file implements the concept of physical dimensions
as we've understood it from, e.g., the SI system of dimensions and units.
Our insight is that that approach leaves too much structure behind. What
we do here, instead, it implement the concept of physical spaces. So, for
example, the vector space concept of (directed) lengths is replaced by the
affine space concept of a torsor of geometric points over a vector space 
of displacements. We will then define an algebra of *spaces* rather than
an algebra of dimensions, and that, I think, it really what we need in
order to implement a richly library of abstractions for doing strongly
and statically typed physics. --Sullivan Oct 20/2020
-/

inductive space : Type
| geometry          -- real affine 3
| time              -- real affine 1
| mass              -- real quasi-affine monus 1 (negative mass speculative)
| temperature       -- real quasi-affine monus 1 (negative mass speculative)
| quantity          -- nat quasi-affine monus 1
-- intensity        -- 
-- current

