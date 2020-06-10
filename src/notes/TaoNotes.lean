/-
"The metre is the length of the path travelled by light in vacuum during a time interval of 1 / 299792458 of a second."
17th CGPM (1983, Resolution 1, CR, 97)
-/


/-
"A related limitation, which is not always made explicit in physics texts, is that transcendental mathematical functions such as {\sin} or {\exp} should only be applied to arguments that are dimensionless; thus, for instance, if {v} is a speed, then {\hbox{arctanh}(v)} is not physically meaningful, but {\hbox{arctanh}(v/c)} is (this particular quantity is known as the rapidity associated to this speed)." --T Tao
-/

/-
A system of units gives a coordinate system on some space of quantities we’re trying to measure. --https://golem.ph.utexas.edu/category/2006/09/dimensional_analysis_and_coord.html
-/

/-
 advantageous to retain the limitation to only perform dimensionally consistent operations. One is that of error correction ... [and]  one can often identify the form of a physical law before one has fully derived it." --T Tao

 "
 The use of units and dimensional analysis has certainly been proven to be very effective tools in physics. But one can pose the question of whether it has a properly grounded mathematical foundation, in order to settle any lingering unease about using such tools in physics, and also in order to rigorously develop such tools for purely mathematical purposes (such as analysing identities and inequalities in such fields of mathematics as harmonic analysis or partial differential equations).    
 " -- Tao

 Ways of formalizing, e.g., length
 1. equivalence class of congruent line seqments
 2. parametric model using numbers (scalar, vector, matrix... "depending on base dimensional parameters (such as units of length, mass, and time, or a coordinate system for space or spacetime), transforming according to some representation of a structure group that encodes the range of these parameters"
 3. “abstract”, “coordinate-free”, model in which dimensionful objects now live in an abstract mathematical space (e.g. an abstract vector space), in which only a subset of the operations available to general-purpose number systems such as {{\bf R}} or {{\bf R}^3} are available, namely those operations which are “dimensionally consistent” or invariant (or more precisely, equivariant) with respect to the action of the underlying structure group"


Coordinate-free
     "explicit use of coordinates is avoided whenever possible, in order to keep the mathematical framework as close as possible to the underlying geometry or physics of the situation, and also in order to allow for easy generalisation to other contexts of mathematical interest in which coordinate systems become inconvenient to use (as we already saw in the case of general relativity on a topologically non-trivial situations, in which global coordinate systems had to be replaced by local ones), or completely unavailable (e.g. in studying more general topological spaces than manifolds)"

    one models objects as elements of abstract structures in which only the bare minimum of operations (namely, the “geometric”, “physical”, or “dimensionally consistent” operations) are permitted, viewing any excess structure (such as coordinates) as superfluous ontological baggage to be discarded if possible.

    One can add or remove structures to this vector space {V}, depending on the situation. For instance, if one wants to remove the preferred origin from the vector space, one can work instead with the slightly weaker structure of an affine space, in which no preferred origin is present. In order to recover the operations of Euclidean geometry, one can then place a Euclidean metric on the affine space; in some situations, one may also wish to add an orientation or a Haar measure to the list of structures. By adding or deleting such structures, one changes the group of isomorphisms of the space (or the groupoid of isomorphisms between different spaces in the same category), which serve as the analogue of the structure group in the parametric viewpoint

    It is possible to convert the abstract framework into the parametric one by making some non-canonical choices of a reference unit system.

    For instance, in the abstract {M,L,T} dimensional system, after selecting a reference system of units {M_0 \in V^M}, {L_0 \in V^L}, {T_0 \in V^T}, one can then identify {{\bf R}^{M^a L^b T^c}} with {{\bf R}} by identifying {M_0^a L_0^b T_0^c} with {1}, so that any {x \in {\bf R}^{M^a L^b T^c}} gets identified with some real number {\tilde x \in {\bf R}}. For any {M,L,T \in {\bf R}^+}, one can then replace the units {M_0,L_0,T_0} with rescaled units {MM_0, LL_0, TT_0}, which changes the identification of {{\bf R}^{M^a L^b T^c}} with {{\bf R}}, so that an element {x \in {\bf R}^{M^aL^bT^c}} is now identified with the real number

\displaystyle  x_{M,L,T} := \tilde x M^{-a} L^{-b} T^{-c}

 Grassman-Cayley algebra "It also "has a number of applications in robotics, particularly for the kinematical analysis of manipulators." --Wikipedia
 -/

 /-
 Plank units
 -/

 /-
 dimensional functions
 -/

 /-
dimensionalities of integrals and derivatives of dimensionful functions
 -/

 /-
 But, when dealing with vector quantities, one can perform a more powerful form of dimensional analysis in which the dimensional parameters lie in a more general group [than R](which we call the structure group of the dimensionful universe being analysed).... Indeed, one can view units as being simply the one-dimensional special case of coordinate systems. 
 -/

 /-
 A linear functional taking vectors to scalars is also representable as a row vector but it transforms differently and so isn't compatible ...

 We will call a dimensionful vector-valued quantity {w=w_L} of the form (7) a covector or type {(0,1)} tensor. Thus we see that while polar vectors and covectors can both be expressed (for each choice of {L}) as an element of {{\bf R}^3}, they transform differently with respect to coordinate change (coming from the two different right-actions of the structure group {GL_3({\bf R})} on {{\bf R}^3}
 -/

 /-
 One can also assign dimensions to higher rank tensors, such as matrices, {k}-vectors, or {k}-forms; the notation here becomes rather complicated, but is perhaps best described using abstract index notation. The dimensional consistency of equations involving such tensors then becomes the requirement in abstract index notation that the subscripts and superscripts on the left-hand side of a tensor equation must match those on the right-hand side, after “canceling” any index that appears as both a subscript and a superscript on one side. 
 -/

 /-
 Another type of dimensional analysis arises when one takes the structure group to be a Euclidean group such as {E(2)} or {E(3)}, rather than {GL_3({\bf R})} or (some power of) {{\bf R}^+}. 
 
 we can then define a position vector to be a dimensionful quantity {p = p_L} taking values in {{\bf R}^2} that transforms according to the law

 \displaystyle  p_L = L^{-1} \tilde p \ \ \ \ \ (8)

for some {\tilde p \in {\bf R}^2}. If, instead of considering the position of a single point {p} in the Euclidean plane, one considers the displacement {v = q-p} between two points {p,q} in that plane, a similar line of reasoning leads to the concept of a displacement vector, which would be a dimensionful quantity {v = v_L} taking values in {{\bf R}^2} that transforms according to the law

 \displaystyle  p_L = \dot L^{-1} \tilde p \ \ \ \ \ (9)
 
  in addition to the position/displacement vector distinction,one can also distinguish polar vectors from axial vectors, leading in particular to the conclusion that the cross product of two polar vectors is an axial vector rather than a polar vector
  
  In a similar vein, one can dimensionally analyse physical quantities in spacetime using the Poincaré group {SO(3,1) \ltimes {\bf R}^{3+1}} as the structure group

  if one enlarges the structure group to the diffeomorphism group of spacetime, one recovers the principle of general relativity (though an important caveat here is that if the spacetime is topologically non-trivial, one needs to work with local coordinate charts (or atlases of such charts, and the structure group needs to be relaxed to a looser concept, such as that of a pseudogroup) rather than a single global coordinate chart, which greatly complicates the parametrisation space

  In the preceding examples, the structure groups were all examples of continuous Lie groups: {({\bf R}^+)^3}, {GL_3({\bf R})}, {E(2)}, etc.. But even a discrete structure group can lead to a non-trivial capability for dimensional analysis. Perhaps the most familiar example is the use of the structure group {\{-1,+1\}} as the range of the dimensional parameter {L}, leading to two types of scalars: symmetric scalars {x = x_L}, which are dimensionless (so {x_{-1}=x_{+1}}), and antisymmetric scalars {x = x_L}, which transform according to the law {x_{-1} = -x_{+1}}. 
  -/