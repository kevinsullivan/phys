In this directory, we define the various spaces of physical quantities,
aka dimensions. We currently focus on classical versions of the following: 
- time
- geometry
- velocity

Original concept. Review how "on" it was, including where it was off.

- DSL defines term something like this: (Lit_Geom_Expr "world" 3 si_system ...)
- What are the semantics of this term? To what does the following evaluate?
**    eval(Lit_Geom_Expr "world" 3 si_system ...) ----> something in phys
- Intuition: It evaluates to a "space". Idea: Dimensions are spaces.
- A space (phys) in turn is a physical concept with an algebraic structure (affine space)
- For example, a 1D geometric space has the structure of an real affine 1 space. 
- Another intuition: Spaces (qua dimensions) can be multiplied
- For example, we can multiple 2 1-d geometric spaces to get a 2D space.
