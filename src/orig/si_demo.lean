import .physical

-- DEMO
def time_1 := mk_time 50
def time_2 := mk_time 2000
def duration_1 := point_point_sub time_2 time_1
def location_1 := mk_loc 50
def oops := point_point_sub location_1  time_1
-- def time_3 := time_1 + time_2    -- no such op
--def time_3 := point_vector_add (mk_time 100) duration_1
--def type_error := point_point_sub time_2 location_1 


def new_time_frame := frame.mk time_2 std_time_vector
def new_point := point.mk new_time_frame 77

#reduce is_reduced_point time_2
#reduce is_reduced_point new_point
#reduce std_time_point
#reduce time_2
#reduce new_point
#reduce coord_of_point new_point
#reduce reduce_point std_time_point
#reduce step_reduce_point new_point
#reduce is_reduced_point std_loc_point
#reduce is_reduced_point (step_reduce_point new_point)
#eval reduce_point new_point
#eval is_reduced_point (reduce_point new_point)

/- Future Work -/

/-
Prove to Lean that the recursions are well-founded

--see https://github.com/EdAyers/mathlib/blob/rb/docs/extras/well_founded_recursion.md

-/

/-
We should allow for the instantiation of an arbitrary 
point in a given given space. To distinguish different 
arbitrary points from each other, assign different ids. 
See Voldemort's theorem. TBD: How to handle spaces with 
distinguished origins?
-/


/-
def height_frame: ∀ { s : space }, frame s → ℕ
| s frame.mk_std := 0
| s (frame.mk point.mk_std c) := 1
| s (frame.mk (point.mk frame.mk_std c) fv) := 1 
| s (frame.mk (point.mk f c) fv) := 1 + height_frame f
-/


