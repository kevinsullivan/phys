import .affine_space
import data.real.basic


-- Test tuple type
def oneTuple : tuple 1 ℝ := ⟨ [2], rfl ⟩ 
def aTuple : tuple 3 ℝ := ⟨[2,1,-1], rfl⟩ 
def aTuple' : tuple 1 ℝ := ⟨[2], rfl⟩ 
def aReal3ZeroTuple : tuple 3 ℝ := 
    subtype.mk [0,0,0] rfl
def aReal4ZeroTuple : tuple 4 ℝ := 
    ⟨ [0,0,0,0], rfl⟩ 


-- Test space type
def time : space 1 ℝ :=      -- non-computable
    space.mk 1 ℝ "time" 
def geometry : space 3 ℝ :=  -- non-computable
    space.mk 3 ℝ "geometry"
#check time
#check space 1 real


/-
Test affine point, vector, frame types.
Time as an affine space.
-/ 

-- standard frame, interpret as origin t = 0, unit = 1 second
def std_time_frame : 
    affine_frame time := 
    affine_frame.mk_std time

-- standard origin
def t_eq_zero := affine_point.mk_std time

-- standard unit vector (interpret as 1 second)
def one_second := affine_vector.mk_std time

-- time with coordinates 60, i.e., t = 1 min, wrt to std
def t_eq_one_min_std := affine_point.mk std_time_frame ⟨ [60], rfl ⟩ 

-- new vector with length 60, i.e., one min, wrt std frame
def one_min_std := affine_vector.mk std_time_frame ⟨ [60], rfl ⟩ 

-- new frame, origin at 1 min, unit length 1 min, wrt std
def new_frame := affine_frame.mk t_eq_one_min_std [one_min_std] 

-- New point at t = 60 min wrt new frame, t = 61 min wrt std 
def new_time := affine_point.mk new_frame ⟨ [60], rfl ⟩ 

/-
Test affine point, vector, frame types.
3D geometry as an affine space.
-/ 

-- std frame
def geomFrame1 : affine_frame geometry :=
    affine_frame.mk_std geometry

-- std origin
def geomPoint1 := affine_point.mk_std geometry

-- std vector [one of them, anyway, need to enhance type]
def geomVector1 := affine_vector.mk_std geometry

-- new point at [1,1,1] wrt std frame
def geomPoint2 := affine_point.mk geomFrame1 ⟨ [1,1,1], rfl ⟩ 

-- new vector at [-1,1,2] wrt std frame
def geomVector2 := affine_vector.mk geomFrame1 ⟨ [-1,1,2], rfl ⟩ 

-- new frame with new basis (need lin. indep. constraint)
def geomFrame2 := affine_frame.mk 
                    geomPoint2 
                    [geomVector1, geomVector2, geomVector1]


-- testing
#eval mk_indicator_tuple 6 ℚ 2
#print vector
#print list.map
