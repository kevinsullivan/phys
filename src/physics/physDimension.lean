import data.real.basic
import ..affine.aff_coord_space

noncomputable theory

/-
physicalDimension
time and distance are base types
can create derived types with the inverse and multiplication operations
-/
inductive physicalDimension : Type
| time
| distance
| inverse : (physicalDimension → physicalDimension)
| multiply : (physicalDimension → physicalDimension → physicalDimension)

--define velocity to be physical dimension of (distance / time)
def velocity : physicalDimension :=
    physicalDimension.multiply physicalDimension.distance (physicalDimension.inverse physicalDimension.time)

--take affine_frame to be a type 
--since we want some notion of a frame attached to any points/vectors we define
axiom affine_frame : Type



/-
phys_space

can construct any physical space for a given dimension and physical dimension
i.e. 3D Geometric space (distance as its physical dimension)
    1D time space (time as its physical dimension)
-/
structure phys_space (d : physicalDimension) : Type :=
    mk ::  (dimension : ℕ) (std_frame : affine_frame)

--take std to be some affine frame
axiom std : affine_frame


/-
for line: 
@@EuclideanGeometry geom3d<3,"worldGeometry">;  

we create a physical space for a 3d geometric space (equipped with a std frame)
-/


def geom3 : phys_space physicalDimension.distance := phys_space.mk 3 std


/-
for line: 
 @@ClassicalTime time<"worldTime">;   

we create a physical space for a 1d time space (equipped with a std frame)
-/
def time : phys_space physicalDimension.time:= phys_space.mk 1 std


/-
for line: 
@@ClassicalVelocity vel<"worldVelocities">  

we create a physical space for a 3d velocity space (equipped with a std frame)
-/
def vel : phys_space velocity := phys_space.mk 3 std


/-
We now create a distinction between Points and Vectors, which builds upon
the existing abstraction of affine points and affine vectors.

For example: 

GeometricPoint takes in some physical space, an affine point, and an affine frame
GeometricVector takes in some physical space, an affine vector, and an affine frame
-/
structure GeometricPointStruct : Type :=
    mk :: (sp : phys_space physicalDimension.distance) (pt : aff_pt ℝ 3) (B : affine_frame)

structure TimePointStruct : Type :=
    mk :: (sp : phys_space physicalDimension.time) (pt : aff_pt ℝ 1) (B : affine_frame)



structure GeometricVector : Type :=
    mk :: (sp : phys_space physicalDimension.distance) (vec : aff_vec ℝ 3) (B : affine_frame)

structure TimeVector : Type :=
    mk :: (sp : phys_space physicalDimension.time) (vec : aff_vec ℝ 1) (B : affine_frame)




structure VelocityVector : Type :=
    mk :: (sp : phys_space velocity) (vec : aff_vec ℝ 3) (B : affine_frame)


/-
Norm Function:
takes in some 1-dimensional Time vector and returns its magnitude (i.e. first element in the list)
-/
def magnitude : TimeVector → ℝ
| _ := 0

/-
match vec with
                                | (aff_vec.mk l pf1 pf2) := 
                                    match l with 
                                    | (list.cons x t) := x
                                    | (list.nil) := 0
                                    end
                                end
-/

/-
Example function for creating GeometricPoint from 3 reals and a physical space
-/
def GeometricPoint (p : phys_space physicalDimension.distance) (x y z : ℝ) : GeometricPointStruct :=
    GeometricPointStruct.mk p (aff_pt.mk [1,x,y,z] rfl rfl) p.std_frame

def TimePoint (p : phys_space physicalDimension.time) (t : ℝ) : TimePointStruct :=
    TimePointStruct.mk p (aff_pt.mk [1, t] rfl rfl) p.std_frame

def example_point := GeometricPoint geom3 1 1 1
def example_time := TimePoint time 10




def GeometricSpace (name : string) (n : nat): phys_space physicalDimension.distance :=
    phys_space.mk n std

def TimeSpace (name : string) : phys_space physicalDimension.time :=
    phys_space.mk 1 std

def VelocitySpace (name : string) (n : nat) : phys_space velocity :=
    phys_space.mk n std




def geom3' := GeometricSpace "geom3" 3

def time' := TimeSpace "time"

def vel' := VelocitySpace "vel" 3



/-
for line: 
    @@GeometricPoint geom_start_(geom3, [0.0,0.0,0.0], geom3.stdFrame)
-/
def start_pt : GeometricPoint :=
    GeometricPoint.mk geom3 (aff_pt.mk [1,0,0,0] rfl rfl) geom3.std_frame

/-
for line: 
    @@GeometricPoint geom_end_(geom3, [10.0,10.0,10.0], geom3.stdFrame)
-/
def end_pt : GeometricPoint :=
    GeometricPoint.mk geom3 (aff_pt.mk [1,10,10,10] rfl rfl) geom3.std_frame

/-
for line: 
    @@TimePoint time_then_(time, [-10.0], time.stdFrame);
-/
def start_time : TimePoint :=
    TimePoint.mk time (aff_pt.mk [1,0] rfl rfl) time.std_frame

/-
for line: 
    @@TimePoint time_now_(time, [0.0], time.stdFrame);
-/
def end_time : TimePoint :=
    TimePoint.mk time (aff_pt.mk [1,10] rfl rfl) time.std_frame

/-
for line: 
    Vector1 time_displacement = time_now - time_then;

-/
def duration : TimeVector :=
    TimeVector.mk time (end_time - start_time) time.std_frame

/-
for line: 
    @@GeometricPoint geom_start_(geom3, [0.0,0.0,0.0], geom3.stdFrame)
-/
def displacement : GeometricVector :=
    GeometricVector.mk geom3 (end_pt - start_pt) geom3.std_frame

/-
for line: 
    @@VelocityVector(vel, [<computed>], <coordinate-free>)
-/
def vel_vector : VelocityVector :=
    VelocityVector.mk vel (displacement.vec * ( 1 / (magnitude duration))) vel.std_frame






