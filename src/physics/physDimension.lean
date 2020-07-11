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

inductive phys_unit (d : physicalDimension) : Type
| std : phys_unit
| mk : ℝ → phys_unit

def meters : phys_unit physicalDimension.distance := phys_unit.std
def kilometers : phys_unit physicalDimension.distance := phys_unit.mk 0.001

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


structure Geometric3PointStruct : Type :=
    mk :: (sp : phys_space physicalDimension.distance) (pt : aff_pt ℝ 3) (B : affine_frame)

structure TimePointStruct : Type :=
    mk :: (sp : phys_space physicalDimension.time) (pt : aff_pt ℝ 1) (B : affine_frame)

structure Velocity3PointStruct : Type :=
    mk :: (sp : phys_space velocity) (pt : aff_pt ℝ 3) (B : affine_frame)

--expression.add (x : TimeVector y : GeometricVector)



structure Geometric3Vector : Type :=
    mk :: (sp : phys_space physicalDimension.distance) (vec : aff_vec ℝ 3) (B : affine_frame)



/-
def GeomAdd : GeometricVector → GeometricVector → GeometricVector
| (GeometricVector.mk a x b) (GeometricVector.mk a y b) := GeometricVector.mk a (x+y) b
| _ _ := sorry --should throw an error

instance : has_add GeometricVector := ⟨GeomAdd⟩

-/


structure TimeVector : Type :=
    mk :: (sp : phys_space physicalDimension.time) (vec : aff_vec ℝ 1) (B : affine_frame)




structure Velocity3Vector : Type :=
    mk :: (sp : phys_space velocity) (vec : aff_vec ℝ 3) (B : affine_frame)


/-
Norm Function:
takes in some 1-dimensional Time vector and returns its magnitude (i.e. first element in the list)
-/
def magnitude : TimeVector → ℝ
| _ := 0


/-
Example function for creating GeometricPoint from 3 reals and a physical space
-/
def Geometric3Point (p : phys_space physicalDimension.distance) (x y z : ℝ) : Geometric3PointStruct :=
    Geometric3PointStruct.mk p (aff_pt.mk [1,x,y,z] rfl rfl) p.std_frame

def TimePoint (p : phys_space physicalDimension.time) (t : ℝ) : TimePointStruct :=
    TimePointStruct.mk p (aff_pt.mk [1, t] rfl rfl) p.std_frame

def Velocity3Point (p : phys_space velocity) (x y z : ℝ) : Velocity3PointStruct :=
    Velocity3PointStruct.mk p (aff_pt.mk [1,x,y,z] rfl rfl) p.std_frame
--def example_point := GeometricPoint geom3 1 1 1
--def example_time := TimePoint time 10


def geom3 : phys_space physicalDimension.distance := phys_space.mk 3 std

def vel : phys_space velocity := phys_space.mk 3 std

def time : phys_space physicalDimension.time := phys_space.mk 1 std



def EuclideanGeometry (name : string) (n : nat): phys_space physicalDimension.distance :=
    phys_space.mk n std

def ClassicalTime (name : string) : phys_space physicalDimension.time :=
    phys_space.mk 1 std

def ClassicalVelocity (name : string) (n : nat) : phys_space velocity :=
    phys_space.mk n std

