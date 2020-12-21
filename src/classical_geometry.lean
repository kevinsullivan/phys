import 
    .....math.affine.affine_coordinate_framed_space_lib
    .....math.affine.affine_coordinate_transform
import ..metrology.dimensions 
import ..metrology.measurement
import data.real.basic

noncomputable theory
--open real_lib
open measurementSystem
open aff_fr
open aff_lib

structure euclideanGeometry3 : Type :=
mk :: 
    (sp : aff_lib.affine_coord_space.standard_space ℝ 3) 
    (id : ℕ) -- id serves as unique ID for a given geometric space


attribute [reducible]
def euclideanGeometry3.build (id : ℕ) : euclideanGeometry3 :=
    ⟨aff_lib.affine_coord_space.mk_with_standard ℝ 3, id⟩

noncomputable def euclideanGeometry3Algebra : euclideanGeometry3 →  
     aff_lib.affine_coord_space.standard_space ℝ 3
| (euclideanGeometry3.mk sp n) := sp

structure euclideanGeometry3Scalar :=
mk ::
    (sp : euclideanGeometry3)
    (val : ℝ)

attribute [reducible]
def euclideanGeometry3Scalar.build
    (sp : euclideanGeometry3)
    (val : vector ℝ 1) := 
    euclideanGeometry3Scalar.mk sp (val.nth 1)



attribute [reducible]
def euclideanGeometry3ScalarAlgebra 
    (s : euclideanGeometry3Scalar)
    := 
    s.val

structure euclideanGeometry3Vector :=
mk ::
    (sp : euclideanGeometry3)
    (coords : vector ℝ 3)

attribute [reducible]
def euclideanGeometry3Vector.build
    (sp : euclideanGeometry3)
    (coords : vector ℝ 3) :=
    euclideanGeometry3Vector.mk
        sp 
        --⟨[coord], by refl⟩
        coords


attribute [reducible]
def euclideanGeometry3VectorAlgebra 
    (v : euclideanGeometry3Vector)
    := 
        (aff_lib.affine_coord_space.mk_coord_vec
        (euclideanGeometry3Algebra v.sp) 
        v.coords)


structure euclideanGeometry3Point :=
mk ::
    (sp : euclideanGeometry3)
    (coords : vector ℝ 3)

attribute [reducible]
def euclideanGeometry3Point.build
    (sp : euclideanGeometry3)
    (coords : vector ℝ 3) :=
    euclideanGeometry3Point.mk
        sp 
        --⟨[coord], by refl⟩
        coords

attribute [reducible]
def euclideanGeometry3PointAlgebra 
    (v : euclideanGeometry3Point)
    := 
        (aff_lib.affine_coord_space.mk_coord_point
        (euclideanGeometry3Algebra v.sp) 
        v.coords)



abbreviation euclideanGeometry3Basis :=
    (fin 3) → euclideanGeometry3Vector

inductive euclideanGeometry3Frame : Type
| std 
    (sp : euclideanGeometry3)
    : euclideanGeometry3Frame
| derived 
    (sp : euclideanGeometry3) --ALERT : WEAK TYPING
    (fr : euclideanGeometry3Frame) --ALERT : WEAK TYPING
    (origin : euclideanGeometry3Point)
    (basis : euclideanGeometry3Basis)
    (m : MeasurementSystem)
    : euclideanGeometry3Frame
| interpret
    (fr : euclideanGeometry3Frame)
    (m : MeasurementSystem)

attribute [reducible]
def euclideanGeometry3Frame.space : euclideanGeometry3Frame → euclideanGeometry3
| (euclideanGeometry3Frame.std sp) := sp
| (euclideanGeometry3Frame.derived s f o b m) :=  s
| (euclideanGeometry3Frame.interpret f m) := euclideanGeometry3Frame.space f

attribute [reducible]
def euclideanGeometry3Basis.build : euclideanGeometry3Vector → euclideanGeometry3Vector → euclideanGeometry3Vector → euclideanGeometry3Basis
| v1 v2 v3 := λi, if i = 1 then v1 else (if i = 2 then v2 else v3)

attribute [reducible]
def euclideanGeometry3Frame.build_derived
   : euclideanGeometry3Frame → euclideanGeometry3Point → euclideanGeometry3Basis → MeasurementSystem → euclideanGeometry3Frame
| (euclideanGeometry3Frame.std sp) p v m := euclideanGeometry3Frame.derived sp (euclideanGeometry3Frame.std sp) p v m
| (euclideanGeometry3Frame.derived s f o b m) p v ms :=  euclideanGeometry3Frame.derived s (euclideanGeometry3Frame.derived s f o b m) p v ms
| (euclideanGeometry3Frame.interpret f m) p v ms :=  euclideanGeometry3Frame.derived (euclideanGeometry3Frame.space f) (euclideanGeometry3Frame.interpret f m) p v ms

attribute [reducible]
def euclideanGeometry3Frame.build_derived_from_coords
    : euclideanGeometry3Frame → vector ℝ 3 → vector ℝ 3 → vector ℝ 3 → vector ℝ 3 → 
        MeasurementSystem → euclideanGeometry3Frame
| f p v1 v2 v3 m := 
    let s := euclideanGeometry3Frame.space f in
    (euclideanGeometry3Frame.build_derived f (euclideanGeometry3Point.build s p) 
        (euclideanGeometry3Basis.build (euclideanGeometry3Vector.build s v1) 
                                        (euclideanGeometry3Vector.build s v1) 
                                        (euclideanGeometry3Vector.build s v1)) m)


attribute [reducible]
noncomputable def euclideanGeometry3FrameAlgebra :
    euclideanGeometry3Frame → aff_fr.affine_coord_frame ℝ 3
| (euclideanGeometry3Frame.std sp) := 
    aff_lib.affine_coord_space.frame 
        (euclideanGeometry3Algebra sp)
| (euclideanGeometry3Frame.derived s f o b m) :=
    let base_fr := (euclideanGeometry3FrameAlgebra f) in
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame base_fr in
                aff_lib.affine_coord_space.mk_frame
                    base_sp
                    (aff_lib.affine_coord_space.mk_point base_sp o.coords)
                    (aff_lib.affine_coord_space.mk_basis base_sp 
                      ⟨[aff_lib.affine_coord_space.mk_vec base_sp ((b 1)).coords,
                      aff_lib.affine_coord_space.mk_vec base_sp ((b 2)).coords,
                      aff_lib.affine_coord_space.mk_vec base_sp ((b 3)).coords], by refl⟩)
        base_fr 
| (euclideanGeometry3Frame.interpret f m) := euclideanGeometry3FrameAlgebra f

attribute [reducible]
def euclideanGeometry3.stdFrame (sp : euclideanGeometry3)
    := euclideanGeometry3Frame.std sp


structure euclideanGeometry3CoordinateVector
    extends euclideanGeometry3Vector :=
mk ::
    (frame : euclideanGeometry3Frame) 

attribute [reducible]
def euclideanGeometry3CoordinateVector.build
    (sp : euclideanGeometry3)
    (fr : euclideanGeometry3Frame)
    (coords : vector ℝ 3) :
    euclideanGeometry3CoordinateVector :=
    {
        frame := fr,
        ..(euclideanGeometry3Vector.build sp coords)
    }

attribute [reducible]
def euclideanGeometry3CoordinateVector.fromalgebra
    {f : affine_coord_frame ℝ 3}
    (sp : euclideanGeometry3)
    (fr : euclideanGeometry3Frame)
    (vec : aff_coord_vec ℝ 3 f)
    --(vec : aff_coord_vec ℝ 1 (euclideanGeometry3FrameAlgebra fr))
    : euclideanGeometry3CoordinateVector
    := 
    euclideanGeometry3CoordinateVector.build sp fr (affine_coord_vec.get_coords vec)

attribute [reducible]
def euclideanGeometry3CoordinateVectorAlgebra 
    (v : euclideanGeometry3CoordinateVector)
    := 
        let base_fr := (euclideanGeometry3FrameAlgebra v.frame) in
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame base_fr in
                aff_lib.affine_coord_space.mk_vec
                    base_sp
                    v.coords



structure euclideanGeometry3CoordinatePoint 
    extends euclideanGeometry3Point :=
mk ::
    (frame : euclideanGeometry3Frame) 

attribute [reducible]
def euclideanGeometry3CoordinatePoint.build
    (sp : euclideanGeometry3)
    (fr : euclideanGeometry3Frame)
    (coords : vector ℝ 3) :
    euclideanGeometry3CoordinatePoint :=
    {
        frame := fr,
        ..(euclideanGeometry3Point.build sp coords)
    }

attribute [reducible]
def euclideanGeometry3CoordinatePoint.fromalgebra
    {f : affine_coord_frame ℝ 3}
    (sp : euclideanGeometry3)
    (fr : euclideanGeometry3Frame)
    (pt : aff_coord_pt ℝ 3 f)
    : euclideanGeometry3CoordinatePoint
    := 
    euclideanGeometry3CoordinatePoint.build sp fr (affine_coord_pt.get_coords pt)

attribute [reducible]
def euclideanGeometry3CoordinatePointAlgebra 
    (v : euclideanGeometry3CoordinatePoint)
    := 
        let base_fr := (euclideanGeometry3FrameAlgebra v.frame) in
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame base_fr in
                aff_lib.affine_coord_space.mk_point
                    base_sp
                    v.coords

--attribute [reducible]
structure euclideanGeometry3Transform :=
    (sp : euclideanGeometry3)
    (from_ : euclideanGeometry3Frame)
    (to_ : euclideanGeometry3Frame)

def euclideanGeometry3Transform.build
    (sp : euclideanGeometry3)
    (from_ : euclideanGeometry3Frame)
    (to_ : euclideanGeometry3Frame)
    :=
    euclideanGeometry3Transform.mk sp from_ to_

def euclideanGeometry3Transform.fromalgebra
    (sp : euclideanGeometry3)
    (from_ : euclideanGeometry3Frame)
    (to_ : euclideanGeometry3Frame)
    (tr : affine_coord_frame_transform ℝ 3 (euclideanGeometry3FrameAlgebra from_) (euclideanGeometry3FrameAlgebra to_))
    :=
    euclideanGeometry3Transform.mk sp from_ to_

attribute [reducible]
def euclideanGeometry3TransformAlgebra 
    (tr : euclideanGeometry3Transform)
    :=
    affine_coord_space.build_transform 
        (⟨⟩ : affine_coord_space ℝ 3 
            ((euclideanGeometry3FrameAlgebra tr.from_)))
        (⟨⟩ : affine_coord_space ℝ 3 
            ((euclideanGeometry3FrameAlgebra tr.to_)))