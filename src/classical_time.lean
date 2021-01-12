import .....math.affine.affine_coordinate_framed_space_lib
import .....math.affine.affine_coordinate_transform
import ..metrology.dimensions 
import ..metrology.measurement
import data.real.basic

noncomputable theory
--open real_lib
open measurementSystem
open aff_fr
open aff_lib
open aff_trans

structure classicalTime : Type :=
mk :: 
    (sp : aff_lib.affine_coord_space.standard_space ℝ 1) 
    (id : ℕ) -- id serves as unique ID for a given geometric space


attribute [reducible]
def classicalTime.build (id : ℕ) : classicalTime :=
    ⟨aff_lib.affine_coord_space.mk_with_standard ℝ 1, id⟩

noncomputable def classicalTimeAlgebra : classicalTime →  
     aff_lib.affine_coord_space.standard_space ℝ 1
| (classicalTime.mk sp n) := sp

structure classicalTimeScalar :=
mk ::
    (sp : classicalTime)
    (val : ℝ)

attribute [reducible]
def classicalTimeScalar.build
    (sp : classicalTime)
    (val : vector ℝ 1) := 
    classicalTimeScalar.mk sp (val.nth 1)



attribute [reducible]
def classicalTimeScalarAlgebra 
    (s : classicalTimeScalar)
    := 
    s.val

structure classicalTimeVector :=
mk ::
    (sp : classicalTime)
    (coords : vector ℝ 1)

attribute [reducible]
def classicalTimeVector.build
    (sp : classicalTime)
    (coords : vector ℝ 1) :=
    classicalTimeVector.mk
        sp 
        --⟨[coord], by refl⟩
        coords


attribute [reducible]
def classicalTimeVectorAlgebra 
    (v : classicalTimeVector)
    := 
        (aff_lib.affine_coord_space.mk_coord_vec
        (classicalTimeAlgebra v.sp) 
        v.coords)


structure classicalTimePoint :=
mk ::
    (sp : classicalTime)
    (coords : vector ℝ 1)

attribute [reducible]
def classicalTimePoint.build
    (sp : classicalTime)
    (coords : vector ℝ 1) :=
    classicalTimePoint.mk
        sp 
        --⟨[coord], by refl⟩
        coords

attribute [reducible]
def classicalTimePointAlgebra 
    (v : classicalTimePoint)
    := 
        (aff_lib.affine_coord_space.mk_coord_point
        (classicalTimeAlgebra v.sp) 
        v.coords)



abbreviation classicalTimeBasis :=
    (fin 1) → classicalTimeVector

inductive classicalTimeFrame : Type
| std 
    (sp : classicalTime)
    : classicalTimeFrame
| derived 
    (sp : classicalTime) --ALERT : WEAK TYPING
    (fr : classicalTimeFrame) --ALERT : WEAK TYPING
    (origin : classicalTimePoint)
    (basis : classicalTimeBasis)
    (m : MeasurementSystem)
    : classicalTimeFrame
| interpret
    (fr : classicalTimeFrame)
    (m : MeasurementSystem)

attribute [reducible]
def classicalTimeFrame.space : classicalTimeFrame → classicalTime
| (classicalTimeFrame.std sp) := sp
| (classicalTimeFrame.derived s f o b m) :=  s
| (classicalTimeFrame.interpret f m) := classicalTimeFrame.space f


attribute [reducible]
def classicalTimeFrame.build_derived
   : classicalTimeFrame → classicalTimePoint → classicalTimeBasis → MeasurementSystem → classicalTimeFrame
| (classicalTimeFrame.std sp) p v m := classicalTimeFrame.derived sp (classicalTimeFrame.std sp) p v m
| (classicalTimeFrame.derived s f o b m) p v ms :=  classicalTimeFrame.derived s (classicalTimeFrame.derived s f o b m) p v ms
| (classicalTimeFrame.interpret f m) p v ms :=  classicalTimeFrame.derived (classicalTimeFrame.space f) (classicalTimeFrame.interpret f m) p v ms

attribute [reducible]
noncomputable def classicalTimeFrameAlgebra :
    classicalTimeFrame → aff_fr.affine_coord_frame ℝ 1
| (classicalTimeFrame.std sp) := 
    aff_lib.affine_coord_space.frame 
        (classicalTimeAlgebra sp)
| (classicalTimeFrame.derived s f o b m) :=
    let base_fr := (classicalTimeFrameAlgebra f) in
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame base_fr in
                aff_lib.affine_coord_space.mk_frame
                    base_sp
                    (aff_lib.affine_coord_space.mk_point base_sp o.coords)
                    (aff_lib.affine_coord_space.mk_basis base_sp ⟨[aff_lib.affine_coord_space.mk_vec base_sp (b 1).coords], by refl⟩)
        base_fr 
| (classicalTimeFrame.interpret f m) := classicalTimeFrameAlgebra f

attribute [reducible]
def classicalTime.stdFrame (sp : classicalTime)
    := classicalTimeFrame.std sp


structure classicalTimeCoordinateVector
    extends classicalTimeVector :=
mk ::
    (frame : classicalTimeFrame) 

attribute [reducible]
def classicalTimeCoordinateVector.build
    (sp : classicalTime)
    (fr : classicalTimeFrame)
    (coords : vector ℝ 1) :
    classicalTimeCoordinateVector :=
    {
        frame := fr,
        ..(classicalTimeVector.build sp coords)
    }

attribute [reducible]
def classicalTimeCoordinateVector.fromalgebra
    {f : affine_coord_frame ℝ 1}
    (sp : classicalTime)
    (fr : classicalTimeFrame)
    (vec : aff_coord_vec ℝ 1 f)
    --(vec : aff_coord_vec ℝ 1 (classicalTimeFrameAlgebra fr))
    : classicalTimeCoordinateVector
    := 
    classicalTimeCoordinateVector.build sp fr (affine_coord_vec.get_coords vec)

attribute [reducible]
def classicalTimeCoordinateVectorAlgebra 
    (v : classicalTimeCoordinateVector)
    := 
        let base_fr := (classicalTimeFrameAlgebra v.frame) in
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame base_fr in
                aff_lib.affine_coord_space.mk_vec
                    base_sp
                    v.coords



structure classicalTimeCoordinatePoint 
    extends classicalTimePoint :=
mk ::
    (frame : classicalTimeFrame) 

attribute [reducible]
def classicalTimeCoordinatePoint.build
    (sp : classicalTime)
    (fr : classicalTimeFrame)
    (coords : vector ℝ 1) :
    classicalTimeCoordinatePoint :=
    {
        frame := fr,
        ..(classicalTimePoint.build sp coords)
    }

attribute [reducible]
def classicalTimeCoordinatePoint.fromalgebra
    {f : affine_coord_frame ℝ 1}
    (sp : classicalTime)
    (fr : classicalTimeFrame)
    (pt : aff_coord_pt ℝ 1 f)
    : classicalTimeCoordinatePoint
    := 
    classicalTimeCoordinatePoint.build sp fr (affine_coord_pt.get_coords pt)

attribute [reducible]
def classicalTimeCoordinatePointAlgebra 
    (v : classicalTimeCoordinatePoint)
    := 
        let base_fr := (classicalTimeFrameAlgebra v.frame) in
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame base_fr in
                aff_lib.affine_coord_space.mk_point
                    base_sp
                    v.coords

--attribute [reducible]
structure classicalTimeTransform :=
    (sp : classicalTime)
    (from_ : classicalTimeFrame)
    (to_ : classicalTimeFrame)

def classicalTimeTransform.build
    (sp : classicalTime)
    (from_ : classicalTimeFrame)
    (to_ : classicalTimeFrame)
    :=
    classicalTimeTransform.mk sp from_ to_

attribute [reducible]
def classicalTimeTransformAlgebra 
    (tr : classicalTimeTransform)
    [inhabited (affine_coord_frame ℝ 1)]
    :=
    affine_coord_space.build_transform ℝ 1 ((classicalTimeFrameAlgebra tr.from_)) ((classicalTimeFrameAlgebra tr.to_))
        (⟨⟩ : affine_coord_space ℝ 1 
            ((classicalTimeFrameAlgebra tr.from_)))
        (⟨⟩ : affine_coord_space ℝ 1 
            ((classicalTimeFrameAlgebra tr.to_)))
        
