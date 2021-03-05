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

noncomputable def classicalTime.algebra : classicalTime →  
     aff_lib.affine_coord_space.standard_space ℝ 1
| (classicalTime.mk sp n) := sp

structure classicalTimeQuantity
    (sp : classicalTime)
    (m : MeasurementSystem) :=
mk ::
    (val : ℝ)

attribute [reducible]
def classicalTimeQuantity.build
    (sp : classicalTime)
    (m : MeasurementSystem)
    (val : vector ℝ 1) :
    classicalTimeQuantity sp m := 
    classicalTimeQuantity.mk (val.nth 1)



attribute [reducible]
def classicalTimeQuantity.algebra 
    {sp : classicalTime}
    {m : MeasurementSystem}
    (s : classicalTimeQuantity sp m)
    := 
    s.val

structure classicalTimeVector
    (sp : classicalTime) :=
mk ::
    (coords : vector ℝ 1)

attribute [reducible]
def classicalTimeVector.build
    (sp : classicalTime)
    (coords : vector ℝ 1)
    : classicalTimeVector sp :=
    classicalTimeVector.mk
        --⟨[coord], by refl⟩
        coords


attribute [reducible]
def classicalTimeVector.algebra 
    {sp : classicalTime}
    (v : classicalTimeVector sp)
    := 
        (aff_lib.affine_coord_space.mk_coord_vec
        (classicalTime.algebra sp) 
        v.coords)


structure classicalTimePoint
    (sp : classicalTime) :=
mk ::
    (coords : vector ℝ 1)

attribute [reducible]
def classicalTimePoint.build
    (sp : classicalTime)
    (coords : vector ℝ 1) :
    classicalTimePoint sp :=
    classicalTimePoint.mk
        coords

attribute [reducible]
def classicalTimePoint.algebra 
    {sp : classicalTime}
    (v : classicalTimePoint sp)
    := 
        (aff_lib.affine_coord_space.mk_coord_point
        (classicalTime.algebra sp) 
        v.coords)



abbreviation classicalTimeBasis
    (sp : classicalTime) :=
    (fin 1) → classicalTimeVector sp

inductive classicalTimeFrame (sp : classicalTime)
| std 
    (sp : classicalTime)
    : classicalTimeFrame
| derived 
    (fr : classicalTimeFrame)
    (origin : classicalTimePoint sp)
    (basis : classicalTimeBasis sp)
    (m : MeasurementSystem)
    : classicalTimeFrame
| interpret
    (fr : classicalTimeFrame)
    (m : MeasurementSystem)
    : classicalTimeFrame

def classicalTimeFrame.measurementSystem
    {sp : classicalTime} 
    (f : classicalTimeFrame sp) : option MeasurementSystem
    := 
    begin
        cases f,
        {exact (option.none)},
        {exact (option.some f_m)},
        {exact (option.some f_m)}
    end

attribute [reducible]
def classicalTimeFrame.space {sp : classicalTime} (fr : classicalTimeFrame sp) := sp


attribute [reducible]
def classicalTimeFrame.build_derived {sp : classicalTime}
   : classicalTimeFrame sp → classicalTimePoint sp → classicalTimeBasis sp → MeasurementSystem → classicalTimeFrame sp
| (classicalTimeFrame.std sp) p v m := classicalTimeFrame.derived (classicalTimeFrame.std sp) p v m
| (classicalTimeFrame.derived f o b m) p v ms :=  classicalTimeFrame.derived (classicalTimeFrame.derived f o b m) p v ms
| (classicalTimeFrame.interpret f m) p v ms :=  classicalTimeFrame.derived (classicalTimeFrame.interpret f m) p v ms

attribute [reducible]
noncomputable def classicalTimeFrame.algebra {sp : classicalTime} :
    classicalTimeFrame sp → aff_fr.affine_coord_frame ℝ 1
| (classicalTimeFrame.std sp) := 
    aff_lib.affine_coord_space.frame 
        (classicalTime.algebra sp)
| (classicalTimeFrame.derived f o b m) :=
    let base_fr := (classicalTimeFrame.algebra f) in
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame base_fr in
                aff_lib.affine_coord_space.mk_frame
                    base_sp
                    (aff_lib.affine_coord_space.mk_coord_point base_sp o.coords)
                    (aff_lib.affine_coord_space.mk_basis base_sp ⟨[aff_lib.affine_coord_space.mk_coord_vec base_sp (b 1).coords], by refl⟩)
        base_fr 
| (classicalTimeFrame.interpret f m) := classicalTimeFrame.algebra f

attribute [reducible]
def classicalTime.stdFrame (sp : classicalTime)
    : classicalTimeFrame sp
    := classicalTimeFrame.std sp 


structure classicalTimeCoordinateVector {sp : classicalTime} (fr : classicalTimeFrame sp)
    extends classicalTimeVector sp :=
mk ::

attribute [reducible]
def classicalTimeCoordinateVector.build
    {sp : classicalTime}
    (fr : classicalTimeFrame sp)
    (coords : vector ℝ 1) :
    classicalTimeCoordinateVector fr :=
    {
        ..(classicalTimeVector.build sp coords)
    }

attribute [reducible]
def classicalTimeCoordinateVector.fromalgebra
    {f : affine_coord_frame ℝ 1}
    {sp : classicalTime}
    (fr : classicalTimeFrame sp)
    (vec : aff_coord_vec ℝ 1 f)
    --(vec : aff_coord_vec ℝ 1 (classicalTimeFrame.algebra fr))
    : classicalTimeCoordinateVector fr
    := 
    classicalTimeCoordinateVector.build fr (affine_coord_vec.get_coords vec)

attribute [reducible]
def classicalTimeCoordinateVector.algebra 
    {sp : classicalTime }
    {fr : classicalTimeFrame sp}
    (v : classicalTimeCoordinateVector fr)
    --: aff_coord_vec ℝ 1 (v.frame.algebra)
    := 
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame fr.algebra in
                aff_lib.affine_coord_space.mk_coord_vec
                    base_sp
                    v.coords

structure classicalTimeCoordinatePoint  {sp : classicalTime} (fr : classicalTimeFrame sp)
    extends classicalTimePoint sp :=
mk ::

attribute [reducible]
def classicalTimeCoordinatePoint.build
    {sp : classicalTime}
    {fr : classicalTimeFrame sp}
    (coords : vector ℝ 1) :
    classicalTimeCoordinatePoint fr :=
    {
        ..(classicalTimePoint.build sp coords)
    }

attribute [reducible]
def classicalTimeCoordinatePoint.fromalgebra
    {f : affine_coord_frame ℝ 1}
    {sp : classicalTime}
    (fr : classicalTimeFrame sp)
    (pt : aff_coord_pt ℝ 1 f)
    : classicalTimeCoordinatePoint fr
    := 
    classicalTimeCoordinatePoint.build (affine_coord_pt.get_coords pt)

attribute [reducible]
def classicalTimeCoordinatePoint.algebra 
    {sp : classicalTime}
    {fr : classicalTimeFrame sp}
    (v : classicalTimeCoordinatePoint fr)
    := 
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame fr.algebra in
                aff_lib.affine_coord_space.mk_coord_point
                    base_sp
                    v.coords

--attribute [reducible]
structure classicalTimeTransform
    {sp : classicalTime}
    (from_ : classicalTimeFrame sp)
    (to_ : classicalTimeFrame sp) :=
    mk::
    (tr : aff_coord_pt ℝ 1 from_.algebra ≃ᵃ[ℝ] aff_coord_pt ℝ 1 to_.algebra)

def classicalTimeTransform.build
    {sp : classicalTime}
    (from_ : classicalTimeFrame sp)
    (to_ : classicalTimeFrame sp)
    : classicalTimeTransform from_ to_
    :=
    classicalTimeTransform.mk 
        (affine_coord_space.build_transform ℝ 1 from_.algebra to_.algebra
        (⟨⟨⟩⟩ : affine_coord_space ℝ 1 
            _)
        (⟨⟨⟩⟩ : affine_coord_space ℝ 1 
            _))

attribute [reducible]
def classicalTimeTransform.algebra 
    {sp : classicalTime}
    {from_ : classicalTimeFrame sp}
    {to_ : classicalTimeFrame sp}
    (tr : classicalTimeTransform from_ to_)
    :=
    tr.tr
    --affine_coord_space.build_transform ℝ 1 from_.algebra to_.algebra
    --    (⟨⟨⟩⟩ : affine_coord_space ℝ 1 
    --        _)
    --    (⟨⟨⟩⟩ : affine_coord_space ℝ 1 
    --        _)
/-      
attribute [reducible]
def classicalTimeCoordinateTransform.fromalgebra
    {sp : classicalTime}
    {from_ : classicalTimeFrame sp}
    {to_ : classicalTimeFrame sp}
    (tr : classicalTimeTransform from_ to_)
    : classicalTimeTransform
    := 
    classicalTimeTransform.build (affine_coord_pt.get_coords pt)
-/
attribute [reducible]
def time_vec_plus_vec
    {sp : classicalTime}
    {fr : classicalTimeFrame sp} : 
    classicalTimeCoordinateVector fr → classicalTimeCoordinateVector fr → classicalTimeCoordinateVector fr := 
    λ (v1 v2 : _), classicalTimeCoordinateVector.fromalgebra fr (v1.algebra +ᵥ v2.algebra)
attribute [reducible]
def time_vec_plus_pt
    {sp : classicalTime}
    {fr : classicalTimeFrame sp} : 
    classicalTimeCoordinateVector fr → classicalTimeCoordinatePoint fr → classicalTimeCoordinatePoint fr := 
    λ (v p : _), classicalTimeCoordinatePoint.fromalgebra fr (v.algebra +ᵥ p.algebra)
attribute [reducible]
def time_pt_plus_vec
    {sp : classicalTime}
    {fr : classicalTimeFrame sp} : 
    classicalTimeCoordinatePoint fr → classicalTimeCoordinateVector fr → classicalTimeCoordinatePoint fr := 
    λ (p v : _), time_vec_plus_pt v p
attribute [reducible]
def time_scalar_mul_vec -- this should get changed 
    {sp : classicalTime}
    {fr : classicalTimeFrame sp} : 
    ℝ → classicalTimeCoordinateVector fr → classicalTimeCoordinateVector fr :=
    λ (s v), classicalTimeCoordinateVector.fromalgebra fr (s•v.algebra)
attribute [reducible]
def time_vec_mul_scalar
    {sp : classicalTime}
    {fr : classicalTimeFrame sp} : 
    classicalTimeCoordinateVector fr → ℝ → classicalTimeCoordinateVector fr :=
    λ (v s), classicalTimeCoordinateVector.fromalgebra fr (s•v.algebra)
attribute [reducible]
def time_vec_minus_vec
    {sp : classicalTime}
    {fr : classicalTimeFrame sp} : 
    classicalTimeCoordinateVector fr → classicalTimeCoordinateVector fr → classicalTimeCoordinateVector fr := 
    λ (v1 v2 : _), classicalTimeCoordinateVector.fromalgebra fr (v1.algebra+ᵥ(-v2.algebra))
attribute [reducible]
def time_pt_minus_vec
    {sp : classicalTime}
    {fr : classicalTimeFrame sp} : 
    classicalTimeCoordinatePoint fr → classicalTimeCoordinateVector fr → classicalTimeCoordinatePoint fr := 
    λ (p v : _), classicalTimeCoordinatePoint.fromalgebra fr ((-v.algebra)+ᵥp.algebra)
attribute [reducible]
def time_trans_apply_vec
    {sp : classicalTime}
    {from_ : classicalTimeFrame sp}
    {to_ : classicalTimeFrame sp} :
    classicalTimeTransform from_ to_ → classicalTimeCoordinateVector from_ → classicalTimeCoordinateVector to_ :=
    λ t v, classicalTimeCoordinateVector.fromalgebra to_ 
        ((t.algebra (v.algebra +ᵥ (pt_zero_coord ℝ 1 from_.algebra))) -ᵥ (pt_zero_coord ℝ 1 to_.algebra))
attribute [reducible]
def time_trans_compose
    {sp : classicalTime}
    {from_ : classicalTimeFrame sp}
    {inner_ : classicalTimeFrame sp}
    {to_ : classicalTimeFrame sp} :
    classicalTimeTransform from_ inner_ → classicalTimeTransform inner_ to_ → classicalTimeTransform from_ to_ :=
    λ t1 t2, ⟨t1.algebra.trans t2.algebra⟩


notation v+v := time_vec_plus_vec v v
notation v+p := time_vec_plus_pt v p
notation p+v := time_pt_plus_vec p v
notation s•v := time_scalar_mul_vec s v
notation v•s := time_vec_mul_scalar v s
notation v-v := time_vec_minus_vec v v
notation p-v := time_pt_minus_vec p v
notation t⬝v := time_trans_apply_vec v 
notation t1∘t2 := time_trans_compose t1 t2
