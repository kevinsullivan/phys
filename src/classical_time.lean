import .....math.affine.affine_coordinate_framed_space_update_lib
--import .....math.affine.algebra
import ..metrology.dimension 
import ..metrology.measurement
import data.real.basic
--import .....math.affine.affine_coordinate_space

noncomputable theory
--open real_lib
open measurementSystem


structure classicalTime : Type :=
mk :: 
    (sp : aff_lib.affine_coord_space.standard_space ℝ 1) 
    (id : ℕ) -- id serves as unique ID for a given geometric space


def classicalTime.build (id : ℕ) : classicalTime :=
    ⟨aff_lib.affine_coord_space.mk_with_standard ℝ 1, id⟩

noncomputable def classicalTimeAlgebra : classicalTime →  
     aff_lib.affine_coord_space.standard_space ℝ 1
| (classicalTime.mk sp n) := sp


structure classicalTimeVector :=
mk ::
    (sp : classicalTime)
    (coords : vector ℝ 1)

def classicalTimeVector.build
    (sp : classicalTime)
    (coord : ℝ) :=
    classicalTimeVector.mk
        sp 
        ⟨[coord], by refl⟩

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

def classicalTimePoint.build
    (sp : classicalTime)
    (coord : ℝ) :=
    classicalTimePoint.mk
        sp 
        ⟨[coord], by refl⟩

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
    (basis : classicalTimeVector)
    (m : MeasurementSystem)
    : classicalTimeFrame
| interpret
    (fr : classicalTimeFrame)
    (m : MeasurementSystem)

def classicalTimeFrame.space : classicalTimeFrame → classicalTime
| (classicalTimeFrame.std sp) := sp
| (classicalTimeFrame.derived s f o b m) :=  s
| (classicalTimeFrame.interpret f m) := classicalTimeFrame.space f


def classicalTimeFrame.build_derived
   : classicalTimeFrame → classicalTimePoint → classicalTimeVector → MeasurementSystem → classicalTimeFrame
| (classicalTimeFrame.std sp) p v m := classicalTimeFrame.derived sp (classicalTimeFrame.std sp) p v m
| (classicalTimeFrame.derived s f o b m) p v ms :=  classicalTimeFrame.derived s (classicalTimeFrame.derived s f o b m) p v ms
| (classicalTimeFrame.interpret f m) p v ms :=  classicalTimeFrame.derived (classicalTimeFrame.space f) (classicalTimeFrame.interpret f m) p v ms

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
                    (aff_lib.affine_coord_space.mk_basis base_sp ⟨[aff_lib.affine_coord_space.mk_vec base_sp b.coords], by refl⟩)
        base_fr 
| (classicalTimeFrame.interpret f m) := classicalTimeFrameAlgebra f
   -- aff_lib.affine_coord_space.mk_derived
    --    (classicalTimeAlgebra sp)
def classicalTime.stdFrame (sp : classicalTime)
    := classicalTimeFrame.std sp


structure classicalTimeCoordinateVector
    extends classicalTimeVector :=
mk ::
    (frame : classicalTimeFrame) 

def classicalTimeCoordinateVector.build
    (sp : classicalTime)
    (fr : classicalTimeFrame)
    (coord : ℝ) :
    classicalTimeCoordinateVector :=
    {
        frame := fr,
        ..(classicalTimeVector.build sp coord)
    }

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

def classicalTimeCoordinatePoint.build
    (sp : classicalTime)
    (fr : classicalTimeFrame)
    (coord : ℝ) :
    classicalTimeCoordinatePoint :=
    {
        frame := fr,
        ..(classicalTimePoint.build sp coord)
    }

def classicalTimeCoordinatePointAlgebra 
    (v : classicalTimeCoordinatePoint)
    := 
        let base_fr := (classicalTimeFrameAlgebra v.frame) in
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame base_fr in
                aff_lib.affine_coord_space.mk_point
                    base_sp
                    v.coords
/-
noncomputable def classicalTimeAlgebraDerived 
    (t : classicalTime) (o : vector ℝ 1) (b : vector ℝ 1): 
    real_affine_coord_nspace 1 --(real_affine_coord_nspace.get_standard 1)
        (real_affine_coord_nspace.mk_derived_frame
            t.sp
            (real_affine_coord_nspace.mk_point t.sp o)
            (λi : fin 1, real_affine_coord_nspace.mk_vec t.sp b))
    :=
    real_affine_coord_nspace.mk_derived t.sp 
            (real_affine_coord_nspace.mk_point t.sp o)
            (λi : fin 1, real_affine_coord_nspace.mk_vec t.sp b)

mutual inductive
    classicalTimeVector, 
    classicalTimePoint, 
    classicalTimeBasis, 
    classicalTimeFrame
    (t : classicalTime)
    (val : vector ℝ 1) 
with classicalTimeVector : classicalTime → Type
| mk 
    (f : classicalTimeFrame t) 
    : classicalTimeVector t
with classicalTimePoint : classicalTime → Type
| mk
    (f : classicalTimeFrame t)
    : classicalTimePoint t
with classicalTimeBasis : classicalTime → Type
| std 
    {val : vector ℝ 1}
    (v1 : classicalTimeVector t)
    : classicalTimeBasis t
with classicalTimeFrame : classicalTime → Type 
| standard 
     (sp : real_affine_coord_nspace 1 (real_affine_coord_nspace.get_standard 1)) : classicalTimeFrame t
| derived 
    {oval : vector ℝ 1}
    {bval : vector ℝ 1}
    (o : classicalTimePoint t) 
    (b : classicalTimeBasis  t) 
    (m : MeasurementSystem)
    (s :     real_affine_coord_nspace 1 --(real_affine_coord_nspace.get_standard 1)
        (real_affine_coord_nspace.mk_derived_frame
            t.sp
            (real_affine_coord_nspace.mk_point t.sp oval)
            (λi : fin 1, real_affine_coord_nspace.mk_vec t.sp bval)))
     : classicalTimeFrame t
| interpret (m : MeasurementSystem) : classicalTimeFrame t

def classicalTimeVectorAlgebra {t : classicalTime} : classicalTimeVector t → algebra.AlgebraicVector := 
    sorry
def classicalTimePointAlgebra {t : classicalTime} : classicalTimePoint t → classicalTimeFrame t :=
    sorry




structure classicalTimeVector (t : classicalTime) :=
mk :: (id : ℕ) (val : real_affine_coord_nspace.point t.sp)

structure classicalTimePoint (t : classicalTime) : Type :=
mk :: (id : ℕ) (val : real_affine_coord_nspace.vec t.sp)

def classicalTimeBasis {t : classicalTime} := fin 1 → classicalTimeVector t
def classicalTimeBasis.mk {t : classicalTime} (v :vector (classicalTimeVector t) 1)
    := ((λ i : fin 1, v.nth 1) : classicalTimeBasis)

inductive classicalTimeFrame : classicalTime → Type 
| standard (t : classicalTime) : classicalTimeFrame t
| derived {t : classicalTime} (f : classicalTimeFrame t) (o : classicalTimePoint t) (b : @classicalTimeBasis t) (m : MeasurementSystem) : classicalTimeFrame t
| interpret {t : classicalTime} (f : classicalTimeFrame t) (m : MeasurementSystem) : classicalTimeFrame t




def classicalTime.stdFrame (t : classicalTime) :=
    classicalTimeFrame.standard t

def classicalTime.derivedFrame {t: classicalTime}
    (f : classicalTimeFrame t) (o : classicalTimePoint t) (b : @classicalTimeBasis t) (m : MeasurementSystem)   
    :=
    classicalTimeFrame.derived f o b m

def classicalTime.interpretFrame {t : classicalTime} (f : classicalTimeFrame t) (m : MeasurementSystem) :=
    classicalTimeFrame.interpret f m

    
structure classicalTimeinateVector (s : classicalTime) extends classicalTimeVector s :=
(f : classicalTimeFrame s)--mk :: (id : ℕ) (val : vector ℝ 1) {s : classicalTime} (f : classicalTimeFrame s)


structure classicalTimeinatePoint (s : classicalTime) extends classicalTimePoint s :=
(f : classicalTimeFrame s)--mk 

def tm := get_classicalTime 1

#check tm
-/
/--/
noncomputable def classicalTimeFrameAlgebra : classicalTimeFrame → Algebra
| (classicalTime.mk sp n) := sp
-/

/-
structure classicalTimeVector (t : classicalTime) :=
mk :: (id : ℕ) (vec : real_affine_vector 1)

variables sp1 : classicalTime
variables (v1 : classicalTimeVector sp1) (v2 : classicalTimeVector sp1)
variables (a : aff_vec_coord_tuple ℝ 1) (b : aff_vec_coord_tuple ℝ 1)
def tt : _ := a + b

def classicalTimeVectorAdd {t : classicalTime} 
    : classicalTimeVector t → classicalTimeVector t → classicalTimeVector t
| v1 v2 := classicalTimeVector.mk (0) (v1.vec + v2.vec)
instance ct_vec_add {sp : classicalTime} : has_add (classicalTimeVector sp) := ⟨classicalTimeVectorAdd⟩
def classicalTimeVectorSub {t : classicalTime}
    : classicalTimeVector t → classicalTimeVector t → classicalTimeVector t
| v1 v2 := classicalTimeVector.mk (0) (v1.vec - v2.vec)
instance ct_vec_sub {sp : classicalTime} : has_sub (classicalTimeVector sp) := ⟨classicalTimeVectorSub⟩
def classicalTimeVectorNeg {t : classicalTime}
    : classicalTimeVector t → classicalTimeVector t
| v1 := ⟨0,-v1.vec⟩
instance ct_vec_neg {sp : classicalTime} : has_neg (classicalTimeVector sp) := ⟨classicalTimeVectorNeg⟩

structure classicalTimePoint (t : classicalTime) : Type :=
mk :: (id : ℕ) (pt : real_affine_point 1)
-/

/-
structure classicalTimeinateVector (s : classicalTime) extends classicalTimeVector s :=
(f : classicalTimeFrame s)--mk :: (id : ℕ) (val : vector ℝ 1) {s : classicalTime} (f : classicalTimeFrame s)


structure classicalTimeinatePoint (s : classicalTime) extends classicalTimePoint s :=
(f : classicalTimeFrame s)--mk 
-/
/-
The Algebra type is simply a variant type for encapsulating different kinds
of algebras (e.g., affine space, monoid, or whatever). It's currently situated
in the real_affine_space file, but should be moved.
-/
/-
-/

-- provide standard world time object
--def worldTime := getClassicalTime 0
--#check worldTime

/-
noncomputable def classicalTimeAlgebra : classicalTime → real_affine.Algebra
| (classicalTime.mk n) := real_affine.Algebra.aff_space (real_affine.to_affine_space 1)
-/

/-
noncomputable def classicalTimeVectorAlgebra {t : classicalTime} : classicalTimeVector t → real_affine.Algebra
| (classicalTimeVector.mk _ v) := real_affine.Algebra.aff_vec_coord_tupletor (real_affine.to_affine_vector v)

noncomputable def classicalTimePointAlgebra {t : classicalTime} : classicalTimeVector t → real_affine.Algebra
| (classicalTimeVector.mk _ v) := real_affine.Algebra.aff_point (real_affine.to_affine_point v)

noncomputable def classicalTimeFrameHelper  {t : classicalTime} : classicalTimeFrame t → real_affine.real_affine_frame 1
| (@classicalTimeFrame.standard t m) := real_affine.to_standard_frame 1
| (@classicalTimeFrame.derived t f p v m) := real_affine.to_derived_frame 1 p.val 
    (λn : fin 1, (v n).val) (real_affine.to_coordinatized_affine_space 1 
    (classicalTimeFrameHelper f).1)

noncomputable def classicalTimeFrameAlgebra {t : classicalTime} : classicalTimeFrame t → real_affine.Algebra
| f := real_affine.Algebra.aff_frame (classicalTimeFrameHelper f)
noncomputable def classicalTimeinateVectorAlgebra {t : classicalTime} : classicalTimeinateVector t → real_affine.Algebra :=
    λ v, real_affine.Algebra.aff_vec_coord_tupletor (real_affine.to_affine_vector_with_frame v.val (real_affine.to_coordinatized_affine_space 1 (classicalTimeFrameHelper v.f).1))

noncomputable def classicalTimeinatePointAlgebra {t : classicalTime} : classicalTimeinatePoint t → real_affine.Algebra :=
    λ v, real_affine.Algebra.aff_point (real_affine.to_affine_point_with_frame v.val (real_affine.to_coordinatized_affine_space 1 (classicalTimeFrameHelper v.f).1))
-/

-- Kevin: add has_to_algebra typeclass

/--/