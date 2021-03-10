import 
    .....math.affine.affine_coordinate_framed_space_lib
    .....math.affine.affine_coordinate_transform
    .....math.affine.affine_euclidean_space
    .....math.affine.affine_euclidean_space_lib
import ..metrology.dimensions 
import ..metrology.measurement
import ..metrology.axis_orientation
import data.real.basic

noncomputable theory
--open real_lib
open measurementSystem
open orientation
open aff_fr
open aff_lib
open aff_trans
open eucl_lib

structure euclideanGeometry (n : ℕ) : Type :=
mk :: 
    (sp : eucl_lib.affine_euclidean_space.standard_space ℝ n)
    (id : ℕ) -- id serves as unique ID for a given geometric space


attribute [reducible]
def euclideanGeometry.build (n : ℕ) (id : ℕ) : euclideanGeometry n :=
    ⟨affine_euclidean_space.mk_with_standard ℝ n, id⟩

noncomputable def euclideanGeometry.algebra  {n : ℕ }  : euclideanGeometry n →  
     affine_euclidean_space.standard_space ℝ n
| (euclideanGeometry.mk sp id) := sp

structure euclideanGeometryQuantity 
    {n : ℕ } 
    (sp : euclideanGeometry n)
    (m : MeasurementSystem)
     :=
mk ::
    (val : ℝ)

attribute [reducible]
def euclideanGeometryQuantity.build
    {n : ℕ } 
    (sp : euclideanGeometry n)
    (m : MeasurementSystem)
    (val : vector ℝ 1) :
    euclideanGeometryQuantity sp m := 
    euclideanGeometryQuantity.mk (val.nth 1)



attribute [reducible]
def euclideanGeometryQuantity.algebra 
    {n : ℕ }  
    {sp : euclideanGeometry n}
    {m : MeasurementSystem}
    (s : euclideanGeometryQuantity sp m)
    := 
    s.val

structure euclideanGeometryVector
    {n : ℕ }  
    (sp : euclideanGeometry n) :=
mk ::
    (coords : vector ℝ n)

attribute [reducible]
def euclideanGeometryVector.build
    {n : ℕ }  
    (sp : euclideanGeometry n)
    (coords : vector ℝ n) :
    euclideanGeometryVector sp :=
    euclideanGeometryVector.mk
        coords

attribute [reducible]
def euclideanGeometryVector.algebra 
    {n : ℕ }  
    (sp : euclideanGeometry n)
    (v : euclideanGeometryVector sp)
    := 
        (aff_lib.affine_coord_space.mk_coord_vec
        (euclideanGeometry.algebra sp).1 
        v.coords)


structure euclideanGeometryPoint
    {n : ℕ }  
    (sp : euclideanGeometry n) :=
mk ::
    (coords : vector ℝ n)

attribute [reducible]
def euclideanGeometryPoint.build
    {n : ℕ }  
    (sp : euclideanGeometry n)
    (coords : vector ℝ n) :
    euclideanGeometryPoint sp :=
    euclideanGeometryPoint.mk
        coords

attribute [reducible]
def euclideanGeometryPoint.algebra 
    {n : ℕ }  
    (sp : euclideanGeometry n)
    (v : euclideanGeometryPoint sp)
    := 
        (aff_lib.affine_coord_space.mk_coord_point
        (euclideanGeometry.algebra sp).1 
        v.coords)



abbreviation euclideanGeometryBasis
    {n : ℕ }  
    (sp : euclideanGeometry n) :=
    (fin n) → euclideanGeometryVector sp

inductive euclideanGeometryFrame
    {n : ℕ }  
    (sp : euclideanGeometry n) : Type
| std 
    : euclideanGeometryFrame
| derived 
    (fr : euclideanGeometryFrame)
    (origin : euclideanGeometryPoint sp)
    (basis : euclideanGeometryBasis sp)
    (m : MeasurementSystem)
    (or : AxisOrientation n)
    : euclideanGeometryFrame
| interpret
    (fr : euclideanGeometryFrame)
    (m : MeasurementSystem)
    (or : AxisOrientation n)
    : euclideanGeometryFrame

attribute [reducible]
def euclideanGeometryFrame.space
    {n : ℕ }  
    {sp : euclideanGeometry n} (fr : euclideanGeometryFrame sp) := sp

attribute [reducible]
def euclideanGeometryBasis.build
    {n : ℕ }  
    {sp : euclideanGeometry n} 
    (v : vector (euclideanGeometryVector sp) n) : euclideanGeometryBasis sp
    := λi, v.nth i

attribute [reducible]
def euclideanGeometryFrame.build_derived
    {n : ℕ }  
    {sp : euclideanGeometry n} 
   : euclideanGeometryFrame sp → euclideanGeometryPoint sp → euclideanGeometryBasis sp 
        → MeasurementSystem → AxisOrientation n → euclideanGeometryFrame sp
| (euclideanGeometryFrame.std) p v m or := euclideanGeometryFrame.derived (euclideanGeometryFrame.std) p v m or
| (euclideanGeometryFrame.derived f o b m or) p v ms or_ :=  euclideanGeometryFrame.derived (euclideanGeometryFrame.derived f o b m or) p v ms or
| (euclideanGeometryFrame.interpret f m o) p v ms or :=  euclideanGeometryFrame.derived (euclideanGeometryFrame.interpret f m o) p v ms or

attribute [reducible]
def euclideanGeometryFrame.build_derived_from_coords
    {n : ℕ }  
    {sp : euclideanGeometry n} 
    : euclideanGeometryFrame sp → vector ℝ n → vector (vector ℝ n) n → 
        MeasurementSystem → AxisOrientation n → euclideanGeometryFrame sp
| f or v m ax := 
    (euclideanGeometryFrame.build_derived f (euclideanGeometryPoint.build sp or) 
        (euclideanGeometryBasis.build ⟨(list.map (λv, euclideanGeometryVector.build sp v) v.1),sorry⟩) m ax)


attribute [reducible]
noncomputable def euclideanGeometryFrame.algebra
    {n : ℕ }  
    {sp : euclideanGeometry n} :
    euclideanGeometryFrame sp → aff_fr.affine_coord_frame ℝ n
| (euclideanGeometryFrame.std) := 
        sp.algebra.1.frame
| (euclideanGeometryFrame.derived f o b m or) :=
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame f.algebra in
                aff_lib.affine_coord_space.mk_frame
                    base_sp
                    (aff_lib.affine_coord_space.mk_coord_point base_sp o.coords)
                    (λi, aff_lib.affine_coord_space.mk_coord_vec base_sp ((b i)).coords)
                f.algebra
| (euclideanGeometryFrame.interpret f m o) := euclideanGeometryFrame.algebra f

attribute [reducible]
def euclideanGeometry.stdFrame
    {n : ℕ }  
    (sp : euclideanGeometry n)
    : euclideanGeometryFrame sp
    := euclideanGeometryFrame.std


structure euclideanGeometryCoordinateVector
    {n : ℕ }  
    {sp : euclideanGeometry n}
    (fr : euclideanGeometryFrame sp) 
    extends euclideanGeometryVector sp :=
mk ::

attribute [reducible]
def euclideanGeometryCoordinateVector.build
    {n : ℕ }  
    {sp : euclideanGeometry n}
    (fr : euclideanGeometryFrame sp) 
    (coords : vector ℝ n) :
    euclideanGeometryCoordinateVector fr :=
    {
        ..(euclideanGeometryVector.build sp coords)
    }

attribute [reducible]
def euclideanGeometryCoordinateVector.fromalgebra
    {n : ℕ }  
    {sp : euclideanGeometry n}
    (fr : euclideanGeometryFrame sp) 
    (vec : aff_coord_vec ℝ n fr.algebra)
    --(vec : aff_coord_vec ℝ 1 (euclideanGeometryFrame.algebra fr))
    : euclideanGeometryCoordinateVector fr
    := 
    euclideanGeometryCoordinateVector.build fr (affine_coord_vec.get_coords vec)

attribute [reducible]
def euclideanGeometryCoordinateVector.algebra 
    {n : ℕ }  
    {sp : euclideanGeometry n}
    {fr : euclideanGeometryFrame sp} 
    (v : euclideanGeometryCoordinateVector fr)
    := 
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame fr.algebra in
                aff_lib.affine_coord_space.mk_coord_vec
                    base_sp
                    v.coords



structure euclideanGeometryCoordinatePoint 
    {n : ℕ }  
    {sp : euclideanGeometry n}
    (fr : euclideanGeometryFrame sp) 
    extends euclideanGeometryPoint sp :=
mk ::

attribute [reducible]
def euclideanGeometryCoordinatePoint.build
    {n : ℕ }  
    {sp : euclideanGeometry n}
    (fr : euclideanGeometryFrame sp) 
    (coords : vector ℝ n) :
    euclideanGeometryCoordinatePoint fr :=
    {
        ..(euclideanGeometryPoint.build sp coords)
    }

attribute [reducible]
def euclideanGeometryCoordinatePoint.fromalgebra
    {n : ℕ }  
    {sp : euclideanGeometry n}
    (fr : euclideanGeometryFrame sp) 
    (pt : aff_coord_pt ℝ n fr.algebra)
    : euclideanGeometryCoordinatePoint fr
    := 
    euclideanGeometryCoordinatePoint.build fr (affine_coord_pt.get_coords pt)

attribute [reducible]
def euclideanGeometryCoordinatePoint.algebra 
    {n : ℕ }  
    {sp : euclideanGeometry n}
    {fr : euclideanGeometryFrame sp}
    (v : euclideanGeometryCoordinatePoint fr)
    := 
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame fr.algebra in
                aff_lib.affine_coord_space.mk_coord_point
                    base_sp
                    v.coords

--attribute [reducible]
structure euclideanGeometryTransform
    {n : ℕ }  
    {sp : euclideanGeometry n}
    (from_ : euclideanGeometryFrame sp)
    (to_ : euclideanGeometryFrame sp) :=
    mk ::
    (tr : affine_coord_frame_transform ℝ n from_.algebra to_.algebra)

def euclideanGeometryTransform.build
    {n : ℕ }  
    {sp : euclideanGeometry n}
    (from_ : euclideanGeometryFrame sp)
    (to_ : euclideanGeometryFrame sp) 
    : euclideanGeometryTransform from_ to_
    :=
    ⟨ affine_coord_space.build_transform ℝ n from_.algebra to_.algebra
        (⟨⟨⟩⟩ : affine_coord_space ℝ n 
            _)
        (⟨⟨⟩⟩ : affine_coord_space ℝ n
            _)    
    ⟩
def euclideanGeometryTransform.fromalgebra
    {n : ℕ }  
    {sp : euclideanGeometry n}
    (from_ : euclideanGeometryFrame sp)
    (to_ : euclideanGeometryFrame sp) 
    (tr : affine_coord_frame_transform ℝ n from_.algebra to_.algebra)
    : euclideanGeometryTransform from_ to_ :=
    ⟨tr⟩

attribute [reducible]
def euclideanGeometryTransform.algebra 
    {n : ℕ }  
    {sp : euclideanGeometry n}
    {from_ : euclideanGeometryFrame sp}
    {to_ : euclideanGeometryFrame sp}
    (tr : euclideanGeometryTransform from_ to_)
    :=
    tr.tr

--attribute [reducible]
structure euclideanGeometryAngle
    {n : ℕ }
    (sp : euclideanGeometry n) :=
    (val : vector ℝ 1)

def euclideanGeometryAngle.build
    {n : ℕ }
    (sp : euclideanGeometry n) 
    (val : vector ℝ 1)
    : euclideanGeometryAngle sp
    :=
    euclideanGeometryAngle.mk val

def euclideanGeometryAngle.fromalgebra
    {n : ℕ }
    (sp : euclideanGeometry n) 
    (a: euclidean.affine_euclidean_space.angle) 
    : euclideanGeometryAngle sp
    :=
    euclideanGeometryAngle.mk ⟨[a.val],rfl⟩

attribute [reducible]
def euclideanGeometryAngle.algebra 
    {n : ℕ }
    {sp : euclideanGeometry n}
    {a : euclideanGeometryAngle sp}
    : euclidean.affine_euclidean_space.angle
    :=
    ⟨a.val.nth 0⟩


--attribute [reducible]
structure euclideanGeometryOrientation
    {n : ℕ }
    (sp : euclideanGeometry n) :=
    (o : eucl_lib.affine_euclidean_orientation n)
   -- (val : vector ℝ 1)

def euclideanGeometryOrientation.build
    {n : ℕ }
    (sp : euclideanGeometry n)
    (v : vector (vector ℝ n) n)
    : euclideanGeometryOrientation sp
    := ⟨⟨λ i, affine_coord_space.mk_tuple_vec (v.nth i),sorry,sorry⟩⟩


def euclideanGeometryOrientation.fromalgebra
    {n : ℕ }
    (sp : euclideanGeometry n)
    (or: eucl_lib.affine_euclidean_orientation n) 
    : euclideanGeometryOrientation sp
    :=
    euclideanGeometryOrientation.mk or

attribute [reducible]
def euclideanGeometryOrientation.algebra 
    {n : ℕ }
    (sp : euclideanGeometry n)
    (a : euclideanGeometryOrientation sp)
    : eucl_lib.affine_euclidean_orientation n
    :=
    a.o

structure euclideanGeometryRotation
    {n : ℕ }
    (sp : euclideanGeometry n) :=
    (r : eucl_lib.affine_euclidean_rotation n)
   -- (val : vector ℝ 1)

def euclideanGeometryRotation.build
    {n : ℕ }
    (sp : euclideanGeometry n)
    (v : vector (vector ℝ n) n)
    : euclideanGeometryRotation sp
    :=
    euclideanGeometryRotation.mk ⟨λ i, affine_coord_space.mk_tuple_vec (v.nth i),sorry,sorry⟩

def euclideanGeometryRotation.fromalgebra
    {n : ℕ }
    (sp : euclideanGeometry n)
    (r : eucl_lib.affine_euclidean_rotation n)
    : euclideanGeometryRotation sp
    :=
    euclideanGeometryRotation.mk r

attribute [reducible]
def euclideanGeometryRotation.algebra 
    {n : ℕ }
    (sp : euclideanGeometry n)
    (a : euclideanGeometryRotation sp)
    : eucl_lib.affine_euclidean_rotation n
    :=
    a.r
    
attribute [reducible]
def geom_vec_plus_vec
    {n : ℕ }
    {sp : euclideanGeometry n}
    {fr : euclideanGeometryFrame sp} : 
    euclideanGeometryCoordinateVector fr → 
    euclideanGeometryCoordinateVector fr → 
    euclideanGeometryCoordinateVector fr := 
    λ (v1 v2 : _), 
        let add_ : aff_coord_vec ℝ n fr.algebra := (v1.algebra +ᵥ v2.algebra) in
        euclideanGeometryCoordinateVector.fromalgebra fr add_


attribute [reducible]
def geom_vec_plus_pt
    {n : ℕ }
    {sp : euclideanGeometry n}
    {fr : euclideanGeometryFrame sp} : 
    euclideanGeometryCoordinateVector fr → 
    euclideanGeometryCoordinatePoint fr → 
    euclideanGeometryCoordinatePoint fr := 
    λ (v p : _), euclideanGeometryCoordinatePoint.fromalgebra fr (v.algebra +ᵥ p.algebra)
attribute [reducible]
def geom_pt_plus_vec
    {n : ℕ }
    {sp : euclideanGeometry n}
    {fr : euclideanGeometryFrame sp} : 
    euclideanGeometryCoordinatePoint fr → euclideanGeometryCoordinateVector fr → euclideanGeometryCoordinatePoint fr := 
    λ (p v : _), geom_vec_plus_pt v p
attribute [reducible]
def geom_scalar_mul_vec 
    {n : ℕ }
    {sp : euclideanGeometry n}
    {fr : euclideanGeometryFrame sp} : 
    ℝ → euclideanGeometryCoordinateVector fr → euclideanGeometryCoordinateVector fr :=
    λ (s v), euclideanGeometryCoordinateVector.fromalgebra fr (s•v.algebra)
attribute [reducible]
def geom_vec_mul_scalar
    {n : ℕ }
    {sp : euclideanGeometry n}
    {fr : euclideanGeometryFrame sp} : 
    euclideanGeometryCoordinateVector fr → ℝ → euclideanGeometryCoordinateVector fr :=
    λ (v s), euclideanGeometryCoordinateVector.fromalgebra fr (s•v.algebra)
attribute [reducible]
def geom_vec_minus_vec
    {n : ℕ }
    {sp : euclideanGeometry n}
    {fr : euclideanGeometryFrame sp} : 
    euclideanGeometryCoordinateVector fr → euclideanGeometryCoordinateVector fr → euclideanGeometryCoordinateVector fr := 
    λ (v1 v2 : _), euclideanGeometryCoordinateVector.fromalgebra fr (v1.algebra+ᵥ(-v2.algebra))
attribute [reducible]
def geom_pt_minus_vec
    {n : ℕ }
    {sp : euclideanGeometry n}
    {fr : euclideanGeometryFrame sp} : 
    euclideanGeometryCoordinatePoint fr → euclideanGeometryCoordinateVector fr → euclideanGeometryCoordinatePoint fr := 
    λ (p v : _), euclideanGeometryCoordinatePoint.fromalgebra fr ((-v.algebra)+ᵥp.algebra)
attribute [reducible]
def geom_trans_apply_vec
    {n : ℕ }
    {sp : euclideanGeometry n}
    {from_ : euclideanGeometryFrame sp}
    {to_ : euclideanGeometryFrame sp} :
    euclideanGeometryTransform from_ to_ → euclideanGeometryCoordinateVector from_ → euclideanGeometryCoordinateVector to_ :=
    λ t v, euclideanGeometryCoordinateVector.fromalgebra to_ 
        ((t.algebra (v.algebra +ᵥ (pt_zero_coord ℝ n from_.algebra))) -ᵥ (pt_zero_coord ℝ n to_.algebra))

attribute [reducible]
def geom_trans_compose
    {n : ℕ }
    {sp : euclideanGeometry n}
    {from_ : euclideanGeometryFrame sp}
    {inner_ : euclideanGeometryFrame sp}
    {to_ : euclideanGeometryFrame sp} :
    euclideanGeometryTransform from_ inner_ → euclideanGeometryTransform inner_ to_ → euclideanGeometryTransform from_ to_ :=
    λ t1 t2, ⟨t1.algebra.trans t2.algebra⟩


notation v+v := geom_vec_plus_vec v v
notation v+p := geom_vec_plus_pt v p
notation p+v := geom_pt_plus_vec p v
notation s•v := geom_scalar_mul_vec s v
notation v•s := geom_vec_mul_scalar v s
notation v-v := geom_vec_minus_vec v v
notation p-v := geom_pt_minus_vec p v
notation t⬝v := geom_trans_apply_vec v 
notation t1∘t2 := geom_trans_compose t1 t2
