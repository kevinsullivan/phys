
import data.matrix
import data.rat
import data.real.basic
import algebra.pi_instances

-- See https://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.vector.html
-- See https://hal.inria.fr/inria-00377431/document
-- See! http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.652.3183&rep=rep1&type=pdf


#print add_comm_group

#check vector   -- data.vector
#print vector
#print field

#check field

variable F : field ℝ 

def ℝspace' (n : ℕ) := fin n → ℝ
def ℝspace (n : ℕ) := (vector ℝ n)

#print add_comm_group

#print vector
#reduce vector

def v1 : vector ℕ 3 := subtype.mk [1,2,3] rfl
#print v1

#eval vector.nth v1 0

instance spacex (n : ℕ): add_comm_group (ℝspace n) := 
begin 
unfold ℝspace,
--apply_instance,
apply add_comm_group.mk,

-- inverses
intro v, 

end

#print vector_space

noncomputable instance (n : ℕ): vector_space ℝ (ℝspace n) := 
begin
dunfold ℝspace,
apply_instance,
end

variables (n : ℕ) (v w : ℝspace n) (r : ℝ)

#check v + w -- adding vectors
#check r • v -- scalar times vector


namespace real_affine_3space




/- ************** -/
/- *** Scalar *** -/
/- ************** -/

abbreviation scalar := ℕ 

/- ************* -/
/- *** Space *** -/
/- ************* -/

/-
1-D space over scalar values indexed by ℕ
-/

inductive space : Type
| mk (id : ℕ) : space 

def id_space (s : space) : ℕ :=
match s with
    | space.mk n := n
end

def eq_space (s1 s2: space) : bool :=
    match  s1, s2 with
    | (space.mk n1), (space.mk n2) := n1 = n2
    end

/- **************************** -/
/- *** point, vector, frame *** -/
/- **************************** -/

mutual inductive point, vector, frame
with point : ∀ s : space, Type
| mk_std : Π { s : space }, point s 
| mk : Π {s : space}, frame s → scalar → point s
with vector : ∀ (s : space), Type
| mk_std : Π { s : space }, vector s -- implicitly: std frame, std coord = 1
| mk : Π {s : space}, frame s → scalar → vector s
with frame : ∀ s : space, Type 
| mk_std : Π { s : space }, frame s -- implicit has std point and std vector
| mk : Π { s : space }, point s → vector s → frame s 


/- ************************ -/
/- *** Standard objects *** -/
/- ************************ -/

def is_std_vector { s : space } (v : vector s) : bool :=
match v with
    | vector.mk_std := tt
    | _ := ff
end

def is_std_frame { s : space } (f : frame s) : bool :=
match f with
    | frame.mk_std := tt
    | _ := ff
end

def is_std_point { s : space } (p : point s) : bool :=
match p with
    | point.mk_std := tt
    | _ := ff
end

/- **************** -/
/- *** Equality *** -/
/- **************** -/

mutual def eq_point, eq_frame, eq_vector
with eq_point : ∀ {s : space}, ∀ (p1 p2 : point s), bool
    | s point.mk_std point.mk_std := tt 
    | s (point.mk f1 c1) point.mk_std := (is_std_frame f1) ∧ (c1 = 0)
    | s point.mk_std (point.mk f2 c2) := (is_std_frame f2) ∧ (0 = c2)
    | s (point.mk f1 c1) (point.mk f2 c2) := (eq_frame f1 f2) ∧ (c1 = c2)
with eq_frame : ∀ { s : space } (f1 f2 : frame s), bool     
    | s frame.mk_std frame.mk_std := tt
    | s (frame.mk p1 v1) frame.mk_std := (is_std_point p1) ∧ (is_std_vector v1)
    | s frame.mk_std (frame.mk p2 v2) := (is_std_point p2) ∧ (is_std_vector v2)
    | s (frame.mk p1 v1) (frame.mk p2 v2) := (eq_point p1 p2) ∧ (eq_vector v1 v2)
with eq_vector: ∀ {s : space}, ∀ (v1 v2 : vector s), bool
    | s vector.mk_std vector.mk_std := tt 
    | s (vector.mk f1 c1) vector.mk_std :=  (is_std_frame f1) ∧ (c1 = 0)
    | s vector.mk_std (vector.mk f2 c2) := (is_std_frame f2) ∧ (0 = c2)
    | s (vector.mk f1 c1) (vector.mk f2 c2) := (eq_frame f1 f2) ∧ (c1 = c2)


#check eq_point

/- ****************** -/
/- *** Projection *** -/
/- ****************** -/

def frame_of_point {s : space} (p : point s) : frame s :=
match p with
    | point.mk_std := frame.mk_std
    | point.mk f c := f
end

def coord_of_point {s : space} (p : point s) : scalar :=
match p with
    | point.mk_std := 0
    | point.mk f c := c
end

def frame_of_vector {s : space} (v : vector s) : frame s :=
match v with
    | vector.mk_std := frame.mk_std
    | vector.mk f c := f
end

def coord_of_vector {s : space} (v : vector s) : scalar :=
match v with
    | vector.mk_std := 1
    | vector.mk f c := c
end

def point_of_frame {s : space} (f : frame s) : point s :=
match f with
    | frame.mk_std := point.mk_std
    | frame.mk p v := p
end

def vector_of_frame {s : space} (f : frame s) : vector s :=
match f with
    | frame.mk_std := vector.mk_std
    | frame.mk p v := v
end

/- ******************************************** -/
/- *** Change of coordinates to std. frame ***  -/
/- ******************************************** -/

def is_reduced_point { s : space} (p : point s) : bool :=
match p with
| point.mk_std := tt
| point.mk frame.mk_std c := tt
| _ := ff
end

def step_reduce_point { s : space } ( p : point s) : point s :=
match p with
    | point.mk_std := p
    | point.mk frame.mk_std c := p
    | point.mk (frame.mk o v) c := 
        -- o + c * b
        point.mk (frame_of_point o) ((coord_of_point o) + c * (coord_of_vector v))
end

def reduce_point : ∀ { s : space },  point s → point s 
| s p := if (is_reduced_point p) then p else p /-(reduce_point (step_reduce_point p)) FIX!!!-/


/- ****************** -/
/- *** Operations *** -/
/- ****************** -/

-- point - point : vector 
-- args and results must in same space, and, currently, frame
def point_point_sub {s : space} (p1 p2 : point s) : option (vector s) :=
    match p1, p2 with
    | (point.mk f1 c1), (point.mk f2 c2) := 
        if (eq_frame f1 f2) then vector.mk f1 (c1 - c2) else none
    | point.mk_std, point.mk_std := some vector.mk_std
    | _, _ := none
    end

-- scalar * vector : vector (result in same space and frame)
def scalar_vector_mult' {s : space} (a : scalar) (v : vector s) :=
    match v with
    | vector.mk_std := vector.mk frame.mk_std (1 * a)
    | vector.mk f c := vector.mk f (c * a) 
    end

-- vector + vector : vector (args, result in same space, frame)
def vector_vector_add {s : space } (v1 v2 : vector s) : option (vector s) :=
    match v1, v2 with
    | (vector.mk f1 c1), (vector.mk f2 c2) :=  
         if (eq_frame f1 f2) then some (vector.mk f1 (c1 + c2)) else none
    | vector.mk_std, (vector.mk f2 c2) :=       
        if (eq_frame f2 frame.mk_std) then some (vector.mk frame.mk_std (1 + c2)) else none 
    | (vector.mk f1 c1), vector.mk_std :=       
        if (eq_frame f1 frame.mk_std) then some (vector.mk frame.mk_std (c1 + 1)) else none 
    | (vector.mk_std), (vector.mk_std) :=  some (vector.mk frame.mk_std (1 + 1))
    end

--point + vector : point (args, result in same space, frame)
def point_vector_add {s : space } (p : point s) (v : vector s) : option (point s) :=
    match p, v with
    | (point.mk f1 c1), (vector.mk f2 c2) :=    
        if (eq_frame f1 f2) then some (point.mk f1 (c1 + c2)) else none
    | (point.mk f1 c1), (vector.mk_std) :=    
        if (eq_frame f1 frame.mk_std) then some (point.mk f1 (c1 + 1)) else none
    | (point.mk_std), (vector.mk f2 c2) :=    
        if (eq_frame frame.mk_std f2) then some (point.mk f2 (1 + c2)) else none
    | (point.mk_std), (vector.mk_std) :=    some (point.mk frame.mk_std (0 + 1))
    end

-- standard frame, vector, point on a space 
def std_frame (s: space) := @frame.mk_std s
def std_vector (s: space) := @vector.mk_std s
def std_point (s: space) := @point.mk_std s



end  real_affine_3space