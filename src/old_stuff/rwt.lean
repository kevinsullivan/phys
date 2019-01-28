/- ********************* -/
/- *** Machine World *** -/
/- ********************* -/

/-
The machine world is a world of
ordinary arithmetic expressions
with an operational semantics.
-/


-- a type of nat-indexed variables
inductive avar_m 
| mk: ℕ → avar_m

-- equality of variables
def avar_m_eq: avar_m → avar_m → bool
| (avar_m.mk n) (avar_m.mk m) := n = m

-- abstract syntax of expression language
inductive aexp_m
| alitexp_m: ℕ → aexp_m
| avarexp_m: avar_m → aexp_m 
| aaddexp_m: aexp_m → aexp_m → aexp_m
open aexp_m

-- equality of expressions
def aexp_m_eq: aexp_m → aexp_m → bool
| (alitexp_m n) (alitexp_m m) := m = n
| (avarexp_m v) (avarexp_m w) := avar_m_eq v w 
| (aaddexp_m e₁ e₂) (aaddexp_m e₃ e₄) := 
    (aexp_m_eq e₁ e₃) && (aexp_m_eq e₂ e₄)
| _ _ := ff

-- type of environment mapping variables to values 
def env_m := avar_m → ℕ 

-- environment update (models assignment to variable)
def update_m (e: env_m) (vₒ: avar_m) (n : ℕ) : env_m :=
  λ v, if (avar_m_eq v vₒ) then n else e v

-- operational semantics
def eval_m: aexp_m → env_m →  ℕ
| (alitexp_m n) env := n 
| (avarexp_m v) env := env v
| (aaddexp_m e1 e2) env := (eval_m e1 env) + (eval_m e2 env)



/- ****************** -/
/- *** Real World *** -/
/- ****************** -/


-- distance units
-- includes special value for "no units given"
inductive distunit_w
| no_unit : distunit_w
| m : distunit_w
| ft : distunit_w
open distunit_w

-- distance unit equality
def distunit_w_eq : distunit_w → distunit_w → bool
| no_unit no_unit := tt
| m m := tt
| ft ft := tt
| _ _ := ff

-- true iff distance unit is no_unit
def is_no_unit : distunit_w → bool 
| no_unit := tt
| _ := ff

-- frames of reference (including no_frame)
inductive frame_w
| no_frame : frame_w
| up : frame_w
| over : frame_w
open frame_w

-- frame equality
def frame_w_eq : frame_w → frame_w → bool
| no_frame no_frame := tt
| up up := tt
| over over := tt
| _ _ := ff

-- true iff a frame is no_frame
def is_no_frame : frame_w → bool 
| no_frame := tt
| _ := ff

/-
The "real" world in this case is a world of 
corresponding expressions that include units
and frames of reference.
-/

-- real-world variable
inductive avar_w 
| mk: ℕ → avar_w

-- real-world variable equality
def avar_eq: avar_w → avar_w → bool
| (avar_w.mk n) (avar_w.mk k) := n = k

-- real-world expressions (include unit and frame)
inductive aexp_w 
| alitexp_w: distunit_w → frame_w → ℕ → aexp_w 
| avarexp_w: distunit_w → frame_w → avar_w → aexp_w
| aaddexp_w: distunit_w → frame_w → aexp_w → aexp_w → aexp_w
open aexp_w


/- ********************** -/
/- *** Interpretation *** -/
/- ********************** -/


/-
An interpretation is a function from 
machine expressions to (unit, frame)
pairs. The pair, (no_unit, no_frame),
is the default image of an expression
under this mapping. We build up an
interpretation by overring tuples in
an interpretation function (yielding
an updated interpretation). 
-/

-- define rwt as unit-frame pair
def rwt := (distunit_w × frame_w)

-- optional interpretation of variables
def rwt_interp := aexp_m → /-option-/ rwt

-- default interpretation: (no_unit, no_frame)
def rwt_interp_empty : rwt_interp := λ e, (no_unit, no_frame)

-- tuple override for updating interpretation
def update_rwt 
  (i : rwt_interp) 
  (e : aexp_m) 
  (t : rwt) 
    : rwt_interp :=
      λ e₀, if aexp_m_eq e₀ e then t else i e₀


/- ****************************** -/
/- *** Inference and Checking *** -/
/- ****************************** -/

/-
Finally, we can infer missing RWT information from
context, and check for consistency of RWT information.

The idea is that we will lift machine expressions to
real-world expressions (which include real world unit
and frame information), inferring and filling in "no_" 
default unit and frame values based on context during 
the lifting operation when possible. For example, if we 
add an expression with no_unit to an expression with
unit = ft, we will infer ft for no_unit in the result.

If a conflict in RWT information is founding during
lifting, the lifting operation will fail.

The return value of the lifting operation is thus a 
pai: an option real-world expression along with a
new interpretation, in which any newly inferred real 
world type information is associated with machine
expressions. 
-/


-- lift machine variable to real-world variable
def lift_var_m: avar_m → avar_w
| (avar_m.mk n) := avar_w.mk n

-- lift expression machine expression to real-world (with unit, frame)
def lift_aexp_m (u: distunit_w) (d: frame_w): aexp_m → aexp_w 
| (alitexp_m n) := alitexp_w u d n
| (avarexp_m v) := avarexp_w u d (lift_var_m v)
| (aaddexp_m e₁ e₂) := aaddexp_w u d (lift_aexp_m e₁) (lift_aexp_m e₂) 

/-
The main routine. Given a machine aexp and and a "partial" 
interpretation, return "some" lifted aexp if the real world 
types given by the interpretation are compatible, along with a 
potentially extended interpretation where no_ values might be
replaced by inferred values, or "none if the real-world types
are simply incompatible, along with a potentially extended
interpretation that includes addition real-world type data
inferred up to the point where the conflict was detected.
-/
def interp_aexp_m : aexp_m → rwt_interp → ((option aexp_w) × rwt_interp)
| (alitexp_m n) i := (some (lift_aexp_m (i (alitexp_m n)).1 (i (alitexp_m n)).2 (alitexp_m n)), i)
| (avarexp_m v) i := (some (lift_aexp_m (i (avarexp_m v)).1 (i (avarexp_m v)).2 (avarexp_m v)), i)
| (aaddexp_m e₁ e₂) i := 
    let e₁_interp := i e₁ in
    let e₂_interp := i e₂ in 
    let e₁_unit := e₁_interp.1 in
    let e₁_frame := e₁_interp.2 in
    let e₂_unit := e₂_interp.1 in
    let e₂_frame := e₂_interp.2 in
    -- if rwts are same, proceed to lift
    if ((distunit_w_eq e₁_unit e₂_unit) ∧ (frame_w_eq e₁_frame e₂_frame))
    then (some (lift_aexp_m e₁_unit e₁_frame (aaddexp_m e₁ e₂)), i)
    -- else try to infer no_unit or no_frame from other arg
    else 
      let new_e₁_unit := if (is_no_unit e₁_unit) then e₂_unit else e₁_unit in 
      let new_e₂_unit := if (is_no_unit e₂_unit) then e₁_unit else e₂_unit in 
      let new_e₁_frame := if (is_no_frame e₁_frame) then e₂_frame else e₁_frame in 
      let new_e₂_frame := if (is_no_frame e₂_frame) then e₁_frame else e₂_frame in 
      let new_interp₁ := update_rwt i e₁ (new_e₁_unit, new_e₁_frame) in 
      let new_interp₂ := update_rwt new_interp₁ e₂ (new_e₂_unit, new_e₂_frame) in 
      -- and try again to lift, and if it fails return (none, new_interp₂)
      if ((distunit_w_eq new_e₁_unit new_e₂_unit) ∧ (frame_w_eq new_e₁_frame new_e₂_frame)) 
      then (some (lift_aexp_m new_e₁_unit new_e₁_frame (aaddexp_m e₁ e₂)),  new_interp₂)
      else (none, new_interp₂)


/- ********************* -/
/- *** Demonstration *** -/
/- ********************* -/

-- machine variables
def Xvar_m : avar_m := avar_m.mk 0
def Yvar_m : avar_m := avar_m.mk 1
def Zvar_m : avar_m := avar_m.mk 2
def Wvar_m : avar_m := avar_m.mk 3

-- machine variable expressions
def X_m : aexp_m := avarexp_m Xvar_m
def Y_m : aexp_m := avarexp_m Yvar_m
def Z_m : aexp_m := avarexp_m Zvar_m
def W_m : aexp_m := avarexp_m Wvar_m

-- interpretation for these exprs
def xy_interp := 
  update_rwt
    (update_rwt
      (update_rwt  
        (update_rwt 
          rwt_interp_empty 
          X_m (ft, up)) 
        Y_m (m, over))
      Z_m (ft, up))
    W_m (no_unit, over)

-- some machine-world "add" expressions
def S_m := aaddexp_m X_m Y_m
def T_m := aaddexp_m X_m Z_m 
def V_m := aaddexp_m Y_m W_m

-- attempts to "lift" machine expressions
def S_w := interp_aexp_m S_m xy_interp 
def T_w := interp_aexp_m T_m xy_interp 
def V_w := interp_aexp_m V_m xy_interp 

-- results 
#reduce S_w   -- rwt error, returns "none"
#reduce T_w   -- compatible types
#reduce V_w   -- infers m for W_m

/- *** DEMO: PID *** -/

