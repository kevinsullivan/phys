def quantity := ℕ 

inductive quant_var : Type
| mk (n : ℕ)

def Q1 := quant_var.mk 0 
def Q2 := quant_var.mk 1

/------/

inductive PhysL : Type
| quantity_lit_expr (amt : quantity)
| quantity_var_expr (v: quant_var)
| quantity_add_expr  (v1 v2: PhysL)

-- Literal expressions
def P1 := PhysL.quantity_lit_expr 120
def P2 := PhysL.quantity_lit_expr 75

-- variable expressions

def P3 := PhysL.quantity_var_expr Q1
def P4 := PhysL.quantity_var_expr Q2

-- addition expressions

def P5 := PhysL.quantity_add_expr P1 P3

/-- Semantics --/


/- Interpretation -/

def default_interp : quant_var → ℕ := λ q, 0


def PhysL_eval : PhysL → (quant_var → ℕ) → ℕ 
| (PhysL.quantity_lit_expr amt) _ := amt
| (PhysL.quantity_var_expr v) i := i v
| (PhysL.quantity_add_expr e1 e2) i := nat.add (PhysL_eval e1 i) (PhysL_eval e2 i)

#reduce PhysL_eval P5 default_interp



