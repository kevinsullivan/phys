import ..math.affnKcoord.affnKcoord_std
import data.real.basic

--configure field here
abbreviation scalar := ℚ
abbreviation real_scalar := ℝ

/-
enforce constraint here 
(and up the stack - but to make it immediately clear when you do something bad)
-/
instance : inhabited scalar := by apply_instance
instance : field scalar := by apply_instance