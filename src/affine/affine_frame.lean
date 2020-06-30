import .aff_coord_space linear_algebra.basis
import data.list.zip

universes u v w

variables (K : Type u) (n : ℕ)
[field K] [inhabited K]

structure frame :=
(orig : aff_pt K n)
(basis : fin n → aff_vec K n)
(lin_indep : linear_independent K basis)

#print fin

def std_origin : aff_pt K n := pt_zero K n

open list
def list.std_basis : fin n → list K
| ⟨m, _⟩ := update_nth (field_zero K m) (m+1) 1

def std_basis : fin n → aff_vec K n
| ⟨m, _⟩ := ⟨list.std_basis K n ⟨m, _x⟩, sorry, sorry⟩

theorem std_basis_li : linear_independent K (std_basis K n) := sorry

def std_frame : frame K n := ⟨std_origin K n, std_basis K n, std_basis_li K n⟩