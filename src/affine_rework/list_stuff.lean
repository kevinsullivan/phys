import data.list.zip

open list

/-- Implements list addition coordinate-wise w.r.t. the addition function on the list entries. -/
instance (α : Type*) [has_add α] : has_add (list α) := ⟨zip_with has_add.add⟩

universe u
variables (K : Type u) [field K]

/-- returns list rep of 0 vector of given length. -/
def list.field_zero : ℕ → list K
| 0 := []
| (nat.succ n) := 0 :: (list.field_zero n)

/-- returns a list multiplied element-wise by a scalar. -/
def list.field_scalar : K → list K → list K
| x [] := []
| x (a :: l) := (x * a) :: (list.field_scalar x l)


-- TODO: implement list negation
#check map
