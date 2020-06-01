import affine.orig.n_K_tuple
import algebra.module
import data.list.zip

open list

/-- allows pairwise list addition -/
instance (α : Type*) [has_add α] : has_add (list α) := ⟨zip_with has_add.add⟩

/-- R3 is the type of all lists of length 3 with entries in ℝ (implemented as the vector type) -/
abbreviation R3 := n_tuple ℝ 3
abbreviation Q3 := n_tuple ℚ 3

lemma vec_sum (α : Type*) (n : ℕ) [has_add α] : ∀ a b : vector α n, length (a.1 + b.1) = n :=
begin
  induction n,
  sorry,
  sorry,
end

/-- Lemma used to show that R3 has a notion of addition. -/
lemma sum_r3 : ∀ (x y : R3), length (x.1 + y.1) = 3
| ⟨[x₁, x₂, x₃], _⟩ ⟨[y₁, y₂, y₃], _⟩ := rfl

/-- same lemma but with Q3. -/
lemma sum_q3 : ∀ (x y : Q3), length (x.1 + y.1) = 3
| ⟨[x₁, x₂, x₃], _⟩ ⟨[y₁, y₂, y₃], _⟩ := rfl

/-- Addition function on R3. -/
def vec_add_r3 : R3 → R3 → R3 := λ x y, ⟨x.1 + y.1, sum_r3 x y⟩

/-- Addition function on Q3. -/
def vec_add_q3 : Q3 → Q3 → Q3 := λ x y, ⟨x.1 + y.1, sum_q3 x y⟩

/-- Can now use the addition operator `+` on objects of type R3. -/
instance : has_add R3 := ⟨vec_add_r3⟩

instance : has_add Q3 := ⟨vec_add_q3⟩
/-
  when constructing objects of type R3, you need to give a list of reals, and a proof that the list
  is of length 3. when explicitly writing out the list, the proof is immediate, so rfl solves it.
-/
def a : R3 := ⟨[1,2,3], rfl⟩
def b : R3 := ⟨[4,5,6], rfl⟩

-- the following two are equivalent, because vec_add is used as the addition operator on R3
#check a+b
#check vec_add_r3 a b

/-
  There is no computable way to create a real.to_string function. So if we wanted this to output
  [5, 7, 9], there's no way to do that. So when doing any computation, we should use n_tuple ℚ 3.
-/
#eval a+b
#eval (1.2 : ℚ) -- notice that ℚ has a representation. Useful for computation.

def x : Q3 := ⟨[1, 2, 3], rfl⟩
def y : Q3 := ⟨[4, 5, 6], rfl⟩

/--
  allows evaluations to output the list part of the resulting vector as a string. This cannot be
  done over the reals, because there is no computable instance of real.to_string
-/
instance : has_repr Q3 := ⟨λ x, x.1.to_string⟩

#eval x+y

/-- generic negative function on lists. Sends a list [a₁, a₂, ...] to [-a₁, -a₂, ...]-/
def list_neg (α : Type*) [has_neg α] : list α → list α
| [] := []
| (a :: ab) := (-a) :: list_neg ab

/-- list length of vectors stays the same sending them through the function `list_neg`-/
lemma neg_r3 : ∀ (x : R3), length (list_neg ℝ x.1) = 3
| ⟨[x₁, x₂, x₃], _⟩ := rfl

/-- function that takes a vector in R3 to its negative. -/
def r3_neg : R3 → R3 := λ x, ⟨list_neg ℝ x.1, neg_r3 x⟩

/-- can now represent negative vectors. -/
instance : has_neg R3 := ⟨r3_neg⟩

def r3_zero : R3 := ⟨[0,0,0], rfl⟩
/-- R3 has a zero element, the zero vector. -/
instance : has_zero R3 := ⟨r3_zero⟩

#print add_group

/-- WTS that adding x to the zero vector gives zero. -/
lemma r3_zero_add : ∀ x : R3, 0 + x = x := sorry

/-- WTs that adding the zero vector to x gives zero. -/
lemma r3_add_zero : ∀ x : R3, x + 0 = x := sorry
