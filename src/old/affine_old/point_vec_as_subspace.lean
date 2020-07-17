import ..orig.n_K_tuple
import algebra.module 
import data.list.zip

open list

instance (α : Type*) [has_add α] : has_add (list α) := ⟨zip_with has_add.add⟩

abbreviation R3 := n_tuple ℝ 3

#eval [1, 2, 3] + [4, 5, 6]

def r2v := {l : R3 // ∃ x y : ℝ, l.1 = [0, x, y]}

/-- Lemma used to show that R3 has a notion of addition. -/
lemma sum_r3 : ∀ (x y : R3), length (x.1 + y.1) = 3
| ⟨[x₁, x₂, x₃], _⟩ ⟨[y₁, y₂, y₃], _⟩ := rfl

/-- Addition function on R3. -/
def vec_add_r3 : R3 → R3 → R3 := λ x y, ⟨x.1 + y.1, sum_r3 x y⟩

/-- Can now use the addition operator `+` on objects of type R3. -/
instance : has_add R3 := ⟨vec_add_r3⟩

lemma sum_r2v : ∀ (x y : r2v), ∃ a b : ℝ, (x.1 + y.1).1 = [0, a, b]
| ⟨⟨[x₁, x₂, x₃], _⟩, _⟩ ⟨⟨[y₁, y₂, y₃], _⟩, _⟩ := sorry

def r2_add : r2v → r2v → r2v := λ x y, ⟨x.1 + y.1, sorry⟩

instance : has_add r2v := ⟨r2_add⟩

lemma zero_works : ∃ x y : ℝ, [0,0,0] = [0,x,y] :=
begin
apply exists.intro (0 : ℝ),
apply exists.intro (0 : ℝ),
trivial,
end

def r2v_zero : r2v := ⟨⟨[0,0,0], rfl⟩, zero_works⟩

instance : has_zero r2v := ⟨r2v_zero⟩

lemma add_assoc_r2v : ∀ a b c : r2v, a+b+c = (a+b)+c := sorry

#print add_comm_group
instance : add_comm_group r2v := sorry

#print vector_space
instance : vector_space ℝ r2v := sorry
