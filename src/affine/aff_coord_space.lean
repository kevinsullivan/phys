import affine.affine affine.list_stuff
import data.list.zip data.real.basic

universes u v w

variables (X : Type u) (K : Type v) (V : Type w) (n : ℕ) (id : ℕ)
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space X K V]

open list

/-- type class for affine vectors. This models n-1 dimensional K-coordinate space. -/
structure aff_vec :=
(l : list K)
(len_fixed : l.length = n + 1)
(fst_zero : head l = 0)


/-
-- Note: Preceding definition equivalent to the following.
-- Just a notational difference to avoid nested <<>,_>s
def vec_list := { l : vector K n // head l.1 = 0 }
def v1 : vec_list ℝ 3 := ⟨ ⟨[0,1,2], rfl⟩, sorry ⟩
def v2 : vec_list ℝ 3 := ⟨ ⟨[0,3,-2], rfl⟩, sorry ⟩
#check @vec_list
-/

/-- type class for affine points for coordinate spaces. -/
structure aff_pt :=
(l : list K)
(len_fixed : l.length = n + 1)
(fst_one : head l = 1)


variables (x y : aff_vec K n) (a b : aff_pt K n)

-- lemmas so that the following operations are well-defined

/-- the length of the sum of two length n+1 vectors is n+1 -/
lemma list_sum_fixed : length (x.1 + y.1) = n + 1 := 
    by simp only [sum_test K x.1 y.1, length_sum x.1 y.1, x.2, y.2, min_self]

/-- head is compatible with addition -/
lemma head_sum : head x.1 + head y.1 = head (x.1 + y.1) := 
begin
cases x,
cases y,
cases x_l,
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm nil_len) x_len_fixed,
    contradiction,
cases y_l,
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm nil_len) y_len_fixed,
    contradiction,
have head_xh : head (x_l_hd :: x_l_tl) = x_l_hd := rfl,
have head_yh : head (y_l_hd :: y_l_tl) = y_l_hd := rfl,
rw head_xh at x_fst_zero,
rw head_yh at y_fst_zero,
simp [x_fst_zero, y_fst_zero, sum_test, add_cons_cons 0 0 x_l_tl y_l_tl],
end

/-- the head of the sum of two vectors is 0 -/
lemma sum_fst_fixed : head (x.1 + y.1) = 0 := by simp [eq.symm (head_sum K n x y), x.3, y.3]

/-- the length of the zero vector is n+1 -/
lemma len_zero : length (field_zero K n) = n + 1 :=
begin
induction n with n',
refl,
{
have h₃ : nat.succ (n' + 1) = nat.succ n' + 1 := rfl,
have h₄ : length (field_zero K (nat.succ n')) = nat.succ (n' + 1) :=
    by {rw eq.symm n_ih, refl},
rw eq.symm h₃,
exact h₄,
}
end

/-- the head of the zero vector is zero -/
lemma head_zero : head (field_zero K n) = 0 := by {cases n, refl, refl}

lemma len_neg : length (neg K x.1) = n + 1 := sorry -- following proof is unfinished
/-
begin
cases x,
induction n,
cases x_l,

have f : 0 ≠ 1 := zero_ne_one,
have bad := eq.trans (eq.symm nil_len) x_len_fixed,
contradiction,
end
-/

lemma head_neg_0 : head (neg K x.1) = 0 :=
begin
cases x,
cases x_l,

have f : 0 ≠ 1 := zero_ne_one,
have bad := eq.trans (eq.symm nil_len) x_len_fixed,
contradiction,

rw neg_cons K x_l_hd x_l_tl,
have head_xh : head (x_l_hd :: x_l_tl) = x_l_hd := rfl,
have head_0 : head (0 :: neg K x_l_tl) = 0 := rfl,
rw head_xh at x_fst_zero,
simp only [x_fst_zero, neg_zero, head_0],
end

-- abelian group operations

def vec_add : aff_vec K n → aff_vec K n → aff_vec K n :=
    λ x y, ⟨x.1 + y.1, list_sum_fixed K n x y, sum_fst_fixed K n x y⟩

def vec_zero : aff_vec K n := ⟨field_zero K n, len_zero K n, head_zero K n⟩

def vec_neg : aff_vec K n → aff_vec K n
| ⟨l, len, fst⟩ := ⟨list.neg K l, len_neg K n ⟨l, len, fst⟩, head_neg_0 K n ⟨l, len, fst⟩⟩ -- TODO: write out lemmata for these sorrys



-- type class instances for the abelian group operations
instance : has_add (aff_vec K n) := ⟨vec_add K n⟩
instance : has_zero (aff_vec K n) := ⟨vec_zero K n⟩
instance : has_neg (aff_vec K n) := ⟨vec_neg K n⟩



-- properties necessary to show aff_vec K n is an instance of add_comm_group
#print add_comm_group

lemma vec_add_assoc : ∀ x y z : aff_vec K n,  x + y + z = x + (y + z) := sorry

lemma vec_zero_add : ∀ x : aff_vec K n, 0 + x = x := sorry

lemma vec_add_zero : ∀ x : aff_vec K n, x + 0 = x := sorry

lemma vec_add_left_neg : ∀ x : aff_vec K n, -x + x = 0 := sorry

lemma vec_add_comm : ∀ x y : aff_vec K n, x + y = y + x := sorry

instance : add_comm_group (aff_vec K n) :=
begin
split,
exact vec_add_left_neg K n,
exact vec_add_comm K n,
exact vec_add_assoc K n,
exact vec_zero_add K n,
exact vec_add_zero K n,
end


-- need to define scalar multiplication to show it's a module
instance : vector_space K (aff_vec K n) := sorry


-- WTS the pair aff_vec and aff_pt form an affine space
instance : affine_space (aff_pt K n) K (aff_vec K n) := sorry

-- Different file, physical quantities
/-
def time' := space.mk 1
def geom3 := space.mk 2

def duration := aff_vec ℝ 1 time'
def time     := aff_pt  ℝ 1 time'

noncomputable def std_origin : time := ⟨[1, 0], rfl, rfl⟩

def length   := aff_vec ℝ 3 geom3
def phys_pt  := aff_pt  ℝ 3 geom3
-/
