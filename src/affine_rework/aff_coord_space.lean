import affine_rework.affine affine_rework.list_stuff
import data.list.zip data.real.basic

universes u v w

structure space :=
(id : ℕ)

variables (X : Type u) (K : Type v) (V : Type w) (n : ℕ) (id : ℕ) (s : space)
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space X K V]

open list

/-- type class for affine vectors. This models n-1 dimensional K-coordinate space. -/
structure aff_vec (s : space) :=
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
structure aff_pt (s : space) :=
(l : list K)
(len_fixed : l.length = n + 1)
(fst_one : head l = 1)





-- lemmas so that the following operations are well-defined

lemma list_sum_fixed : ∀ (x y : aff_vec K n s), length (x.1 + y.1) = n + 1 := sorry

lemma sum_fst_fixed : ∀ (x y : aff_vec K n s),
      head (x.1 + y.1) = 0 := sorry -- note: + is from list_stuff (TODO: rename file)


-- abelian group operations

def vec_add {s: space} : aff_vec K n s → aff_vec K n s → aff_vec K n s :=
    λ x y, ⟨x.1 + y.1, list_sum_fixed K n s x y, sum_fst_fixed K n s x y⟩

def vec_zero : aff_vec K n s := ⟨field_zero K n, sorry, sorry⟩

def vec_neg : aff_vec K n s → aff_vec K n s
| ⟨l, len, fst⟩ := sorry -- TODO: plug in list neg impl


-- type class instances for the abelian group operations
instance : has_add (aff_vec K n s) := ⟨vec_add K n⟩
instance : has_zero (aff_vec K n s) := ⟨vec_zero K n s⟩
instance : has_neg (aff_vec K n s) := ⟨vec_neg K n s⟩




-- properties necessary to show aff_vec K n is an instance of add_comm_group
#print add_comm_group

lemma vec_add_assoc : ∀ x y z : aff_vec K n s,  x + y + z = x + (y + z) := sorry

lemma vec_zero_add : ∀ x : aff_vec K n s, 0 + x = x := sorry

lemma vec_add_zero : ∀ x : aff_vec K n s, x + 0 = x := sorry

lemma vec_add_left_neg : ∀ x : aff_vec K n s, -x + x = 0 := sorry

lemma vec_add_comm : ∀ x y : aff_vec K n s, x + y = y + x := sorry

instance : add_comm_group (aff_vec K n s) :=
⟨vec_add K n,
vec_add_assoc K n s,
vec_zero K n s,
vec_zero_add K n s, vec_add_zero K n s,
vec_neg K n s,
vec_add_left_neg K n,
vec_add_comm K n⟩


-- need to define scalar multiplication to show it's a module
instance : vector_space K (aff_vec K n s) := sorry


-- WTS the pair aff_vec and aff_pt form an affine space
instance : affine_space (aff_pt K n s) K (aff_vec K n s) := sorry

-- Different file, physical quantities

def time' := space.mk 1
def geom3 := space.mk 2

def duration := aff_vec ℝ 1 time'
def time     := aff_pt  ℝ 1 time'

noncomputable def std_origin : time := ⟨[0, 0], rfl, sorry⟩

def length   := aff_vec ℝ 3 geom3
def phys_pt  := aff_pt  ℝ 3 geom3
