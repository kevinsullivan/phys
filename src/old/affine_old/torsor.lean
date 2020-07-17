import topology.basic 
import group_theory.group_action
import topology.instances.real 
import topology.algebra.group
import .add_group_action

-- Charlie Conneen, May 2020
-- TODO: implement additive and multiplicative torsors separately.

/-
Homogeneous spaces defined by a group acting transitively on a topological space

Could add definition specifically for manifolds; might make construction easier later
-/

/-- The class of homogeneous spaces. Traditionally, a `torsor`, or `principal homogeneous space`, is
    built up from homogeneous spaces. This is a nice way of doing things from a mathlib perspective,
    because it treats the construction more generally. α is a topological space (points), β is a
    group acting on those points.
-/
class homogeneous_space (α β : Type*)
  [topological_space α] [group β]
  extends inhabited α:=
(act : α → β → α) -- action on the right by the group
(act_id : ∀ x : α, act x (1 : β) = x) -- the group action obeys the identity
(act_comp : ∀ (x : α) (a b : β), act (act x a) b = act x (a*b)) -- the group action is compatible
(act_trans : ∀ a b : α, ∃ g : β, act a g = b) -- the action is transitive

infix ⬝ := homogeneous_space.act -- notation for the action

-- A principal homogeneous space is a homogeneous space in which the action by G is free.
-- this is also called a torsor.
class torsor'' (α β : Type*)
  [topological_space α] [group β]
  extends homogeneous_space α β :=
(act_free : ∀ x y : β, (∃ a : α, a ⬝ x = a ⬝ y) → x = y)

/-- The class of homogeneous spaces, defined in reference to group action. This construction is
    currently inaccurate for our uses, because with vector spaces, we want to act by addition, but
    mathlib currently has group action only in terms of multiplication. We could still do things in
    this way, but we would have to split torsors into "additive torsors" and
    "multiplicative torsors"
-/
class homogeneous_space' (G X : Type*) [topological_space X] [group G]
  extends mul_action G X :=
(act_trans : ∀ a b : X, ∃ g : G, g • a = b)

def stab (G X : Type*) (x : X)
  [group G] [mul_action G X] : set G :=
{g : G | g • x = x}

/-- torsors, but built up from homogeneous spaces, where the statement "the action is free" is
    restated in terms of an equivalent condition: namely, by saying the stabilizer at any point
    is trivial
-/
class torsor' (G X : Type*) [topological_space X] [group G]
  extends homogeneous_space' G X :=
(act_free : ∀ x : X, stab G X x = {(1 : G)})

/-- the torsor class. Currently X is an arbitrary type, and the element in the existential
    quantifier is not unique. We can change that easily, but it changes how some proofs work below.
-/
class torsor (G X : Type*) [add_group G] --[topological_space X]
  extends add_action G X :=
(free_trans_action : ∀ a b : X, ∃ g : G, g ⊹ a = b)
/-  currently omitted the "free" part. Will need to be changed when affine spaces aren't just vector
    spaces over themselves, because the uniqueness of that vector is required for defining a
    subtraction function on points.
-/


/-  TODO:
    ℝ is a torsor over itself (DONE)
    affine space construction (NEEDS MORE VERSIONS)
    ℝ^n a vector space over itself (NEED TO IMPLEMENT INDUCTIVE PROD)
    elements of ℝ^n (probably n=3), and example operations on them
-/


/-- instantiating the preorder topology on ℝ. In the event that, in the definition of torsor, we
    want X to be a topological space, this will allow us to construct torsors over the reals with
    the topology that we like.
-/
instance : topological_space ℝ := preorder.topology ℝ

#check real.add_group


/-- the following two instances allow for fields to be torsors over themselves, with the action
    being addition.
-/
instance field.has_trans (K : Type*) [field K] : has_trans K K := ⟨has_add.add⟩
instance field.add_action (K : Type*) [field K] : add_action K K := ⟨zero_add, add_assoc⟩

/-- the ℝ version of the above two instances-/
instance : has_trans ℝ ℝ := ⟨has_add.add⟩
instance : add_action ℝ ℝ := ⟨zero_add, add_assoc⟩

/-- An affine space defined as a torsor over a vector space. No difference function implemented,
    because we can readily construct a difference function (either from the vector space structure,
    or the fact that the action is free)
-/
abbreviation affine_space (K V : Type*)
  [field K] [add_comm_group V] [vector_space K V] :=
torsor V V

/-
  A little bit of context for the direction of this code:

  V acts on itself by addition. We treat the first V in "torsor V V" as vectors (additive group)
  *acting* on the second V, which we consider "points". This is a nice way of doing things because
  our spaces G and X need to be isomorphic in the case affine spaces, and this is implicit here in
  that G and X are both the same object, V. However, this means that Lean does not treat vectors
  differently from points in some clear sense, you just have to pretend that your vector is acting
  on a point and not another vector.

  In essence, to get around this, we would have to construct a forgetful functor from `vec` to
  `Set`. This is tricky, because we don't want to be redundant and essentially redefine what it
  means to be a vector space.

  For those of you unfamiliar with category theory, by "forgetful functor" just think of a function
  that carries vector spaces to sets by taking away the vector space structure, and just leaving a
  collection of objects called points. In doing so, we would be able to not just stoically consider
  vectors "just points," but concretely construct a difference between points and vectors.

  The other, more practical direction this could take is to just define points as n-tuples, although
  this would make for a loss of generality. We would be unable to work with anything other than
  coordinate spaces.
-/

/-- the `difference` function for affine spaces. This carries two vectors (which we treat as points)
    to the vector that carries one to the other
-/
def affine_space.diff (K V : Type*)
    [field K] [add_comm_group V] [vector_space K V] [affine_space K V] :
  V → V → V :=
λ a b, b-a

/-
  The difference function above is really nice, but it's only nice because we already have vector
  subtraction. Luckily, even if we don't have this structure, we can easily construct a subtraction
  from the existence of a unique vector carrying one point to the other. Namely, we just map b-a to
  that vector.
-/

namespace field

/-- Any field is a torsor over itself -/
instance to_torsor (K : Type*) [field K] : torsor K K :=
begin
  split,
  intros,
  apply exists.intro (b-a),
  exact sub_add_cancel b a,
end

/-- Any field is an affine space over itself -/
instance to_affine (K : Type*) [field K] : affine_space K K :=
begin
  split,
  intros,
  apply exists.intro (b-a),
  exact sub_add_cancel b a,
end

end field

namespace real

/-- ℝ is a torsor over itself-/
noncomputable instance to_torsor : torsor ℝ ℝ := field.to_torsor ℝ
/-- ℝ is an affine space over itself -/
noncomputable instance to_affine : affine_space ℝ ℝ := real.to_torsor

end real

/-- ℝ is a vector space over itself -/
noncomputable instance : vector_space ℝ ℝ := field.to_vector_space
/-- ℝ^2 is a vector space over ℝ -/
noncomputable instance R2_vs : vector_space ℝ (ℝ × ℝ) := by split
/-- ℝ^3 is a vector space over ℝ -/
noncomputable instance R3_vs : vector_space ℝ (ℝ × ℝ × ℝ) := by split

/-- first step in defining functions on R^3 -/
def f : ℝ×ℝ×ℝ → ℝ×ℝ×ℝ := λ a, prod.mk a.1 (prod.mk a.2.2 a.2.1)

-- #eval f (prod.mk 3 (prod.mk 5 7))

def f' : ℤ×ℤ×ℤ → ℤ×ℤ×ℤ := λ z, prod.mk z.1 (prod.mk z.2.2 z.2.1)

#eval f' (prod.mk 1 (prod.mk 2 3))
-- cannot eval function outputs for f, just f'. Also, prod seems to be really messy.

notation please : ℤ×ℤ×ℤ := (1, (1, 1))

/- to show a map is linear from ℝ^3 to ℝ^3, we just neet to show it respects vector addition and
   scalar multiplication
-/
#check linear_map

/-  TODO:
    Inductive product of `n` copies of ℝ (or just any field K)
    Construct affine spaces in a way that explicitly states the properties of the diff function
     - could do this at the affine space level or the torsor level
     - test this out in both?
    construct the plane z=1 and show it is an affine space
-/

-- coordinate spaces. construct K^n
-- first constructor takes in a field K and returns "vector_space K K"
-- second constructor should take in K and "vector_space K K^n" and return "vector_space K K^{n+1}"

#check vector_space
