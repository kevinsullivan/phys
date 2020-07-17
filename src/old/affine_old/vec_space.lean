import group_theory.group_action

class vec_space (K V : Type*) [field K] extends has_add V, has_zero V, has_neg V, mul_action K V :=
(add_assoc : ∀ a b c : V, a + b + c = a + (b + c))
(zero_add : ∀ a : V, 0 + a = a) (add_zero : ∀ a : V, a + 0 = a)
(add_left_neg : ∀ a : V, -a + a = 0)
(add_comm : ∀ a b : V, a + b = b + a) -- V is an additive commutative group
(smul_add : ∀(r : K) (x y : V), r • (x + y) = r • x + r • y)
(add_smul : ∀ (r s : K) (x : V), (r + s) • x = r • x + s • x) -- distrib
(smul_zero : ∀ r : K, r • (0 : V) = 0)
(zero_smul : ∀ x : V, (0 : K) • x = 0) -- zero left and right

theorem vs_equiv_left (K V : Type*) [field K] [add_comm_group V] [vector_space K V] : vec_space K V :=
sorry

theorem vs_equiv_right (K V : Type*) [field K] [add_comm_group V] [vec_space K V] : vector_space K V :=
sorry
