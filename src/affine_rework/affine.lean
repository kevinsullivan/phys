import group_theory.group_action a_code.affine.add_group_action
import a_code.affine.g_space algebra.module

universes u v w
variables (X : Type u) (K : Type v) (V : Type w)
[field K] [add_comm_group V] [vector_space K V] [add_torsor X V]


abbreviation affine_space
  (X K V : Type*)
  [field K] [add_comm_group V] [vector_space K V] := add_torsor X V


def affine.diff : X → X → V := sorry

-- TODO: affine combinations, affine transformations, affine frames
