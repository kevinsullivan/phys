/-
We will start by summarizing the key features of the PID controller. The
“textbook” version of the PID algorithm is described by:
u(t) = K

e(t) + 1
Ti
Zt
0
e(τ )dτ + Td
de(t)
dt 
(6.1)



t is time
y is the measured process variable, 
r the reference variable, 
u is the control signal and 
e is the control error (e = ysp − y). 

u(t)


The reference
variable is often called the set point. The control signal is thus a sum of
three terms: the P-term (which is proportional to the error), the I-term
(which is proportional to the integral of the error), and the D-term (which
is proportional to the derivative of the error). The controller parameters
are proportional gain K, integral time Ti, and derivative time Td. The
integral, proportional and derivative part can be interpreted as control
actions based on the past, the present and the future as is illustrated
in Figure 2.2. The derivative part can also be interpreted as prediction
by linear extrapolation as is illustrated in Figure 2.2. The action of the
different terms can be illustrated by the following figures which show the
response to step changes in the reference value in a typical case.
-/

/-
representation of time
-/
def time_torsor := ℕ 
def time_origin := 0
def time_unit := 1

structure pid (α : Type) (t : Type) :=
mk ::
(y : t → α)
(r : t → α)
(u : t)
(e : t )
