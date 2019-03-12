import analysis.real

inductive space : Type
| mk (id : ℕ) : space 

abbreviation scalar := ℕ 

inductive vector : space → Type 
| mkVector : Π s : space, scalar → scalar → scalar → vector s

def add { s : space } (v1 v2 : vector s) : vector s :=
    vector.mkVector s 0 0 0

