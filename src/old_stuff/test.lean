example : ∀ n, n - n = 0 :=
begin
intro,
induction n,
apply rfl,
end