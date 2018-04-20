constant m : Type
constant star : m → m → m
local infix * := star
constant o : m
axiom star_comm (a b : m) :    a * b = b * a
axiom star_assoc (a b c : m) : (a * b) * c = a * (b * c)
axiom one_star (a : m) :       o * a = a

axiom asM : nat → m /- Just a way to construct 'm's -/
