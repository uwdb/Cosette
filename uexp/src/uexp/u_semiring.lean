-- definition of u-semiring
constant usr : Type
constant plus : usr → usr → usr
constant time : usr → usr → usr
constant zero : usr
constant one : usr
constant sig : (string → usr) → usr -- is that right?
-- TODO: define sig

local infix * := time
local infix + := plus

-- commutative semiring axioms
axiom plus_comm (a b : usr) :       a + b = b + a
axiom plus_zero (a : usr) :         a + zero = a
axiom plus_assoc (a b c : usr) :    a + b + c = a + (b + c)
axiom time_comm (a b c : usr) :     a * b * c =  a * (b * c)
axiom time_assoc_l (a b c : usr) :    a * (b + c) = a * b + a * c 
axiom time_assoc_r (a b c : usr) :    (a + b) * c = a * c + b * c
axiom time_zero (a : usr): a * zero = zero

