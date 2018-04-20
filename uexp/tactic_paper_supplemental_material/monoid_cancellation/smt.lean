import .monoid
local infix * := star

-- necessary instances for the AC support in the SMT state

instance : is_associative _ star :=
⟨star_assoc⟩

instance : is_commutative _ star :=
⟨star_comm⟩
