import .cancellation_solver
local infix * := star

open tactic expr

namespace opt

set_option eqn_compiler.max_steps 20000

meta def iter_right : tactic unit :=
do t ← target,
match t with
| `(%%a = o * %%b)             := apply `(@plus_unit_c %%a %%b)
| `((%%a * %%b) * %%c = %%d)   :=
  (apply `(@plus_assoc_c1 %%a %%b %%c %%d) >> iter_right) <|>
  (apply `(@plus_assoc_c2 %%a %%b %%c %%d) >> iter_right)
| `((%%a * %%b) = (%%c * %%d)) := apply `(@plus_cancel %%a %%b %%c %%d) >> reflexivity
| _                             := failed
end

meta def iter_left : tactic unit :=
do t ← target,
match t with
| `(o * %%a = %%b)             := apply `(@plus_unit_p %%a %%b)
| `((%%a * %%b) * %%c = %%d)   :=
  (apply `(@plus_assoc_p1 %%a %%b %%c %%d) >> iter_left) <|>
  (apply `(@plus_assoc_p2 %%a %%b %%c %%d) >> iter_left)
| _                             := iter_right <|> applyc `plus_comm_p >> iter_right
end

meta def cancel :=
iter_left <|> applyc `plus_comm_p >> iter_left

meta def solve :=
repeat $ reflexivity <|> cancel

end opt
