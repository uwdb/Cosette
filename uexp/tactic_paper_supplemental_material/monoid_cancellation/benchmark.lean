-- You need to run this file using `lean -j0`, otherwise the timings
-- will be influenced by parallel compilation.

import .monoid .smt .simp .cancellation_solver .cancellation_solver_opt
local infix * := star

meta def build_plus_l : ℕ → tactic expr
| 0     := tactic.to_expr ``(asM 0)
| (n+1) := do x ← build_plus_l n,
        tactic.to_expr ``(asM %%(reflect n.succ) * %%x)

meta def build_plus_r : ℕ → tactic expr
| 0     := tactic.to_expr ``(asM 0)
| (n+1) := do 
     right ← build_plus_r n,
     tactic.to_expr ``(%%right * asM %%(reflect n.succ))

meta def x : pexpr := ``(1) 

#check tactic.to_expr

meta def benchmark (n : ℕ) : tactic expr :=
 do left ← build_plus_l n,
    right ← build_plus_r n,
    return `(%%left = (%%right : m))

open tactic monad

meta def run_single_bench (n : ℕ) (t : tactic unit) := run_async $ do
ty ← benchmark n,
bench_goal ← mk_meta_var ty,
set_goals [bench_goal],
dunfold [`benchmark, `build_plus_l, `build_plus_r],
timetac ("n = " ++ to_string n ++ ": ") (abstract t)

meta def run_benchs (solver_name : string) (t : tactic unit) :=
do trace solver_name, sequence' $ do
n ← list.range 11, n ← return (nat.mul 10 n),
[run_single_bench n t]

run_cmd run_benchs "simp" `[simp]
run_cmd run_benchs "smt" `[cc]
run_cmd run_benchs "cancellation_solver" `[solve]
run_cmd run_benchs "cancellation_solver_opt" `[opt.solve]
