-- You need to run this file using `lean -j0`, otherwise the timings
-- will be influenced by parallel compilation.

import .monoid .smt .simp .cancellation_solver .cancellation_solver_opt
local infix * := star

meta def build_plus_l : ℕ → expr
| 0     := `(asM 0)
| (n+1) := `(asM %%(reflect n.succ) * %%(build_plus_l n))

meta def build_plus_r : ℕ → expr
| 0     := `(asM 0)
| (n+1) := `(%%(build_plus_r n) * asM %%(reflect n.succ))

meta def benchmark (n : ℕ) : expr :=
`(%%(build_plus_l n) = (%%(build_plus_r n) : m))

open tactic monad

meta def run_single_bench (n : ℕ) (t : tactic unit) := run_async $ do
bench_goal ← mk_meta_var (benchmark n),
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
