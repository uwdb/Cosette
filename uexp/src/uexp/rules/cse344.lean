import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..cosette_tactics


open Expr
open Proj
open Pred
open SQL

section

parameter uid : datatype
parameter uname : datatype
parameter size : datatype
parameter city : datatype
parameter pid : datatype

parameter Usr : Schema
parameter usr : relation Usr
parameter usrUid : Column uid Usr
parameter usrUname : Column uname Usr
parameter usrCity : Column city Usr

parameter Pic : Schema
parameter pic : relation Pic
parameter picUid : Column uid Pic
parameter picSize : Column size Pic
parameter picPid : Column pid Pic

parameter denver : const city
parameter denverNonNull : null ≠ denver

parameter gt1000000 : Pred (tree.leaf size)
parameter gt3000000 : Pred (tree.leaf size)

parameter Γ : Schema

definition x'' : Proj (Γ ++ Usr) Usr := right
noncomputable definition x''' : Proj ((Γ ++ Usr) ++ Pic) Usr := left ⋅ right
noncomputable definition y'' : Proj ((Γ ++ Usr) ++ Pic) Pic := right
  
noncomputable definition x'''' : Proj (Γ ++ (Usr ++ Pic)) Usr := right ⋅ left
noncomputable definition y'''' : Proj (Γ ++ (Usr ++ Pic)) Pic := right ⋅ right

noncomputable definition leftOuterJoin {s0 s1 : Schema}
    (q0 : SQL Γ s0) (q1 : SQL Γ s1) (b : Pred (Γ ++ (s0 ++ s1)))
    : SQL Γ (s0 ++ s1)
    := SELECT * (FROM2 q0, q1) WHERE b

-- Precedence?
local notation q0 `LEFT` `OUTER` `JOIN` q1 `ON` b := leftOuterJoin q0 q1 b

theorem problem3 : sorry := sorry

end