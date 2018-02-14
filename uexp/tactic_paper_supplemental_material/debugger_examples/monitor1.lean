import ..nano_crush.nano_crush
open vm

meta def ts_from_current_frame_aux : nat → nat → vm tactic_state
| p top := do
  guard (p < top),
  obj ← stack_obj p,
  if obj.kind = vm_obj_kind.tactic_state
  then return obj.to_tactic_state
  else ts_from_current_frame_aux (p+1) top

meta def ts_from_current_frame : vm tactic_state :=
do csz       ← call_stack_size,
   guard (csz > 0),
   (bp, top) ← call_stack_var_range (csz - 1),
   ts_from_current_frame_aux bp top

meta def trace_step (p : tactic_state → name → bool) (sz : nat) : vm nat :=
do curr_sz ← call_stack_size,
   guard (sz ≠ curr_sz),
   ts      ← ts_from_current_frame,
   fn      ← curr_fn,
   when (p ts fn) $ do {
       put_str $ "tactic state at " ++ to_string fn ++ "\n",
       put_str $ to_string ts,
       put_str "\n----------\n"
   },
   return curr_sz

@[vm_monitor]
meta def my_vm_monitor : vm_monitor nat :=
{ init := 0, step := trace_step (λ s fn, fn = `nano_crush.search) }

set_option debugger true

inductive exp : Type
| Const (n : nat) : exp
| Plus (e1 e2 : exp) : exp
| Mult (e1 e2 : exp) : exp

open exp

def eeval : exp → nat
| (Const n)    := n
| (Plus e1 e2) := eeval e1 + eeval e2
| (Mult e1 e2) := eeval e1 * eeval e2

def times (k : nat) : exp → exp
| (Const n)    := Const (k * n)
| (Plus e1 e2) := Plus (times e1) (times e2)
| (Mult e1 e2) := Mult (times e1) e2

def reassoc : exp → exp
| (Const n)    := (Const n)
| (Plus e1 e2) :=
  let e1' := reassoc e1 in
  let e2' := reassoc e2 in
  match e2' with
  | (Plus e21 e22) := Plus (Plus e1' e21) e22
  | _              := Plus e1' e2'
  end
| (Mult e1 e2) :=
  let e1' := reassoc e1 in
  let e2' := reassoc e2 in
  match e2' with
  | (Mult e21 e22) := Mult (Mult e1' e21) e22
  | _              := Mult e1' e2'
  end

attribute [simp] mul_add

theorem eeval_times (k e) : eeval (times k e) = k * eeval e :=
by nano_crush
