import .core

open tactic

meta def pre {α : Type}
    (st : α)
    (lemmas : simp_lemmas)
    (rel : name)
    (parent : option expr)
    (subterm : expr) : tactic (α × expr × option expr × bool) :=
do trace subterm,
   ty ← infer_type subterm,
   ue ← mk_const `uexp,
   if ty = ue
   then do (subterm', prf) ← lemmas.rewrite subterm (do trace "here", trace_state) `uexp.eq,
            trace subterm',
            trace prf,
            return (st, subterm', prf, ff) -- stop processing here
    else return (st, subterm, none, tt)

meta def post {α : Type} (st : α) (lemmas : simp_lemmas) (rel : name) (parent : option expr) (subterm : expr) : tactic (α × expr × option expr × bool) :=
return (st, subterm, none, ff)

-- apply uexp.eq.trans,
--     apply uexp.eq.mul_distr,
--     apply uexp.eq.trans,
--     apply uexp.eq.add_comm,
--     apply uexp.eq.trans,
--     apply uexp.eq.add_func,
--     apply uexp.eq.mul_comm,
--     apply uexp.eq.refl

@[simp] lemma my_add_comm : forall (e1 e2 : uexp),
  uexp.eq (uexp.plus e1 e2) (uexp.plus e2 e1) := by admit

meta def uexp_simp (e : expr) : tactic (expr × expr) :=
do lemmas ← simp_lemmas.mk.add_simp `my_add_comm,
  -- lemmas ← simp_lemmas.add_simp lemmas `uexp.eq.mul_distr,
   -- lemmas ← simp_lemmas.add_simp lemmas `uexp.eq.add_func,
   -- lemmas ← simp_lemmas.add_simp lemmas `uexp.eq.mul_comm,
   ((), opt_e, opt_prf) ← ext_simplify_core () {} lemmas (fun _, return ()) pre post `uexp.eq e,
   return (opt_e, opt_prf)

meta def usimp : tactic unit :=
do tgt ← target,
   let rel := tgt.get_app_fn,
   let args := tgt.get_app_args,
   if rel.const_name = `uexp.eq
   then match args with
   | lhs::rhs::_ :=
     do (new_tgt, prf) ← uexp_simp lhs,
        trace new_tgt,
        trace prf,
        fail "foo"
   | _ := fail "inv problem"
   end
   else fail "unable to simplify"

