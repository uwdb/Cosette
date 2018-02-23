import .core

open tactic

meta def pre {α : Type} (st : α) (lemmas : simp_lemmas) (rel : name) (parent : option expr) (subterm : expr) : tactic (α × expr × option expr × bool) :=
do if rel = `uexp.eq
   then do trace subterm,
           trace "before rewrite",
           (subterm', prf) ← lemmas.rewrite subterm (do trace "here", trace_state) `uexp.eq,
           trace "after rewrite",
           trace_state,
           return (st, subterm', prf, ff)
   else tactic.fail "foo"

meta def post {α : Type} (st : α) (lemmas : simp_lemmas) (rel : name) (parent : option expr) (subterm : expr) : tactic (α × expr × option expr × bool) :=
-- do if rel = `related
--    then tactic.fail "triggered"
--    else tactic.fail "post does not match
    return (st, subterm, none, ff)

-- apply uexp.eq.trans,
--     apply uexp.eq.mul_distr,
--     apply uexp.eq.trans,
--     apply uexp.eq.add_comm,
--     apply uexp.eq.trans,
--     apply uexp.eq.add_func,
--     apply uexp.eq.mul_comm,
--     apply uexp.eq.refl

meta def uexp_simp (e : expr) : tactic (expr × expr) :=
do lemmas ← simp_lemmas.mk.add_simp `uexp.eq.add_comm,
   -- lemmas ← simp_lemmas.add_simp lemmas `uexp.eq.mul_distr,
   -- lemmas ← simp_lemmas.add_simp lemmas `uexp.eq.add_func,
   -- lemmas ← simp_lemmas.add_simp lemmas `uexp.eq.mul_comm,
   ((), opt_e, opt_prf) ← ext_simplify_core () {} lemmas (fun _, return ()) pre post `uexp.eq e,
   return (opt_e, opt_prf)

meta def usimp : tactic unit :=
do tgt ← target,
   (new_tgt, prf) ← uexp_simp tgt,
   trace new_tgt,
   trace prf,
   fail "yolo"

meta def unfold_all_denotations := `[
    repeat { unfold denoteSQL
            <|> unfold denotePred
            <|> unfold denoteProj
            <|> unfold denoteExpr }
]
