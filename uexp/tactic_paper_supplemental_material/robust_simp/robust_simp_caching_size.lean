open tactic smt_tactic list expr

/-
The replace tactic above is very naive since it recomputes the size of
every subterm without using any cache. This produces a quadratic behavior.
The profiler will report the bottleneck at size.

We can address this performance bottleneck by using a cache.
-/
structure rsimp'_cfg :=
(max_rounds := 5)

meta def collect_implied_eqs (cfg : rsimp'_cfg) : tactic cc_state :=
focus1 $ using_smt $
  do add_lemmas_from_facts,
     /- Execute E-matching for at most max_rounds -/
     repeat_at_most cfg.max_rounds (ematch >> try close),
     /- 'now' succeeds if the goal has been solved -/
     (now >> return cc_state.mk)
     <|>
     /- If the goal was not solved return the state of the congruence closure procedure. -/
     to_cc_state

meta def sz_cache := expr_map nat
meta def mk_sz_cache := expr_map.mk nat

/- We could make it nicer by using the state monad -/
meta def size : expr → sz_cache → nat × sz_cache
| e m := do
  if ¬ e.is_app then (1, m)
  else match m.find e with
       | some n := (n, m)
       | none   :=
         let (n₁, m₁) := size e.app_fn  m,
             (n₂, m₂) := size e.app_arg m₁,
             n        := n₁ + n₂
       in (n, m₂.insert e n)
    end

meta def smaller (m : sz_cache) (t s : expr) : bool × sz_cache :=
let (t_sz, m₁) := size t m,
    (s_sz, m₂) := size s m₁ in
if       t_sz < s_sz then (tt, m₂)
else if  t_sz > s_sz then (ff, m₂)
else     (expr.lex_lt t s, m₂)      /- We use lexicographical order when t and s have the same size -/

meta def choose (ccs : cc_state) (m : sz_cache) (e : expr) : expr × sz_cache :=
ccs.fold_eqc e (e, m) $ λ ⟨best_so_far, m⟩ curr,
  let (is_smaller, new_m) := smaller m curr best_so_far in
  if is_smaller then (curr, new_m) else (best_so_far, new_m)

meta def replace (ccs : cc_state) : tactic unit :=
do t ← target,
   (_, new_t, prf) ← simplify_top_down mk_sz_cache
      (λ m t, do
         root          ← return $ ccs.root t,       /- Retrieve the root of the equivalence class containing subterm 't'. -/
         (repr, new_m) ← return $ choose ccs m root, /- Traverse the equivalence class and select the smallest element. -/
         guard (¬ repr =ₐ t),                        /- (optional) Abort rewrite step if 'repr' is alpha-equivalent to 'e'. -/
         prf     ← ccs.eqv_proof t repr,            /- Construct a proof that 't' = 'repr' -/
         return (new_m, repr, prf))
       t,
   replace_target new_t prf

/- We use the rsimp' name here, since rsimp is already defined by the standard library. -/
meta def rsimp' (cfg : rsimp'_cfg := {}) : tactic unit :=
do ccs ← collect_implied_eqs cfg,
   try (replace ccs)

namespace example_2
set_option profiler true

axiom max_add_cancel : ∀ a b : nat, max a (a + b) = a + b
constant p : nat → nat → Prop
axiom pax : ∀ x, p x x

attribute [simp] [ematch_lhs] max_assoc max_comm max_self max_add_cancel
attribute [simp] max_left_comm

example (a b c d : nat) (h : d = max c (a + b)) : p (max a (max d (b + a))) (max d (a + b)) :=
begin
  rsimp',
  /- The new goal is |- p d d -/
  apply pax
end

end example_2
