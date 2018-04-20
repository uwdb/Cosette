open tactic smt_tactic list expr

/-
cc_state is the state of the congruence closure procedure.
It uses an union-find datastructure to store equivalence classes of terms.
-/

structure rsimp_cfg :=
(max_rounds := 5)

meta def collect_implied_eqs (cfg : rsimp_cfg) : tactic cc_state :=
focus1 $ using_smt $
  do add_lemmas_from_facts,
     /- Execute E-matching for at most max_rounds -/
     repeat_at_most cfg.max_rounds (ematch >> try close),
     /- 'done' succeeds if the goal has been solved -/
     (done >> return cc_state.mk)
     <|>
     /- If the goal was not solved return the state of the congruence closure procedure. -/
     to_cc_state

meta def size : expr → nat
| (app f a) := size f + size a
| _         := 1

/- Fold over the equivalence class containing 'e'. -/
meta def choose (ccs : cc_state) (e : expr) : expr :=
ccs.fold_eqc e e $ λ (best_so_far : expr) (curr : expr),
  if size curr < size best_so_far then curr else best_so_far

/- We use the rsimp' name here, since rsimp is already defined by the standard library. -/
meta def rsimp' (cfg : rsimp_cfg := {}) : tactic unit :=
do ccs ← collect_implied_eqs cfg,
   /- If the goal has not been solved, use top down simplifier and ccs to simplify the goal. -/
   try $ simp_top_down $ λ t,
      /- Rewrite goal using a top-down simplifier, and the equalities stored at 'ccs'. -/
      do root    ← return $ ccs.root t,     /- Retrieve the root of the equivalence class containing subterm 't'. -/
         let t' := choose ccs root,          /- Traverse the equivalence class and select the smallest element. -/
         p       ← ccs.eqv_proof t t',      /- Construct a proof that 't' = 'repr' -/
         return (t', p)

/- Examples -/

namespace example_1

constant f : nat → nat → nat
axiom fax : ∀ x, f x x = x
constant g : nat → nat
constant p : nat → nat → Prop
axiom pax : ∀ x, p x x

attribute [simp] [ematch_lhs] fax

example (a b c : nat) (h₁ : a = g b) (h₂ : a = b) : p (f (g a) a) b :=
begin
  rsimp',
  /- the new goal is  |- p b b -/
  apply pax
end

attribute [ematch] pax

example (a b c : nat) (h₁ : a = g b) (h₂ : a = b) : p (f (g a) a) b :=
by rsimp'

example (a b c : nat) (h₁ : a = g b) (h₂ : a = b) : p (f (g a) a) b :=
begin
  simp_using_hs,
  /- the new goal is |- p (f (g b) b) b -/
  apply pax -- Failed
end

end example_1

namespace example_2
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

example (a b c d : nat) (h : d = max c (a + b)) : p (max a (max d (b + a))) (max d (a + b)) :=
begin
  simp_using_hs,
  /- The new goal is |- p (max a (max c (a + b))) (max c (a + b)) -/
  apply pax -- Failed
end

end example_2

namespace example_3

constant f : nat → nat → nat
constant g : nat → nat
axiom fax : ∀ x, f (g x) x = x
axiom gax : ∀ x, g (g x) = x

constant p : nat → nat → Prop
axiom pax : ∀ x, p x x

attribute [simp] [ematch_lhs] fax gax

example (a b : nat) : p (f (g (g a)) (g a)) (g a) :=
begin
  rsimp',
  apply pax
end

example (a b : nat) : p (f (g (g a)) (g a)) (g a) :=
begin
  simp,
  /- the new goal is |- p (f a (g a)) (g a) -/
  apply pax  -- Failed
end

end example_3
