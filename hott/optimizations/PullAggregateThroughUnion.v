Require Import HoTT. 
Require Import UnivalenceAxiom. 
Require Import HoTTEx. 
Require Import Denotation. 
Require Import UnivalentSemantics. 
Require Import AutoTactics. 
Require Import CQTactics. 
 
Open Scope type. 
 
Module Optimization (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S). 
  Import T S R A. 
  Module SQL_TSRA := SQL T S R A. 
  Import SQL_TSRA. 
  Module AutoTac := AutoTactics T S R A. 
  Import AutoTac. 
  Module CQTac := CQTactics T S R A. 
  Import CQTac. 
 
  Notation combine' := combineGroupByProj.
 
  Parameter count : forall {T}, aggregator T int. 
  Notation "'COUNT' ( e )" := (aggregatorGroupByProj count e). 
  Parameter sum : forall {T}, aggregator T int. 
  Notation "'SUM' ( e )" := (aggregatorGroupByProj sum e). 
  Parameter max : forall {T}, aggregator T int. 
  Notation "'MAX' ( e )" := (aggregatorGroupByProj max e). 
  Parameter min : forall {T}, aggregator T int. 
  Notation "'MIN' ( e )" := (aggregatorGroupByProj min e). 
  Parameter avg : forall {T}, aggregator T int. 
  Notation "'AVG' ( e )" := (aggregatorGroupByProj avg e).
 
  Parameter gt: Pred (node (leaf int) (leaf int)). 
 


  Definition Rule: Type. 
    refine (forall ( Γ scm_t scm_account scm_bonus scm_dept scm_emp: Schema) (rel_t: relation scm_t) (rel_account: relation scm_account) (rel_bonus: relation scm_bonus) (rel_dept: relation scm_dept) (rel_emp: relation scm_emp) (t_k0 : Column int scm_t) (t_c1 : Column int scm_t) (t_f1_a0 : Column int scm_t) (t_f2_a0 : Column int scm_t) (t_f0_c0 : Column int scm_t) (t_f1_c0 : Column int scm_t) (t_f0_c1 : Column int scm_t) (t_f1_c2 : Column int scm_t) (t_f2_c3 : Column int scm_t) (account_acctno : Column int scm_account) (account_type : Column int scm_account) (account_balance : Column int scm_account) (bonus_ename : Column int scm_bonus) (bonus_job : Column int scm_bonus) (bonus_sal : Column int scm_bonus) (bonus_comm : Column int scm_bonus) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp), _). 
    refine (⟦ Γ ⊢ DISTINCT (SELECT1 (combine (right⋅left) (right⋅right)) FROM1 ((DISTINCT (SELECT1 (combine (right⋅emp_deptno) (right⋅emp_job)) FROM1 (table rel_emp) )) UNION ALL (DISTINCT (SELECT1 (combine (right⋅emp_deptno) (right⋅emp_job)) FROM1 (table rel_emp) ))) ) : _ ⟧ =  ⟦ Γ ⊢ DISTINCT (SELECT1 (combine (right⋅left) (right⋅right)) FROM1 (((SELECT1 (combine (right⋅emp_deptno) (right⋅emp_job)) FROM1 (table rel_emp) )) UNION ALL ((SELECT1 (combine (right⋅emp_deptno) (right⋅emp_job)) FROM1 (table rel_emp) ))) ) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule. 
    start.
    destruct t as [a b].
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros h.
      strip_truncations.
      destruct h as [[t1 t2] [t3 t4]].
      destruct t4.
      (*solve disjunction doesn't work here, worth a second look *)
      destruct t3;
      strip_truncations;
      apply tr;
      refine ((t1, t2); _);
      break_and_rewrite;
      refine (inr t). 
    + intros h.
      strip_truncations.
      apply tr.
      destruct h as [[t1 t2] [t3 t4]].
      destruct t4.
      destruct t3 as [c1|c2].
      { refine ((t1, t2); _).
        break_and_rewrite.
        refine (inr (tr c1)). }
      { refine ((t1, t2); _).
        break_and_rewrite.
        refine (inr (tr c2)).
      }
  Qed.
  
End Optimization. 
