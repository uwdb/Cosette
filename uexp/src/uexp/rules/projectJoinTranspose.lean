import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..ucongr
import ..TDP

set_option profiler true

open Expr
open Proj
open Pred
open SQL
open tree

theorem rule:
    forall  (Γ scm_s2 scm_s1: Schema) (rel_r2: relation scm_s2) (rel_r1: relation scm_s1) (s2_a : Column datatypes.int scm_s2) (s2_b : Column datatypes.int scm_s2)  (s1_a : Column datatypes.int scm_s1) (s1_b : Column datatypes.int scm_s1),
    denoteSQL ((SELECT1 (combine (right⋅left⋅s1_b) (right⋅right⋅s2_b))                  FROM1 (product (table rel_r1) (table rel_r2)) ) : SQL Γ _ ) =
    denoteSQL ((SELECT1 (combine (right⋅left) (right⋅right)) FROM1 (product ((SELECT1 (right⋅s1_b) FROM1 (table rel_r1) )) ((SELECT1 (right⋅s2_b) FROM1 (table rel_r2) ))) ) : SQL Γ  _) :=
begin 
    intros,
    unfold_all_denotations,
    funext,
    simp,
    print_size,
    remove_dup_sigs_lhs,
    apply ueq_symm,
    normalize_sig_body get_lhs,
    remove_dup_sigs_lhs,
    TDP,
end