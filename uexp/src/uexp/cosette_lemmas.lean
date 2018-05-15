import .u_semiring
import .extra_constants
/- lemmas used in congruence of u-semirings -/

section
variables {s: Schema} {t₁ t₂ t₃ t₄: Tuple s} {a b c d e f: usr} {R: Tuple s → usr}
private meta def simp_solve :=
    `[intros h, rewrite ← h, try {simp <|> ac_refl}]

lemma ueq_symm: a = b → b = a := 
begin
    intros, rewrite a_1, 
end

lemma ueq_trans_1 : 
(t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * ((t₁ ≃ t₃) * d) * f = e → (t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * d * f = e := 
begin
    intros h,
    rewrite ← h,
    simp,
end

lemma ueq_trans_1' : 
(t₁ ≃ t₂) * (t₂ ≃ t₃) * ((t₁ ≃ t₃) * d) * f = e → (t₁ ≃ t₂) * (t₂ ≃ t₃) * d * f = e := by simp_solve

lemma ueq_trans_2_g : 
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * ((t₂ ≃ t₃) * d) * f = e → (t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * d * f = e := by simp_solve

lemma ueq_trans_2_g' : 
(t₁ ≃ t₂) * (t₁ ≃ t₃) * ((t₂ ≃ t₃) * d) * f = e → (t₁ ≃ t₂) * (t₁ ≃ t₃) * d * f = e := by simp_solve

lemma ueq_trans_2_l :
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * ((t₃  ≃ t₂) * d) * f = e → (t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * d * f = e := by simp_solve

lemma ueq_trans_2_l' :
(t₁ ≃ t₂) * (t₁ ≃ t₃) * ((t₃  ≃ t₂) * d) * f = e → (t₁ ≃ t₂) * (t₁ ≃ t₃) * d * f = e := by simp_solve

lemma ueq_trans_3_g :  
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * ((t₁ ≃ t₃) * d) * f = e → (t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * d * f = e := by simp_solve

lemma ueq_trans_3_g' :  
(t₁ ≃ t₂) * (t₃ ≃ t₂) * ((t₁ ≃ t₃) * d) * f = e → (t₁ ≃ t₂) * (t₃ ≃ t₂) * d * f = e := by simp_solve

lemma ueq_trans_3_l :
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * ((t₃ ≃ t₁) * d) * f = e → (t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * d * f = e := by simp_solve

lemma ueq_trans_3_l' :
(t₁ ≃ t₂) * (t₃ ≃ t₂) * ((t₃  ≃ t₁) * d) * f = e → (t₁ ≃ t₂) * (t₃ ≃ t₂) * d * f = e := by simp_solve

lemma ueq_trans_4 :
(t₁ ≃ t₂) * ((t₃ ≃ t₁) * c) * ((t₃ ≃ t₂) * d) * f = e → (t₁ ≃ t₂) * ((t₃ ≃ t₁) * c) * d * f = e := by simp_solve

lemma ueq_trans_4' :
(t₁ ≃ t₂) * (t₃ ≃ t₁) * ((t₃ ≃ t₂) * d) * f = e → (t₁ ≃ t₂) * (t₃ ≃ t₁) * d * f = e := by simp_solve

lemma prod_symm_assoc :
a * (b * c) = b * (a * c) := by ac_refl 

lemma time_one' :
1 * a = a := by simp

-- change the goal to the form  a x 1 = b x 1
lemma add_unit:
a * 1 = b * 1 → a = b :=
begin
    simp,
    intros, 
    assumption,
end

lemma add_unit_m:
a * 1 * b = c * 1 * d → a * b = c * d :=
begin
    simp,
    intros,
    assumption,
end

lemma add_unit_l:
1 * a = 1 * b → a = b :=
begin
    simp,
    intros,
    assumption,
end

lemma ueq_left_assoc_lem :
a * (t₁ ≃ t₂) * b = c → a * ((t₁ ≃ t₂) * b) = c := by simp_solve

-- TODO: revisit if squash involved
lemma ueq_right_assoc_lem {s₁ s₂: Schema} {t₁ t₂: Tuple s₁} {t₃ t₄: Tuple s₂}:
a * ((t₁ ≃ t₂) * (t₃ ≃ t₄)) * d = e → 
a * (t₁ ≃ t₂) * (t₃ ≃ t₄) * d = e := by simp_solve

lemma ueq_right_assoc_lem' {s₁ s₂: Schema} {t₁ t₂: Tuple s₁} {t₃ t₄: Tuple s₂}:
a * ((t₁ ≃ t₂) * ((t₃ ≃ t₄) * c)) * d = e → a * (t₁ ≃ t₂) * ((t₃ ≃ t₄) * c) * d = e  := by simp_solve

lemma move_ueq_between_com :
((t₁ ≃ t₂) * a) * b * c = d → a * ((t₁ ≃ t₂) * b) * c = d := by simp_solve

--TODO: this requires a good unification
lemma ueq_subst_in_spnf :
(t₁ ≃ t₂) * a * b * (R t₁) = (t₁ ≃ t₂) * a * b * (R t₂) := by simp

lemma ueq_subst_in_spnf' :
(t₁ ≃ t₂) * a * (R t₁) = (t₁ ≃ t₂) * a * (R t₂) := by simp

lemma ueq_dedup :
(t₁ ≃ t₂) * (t₁ ≃ t₂) = (t₁ ≃ t₂) := by simp

lemma ueq_dedup' :
(t₁ ≃ t₂) * ((t₁ ≃ t₂) * a) = (t₁ ≃ t₂) * a := by simp

lemma pred_cancel' {p: Pred s} {t: Tuple s} {a: usr}:
(denotePred p t) * ((denotePred p t) * a) =
(denotePred p t) * a :=
begin
    rewrite ← time_assoc,
    rewrite pred_cancel,
end 

lemma isKey_times_const {s : Schema} {ty : datatype} {c : usr}
    (k : Column ty s) (R : relation s) :
    isKey k R →
    ∀ (t t' : Tuple s), (denoteProj k t≃denoteProj k t') * (denote_r R t * (denote_r R t' * c)) =
    (t≃t') * (denote_r R t * c) :=
begin
    intros ik t t',
    transitivity (c * ((denoteProj k t≃denoteProj k t') * (denote_r R t * denote_r R t'))),
    { simp, ac_refl },
    transitivity (c * ((t≃t') * denote_r R t)),
    { apply congr_arg, rw ik },
    { rw ← time_assoc, rw time_comm c,
      rw time_assoc, apply congr_arg,
      rw time_comm }
end

lemma dup_in_squashed_union (a b: usr) :
    ∥ a * a + b ∥ = ∥ a + b ∥ :=
begin
    rw ← squash_add_squash,
    rw ← squash_time,
    rw squash_squared,
    rw squash_add_squash,
end

lemma factor_plus (a b: usr): 
    a + a * b = a * (1 + b) := by simp

lemma squash_union_factor (a b: usr):
  ∥ a + a * b ∥ = ∥ a ∥ :=
begin
    rw factor_plus,
    rw ← squash_time,
    rw squash_add_one,
    simp,
end  

lemma squash_sig_union_factor {s: Schema} (a b: Tuple s →  usr):
  ∥ (∑ t, a t *(1 + b t)) ∥ = ∥ (∑ t, a t) ∥ :=
begin
    rw squash_sig_squash,
    have h: (∑ (t : Tuple s), ∥a t * (1 + b t)∥) = (∑ (t : Tuple s), ∥a t ∥),
    focus {
        apply congr_arg, funext, 
        rw ← squash_time,
        rw squash_add_one,
        simp,
    },
    rw h,
    clear h,
    rw ←  squash_sig_squash,
end  

end -- end section
