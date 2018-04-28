import .u_semiring
/- lemmas used in congruence of u-semirings -/

section
variables {s: Schema} {t₁ t₂ t₃ t₄: Tuple s} {a b c d e: usr} 
private meta def simp_solve :=
    `[intros h, rewrite ← h, try {simp}]

lemma ueq_symm: a = b → b = a := 
begin
    intros, rewrite a_1, 
end

lemma ueq_trans_1 : 
(t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * ((t₁ ≃ t₃) * d) = e → (t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * d = e := by simp_solve

lemma ueq_trans_1' : 
(t₁ ≃ t₂) * (t₂ ≃ t₃) * ((t₁ ≃ t₃) * d) = e → (t₁ ≃ t₂) * (t₂ ≃ t₃) * d = e := by simp_solve

lemma ueq_trans_2_g : 
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * ((t₂ ≃ t₃) * d) = e → (t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * d = e := by simp_solve

lemma ueq_trans_2_g' : 
(t₁ ≃ t₂) * (t₁ ≃ t₃) * ((t₂ ≃ t₃) * d) = e → (t₁ ≃ t₂) * (t₁ ≃ t₃) * d = e := by simp_solve

lemma ueq_trans_2_l :
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * ((t₃  ≃ t₂) * d) = e → (t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * d = e := by simp_solve

lemma ueq_trans_2_l' :
(t₁ ≃ t₂) * (t₁ ≃ t₃) * ((t₃  ≃ t₂) * d) = e → (t₁ ≃ t₂) * (t₁ ≃ t₃) * d = e := by simp_solve

lemma ueq_trans_3_g :  
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * ((t₁ ≃ t₃) * d) = e → (t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * d = e := by simp_solve

lemma ueq_trans_3_g' :  
(t₁ ≃ t₂) * (t₃ ≃ t₂) * ((t₁ ≃ t₃) * d) = e → (t₁ ≃ t₂) * (t₃ ≃ t₂) * d = e := by simp_solve

lemma ueq_trans_3_l :
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * ((t₃ ≃ t₁) * d) = e → (t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * d = e := by simp_solve

lemma ueq_trans_3_l' :
(t₁ ≃ t₂) * (t₃ ≃ t₂) * ((t₃  ≃ t₁) * d) = e → (t₁ ≃ t₂) * (t₃ ≃ t₂) * d = e := by simp_solve

lemma ueq_trans_4 :
(t₁ ≃ t₂) * ((t₃ ≃ t₁) * c) * ((t₃ ≃ t₂) * d) = e → (t₁ ≃ t₂) * ((t₃ ≃ t₁) * c) * d = e := by simp_solve

lemma ueq_trans_4' :
(t₁ ≃ t₂) * (t₃ ≃ t₁) * ((t₃ ≃ t₂) * d) = e → (t₁ ≃ t₂) * (t₃ ≃ t₁) * d = e := by simp_solve

lemma prod_symm_assoc :
a * (b * c) = b * (a * c) := by ac_refl 

lemma time_one' :
1 * a = a := by simp

-- change the goal to the form  a x 1 = b x 1
lemma add_unit (a b: usr):
a * 1 = b * 1 → a = b :=
begin
    simp,
    intros, 
    assumption,
end

lemma ueq_left_assoc :
a * (t₁ ≃ t₂) * b = c → (a * (t₁ ≃ t₂)) * b = c := by simp_solve

-- TODO: revisit if squash involved
lemma ueq_right_assoc :
a * (t₁ ≃ t₂) * (t₃ ≃ t₄) = a * ((t₁ ≃ t₂) * (t₃ ≃ t₄)) := by simp

end -- end section
