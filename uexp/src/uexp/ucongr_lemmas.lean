import .u_semiring
/- lemmas used in congruence of u-semirings -/

section
variables {s: Schema} {t₁ t₂ t₃: Tuple s} {a b c d e: usr} 
private meta def simp_solve :=
    `[intros h, rewrite ← h, simp]

lemma ueq_symm: a = b → b = a := 
begin
    intros, rewrite a_1, 
end

lemma ueq_trans_1 : 
(t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * (d * (t₁ ≃ t₃)) = e → (t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * d = e := by simp_solve

lemma ueq_trans_1' : 
(t₁ ≃ t₂) * (t₂ ≃ t₃) * (d * (t₁ ≃ t₃)) = e → (t₁ ≃ t₂) * (t₂ ≃ t₃) * d = e := by simp_solve

lemma ueq_trans_2_g : 
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * (d * (t₂ ≃ t₃)) = e → (t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * d = e := by simp_solve

lemma ueq_trans_2_g' : 
(t₁ ≃ t₂) * (t₁ ≃ t₃) * (d * (t₂ ≃ t₃)) = e → (t₁ ≃ t₂) * (t₁ ≃ t₃) * d = e := by simp_solve

lemma ueq_trans_2_l :
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * (d * (t₃  ≃ t₂)) = e → (t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * d = e := by simp_solve

lemma ueq_trans_2_l' :
(t₁ ≃ t₂) * (t₁ ≃ t₃) * (d * (t₃  ≃ t₂)) = e → (t₁ ≃ t₂) * (t₁ ≃ t₃) * d = e := by simp_solve

lemma ueq_trans_3_g :  
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * (d * (t₁ ≃ t₃)) = e → (t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * d = e := by simp_solve

lemma ueq_trans_3_g' :  
(t₁ ≃ t₂) * (t₃ ≃ t₂) * (d * (t₁ ≃ t₃)) = e → (t₁ ≃ t₂) * (t₃ ≃ t₂) * d = e := by simp_solve

lemma ueq_trans_3_l :
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * (d * (t₃ ≃ t₁)) = e → (t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * d = e := by simp_solve

lemma ueq_trans_3_l' :
(t₁ ≃ t₂) * (t₃ ≃ t₂) * (d * (t₃  ≃ t₁)) = e → (t₁ ≃ t₂) * (t₃ ≃ t₂) * d = e := by simp_solve

lemma ueq_trans_4 :
(t₁ ≃ t₂) * ((t₃ ≃ t₁) * c) * (d * (t₃ ≃ t₂)) = e → (t₁ ≃ t₂) * ((t₃ ≃ t₁) * c) * d = e := by simp_solve

lemma ueq_trans_4' :
(t₁ ≃ t₂) * (t₃ ≃ t₁) * (d * (t₃ ≃ t₂)) = e → (t₁ ≃ t₂) * (t₃ ≃ t₁) * d = e := by simp_solve

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

end -- end section
