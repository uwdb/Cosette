import .u_semiring
/- lemmas used in congruence of u-semirings -/

section
variables {s: Schema} {t₁ t₂ t₃: Tuple s} {a b c d e: usr} 
private meta def simp_solve :=
    `[intros, simp]

lemma usr_eq_symm: a = b → b = a := 
begin
    intros, rewrite a_1, 
end

lemma ueq_trans_1 : 
(t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * d = (t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * (d * (t₁ ≃ t₃))  := by simp_solve

lemma ueq_trans_1' : 
(t₁ ≃ t₂) * (t₂ ≃ t₃) * d = (t₁ ≃ t₂) * (t₂ ≃ t₃) * (d * (t₁ ≃ t₃))  := by simp_solve

lemma ueq_trans_2_g : 
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * d = (t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * (d * (t₂ ≃ t₃))  := by simp_solve

lemma ueq_trans_2_g' : 
(t₁ ≃ t₂) * (t₁ ≃ t₃) * d = (t₁ ≃ t₂) * (t₁ ≃ t₃) * (d * (t₂ ≃ t₃))  := by simp_solve

lemma ueq_trans_2_l :
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * d = (t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * (d * (t₃  ≃ t₂))  := by simp_solve

lemma ueq_trans_2_l' :
(t₁ ≃ t₂) * (t₁ ≃ t₃) * d = (t₁ ≃ t₂) * (t₁ ≃ t₃) * (d * (t₃  ≃ t₂))  := by simp_solve

lemma ueq_trans_3_g :  
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * d = (t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * (d * (t₁ ≃ t₃))  := by simp_solve

lemma ueq_trans_3_g' :  
(t₁ ≃ t₂) * (t₃ ≃ t₂) * d = (t₁ ≃ t₂) * (t₃ ≃ t₂) * (d * (t₁ ≃ t₃))  := by simp_solve

lemma ueq_trans_3_l :
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * d = (t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * (d * (t₃  ≃ t₁))  := by simp_solve

lemma ueq_trans_3_l' :
(t₁ ≃ t₂) * (t₃ ≃ t₂) * d = (t₁ ≃ t₂) * (t₃ ≃ t₂) * (d * (t₃  ≃ t₁))  := by simp_solve

lemma prod_symm_assoc :
a * (b * c) = b * (a * c) := by ac_refl 

end -- end section
