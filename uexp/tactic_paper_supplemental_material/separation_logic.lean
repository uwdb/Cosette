/- Basic separation logic example. -/
constant heap   : Type
constant ptr    : Type
constant val    : Type
constant pt     : ptr → val → heap
constant hunion : heap → heap → heap
constant is_def : heap → Prop

infix `∙`:60 := hunion
infix `↣`:70 := pt

axiom hcomm    : ∀ x y, x ∙ y = y ∙ x
axiom hassoc   : ∀ x y z, (x ∙ y) ∙ z = x ∙ (y ∙ z)
axiom hnoalias : ∀ h y₁ y₂ w₁ w₂, is_def (h ∙ y₁ ↣ w₁ ∙ y₂ ↣ w₂) → y₁ ≠ y₂

attribute [ematch] hcomm hassoc hnoalias

example
(h₁ h₂ : heap) (x₁ x₂ x₃ x₄ : ptr) (v₁ v₂ v₃ : val)
: is_def (h₁ ∙ (x₁ ↣ v₁ ∙ x₂ ↣ v₂) ∙ h₂ ∙ (x₃ ↣ v₃)) → x₁ ≠ x₃ ∧ x₁ ≠ x₂ ∧ x₂ ≠ x₃ :=
begin [smt]
  intros,
  eblast
end
