import .ucongr

lemma congr_trans_ex1 {s: Schema} (a b c d e f: Tuple s):
    (a ≃ c) * ((a ≃ b) * (e ≃ f)) = (a ≃ c) * ((a ≃ b) * (f ≃ e)) :=
begin
    ucongr,
end

lemma congr_trans_ex2 {s: Schema} (a b c d e f: Tuple s):
    (a ≃ c) * ((b ≃ a) * (e ≃ f)) = (a ≃ c) * ((a ≃ b) * (f ≃ e)) :=
begin
    ucongr,
end

lemma congr_ex1 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ c) * ((b ≃ c) * (a ≃ d) * (e ≃ f))  = (c ≃ a) * ((a ≃ b) * ((b ≃ d) * (e ≃ f)))  :=
begin
    ucongr,
end

lemma congr_ex2 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ c) * ((c ≃ a) * ((a ≃ b) * ((a ≃ d) * (f ≃ e))))  = (c ≃ a) * ((a ≃ b) * ((b ≃ d) * (e ≃ f)))  :=
begin
    ucongr,
end

lemma congr_ex3 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ c) * (b ≃ c) * (d ≃ e) * (R a) * (R d)  = 
     (a ≃ b) * (b ≃ c) * (e ≃ d) * (R c) * (R e)  :=
begin 
    sorry
end
