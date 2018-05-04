import .ucongr

-- set_option profiler true

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

lemma congr_ex4 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ c) * (b ≃ c) * (d ≃ e) * (R a) * (R d)  = 
     (a ≃ b) * (b ≃ c) * (e ≃ d) * (R c) * (R e)  :=
begin
    ucongr,
end

lemma congr_ex3 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ b) * (R c) * (a ≃ c) * (R d) * (b ≃ c) * (d ≃ e)   = 
     (a ≃ b) * (b ≃ c) * (e ≃ d) * (R c) * (R d)  :=
begin 
    ucongr,
end

lemma congr_ex5 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ c) * ((b ≃ c) * (a ≃ d) * (e ≃ f)) = 
     (c ≃ a) * ((a ≃ b) * ((b ≃ d) * (e ≃ f)))  :=
begin
    ucongr,
end

lemma congr_ex6 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (c ≃ d) * (b ≃ c) * (a ≃ b) * R a = 
     (a ≃ b) * (b ≃ c) * (c ≃ d) * R d :=
begin
    ucongr,
end

lemma congr_ex7 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ c) * ((a ≃ b) * (a ≃ c)) = 
     (c ≃ a) * (a ≃ b):=
begin
    ucongr,
end