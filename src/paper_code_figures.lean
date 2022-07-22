import front_end

/- setup for diagram -/
def row := 1
def col := 2
def channel := 3
def intensity := ℕ

-- Tensor Examples
-- index ordering: i, j, k, l
def mmul1  := Σ j $ (A : i →ₛ j →ₛ R) ⋆ (B : j →ₛ k →ₛ R)
def mmul2  := Σ k $ (A : i →ₛ k →ₛ R) ⋆ (B : j →ₛ k →ₛ R)
def ttv    := Σ k $ (C : i →ₛ j →ₛ k →ₛ R) ⋆ (v : k →ₛ R)
def ttm    := Σ l $ (C : i →ₛ j →ₛ l →ₛ R) ⋆ (A : k →ₛ l →ₛ R)
def mttkrp := Σ j $ Σ k $ (C : i →ₛ j →ₛ k →ₛ R) ⋆
                   (A : j →ₛ l →ₛ R) ⋆ (B : k →ₛ l →ₛ R)
def inner3 := Σ i $ Σ j $ Σ k $
    (C : i →ₛ j →ₛ k →ₛ R) ⋆ (C : i →ₛ j →ₛ k →ₛ R)

-- alternative declaration style:
def M1 : i →ₛ j →ₛ R := A
def M2 : j →ₛ k →ₛ R := B
def mat_mul_alt := Σ j (M1 ⋆ M2)

-- missing index leads to type elaboration error:
-- def mat_mul_err := Σ l (M1 ⋆ M2)

-- a more informative tensor type
def image_type := row →ₛ col →ₛ channel →ₛ intensity

/- END setup for diagram -/
