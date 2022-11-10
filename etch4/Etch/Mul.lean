import Etch.Stream

variable {ι : Type} [Tagged ι] [DecidableEq ι] [LT ι] [DecidableRel (LT.lt : ι → ι → _)]

def S.mul [HMul α β γ] (a : S ι α) (b : S ι β) : (S ι γ) where
  σ := a.σ × b.σ
  value p := a.value p.1 * b.value p.2
  skip  p := λ i => a.skip p.1 i;; b.skip p.2 i
  succ  p := a.succ p.1;; b.succ p.2
  ready p := a.ready p.1 * b.ready p.2 * (a.index p.1 == b.index p.2)
  index p := .call .max ![a.index p.1, b.index p.2]
  valid p := a.valid p.1 * b.valid p.2
  init    := seqInit a b

instance [Mul α] : Mul (S ι α) := ⟨S.mul⟩
instance [HMul α β γ] : HMul (S ι α) (S ι β) (S ι γ) := ⟨S.mul⟩
instance [HMul α β γ] : HMul (ι →ₛ α) (ι →ₐ β) (ι →ₛ γ) where hMul a b := {a with value := λ s => a.value s * b (a.index s)}
instance [HMul β α γ] : HMul (ι →ₐ β) (ι →ₛ α) (ι →ₛ γ) where hMul b a := {a with value := λ s => b (a.index s) * a.value s}
instance [HMul α β γ] : HMul (ι →ₐ α) (ι →ₐ β) (ι →ₐ γ) where hMul a b := λ v => a v * b v
