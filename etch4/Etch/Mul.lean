import Etch.Stream

variable {ι : Type} [Tagged ι] [DecidableEq ι] [LT ι] [DecidableRel (LT.lt : ι → ι → _)]
--[LE ι] [DecidableRel (LE.le : ι → ι → _)]

def S.mul [HMul α β γ] (a : S ι α) (b : S ι β) : (S ι γ) where
  value := a.value * b.value
  skip  := λ i => a.skip i;; b.skip i
  succ  := a.succ;; b.succ
  ready := a.ready * b.ready * (a.bound == b.bound)
  bound := .call .max ![a.bound, b.bound]
  valid := a.valid * b.valid
  init := a.init ;; b.init

instance [Mul α] : Mul (S ι α) := ⟨S.mul⟩
instance [HMul α β γ] : HMul (S ι α) (S ι β) (S ι γ) := ⟨S.mul⟩
instance [HMul α β γ] : HMul (ι →ₛ α) (ι →ₐ β) (ι →ₛ γ) where hMul a b := {a with value := a.value * b a.bound}
instance [HMul β α γ] : HMul (ι →ₐ β) (ι →ₛ α) (ι →ₛ γ) where hMul b a := {a with value := b a.bound * a.value}
instance [HMul α β γ] : HMul (ι →ₐ α) (ι →ₐ β) (ι →ₐ γ) where hMul a b := λ v => a v * b v
