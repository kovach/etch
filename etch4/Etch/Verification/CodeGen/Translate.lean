import Etch.Verification.CodeGen.SyntacticStream

namespace Etch.Verification

variable {ι α : Type _}

structure tr₀ (s : Stream ι α) (t : S ι α) (ϕ : s.σ → Context (.ofσ t.Γ)) (q : s.σ) : Prop where
  (hvalid : s.valid q ↔ t.valid.eval (ϕ q))
  (hready : s.valid q → (s.ready q ↔ t.ready.eval (ϕ q)))
  (hsk₀ : ∀ (i : ι), (h : s.valid q) → ϕ (s.skip q h (i, ff)) = (t.skip₀.eval (i ::ₐ ϕ q)).unconsArg)
  (hsk₁ : ∀ (i : ι), (h : s.valid q) → ϕ (s.skip q h (i, tt)) = (t.skip₁.eval (i ::ₐ ϕ q)).unconsArg)
  (hind : (h : s.valid q) → (s.index q h = t.index.eval (ϕ q)))
  (hvalue : s.valid q → (h : s.ready q) → s.value q h = t.value.eval (ϕ q))

def tr (s : Stream ι α) (t : S ι α) (ϕ : s.σ → Context (.ofσ t.Γ)) : Prop :=
  ∀ q, tr₀ s t ϕ q

end Etch.Verification