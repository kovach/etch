import Etch.Verification.CodeGen.SyntacticStream

namespace Etch.Verification

variable {ι α : Type _}

/-- Proposition indicating that `s` matches `t` at a particular state `q`, for a particular
  "translation function" `ϕ` which interprets stream states `s.σ` as syntactic stream contexts.  -/
structure tr₀ (s : Stream ι α) (t : S ι α) (ϕ : s.σ → Context (.ofσ t.Γ)) (q : s.σ) : Prop where
  (hvalid : s.valid q ↔ t.valid.eval (ϕ q))
  (hready : s.valid q → (s.ready q ↔ t.ready.eval (ϕ q)))
  (hsk₀ : ∀ (i : ι), (h : s.valid q) → (ϕ (s.skip q h (i, ff))).vars = t.skip₀.eval (i ::ₐ ϕ q))
  (hsk₁ : ∀ (i : ι), (h : s.valid q) → (ϕ (s.skip q h (i, tt))).vars = t.skip₁.eval (i ::ₐ ϕ q))
  (hind : (h : s.valid q) → s.index q h = t.index.eval (ϕ q))
  (hvalue : s.valid q → (h : s.ready q) → s.value q h = t.value.eval (ϕ q))

def tr (𝒢 : Set GlobalVars) (s : ∀ g ∈ 𝒢, Stream ι α) (t : S ι α) : Prop :=
  ∀ g (hg : g ∈ 𝒢), ∃ (ϕ : (s g hg).σ → (x : t.σ) → t.Γ x),
    ∀ (q : (s g hg).σ), tr₀ (s g hg) t (fun q' => .mkσ g (ϕ q')) q 

end Etch.Verification