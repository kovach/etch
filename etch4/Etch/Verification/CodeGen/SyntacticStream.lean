import Mathlib.Logic.Encodable.Basic
import Etch.Verification.CodeGen.Prog

namespace Etch.Verification

/-- A one-dimensional stream using the new Expr/Prog type; otherwise same as `Stream.lean` -/
structure S (ι : Type _) (α : Type _) where
  (σ : Type) -- TODO: add [Encodable σ] instance so this can actually be compiled
  (σ_enc : Encodable σ)
  (Γ : σ → Type)
  (valid : Expr (.ofσ Γ) Bool)
  (ready : Expr (.ofσ Γ) Bool)
  (skip₀ : Prog (ι ::ₜ .ofσ Γ))
  (skip₁ : Prog (ι ::ₜ .ofσ Γ))
  (index : Expr (.ofσ Γ) ι)
  (value : Expr (.ofσ Γ) α) -- note Expr Γ α and not just α (this prevents nested streams)
  (init : Prog (.ofσ Γ))

end Etch.Verification