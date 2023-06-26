import Etch.Verification.CodeGen.Expr

namespace Etch.Verification

/-- An expression that can be stored into (lvalue) -/
inductive Storable (Γ : CtxType) : Type → Type _
| var (x : Γ.σ) : Storable Γ (Γ.Γ₁ x)
| arr {τ : Type} (s : Storable Γ (List τ)) (i : Expr Γ ℕ) : Storable Γ τ

inductive Prog : CtxType → Type _
| seq {Γ : CtxType} (a b : Prog Γ) : Prog Γ
| store {τ : Type} {Γ : CtxType} (x : Storable Γ τ) (e : Expr Γ τ) : Prog Γ
| branch {Γ : CtxType} (c : Expr Γ Bool) (a b : Prog Γ) : Prog Γ
| while {Γ : CtxType} (c : Expr Γ Bool) (a : Prog Γ) : Prog Γ
| letin {α : Type} {Γ : CtxType} (x : Expr Γ α) (a : Prog (α ::ₜ Γ)) : Prog Γ

def Prog.eval : {Γ : CtxType} → Prog Γ → Context Γ → (x : Γ.σ) → Γ.Γ₁ x 
| Γ, (Prog.seq a b), ctx => b.eval (ctx.updateVars (a.eval ctx))
| Γ, (Prog.store x e), ctx => sorry
| Γ, (Prog.branch c a b), ctx => bif c.eval ctx then a.eval ctx else b.eval ctx
| Γ, (Prog.while c a), ctx => sorry
| Γ, (Prog.letin x a), ctx => a.eval ((x.eval ctx) ::ₐ ctx)

end Etch.Verification
