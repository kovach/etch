import Etch.Op
import Etch.Verification.CodeGen.MoreOps
import Etch.Verification.CodeGen.Context
import Etch.Verification.Semantics.SkipStream

namespace Etch.Verification

inductive Expr (Γ : CtxType) : Type → Type 1
| var : (x : Γ.σ) → Expr Γ (Γ.Γ₁ x)
| args : (i : Fin Γ.n) → Expr Γ (Γ.Γ₂ i)
| glb : (t : CType) → ℕ → Expr Γ t
| op : (o : Op τ) → (arg : ∀ (i : Fin o.arity), Expr Γ (o.argTypes i)) → Expr Γ τ

variable {Γ : CtxType} {τ : Type}

def Expr.eval {Γ : CtxType} : {τ : Type} → Expr Γ τ → Context Γ → τ
| _, (var x), ctx => ctx.vars x
| _, (args i), ctx => ctx.args i
| _, (glb t i), ctx => ctx.globals t i
| _, (op o arg), ctx => o.spec (fun i => (arg i).eval ctx)

instance [Tagged τ] [Add τ] : Add (Expr Γ τ) :=
  ⟨fun e₁ e₂ => Expr.op Op.add ![e₁, e₂]⟩

instance [Tagged τ] [Mul τ] : Mul (Expr Γ τ) :=
  ⟨fun e₁ e₂ => Expr.op Op.mul ![e₁, e₂]⟩

@[simp] lemma Expr.add_eval [Tagged τ] [Add τ] (e₁ e₂ : Expr Γ τ) (ctx : Context Γ) :
  (e₁ + e₂).eval ctx = (e₁.eval ctx) + (e₂.eval ctx) := rfl

@[simp] lemma Expr.mul_eval [Tagged τ] [Mul τ] (e₁ e₂ : Expr Γ τ) (ctx : Context Γ) :
  (e₁ * e₂).eval ctx = (e₁.eval ctx) * (e₂.eval ctx) := rfl

def Expr.lt [Tagged τ] [LT τ] [DecidableRel (LT.lt : τ → τ → _)] (e₁ e₂ : Expr Γ τ) :
    Expr Γ Bool :=
  Expr.op Op.lt ![e₁, e₂]

@[simp] lemma Expr.lt_eval [Tagged τ] [LT τ] [DecidableRel (LT.lt : τ → τ → _)] (e₁ e₂ : Expr Γ τ) (ctx : Context Γ) :
  (e₁.lt e₂).eval ctx = ((e₁.eval ctx) < (e₂.eval ctx) : Bool) := rfl

end Etch.Verification