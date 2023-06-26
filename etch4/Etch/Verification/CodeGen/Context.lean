import Mathlib.Data.Fin.Tuple.Basic

namespace Etch.Verification

/-- The possible types for global variables 
  (decides how many "registers" of inputs there are) -/
inductive CType
| nn | rr
| lst : CType → CType

def CType.toType : CType → Type
| nn => ℕ
| rr => ℤ
| (lst x) => List x.toType

instance : CoeSort CType Type := 
  ⟨fun t => t.toType⟩

def CType.defaultVal : (t : CType) → t
| nn => (default : ℕ)
| rr => (default : ℤ)
| (lst _) => (default : List _)

instance (t : CType) : Inhabited t := ⟨t.defaultVal⟩

structure CtxType where
  (σ : Type) -- local variables
  (Γ₁ : σ → Type)
  (n : ℕ) -- temporary variables (read-only)
  (Γ₂ : Fin n → Type)

@[simps] def CtxType.ofσ {σ : Type} (Γ : σ → Type) : CtxType :=
  ⟨_, Γ, 0, Fin.elim0⟩

instance : Inhabited CtxType :=
  ⟨Empty, Empty.elim, 0, Fin.elim0⟩

@[simps]
def CtxType.consArgType (α : Type) (Γ : CtxType) : CtxType :=
  ⟨Γ.σ, Γ.Γ₁, Γ.n + 1, Fin.cons α Γ.Γ₂⟩

scoped infixr:67 " ::ₜ " => CtxType.consArgType

/-- The global variables stack -/
@[reducible]
def GlobalVars : Type := (t : CType) → ℕ → t

structure Context (Γ : CtxType) where
  (vars : (x : Γ.σ) → Γ.Γ₁ x)
  (args : (i : Fin Γ.n) → Γ.Γ₂ i)
  (globals : GlobalVars)

instance : Inhabited (Context default) := ⟨Empty.rec, finZeroElim, default⟩

@[simps] def Context.mkσ {σ : Type} {Γ : σ → Type} (glb : GlobalVars) (vars : (x : σ) → Γ x) :
    Context (.ofσ Γ) :=
  ⟨vars, finZeroElim, glb⟩

@[simps] def Context.consArg {Γ : CtxType} {α : Type} (a : α) (ctx : Context Γ) :
    Context (α ::ₜ Γ) :=
  ⟨ctx.vars, Fin.cons a ctx.args, ctx.globals⟩

scoped infixr:67 " ::ₐ " => Context.consArg

@[simps] def Context.unconsArg {Γ : CtxType} {α : Type} (ctx : Context (α ::ₜ Γ)) : Context Γ :=
  ⟨ctx.vars, Fin.tail ctx.args, ctx.globals⟩

@[simps] def Context.updateVars {Γ : CtxType} (ctx : Context Γ) (vars : (x : Γ.σ) → Γ.Γ₁ x) : Context Γ :=
  ⟨vars, ctx.args, ctx.globals⟩

end Etch.Verification