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

/-- Contains the data for what local and temporary variables are assigned -/
structure LocalContext (Γ : CtxType) where
  (vars : (x : Γ.σ) → Γ.Γ₁ x)
  (args : (i : Fin Γ.n) → Γ.Γ₂ i)

@[simps]
def LocalContext.consArg {Γ : CtxType} {α : Type} (a : α) (ctx : LocalContext Γ) :
    LocalContext (α ::ₜ Γ) :=
  ⟨ctx.vars, Fin.cons a ctx.args⟩

scoped infixr:67 " ::ₐ " => LocalContext.consArg

/-- Pop the first argument (i.e. get the tail). -/
@[simps]
def LocalContext.unconsArg {Γ : CtxType} {α : Type} (ctx : LocalContext (α ::ₜ Γ)) : LocalContext Γ :=
  ⟨ctx.vars, Fin.tail ctx.args⟩

@[simp] lemma LocalContext.uncons_consArg {Γ : CtxType} {α : Type} (a : α) (ctx : LocalContext Γ) :
  (a ::ₐ ctx).unconsArg = ctx := rfl

instance : Inhabited (LocalContext default) :=
⟨Empty.rec, finZeroElim⟩

/-- The global variables stack -/
@[reducible]
def GlobalVars : Type := (t : CType) → ℕ → t 

structure Context (Γ : CtxType) extends LocalContext Γ where
  (globals : GlobalVars)

@[simps!] def Context.consArg {Γ : CtxType} {α : Type} (a : α) (ctx : Context Γ) :
    Context (α ::ₜ Γ) :=
  ⟨a ::ₐ ctx.toLocalContext, ctx.globals⟩

scoped infixr:67 " ::ₐ " => Context.consArg

@[simps!] def Context.unconsArg {Γ : CtxType} {α : Type} (ctx : Context (α ::ₜ Γ)) : Context Γ :=
  ⟨ctx.toLocalContext.unconsArg, ctx.globals⟩

instance : Inhabited (Context default) := ⟨default, default⟩

end Etch.Verification