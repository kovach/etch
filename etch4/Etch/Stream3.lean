import Lean

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Tactic.LibrarySearch

import Etch.C
import Etch.Basic
--import Init.WFTactics

namespace Etch

variable (A : Type) [Inhabited A]

@[reducible] abbrev Var := String
def Var.toString : Var → String := id

inductive EType : Type
| attr : A → EType -- user-selected attribute types
| bool -- internal boolean type
| int  -- internal int type
| k : A → EType -- universal semiring type

instance : Coe A (EType A) where coe := EType.attr

class Represented (A : Type) where
  tag : A → String
variable [Represented A]

def EType.toTag : EType A → String
| .bool => "bool"
| .k i => Represented.tag i
| .int => "nat"
| .attr i => Represented.tag i

structure Op (out : EType A) : Type where
  arity : ℕ
  params : Fin arity → EType A
  name : String
attribute [reducible] Op.params
attribute [reducible] Op.arity

variable {A}
-- an operator parametrized by its output type
@[simps, reducible] def monotypicOp {n} (params : Fin n → EType A) (s : String) : Op A t := ⟨ _, params, s!"{t.toTag}_{s}" ⟩

section Op
variable {i : A}
@[reducible] def Op.lt : Op A .bool := monotypicOp ![i, i] "lt"
@[reducible] def Op.le : Op A .bool := monotypicOp ![i, i] "le"
@[reducible] def Op.max : Op A i := monotypicOp ![i, i] "max"
@[reducible] def Op.eq : Op A .bool := monotypicOp ![i, i] "eq"
@[reducible] def Op.min : Op A i := monotypicOp ![i, i] "min"
@[reducible] def Op.true : Op A .bool := ⟨ _, ![], "true" ⟩
@[reducible] def Op.false : Op A .bool := ⟨ _, ![], "false" ⟩
@[reducible] def Op.and : Op A .bool := monotypicOp ![.bool, .bool] "and"
@[reducible] def Op.or : Op A .bool := monotypicOp ![.bool, .bool] "or"
@[reducible] def Op.zero : Op A (.k i) := ⟨ _, ![], "zero" ⟩
@[reducible] def Op.one : Op A (.k i) := ⟨ _, ![], "one" ⟩
@[reducible] def Op.int_one : Op A .int := ⟨ _, ![], "one" ⟩
@[reducible] def Op.add : Op A (.k i) := monotypicOp ![.k i, .k i] "add"
@[reducible] def Op.int_add : Op A .int := monotypicOp ![.int, .int] "add"
@[reducible] def Op.mul {i j k : A} : Op A (.k i) := monotypicOp ![.k j, .k k] "mul"
-- parametrized by input and output type. semantic no-op
@[reducible] def Op.to (i i' : EType A) : Op A i' := ⟨ _, ![i], s!"{i.toTag}_to_{i'.toTag}" ⟩
end Op

variable (A)
inductive E : EType A → Type
| var (t : EType A) (v : Var) : E t
| call {t} (op : Op A t) (args : (i : Fin op.arity) → E (op.params i)) : E t
| access (t : EType A) (v : Var) (ind : E .int) : E t

def E.compile : E A t → Expr
| var _ v => Expr.var v.toString
| call op args => Expr.call (t.toTag ++ op.name) $ List.ofFn λ i => E.compile (args i)
| access _ base i => Expr.index (Expr.var base.toString) [i.compile]

def Var.expr : Var → E A i := .var _

inductive LVal
| local : Var → LVal
| mem   : Var → E A .int → LVal

def LVal.expr : LVal A → E A t
| .local v => .var _ v
| .mem var i => .access _ var i

inductive P : Type
| skip
| seq   : P → P → P
| load  : E A .int → Var → P
| branch: E A .bool → P → P → P
| while : E A .bool → P → P
| store : LVal A → E A t → P
| let : Var → E A t → P → P
--| store_var {t} : Var → E A t → P
--| store_mem {i : A} : Var → E A .int → E A (.k i) → P

instance : Inhabited (P A) where default := .skip

infixr:10 " ;; " => P.seq
def P.if1 {A} : E A .bool → P A → P A := fun c t ↦ P.branch c t P.skip

structure Level {A} (i : A) : Type where
  skip  : E A i → E A .bool → P A
  ready : E A .bool
  index : E A i
  valid : E A .bool

infixr:40 " << " => λ a b => E.call Op.lt ![a, b]
infixr:40 " >> " => λ a b => E.call Op.lt ![b, a]
infixr:40 " <ᵣ " => λ a b => E.call Op.ofBool ![E.call Op.lt ![a, b]]
infixr:40 " >ᵣ " => λ a b => E.call Op.ofBool ![E.call Op.lt ![b, a]]
infixr:40 " == " => λ a b => E.call Op.eq ![a, b]
infixr:40 " != " => λ a b => E.call Op.neg ![(E.call Op.eq ![a, b])]
infixr:40 " <= " => λ a b => E.call Op.le ![a, b]
infixr:40 " >= " => λ a b => E.call Op.le ![b, a]

instance : Zero (E A (.k i)) := ⟨ E.call Op.zero ![] ⟩
instance : One (E A (.k i)) := ⟨ E.call Op.one ![] ⟩
instance : One (E A .int) := ⟨ E.call Op.int_one ![] ⟩

infixr:min "$!" => E.call

def E.and : E A .bool → E A .bool → E A .bool := fun a b ↦ E.call Op.and ![a, b]
def E.or : E A .bool → E A .bool → E A .bool := fun a b ↦ E.call Op.and ![a, b]

variable {A}

def Var.subst (v : Var) (val : Var) : Var → Var
| v' => if v = v' then val else v'

def E.subst (v : Var) (val : Var) : ∀ {t}, E A t → E A t := sorry

def LVal.subst (v : Var) (val : Var) : LVal A → LVal A
| .local l => .local $ l.subst v val
| mem l i => .mem (l.subst v val) (i.subst v val)

def P.subst (v : Var) (val : Var) : P A → P A
| skip => .skip
| seq a b => .seq (subst v val a) (subst v val b)
| load l r => .load (l.subst v val) (r.subst v val)
| branch c t f => .branch (c.subst v val) (t.subst v val) (f.subst v val)
| .while c t => .while (c.subst v val) (t.subst v val)
| .let v' e b => .let v' (e.subst v val) (if v = v' then b else b.subst v val)
| store lval r => .store (lval.subst v val) (r.subst v val)

abbrev M := StateM ℕ
def M.run' : ℕ → M α → α := fun n c ↦ Prod.fst (StateT.run c n).run
def M.run : M α → α := fun c ↦ Prod.fst (StateT.run c 0).run
def freshNat : M ℕ := do let n ← get; modify (. + 1); pure n
def freshen (v : Var) : M Var := do pure s!"{v}_{(← freshNat)}"

--def P.compile : P A → Stmt
--| seq a b            => Stmt.seq a.compile b.compile
--| .while cond body   => Stmt.while cond.compile body.compile
--| branch c a b       => Stmt.conde c.compile a.compile b.compile
--| skip               => Stmt.noop
--| store (.local l) r => Stmt.store (Expr.var l.toString) r.compile
--| store (.mem v i) r => Stmt.store (Expr.index (Expr.var v.toString) [i.compile]) r.compile
--| load addr v        => Stmt.store (Expr.var v.toString) (Expr.index (addr.compile) [0])

def P.compile : P A → M Stmt
| seq a b            => Stmt.seq <$> a.compile <*> b.compile
| .while cond body   => Stmt.while cond.compile <$> body.compile
| branch c a b       => Stmt.conde c.compile <$> a.compile <*> b.compile
| skip               => pure Stmt.noop
| store (.local l) r => pure $ Stmt.store (Expr.var l.toString) r.compile
| store (.mem v i) r => pure $ Stmt.store (Expr.index (Expr.var v.toString) [i.compile]) r.compile
| load addr v        => pure $ Stmt.store (Expr.var v.toString) (Expr.index (addr.compile) [0])
| .let v e b         => do let v' ← freshen v; Stmt.seq (Stmt.store (.var v') e.compile) <$> b.compile

variable {i : A}
def Level.mul (a : Level i) (b : Level i) : Level i where
  ready := .and $! ![.and $! ![a.ready, b.ready], .eq $! ![a.index, b.index]]
  index := .max $! ![a.index, b.index]
  valid := .and $! ![a.valid, b.valid]
  skip  i r := a.skip i r;; b.skip i r

def Level.range (ctr size inds : Var) : Level i :=
  let ind := .access i inds (.var .int ctr)
  { skip := fun i r ↦
    .branch r
      (.store (.local ctr) (.int_add $! ![.var .int ctr, .to _ _ $! ![ind <= i]]))
      (.store (.local ctr) (.int_add $! ![.var .int ctr, .to _ _ $! ![ind << i]]))
    ready := .true $! ![]
    valid := .lt $! ![E.var i ctr, E.var i size]
    index := ind
  }
  --value := .var .int ctr
--| level (σ : Type) (i : A) (is : List A) (l : Level A i) (f : σ → IStream A σ is) : IStream A σ (i :: is)

inductive Stream {A : Type} : List A → A → Type
| level {i v : A} {is : List A} (l : Level i) (val : (Stream is v)) : Stream (i :: is) v
| seq {is : List A} (a b : Stream is v) : Stream is v
| fun {i : A} (f : E A i → Stream is v) : Stream (i :: is) v -- todo, make first order (fix partial)
| scalar {i : A} (e : E A (.k i)) : Stream [] i


infixr:26 " →ₛ " => Stream
#check [] →ₛ i

instance is0 : Inhabited (Stream [] v) where default := .scalar 0
instance iss [Inhabited (Stream is v)] : Inhabited (Stream (i :: is) v) where default := .fun fun _ ↦ default

namespace Stream

partial def mul {is : List A} {v : A} : is →ₛ v → is →ₛ v → is →ₛ v
| level l₁ v₁, level l₂ v₂ => level (l₁.mul l₂) $ v₁.mul v₂

| l, seq a b => seq (l.mul a) (l.mul b)
| seq a b, l => seq (a.mul l) (b.mul l)

| .fun f, .fun g => .fun (fun x ↦ (f x).mul (g x))
| .fun f, .level l v => .level l ((f l.index).mul v)
| .level l v, .fun f => .level l ((f l.index).mul v)

| .scalar e₁, .scalar e₂ => .scalar (.mul $! ![e₁, e₂])
--termination_by _ x y => sizeOf (x, y)
--decreasing_by
--  try decreasing_tactic <;>
--  (simp [sizeOf]; sorry)

inductive LValueStream {A : Type} : List A → Type
| scalar (val : LVal A) : LValueStream []
| level {i : A} (push : E A i → P A) (val : LValueStream is) : LValueStream (i :: is)

def compile {is : List A} : LValueStream is → Stream is v → P A
| _, .fun _ => panic! "cannot generate finite loop for functional stream"
| l, seq a b => a.compile l ;; b.compile l
| .scalar l, scalar r => .store l (.add $! ![l.expr, r])
| .level push l', .level r r' =>
    let ready : Var := "ready"
    let index : Var := "index"
    .while r.valid $
      .let ready r.ready $
      .let index r.index $
      (.if1 (ready.expr _)
        (push r.index;; compile l' r'))
      ;; r.skip (index.expr _) (ready.expr _)

end Stream
end Etch

/- todo
  define contraction, expansion, fast addition for new stream type
  lvalstream
  test output

  refactor lval
-/