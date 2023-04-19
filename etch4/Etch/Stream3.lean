import Init.Data.List.Basic

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

import Etch.C
import Etch.Basic
--import Init.WFTactics

/- TODO: move this to Etch.Basic. -/
namespace List
/-- Same as [List.Mem], except this lives in [Type] -/
inductive Here {α : Type u} (a : α) : List α → Type u
| head (as : List α) : Here a (a::as)
| tail (b : α) {as : List α} : Here a as → Here a (b::as)

def Here.index : Here a as → Fin as.length
| .head _ => ⟨0, Nat.zero_lt_succ _⟩
| .tail _ h => h.index.succ

def Here.mem : Here a as → a ∈ as
| .head _ => .head _
| .tail _ h => .tail _ h.mem

theorem Here.indexGet : ∀ h : Here a as, as.get h.index = a
| .head _ => rfl
| .tail _ h => h.indexGet

@[reducible]
def eraseHere : (xs : List α) → Here x xs → List α
| _ :: xs, .head _ => xs
| _, .tail b tail => b :: eraseHere _ tail

#eval [1,2].eraseHere $ .tail _ (.head _)

example : 1 ∈ [2,1,3] := by decide

class Find (x : α) (xs : List α) where here : Here x xs
instance Find.tail [Find x xs] : Find x (y :: xs) where here := .tail _ Find.here
instance Find.head : Find x (x :: xs) where here := .head _

def remove (x : α) (xs : List α) [Find x xs] : List α := xs.eraseHere (x := x) Find.here
#eval remove 1 [3,3,3,1,2,3,3,1,3,4,5,55,5,6,2]

/-- Same as [List.Sublist], except this lives in [Type]. -/
inductive SublistT {α : Type u} : List α → List α → Type u
/-- the base case: `[]` is a sublist of `[]` -/
| slnil : SublistT [] []
/-- If `l₁` is a subsequence of `l₂`, then it is also a subsequence of `a :: l₂`. -/
| cons a : SublistT l₁ l₂ → SublistT l₁ (a :: l₂)
/-- If `l₁` is a subsequence of `l₂`, then `a :: l₁` is a subsequence of `a :: l₂`. -/
| cons₂ a : SublistT l₁ l₂ → SublistT (a :: l₁) (a :: l₂)
deriving Repr

theorem SublistT.toSublist : SublistT a b → Sublist a b
| .slnil => .slnil
| .cons a h => .cons a h.toSublist
| .cons₂ a h => .cons₂ a h.toSublist

instance SublistT.instCoeSublist : Coe (SublistT a b) (Sublist a b) := ⟨SublistT.toSublist⟩

def nil_sublistT : ∀ l : List α, SublistT [] l
| [] => .slnil
| a :: l => (nil_sublistT l).cons a

def SublistT.refl : ∀ l : List α, SublistT l l
| [] => .slnil
| a :: l => (SublistT.refl l).cons₂ a

/--
Check whether `l₁` is a sublist of `l₂`.
The algorithm is equivalent to [List.decidableSublist], but no proof is provided
if `l₁` is not a sublist of `l₂`.
-/
def SublistT.test [DecidableEq α] : ∀ l₁ l₂ : List α, Option (SublistT l₁ l₂)
| [], _ => some <| nil_sublistT _
| _ :: _, [] => none
| a :: l₁, b :: l₂ =>
  if h : a = b then
    SublistT.test l₁ l₂ |>.map (h ▸ .cons₂ a ·)
  else
    SublistT.test (a :: l₁) l₂ |>.map (.cons b ·)

end List

namespace Etch

variable (A : Type) [Inhabited A]

structure Shape where
  val : List A
  nodup : List.Nodup val
deriving Repr

inductive EType : Type
| bool -- internal boolean type
| int  -- internal int type
| attr : A → EType -- user-selected attribute types
| k    : A → EType -- universal semiring type

@[reducible] abbrev Var (A) (_ : EType A) := String
def Var.toString : Var A i → String := id

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
attribute [reducible] Op.params Op.arity

variable {A}
-- an operator parametrized by its output type
@[simps, reducible] def monotypicOp {n} (params : Fin n → EType A) (s : String) : Op A t := ⟨ _, params, s!"{t.toTag}_{s}" ⟩

section Op
variable {i : A} {t : EType A}
@[reducible] def Op.lt : Op A .bool := monotypicOp ![t, t] "lt"
@[reducible] def Op.neg : Op A .bool := monotypicOp ![.bool] "neg"
@[reducible] def Op.le : Op A .bool := monotypicOp ![t, t] "le"
@[reducible] def Op.max : Op A i := monotypicOp ![i, i] "max"
@[reducible] def Op.eq : Op A .bool := monotypicOp ![t, t] "eq"
@[reducible] def Op.min {t : EType A} : Op A i := monotypicOp ![t, t] "min"
@[reducible] def Op.true : Op A .bool := ⟨ _, ![], "true" ⟩
@[reducible] def Op.false : Op A .bool := ⟨ _, ![], "false" ⟩
@[reducible] def Op.and : Op A .bool := monotypicOp ![.bool, .bool] "and"
@[reducible] def Op.or : Op A .bool := monotypicOp ![.bool, .bool] "or"
@[reducible] def Op.zero : Op A (.k i) := ⟨ _, ![], "zero" ⟩
@[reducible] def Op.one : Op A (.k i) := ⟨ _, ![], "one" ⟩
@[reducible] def Op.int_one : Op A .int := ⟨ _, ![], "one" ⟩
@[reducible] def Op.add : Op A (.k i) := monotypicOp ![.k i, .k i] "add"
@[reducible] def Op.int_add : Op A .int := monotypicOp ![.int, .int] "add" -- sic
@[reducible] def Op.int_sub : Op A .int := monotypicOp ![.int, .int] "sub"
@[reducible] def Op.mul {i j k : A} : Op A (.k i) := monotypicOp ![.k j, .k k] "mul"
-- parametrized by input and output type. semantic no-op
@[reducible] def Op.to (i i' : EType A) : Op A i' := ⟨ _, ![i], s!"{i.toTag}_to_{i'.toTag}" ⟩
end Op

variable (A)
inductive E : EType A → Type
| var {t : EType A} (v : Var A t) : E t
| call {t} (op : Op A t) (args : (i : Fin op.arity) → E (op.params i)) : E t
| access {t : EType A} (v : Var A t) (ind : E .int) : E t

def E.compile : E A t → Expr
| var v => Expr.var v.toString
| call op args => Expr.call (t.toTag ++ op.name) $ List.ofFn λ i => E.compile (args i)
| access base i => Expr.index (Expr.var base.toString) [i.compile]


def Var.expr {A} {t : EType A} : Var A t → E A t := .var
instance : Coe (Var A t) (E A t) := ⟨ Var.expr ⟩

inductive LVal (t : EType A)
| local : Var A t → LVal t
| mem   : Var A t → E A .int → LVal t

def LVal.expr : LVal A t → E A t
| .local v => .var v
| .mem var i => .access var i

inductive P : Type
| skip
| seq   : P → P → P
--| load  {i : EType A} : E A .int → Var A i → P
| branch: E A .bool → P → P → P
| while : E A .bool → P → P
| store : LVal A t → E A t → P
| let : Var A t → E A t → P → P

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
instance : Add (E A .int) := ⟨ λ a b => E.call .int_add ![a, b] ⟩
instance : Sub (E A .int) := ⟨ λ a b => E.call .int_sub ![a, b] ⟩

def LVal.incr : LVal A .int → P A := fun l ↦ .store l (l.expr + (1 : E A .int))

infixr:min "$!" => E.call

def E.and : E A .bool → E A .bool → E A .bool := fun a b ↦ E.call Op.and ![a, b]
def E.or : E A .bool → E A .bool → E A .bool := fun a b ↦ E.call Op.or ![a, b]

variable {A}

def Var.subst (v : Var A t) (val : Var A t) : ∀ {s : EType A}, Var A s → Var A s
| _, v' => if v = v' then val else v'

def E.subst (v : Var A t) (val : Var A t) : {t : EType A} → E A t → E A t := sorry

def LVal.subst (v : Var A t) (val : Var A t) : ∀ {t}, LVal A t → LVal A t
| _, .local l => .local $ l.subst v val
| _, mem l i => .mem (l.subst v val) (i.subst v val)

def P.subst (v : Var A t) (val : Var A t) : P A → P A
| skip => .skip
| seq a b => .seq (subst v val a) (subst v val b)
--| load l r => .load (l.subst (t := .int) v val) (r.subst v val)
| branch c t f => .branch (c.subst v val) (t.subst v val) (f.subst v val)
| .while c t => .while (c.subst v val) (t.subst v val)
| .let v' e b => .let v' (e.subst v val) (if v = v' then b else b.subst v val)
| store lval r => .store (lval.subst v val) (r.subst v val)

abbrev M := StateM ℕ
def M.run' : ℕ → M α → α := fun n c ↦ Prod.fst (StateT.run c n).run
def M.run : M α → α := fun c ↦ Prod.fst (StateT.run c 0).run
def freshNat : M ℕ := do let n ← get; modify (. + 1); pure n
def freshen (v : Var A t) : M (Var A t) := do pure s!"{v}_{(← freshNat)}"

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
--| load addr v        => pure $ Stmt.store (Expr.var v.toString) (Expr.index (addr.compile) [0])
| .let v e b         => do let v' ← freshen v; Stmt.seq (Stmt.store (.var v') e.compile) <$> b.compile

variable {i : A}
def Level.mul (a : Level i) (b : Level i) : Level i where
  ready := .and $! ![.and $! ![a.ready, b.ready], .eq $! ![a.index, b.index]]
  index := .max $! ![a.index, b.index]
  valid := .and $! ![a.valid, b.valid]
  skip  i r := a.skip i r;; b.skip i r

def Level.range (ctr size : Var A .int) (inds : Var A (.attr i)) : Level i :=
  let ind := .access inds (.var ctr)
  { skip := fun i r ↦
    .branch r
      (.store (.local ctr) (.int_add $! ![.var ctr, .to _ _ $! ![ind <= i]]))
      (.store (.local ctr) (.int_add $! ![.var ctr, .to _ _ $! ![ind << i]]))
    ready := .true $! ![]
    valid := .lt $! ![ctr.expr, size.expr]
    index := ind
  }
  --value := .var .int ctr
--| level (σ : Type) (i : A) (is : List A) (l : Level A i) (f : σ → IStream A σ is) : IStream A σ (i :: is)

inductive Stream {A : Type} : List A → A → Type
| scalar {i : A} (e : E A (.k i)) : Stream [] i
| level {i v : A} {is : List A} (l : Level i) (val : (Stream is v)) : Stream (i :: is) v
| seq {is : List A} (a b : Stream is v) : Stream is v
| fun {i : A} (f : E A i → Stream is v) : Stream (i :: is) v -- todo, make first order (fix partial)
| contraction {is : List A} : Stream (_ :: is) v → Stream is v

infixr:26 " →ₛ " => Stream

namespace Stream

def default (is) : Stream is v :=
match is with
| [] => .scalar 0
| (_ :: is) => .fun fun _ ↦ default is

instance : Inhabited (Stream is v) where default := Stream.default is

-- "LVS" = L-value stream

abbrev LVSLevel (i : A) := (E A .int → P A) → E A i → P A × E A .int
inductive LVS : List A → A → Type
| scalar {v : A} (init : P A) (val : LVal A (.k v)) : LVS [] v
| level  {i : A} (init : P A) (push_do : E A i → P A) (push_val : E A i → LVS is v)  : LVS (i :: is) v

def LVS.init {is : List A} : LVS is v → P A
| scalar init _=> init
| level init _ _ => init

section
def VarLVS (is : List A) (v : A) : Type := E A .int → LVS is v

variable {is : List A} {i : A}

def composeLValues (level : E A .int → LVSLevel i × P A) : VarLVS is v → VarLVS (i :: is) v :=
fun val loc ↦
  let ⟨ l, init ⟩  := level loc
  let val_init i   := val i |>.init
  let push_do ind  :=     (l val_init ind).1
  let push_val ind := val (l val_init ind).2
  .level init push_do push_val

def sparseLVSLevel_aux (ind_array : Var A i) (lower upper : LVal A .int)
    : LVSLevel i := fun init ind ↦
  let loc   := upper.expr - 1
  let current := E.access ind_array loc
  let prog := P.if1 (.or $! ![.eq $! ![lower.expr, upper.expr], ind != current]) (upper.incr;; init loc);;
                P.store (.mem ind_array loc) ind
  (prog, loc)

def sparseLVSLevel (i : A) (ind_array : Var A i) (arr : Var A .int)
    : E A .int → LVSLevel i × P A :=
  let init ind := P.store (.mem arr (ind+1)) (.access arr ind)
  fun ind ↦ (sparseLVSLevel_aux ind_array (.mem arr ind) (.mem arr (ind+1)), init ind)

def valueScalar (arr : Var A (.k i)) : E A .int → LVS [] i := fun ind ↦ .scalar .skip (.mem arr ind)

#check composeLValues
#check sparseLVSLevel
variable (i j : A)
#check composeLValues (sparseLVSLevel i "ind0" "pos0") $
       composeLValues (sparseLVSLevel j "ind0" "pos0") $
       (valueScalar "values")

-- todo: make dense lvslevel

end

#check List.Mem
#check Finset.mem_erase
variable [BEq A]

def contract : ∀ {is} (here : is.Here i), Stream is v → Stream (is.eraseHere here) v
| _, h, .contraction e => .contraction (e.contract (.tail _ h))
| _, .head _, .fun .. => panic! "cannot contract functional stream"
| _, .tail _ h', .fun f => .fun fun x ↦ (f x).contract h'
| _, h, seq a b => .seq (a.contract h) (b.contract h)
| _, .head _, s@(level ..) => .contraction s
| _, .tail _ h, level l v => level l (v.contract h)

def contract' (i : A) [h : List.Find i is] : Stream is v → Stream (is.eraseHere h.here) v
| s => s.contract List.Find.here

def expand {is js} : (h : List.SublistT is js) → Stream is u → Stream js u
| .slnil,     a          => a
| .cons  i h, a          => .fun fun _ => a.expand h
| .cons₂ i h, .level l a => .level l (a.expand h)
| .cons₂ i h, .seq a₁ a₂ => .seq (a₁.expand (h.cons₂ i)) (a₂.expand (h.cons₂ i))
| .cons₂ i h, .fun f     => .fun fun x => (f x).expand h
| .cons₂ _ _, .contraction _ => panic! "Cannot expand a contraction"
termination_by expand is js h a => (is, Sigma.mk is a, Sigma.mk is (Sigma.mk js h))


def compile : ∀ {is : List A}, LVS is v → is →ₛ v → P A
| _, _, .fun _ => panic! "cannot generate finite loop for functional stream"
| _, l, seq a b => a.compile l ;; b.compile l
| _, .scalar _ l, scalar r => .store l (.add $! ![l.expr, r])
| _, l, contraction r => compile (.level .skip (fun _ ↦ .skip) (fun _ ↦ l)) r
| i :: _, .level _ push l', .level r r' => let ready : Var A .bool := "ready"; let index : Var A i := "index"
    .while r.valid $
      .let ready r.ready $
      .let index r.index $
      (.if1 ready.expr (push index.expr;; compile (l' index.expr) r'));;
      r.skip index.expr ready.expr

-- | _, l, .memo p s => p ;; compile l s
--| i, .level _ push l', @Stream.level _ _ _ _ r r' => let ready : Var A .bool := "ready"; let index : Var A i := "index"

def mul {is : List A} {v : A} : is →ₛ v → is →ₛ v → is →ₛ v
| l, seq a b => seq (l.mul a) (l.mul b)
| seq a b, l => seq (a.mul l) (b.mul l)

| .fun f, .fun g => .fun (fun x ↦ (f x).mul (g x))
| .fun f, .level l v => .level l ((f l.index).mul v)
| .level l v, .fun f => .level l ((f l.index).mul v)

| level l₁ v₁, level l₂ v₂ => level (l₁.mul l₂) $ v₁.mul v₂

| contraction l, r => sorry -- need fresh names, stream for accumulation
| l, contraction r => sorry

| .scalar e₁, .scalar e₂ => .scalar (.mul $! ![e₁, e₂])
-- | .memo p₁ s₁, .memo p₂ s₂ =>  .memo (p₁ ;; p₂) (s₁.mul s₂)

termination_by mul is v x y => (is, Sigma.mk is (Sigma.mk v x), Sigma.mk is (Sigma.mk v y))
--decreasing_by
--  try decreasing_tactic <;>
--  (simp [sizeOf]; sorry)

/-!
## Merge

### Version 1: Normal attribute ordering, no elaboration
The user defines an explicit "normal" ordering of attributes using [AttrOrder].
The downside is that infinite attribute sets are not allowed.

In the future, we can potentially add a macro like `mul! a b` to
automatically elaborate the type of the result.
-/

/-- Define a linear order for attributes in `A`. -/
class AttrOrder (A : Type) where
  order : Shape A
attribute [reducible] AttrOrder.order

class AttrOrderTotal (A : Type) [o : AttrOrder A] where
  toHere : ∀ (i : A), List.Here i o.order.val

namespace AttrOrderTotal
variable [AttrOrder A] [AttrOrderTotal A]
open AttrOrder (order)

abbrev length (A) [AttrOrder A] := (@order A).val.length
abbrev index (a : A) : Fin (length A) := toHere a |>.index
def indexInj : Function.Injective (index : A → _) := fun a b h =>
  (toHere a).indexGet ▸ (toHere b).indexGet ▸ (congrArg (@order A).val.get h)
def indexSurj : Function.Surjective (index : A → _) := fun b => by
  by_contra h
  rw [not_exists] at h
  let a := (@order A).val.get b
  have heq := (toHere a).indexGet
  have := List.nodup_iff_injective_get.1 (@order A).nodup heq
  exact absurd this (h a)
def indexBij : Function.Bijective (index : A → _) := ⟨indexInj, indexSurj⟩

instance : LinearOrder A := .lift' index indexInj

/- Short circuits -/
instance : LE A := inferInstance
instance : DecidableLE A := inferInstance
instance : LT A := inferInstance
instance : DecidableLT A := inferInstance

end AttrOrderTotal

private def mergeAttr' {A : Type} : ∀ {order a b : List A},
  (ha : List.SublistT a order) → (hb : List.SublistT b order) →
  (out : List A) × (List.SublistT a out × List.SublistT b out × List.SublistT out order)
-- Base case
| _, _, _, .slnil, .slnil => .mk [] (.slnil, .slnil, .slnil)
-- Attribute does not appear
| _, _, _, .cons a ha, .cons _ hb =>
  let ⟨out', ha', hb', ho'⟩ := mergeAttr' ha hb
  ⟨out', ha', hb', .cons a ho'⟩
-- Attribute appears in left
| _, _, _, .cons₂ a ha, .cons _ hb =>
  let ⟨out', ha', hb', ho'⟩ := mergeAttr' ha hb
  ⟨a :: out', ha'.cons₂ a, hb'.cons a, ho'.cons₂ a⟩
-- Attribute appears in right
| _, _, _, .cons a ha, .cons₂ _ hb =>
  let ⟨out', ha', hb', ho'⟩ := mergeAttr' ha hb
  ⟨a :: out', ha'.cons a, hb'.cons₂ a, ho'.cons₂ a⟩
-- Attribute appears in both
| _, _, _, .cons₂ a ha, .cons₂ _ hb =>
  let ⟨out', ha', hb', ho'⟩ := mergeAttr' ha hb
  ⟨a :: out', ha'.cons₂ a, hb'.cons₂ a, ho'.cons₂ a⟩

def mergeAttr {A : Type} [o : AttrOrder A] {a b : List A}
  (ha : List.SublistT a o.order.val) (hb : List.SublistT b o.order.val) :
  (out : Shape A) × (List.SublistT a out.val × List.SublistT b out.val × List.SublistT out.val o.order.val) :=
let ⟨out', ha', hb', ho'⟩ := mergeAttr' ha hb
let out : Shape A := ⟨out', .sublist ho' o.order.nodup⟩
⟨out, ha', hb', ho'⟩

/-- Notice that the best we can do here is to output a [Sigma] containing the output shape.  -/
def weirdMul [o : AttrOrder A] {is js : List A}
  (ha : List.SublistT is o.order.val) (hb : List.SublistT js o.order.val)
  (as : is →ₛ v) (bs : js →ₛ v) :
  (ks : List A) × ((ks →ₛ v) × List.SublistT ks o.order.val) :=
  let ⟨ks, ha, hb, ho⟩ := mergeAttr ha hb
  ⟨ks.val, (as.expand ha).mul (bs.expand hb), ho⟩

/-!
### Version 2: Using [AttrOrder] with type class search
Still uses [AttrOrder], but the merging algorithm is encoded in the instances of the [AttrMerge] type class.
This allows [mul''] to return a stream of the correct type with no fuss.
-/

/-- Solve for how to merge two sets of indices together using a predefined linear order. -/
class AttrMerge {A : Type} (order a b : List A) (out : outParam (List A)) where
  lmerge : List.SublistT a out
  rmerge : List.SublistT b out
  outIsShape : List.SublistT out order

namespace AttrMerge

variable {A : Type}

instance base : AttrMerge ([] : List A) [] [] [] := ⟨List.nil_sublistT _, List.nil_sublistT _, List.nil_sublistT _⟩
instance skip [m : AttrMerge order a b out] : AttrMerge (i :: order) a b out :=
  { m with outIsShape := m.outIsShape.cons i }
instance lsucc [m : AttrMerge order a b out] : AttrMerge (i :: order) (i :: a) b (i :: out) where
  lmerge := m.lmerge.cons₂ i
  rmerge := m.rmerge.cons i
  outIsShape := m.outIsShape.cons₂ i
instance rsucc [m : AttrMerge order a b out] : AttrMerge (i :: order) a (i :: b) (i :: out) where
  lmerge := m.lmerge.cons i
  rmerge := m.rmerge.cons₂ i
  outIsShape := m.outIsShape.cons₂ i
instance succ₂ [m : AttrMerge order a b out] : AttrMerge (i :: order) (i :: a) (i :: b) (i :: out) where
  lmerge := m.lmerge.cons₂ i
  rmerge := m.rmerge.cons₂ i
  outIsShape := m.outIsShape.cons₂ i

end AttrMerge

def merge [o : AttrOrder A] (a b : List A) [AttrMerge o.order.val a b c] := c

def mul' [o : AttrOrder A] {is js ks : List A} [m : AttrMerge o.order.val is js ks] (as : is →ₛ v) (bs : js →ₛ v) : ks →ₛ v :=
(as.expand m.lmerge).mul (bs.expand m.rmerge)

/-!
### Other potential solutions
We could use typeclasses to search for a proof that one attribute is `<`
compared to another. However, this turns out to be really slow in practice.
-/

end Stream
end Etch

/- todo
  define contraction, expansion, fast addition for new stream type
    [X] mapped contraction
    [x] mapped expansion, mul
    [ ] (lval, rval) pairs. memo? finish compile.
  test output

  [X] refactor lval
-/
