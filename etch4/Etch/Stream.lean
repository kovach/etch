import Mathlib.Algebra.Ring.Basic
import Etch.C
import Etch.Op
import Etch.Basic

--notation "𝟚"  => Bool

-- marked irreducible later
--def Var (_ : Type _) := String
structure Var (α : Type _) where
  mk' ::
    instTagged : Tagged α
    data : String
abbrev ArrayVar (α : Type _) [Tagged α] := Var (ℕ → α)
def Var.mk [Tagged α] : String → Var α := fun s ↦ ⟨inferInstance, s⟩
def Var.toString : Var α → String := Var.data
instance [Tagged α] : Coe String (Var α) := ⟨Var.mk⟩

-- an expression language of variables, array access, and fully applied operators
inductive E : Type → Type 1
| var    : (v : Var α) → E α
| access : Var (ℕ → α) → E ℕ → E α
| call {α} (op : Op α) (args : (i : Fin op.arity) → E (op.argTypes i)) : E α
-- | intLit : ℕ → E ℕ

structure TypedVar where
  α : Type
  value : Var α

instance : Inhabited TypedVar := ⟨ℕ, "ERROR_DEFAULT_VAR"⟩

instance : BEq TypedVar where
  beq a b := a.value.toString == b.value.toString

def E.vars' : E α → List TypedVar
| E.var v => [⟨_, v⟩]
| .call _ args => List.ofFn (fun n ↦ (args n).vars') |>.join
| .access v e => ⟨_, v⟩ :: e.vars'
-- | .intLit _ => []

-- todo remove
def E.vars : E α → List String
| .var v => [v.toString]
| .call _ args => List.ofFn (fun n ↦ (args n).vars) |>.join
| .access v e => v.toString :: e.vars
-- | .intLit _ => []

def E.v (α) [Tagged α] (v : String) : E α := E.var $ Var.mk v

structure HeapContext where
  store : Var α → α
  heap {α : Type _} : Var (ℕ → α) → ℕ → α

def E.eval (c : HeapContext) : E α → α
| call f args => f.spec (λ i => (args i).eval c)
| var v => c.store v
| access arr arg => c.heap arr (arg.eval c)
-- | intLit x => x

instance [Tagged α] [Add α] : Add (E α) := ⟨ λ a b => E.call .add ![a, b] ⟩
instance [Tagged α] [Sub α] : Sub (E α) := ⟨ λ a b => E.call .sub ![a, b] ⟩
instance [Tagged α] [Mul α] : Mul (E α) := ⟨ λ a b => E.call .mul ![a, b] ⟩
instance [Tagged α] [OfNat α (nat_lit 0)] : OfNat (E α) (nat_lit 0) := ⟨ E.call .zero ![] ⟩
instance [Tagged α] [OfNat α (nat_lit 1)] : OfNat (E α) (nat_lit 1) := ⟨ E.call .one ![] ⟩
--instance : OfNat (E ℕ) n := ⟨ .intLit n ⟩
instance : OfNat (E ℕ) n := ⟨ E.call (.nat n) ![] ⟩
instance : Inhabited (E R) := ⟨ 0 ⟩
--def E.ext (f : String) : E Unit := E.call (O.voidCall f) ![]

def E.compile : E α → Expr
| @call _ op args => Expr.call op.opName $ List.ofFn λ i => E.compile (args i)
| access base i => Expr.index (Expr.var base.toString) [i.compile]
| var v => Expr.var v.toString
-- | intLit x => Expr.lit x

infixr:40 " << " => λ a b => E.call Op.lt ![a, b]
infixr:40 " <ᵣ " => λ a b => E.call Op.ofBool ![E.call Op.lt ![a, b]]
infixr:40 " == " => λ a b => E.call Op.eq ![a, b]
infixr:40 " != " => λ a b => E.call Op.neg ![(E.call Op.eq ![a, b])]
infixr:40 " <= " => λ a b => E.call Op.le ![a, b]

inductive P
| seq    : P → P → P
| while  : E Bool → P → P
| branch : E Bool → P → P → P
| skip   : P
| decl   : Var α → E α → P
| store_var : Var α → E α → P
| store_mem : Var (ℕ → α) → E ℕ → E α → P

def P.vars' : P → List TypedVar
| seq a b         => a.vars' ++ b.vars'
| .while c b      => c.vars' ++ b.vars'
| branch e t f    => e.vars' ++ t.vars' ++ f.vars'
| skip            => []
| decl  v e       => ⟨_, v⟩ :: e.vars'
| store_var l r   => ⟨_, l⟩ :: r.vars'
| store_mem v i r => ⟨_, v⟩ :: (i.vars' ++ r.vars')

def P.vars : P → List String
| seq a b         => a.vars ++ b.vars
| .while c b      => c.vars ++ b.vars
| branch e t f    => e.vars ++ t.vars ++ f.vars
| skip            => []
| decl  v e       => v.toString :: e.vars
| store_var l r   => l.toString :: r.vars
| store_mem v i r => v.toString :: (i.vars ++ r.vars)

-- needs to come after P to avoid injectivity_lemma issue
attribute [irreducible] Var

def P.if1 := λ c t => P.branch c t P.skip
infixr:10 ";;" => P.seq

def P.compile : P → Stmt
| seq a b => Stmt.seq a.compile b.compile
| .while cond body => Stmt.while cond.compile body.compile
| branch c a b => Stmt.conde c.compile a.compile b.compile
| skip => Stmt.noop
| decl var e => Stmt.decl .Int var.toString e.compile
| store_var var e => Stmt.store (Expr.var var.toString) e.compile
| store_mem v l r => Stmt.store (Expr.index (Expr.var v.toString) [l.compile]) r.compile

def Name := List ℕ
def Name.toString : Name → String := "_".intercalate ∘ List.map ToString.toString
def Name.fresh (n : Name) (new : ℕ) : Name := new :: n
def Name.freshen (n : Name) : Name := n.fresh 0
def emptyName : Name := []

instance : Inhabited Name := ⟨emptyName⟩

structure Index where
  type : Type
  bound : Option ℕ
  rank : ℕ

structure S (ι : Type _) (α : Type _) where
  σ     : Type
  -- next_weak/next_strict?
  -- upto/past ?
  skip  : σ → E ι → P -- skip s i : if current index < i, must advance; may advance to first index ≥ i.
  succ  : σ → E ι → P -- succ s i : if current index ≤ i, must advance; may advance to first index > i.
  value : σ → α
  ready : σ → E Bool
  index : σ → E ι
  valid : σ → E Bool
  init  : Name → P × σ

class LVal (ι : Type _) (α : Type _) where
  loc : Type
  start : α → P
  push : σ → E ι → P × E loc

structure LVS (ι : Type _) (α : Type _) [LVal ι α] extends S ι α, LVal ι α

instance LVal Unit (MemLoc α) where
  start :=  v _ l := (.store_mem l.arr l.ind (l.access + v.access), ())

structure S' (ι : Type _) (α : Type _) where
  σ     : Type
  skip  : σ → E ι → P
  succ  : σ → E ι → P
  value : σ → α
  ready : σ → E Bool
  index : σ → E ι
  valid : σ → E Bool

infixr:25 " →ₛ " => S

instance : Functor (S ι) where map := λ f s => {s with value := f ∘ s.value }
instance : Functor (S' ι) where map := λ f s => {s with value := f ∘ s.value }

--def StreamExec  (ι : Type _) (α : Type _) := (s : ι →ₛ α) × (P × s.σ)
--infixr:25 " →ₛ. " => StreamExec

section ι

variable {ι : Type} [Tagged ι] [DecidableEq ι] [LT ι] [DecidableRel (LT.lt : ι → ι → _)]
{α : Type _}
(v : Var (ℕ → α))
(is : ArrayVar ι)

def Var.access := E.access v
def Var.incr [Tagged α] [Add α] [One α] (v : Var α) : P := .store_var v $ E.var v + 1
def Var.incr_array [Tagged α] [Add α] [OfNat α 1] (ind : E ℕ) : P := .store_mem v ind $ v.access ind + 1
def Var.expr (v : Var α) : E α := E.var v
def Var.fresh [Tagged α] (v : Var α) (n : Name) : Var α := Var.mk (v.toString ++ n.toString)
def Var.store_var (v : Var α) := P.store_var v
def Var.decl (v : Var α) := P.decl v

instance : Coe (Var α) (E α) := ⟨E.var⟩

structure MemLoc (α : Type) := (arr : Var (ℕ → α)) (ind : E ℕ)

def MemLoc.access (m : MemLoc α) : E α := m.arr.access m.ind
def MemLoc.deref (m : MemLoc α) : E α := m.arr.access m.ind
def MemLoc.incr_array (m : MemLoc ℕ) : P := m.arr.incr_array m.ind
def MemLoc.interval (m : MemLoc ℕ) : E ℕ × E ℕ  := (m.arr.access m.ind, m.arr.access $ m.ind + 1)

def simpleSkip (pos : Var ℕ) (max_pos : E ℕ) (tgt : E ι) :=
  .store_var "temp" tgt;;
  .while ((pos.expr << max_pos) * (is.access pos << ("temp" : E ι))) pos.incr

def searchSkip (pos : Var ℕ) (max_pos : E ℕ) (i : E ι) : P :=
let hi : Var ℕ := "hi"; let lo : Var ℕ := "lo"; let m  : Var ℕ := "m";
let tgt : Var ι := "temp"; let not_done : Var Bool := "not_done"
tgt.store_var i;; .store_var lo pos;; .store_var hi max_pos;; .store_var not_done 1;;
(.while ((lo.expr <= hi.expr) * not_done) $
  .store_var m (E.call .mid ![lo.expr, hi.expr]) ;;
  .branch (.access is m << tgt.expr)
    (.store_var lo (m + 1))
    (.branch (tgt.expr << .access is "m")
      (.store_var hi (m - 1))
      ((.store_var not_done 0);; .store_var lo m))) ;;
  .store_var pos lo

inductive IterMethod | step | search

variable [LE ι] [DecidableRel (LE.le : ι → ι → _)]

def S.predRange [One α] (lower upper : E ι) : S ι α where
  σ := Var ι
  value   _ := 1
  succ  _ _ := .skip
  ready   _ := 1
  skip  pos := λ i => pos.store_var i
  index pos := pos
  valid pos := pos.expr << upper
  init  n   := let p := .fresh "pos" n; (p.decl lower, p)

#check instOfNatE
#synth OfNat (E Bool) (nat_lit 0)
def S.interval (h : IterMethod) (pos : Var ℕ) (lower upper : E ℕ) : S ι (E ℕ) where
  σ := Var ℕ
  value pos := pos.expr
  succ  pos i := .if1 (.access is pos.expr <= i) pos.incr
  skip  pos := (match h with | .step => simpleSkip | .search => searchSkip) is pos upper
  ready _   := 1
  index pos := .access is pos.expr
  valid pos := pos.expr << upper
  init  n   := let p := pos.fresh n; (p.decl lower, p)

-- this is meant to characterize a type that is equivalent to (Fin dimension)
class Sized (ι : Type) [Tagged ι] [Add ι] [Mul ι] where
  dimension : E ℕ
  toNat : E ι → E ℕ

def Bounded (_ : ℕ) := ℕ

instance : Tagged (Bounded n) := instTaggedNat
instance : Add (Bounded n) := instAddNat
instance : Mul (Bounded n) := instMulNat

instance : Sized (Bounded n) where
  dimension := E.call (Op.nat n) ![]
  toNat := id

def S.univ' [Add ι] [Mul ι] [Zero ι] [One ι] [Sized ι]  (l : Var ι) : S ι (E ι) where
  value last := last.expr
  succ  last i := .if1 (last.expr <= i) last.incr  -- imprecise but ok
  ready _    := 1
  skip  last := .store_var last
  index last := last.expr
  valid last := Sized.toNat last.expr <= Sized.dimension ι
  init  n    := let v := l.fresh n; (v.decl 0, v)

def S.univ [Zero ι] [Add ι] [One ι] (max l : Var ι) : S ι (E ι) where
  value last := last.expr
  succ  last i := .if1 (last.expr <= i) last.incr  -- imprecise but ok
  ready _    := 1
  skip  last := .store_var last
  index last := last.expr
  valid last := last.expr << max.expr
  init  n    := let v := l.fresh n; (v.decl 0, v)

def S.valFilter (f : α → E Bool) (s : ι →ₛ α) : ι →ₛ α :=
{ s with ready := λ p => s.ready p * f (s.value p),
         skip := λ p i =>
           .branch (s.ready p)
             (.branch (f (s.value p))
               (s.skip p i)
               (s.succ p i;; s.skip p i))
             (s.skip p i) }

def dim : Var ι := "dim"

-- using fmap introduces a universe constraint between α and Type 1 (coming from E ι). this is probably ok anyway
--def S.repl' {α : Type 1} [Zero ι] (last : Var ι) (v : α) : S ι α := (Function.const _ v) <$> (S.univ last)
--def S.repl [Zero ι] (last : Var ι) (v : α) : S ι α := {S.univ last with value := λ _ => v}
def S.function [Zero ι] [Add ι] [OfNat ι 1] (last : Var ι) (f : E ι → α) : S ι α := f <$> S.univ dim last

structure csr (ι α : Type _) := (i : Var (ℕ → ι)) (v : Var (ℕ → α)) (var : Var ℕ)

-- todo remove
def csr.of (name : String) (n : ℕ) (ι := ℕ) [Tagged ι] : csr ι ℕ :=
  let field {ι} [Tagged ι] (x : String) : Var ι := Var.mk $ name ++ n.repr ++ x
  { i := field "_crd", v := field "_pos", var := field "_i" }

def csr.level (h : IterMethod) (vars : csr ι ℕ) (loc : E ℕ) : ι →ₛ (E ℕ) :=
  S.interval vars.i h vars.var (.access vars.v loc) (vars.v.access (loc+1))
def S.level {f} [Functor f] (h : IterMethod) : csr ι ℕ → f (E ℕ) → f (ι →ₛ (E ℕ)) := Functor.map ∘ csr.level h
def S.leaf  {f} [Functor f] : Var (ℕ → α) → f (E ℕ) → f (E α) := Functor.map ∘ E.access
--def S.leaf' : Var α → E ℕ → E α := E.access
structure Contraction (ι : Type) (α : Type _) where stream : ι →ₛ α
--structure Contraction (α : Type _) where
--  f : Type _ → Type _
--  h : Functor f
--  v  : f α
--def Contraction {f : Type → Type _ → Type _} (α : Type _) := (ι : Type) × f ι α
--instance : Functor Contraction where map := λ f ⟨F, h, v⟩ => ⟨F, h, f <$> v⟩
instance : Functor (Contraction ι) where map := fun f ⟨val⟩ ↦ ⟨f <$> val⟩
def S.contract (s : S ι α) : Contraction ι α := ⟨s⟩

end ι

def Fun (ι α : Type _) := E ι → α
infixr:25 " →ₐ "  => Fun -- arbitrarily chosen for ease of typing: \ra
example : (ℕ →ₐ ℕ →ₛ ℕ) = (ℕ →ₐ (ℕ →ₛ ℕ)) := rfl
def Fun.un (h : ι →ₐ α) : E ι → α := h
def Fun.of (h : E ι → α) : ι →ₐ α := h
instance : Functor (Fun ι) where map := λ f v => f ∘ v

def range : ℕ →ₐ E ℕ := id

def seqInit (a : S ι α) (b : S ι β) (n : Name) :=
let (ai, as) := a.init (n.fresh 0);
let (bi, bs) := b.init (n.fresh 1);
(ai ;; bi, (as, bs))

def S.precompose  (s : ι →ₛ α) (f : σ' → s.σ) : S' ι α where
  σ := σ'
  value := s.value ∘ f
  succ  := s.skip ∘ f
  ready := s.ready ∘ f
  skip  := s.skip ∘ f
  index := s.index ∘ f
  valid := s.valid ∘ f

class Stateful (α : Type _) where
  σ : α → Type

class Init (α : Type _) extends Stateful α where
  init' : Name → (v : α) → P × σ v

instance : Init (E α) where
  σ _ := Unit
  init' _ _ := (.skip, ())

instance : Init (MemLoc α) where
  σ _ := Unit
  init' _ _ := (.skip, ())

instance : Init (ι →ₛ α) where
  σ v := v.σ
  init' n v := v.init n

instance : Stateful (S' ι α) where
  σ v := v.σ

instance : Init (Contraction ι α) where
  σ v := v.1.σ
  init' n v := v.1.init n

structure Sequence (α β : Type _) [Stateful α] [Stateful β] where
  (a : α) (b : β)
  f : Stateful.σ a → Stateful.σ b

instance [Stateful α] [Stateful β] : Stateful (Sequence α β) where
  σ v := Stateful.σ v.a

instance [Init α] [Stateful β] : Init (Sequence α β) where
  σ v := Stateful.σ v.a
  init' n v := Init.init' n v.a
