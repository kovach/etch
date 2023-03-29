import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Logic.Function.Basic
import Etch.Basic

variable (A : Type)

variable {τ}
@[reducible]

abbrev Var := String

inductive EType : Type
| attr : A → EType
| bool
| int
| k

example (f : Type → Type) [Functor f] : Functor f := inferInstance
#check @Functor.map

instance Functor.comp (F G : Type _ → Type _) [Functor F] [Functor G] : Functor (F ∘ G) :=
{ map := map (f := F) ∘ map (f := G) }
#check Functor.map (f := List ∘ List) (. + 1) [[1,2]]

inductive E : EType A → Type
| true : E .bool
| false : E .bool
| and (a b : E .bool) : E .bool
| or  (a b : E .bool) : E .bool

| var (v : Var) (i : A) : E (.attr i)
| le (a b : E (.attr i)) : E .bool
| lt (a b : E (.attr i)) : E .bool
| eq (a b : E (.attr i)) : E .bool
| max (a b : E (.attr i)) : E (.attr i)
| min (a b : E (.attr i)) : E (.attr i)

| val_access (v : Var) (ind : E .int) : E .k

inductive P : Type
| skip
| seq : P → P → P
| laod : ℕ → Var → P

infixr:10 " ;; " => P.seq

instance : Coe A (EType A) where coe := EType.attr

structure Level (i : A) : Type where
  skip  : E A i → E A .bool → P
  ready : E A .bool
  index : E A i
  valid : E A .bool
  state : List Var

variable {A}
def Level.mul (a : Level A i) (b : Level A i) : Level A i where
  state := a.state ++ b.state
  ready := a.ready.and b.ready |>.and (a.index.eq b.index)
  index := .max a.index b.index
  valid := a.valid |>.and b.valid
  skip  i r := a.skip i r;; b.skip i r

#check List
section ok

inductive foo1 : Type → Type
| f  (A : Type) (x : A) : foo1 A

inductive foo2 : Type → Type → Type
| f  (α β : Type) (i : A) : foo2 α β

end ok

section notok

inductive foo2' (α : Type) : Type → Type
| f  (β : Type) (i : A) : foo2' α β

end notok

#check foo

-- is this universal?
inductive IStream (A : Type) : Type → List A → Type
--| level (σ : Type) (i : A) (is : List A) (l : Level A i) (f : σ → IStream A σ is) : IStream A σ (i :: is)
| seq (σ : Type) (is : List A) (a : IStream A σ is) (b : σ → IStream A σ is) : IStream A σ is
--| scalar (e : E A a) : IStream A []
--| fun {i : A} (f : E A i → IStream A is) : IStream A (i :: is)

def IStream.mul : IStream A is → IStream A is → IStream A is
| level l1 f1, level l2 f2 => level (l1.mul l2) fun s ↦ (f1 s).mul (f2 s)


/- todo
now:
  [x] index types for S'
  compose Contraction and Then
  run it against TACO

  use freshen to generate A + B code
    nah
    need to freshen stream
    freshen value and also ?state?

refactor:
  redefine streams over attributes
  fix lvals
-/

