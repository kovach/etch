import Etch.Verification.Semantics.SkipStream
import Etch.Verification.Semantics.Mul
import Etch.Verification.Semantics.Add
import Etch.Verification.Semantics.Contract
import Mathlib.Tactic

namespace Etch.Verification

-- stream plus a state
structure SStream (ι : Type) (α : Type u) extends Stream ι α where
  q : σ
  dec_ready : DecidablePred ready
  dec_valid : DecidablePred valid
  -- todo: try constructor with autoparam inferInstance for dec fields?

attribute [instance] SStream.dec_valid SStream.dec_ready

namespace SStream

variable {ι : Type} {α : Type u}
[LinearOrder ι]
(s t : SStream ι α)

def map (f : α → β) (s : SStream ι α) : SStream ι β :=
  { s with value := fun q hq => f (s.value q hq) }

variable [Inhabited ι]

def SStream.zero : SStream ι α where
  σ := Unit
  q := ()
  valid _ := False
  ready _ := False
  skip _ _ _ := ()
  index _ := default
  value _ := (nomatch .)
  dec_valid := inferInstance
  dec_ready := inferInstance

instance : Zero (SStream ι α) := ⟨SStream.zero⟩

variable (l : Array (ι × α))

/- todo fix of/to mismatch -/

def ofArray : SStream ι α where
  σ := ℕ
  q := 0
  valid q := q < l.size
  ready q := q < l.size
  index := fun k h => (l[k]'h).1
  value := fun k h => (l[k]'h).2
  skip q hq := fun ⟨j, r⟩ =>
    let i := (l[q]'hq).fst
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q
  dec_valid := inferInstance
  dec_ready := inferInstance

#check IsBounded
-- todo, use IsBounded
partial def toArray_aux (acc : Array (ι × α)) (q : s.σ) : Array (ι × α) :=
  if hv : s.valid q
  then if hr : s.ready q
       then toArray_aux (acc.push (s.index q hv, s.value q hr)) (s.next q)
       else toArray_aux acc (s.next q)
  else acc

-- for summing an (SStream Unit α) into a scalar
partial def toArray_aux' [Add α] (acc : α) (q : s.σ) : α :=
  if s.valid q
  then if hr : s.ready q
       then toArray_aux' (acc + s.value q hr) (s.next q)
       else toArray_aux' acc (s.next q)
  else acc

def toArray : Array (ι × α) := s.toArray_aux #[] s.q

class ToStream (α : Type u) (β : outParam $ Type v) where
  stream : α → β

instance [ToStream β β'] : ToStream  (Array (ι × β)) (SStream ι β') where
  stream := map ToStream.stream ∘ ofArray

class OfStream (α : Type u) (β : outParam $ Type v) where
  eval : α → β

instance [OfStream β β'] : OfStream (SStream ι β) (Array (ι × β')) where
  eval := toArray ∘ map OfStream.eval

-- todo avoid overlapping instances?
instance [OfStream β β'] [Add β'] [Zero β'] : OfStream (SStream Unit β) β' where
  eval := (fun s => s.toArray_aux' 0 s.q) ∘ map OfStream.eval

class Scalar (α : Type u)
instance : Scalar ℕ := ⟨⟩
instance : Scalar Bool := ⟨⟩

instance [Scalar α] : OfStream α α := ⟨id⟩
instance [Scalar α] : ToStream α α := ⟨id⟩

variable
(a b : Stream ι α) (q : a.σ × b.σ)
[DecidablePred a.valid] [DecidablePred a.ready]
[DecidablePred b.valid] [DecidablePred b.ready]

instance : DecidablePred (Stream.mul.Ready a b)
| q =>
  if hav : a.valid q.1 then
    if hbv : b.valid q.2 then
      if har : a.ready q.1 then
        if hbr : b.ready q.2 then
          if eq : a.index q.1 hav = b.index q.2 hbv
            then isTrue ⟨hav, hbv, har, hbr, eq⟩
            else isFalse fun h => eq h.5
        else isFalse fun h => hbr h.4
      else isFalse fun h => har h.3
    else isFalse fun h => hbv h.2
  else isFalse fun h => hav h.1


variable [Mul α]
variable (sa sb : SStream ι α)

def mul (a b : SStream ι α) : SStream ι α := {
  a.toStream.mul b.toStream with
  q := (a.q, b.q),
  dec_ready := by dsimp only [Stream.mul, Stream.ready]; exact inferInstance
  dec_valid := by dsimp only [Stream.mul, Stream.ready]; exact inferInstance }
instance : Mul (SStream ι α) := ⟨mul⟩

def contract (a : SStream ι α) : SStream Unit α := {
  a.toStream.contract with
  q := a.q,
  dec_ready := by
    dsimp only [Stream.contract]
    exact inferInstance
  dec_valid := by
    dsimp only [Stream.contract]
    exact inferInstance
}

/- New stream combinator: fused subtraction.
   Applicable to semirings like ℕ, Bool that lack additive inverses
-/
section sub

variable [Zero α] [Sub α]
variable (sa sb : SStream ι α)

variable
(a b : Stream ι α) (qa : a.σ) (qb : b.σ)
[DecidablePred a.valid] [DecidablePred a.ready]
[DecidablePred b.valid] [DecidablePred b.ready]

structure Stream.sub.Ready : Prop where
  hv : a.valid qa
  h₂ : a.ready qa
  le : a.toOrder' qa ≤ b.toOrder' qb

def sub.Ready.dec : Decidable (Stream.sub.Ready a b qa qb) :=
  if hv : a.valid qa then
    if hr : a.ready qa then
      if le : a.toOrder' qa ≤ b.toOrder' qb
      then isTrue ⟨hv, hr, by convert le⟩
      else isFalse fun h => le (by convert h.3)
    else isFalse fun h => hr h.2
  else isFalse fun h => hv h.1

instance : Decidable (Stream.sub.Ready a b qa qb) := sub.Ready.dec a b qa qb

def sub : SStream ι α where
  σ := sa.σ × sb.σ
  valid s := sa.valid s.1
  ready q := Stream.sub.Ready sa.toStream sb.toStream q.1 q.2
  skip p hp i := (sa.skip p.1 hp i, sb.skip' p.2 i)
  index s h := sa.index s.1 h
  value s h :=
    sa.value s.1 h.h₂ -
      if hv : sb.valid s.2
      then if eq : sa.toOrder s.1 h.hv = sb.toOrder s.2 hv
           then sb.value s.2 $ by cases h; dsimp at *; simpa [Stream.toOrder, *] using congr_arg Prod.snd eq
           else 0
      else 0
  q := (sa.q, sb.q)
  dec_valid := inferInstance
  dec_ready := inferInstance

instance : Sub (SStream ι α) := ⟨sub⟩

end sub

section add
variable [Zero α] [Add α] (sa sb : SStream ι α)

def add : SStream ι α := { sa.toStream.add sb.toStream with
  q := (sa.q, sb.q)
  dec_valid := by dsimp only [Stream.add, Stream.ready]; exact inferInstance
  dec_ready := by dsimp only [Stream.add, Stream.ready]; exact inferInstance
}

instance : Add (SStream ι α) := ⟨add⟩
end add

section tests
open OfStream ToStream

def l1 := stream #[(1, 3), (3, 2), (5, 2)]
def l2 := stream #[(1, 4), (2, 1), (5, 2)]
def l3 := stream $ Array.range 2000 |>.map fun n => (n,n)

def m1 :=
  let m1' : Array (ℕ × Array (ℕ × ℕ)) :=
    Array.range 3 |>.map (.+1) |>.map $ fun n =>
      (n, Array.range n |>.map fun m => (m, m+10))
  stream m1'

#eval eval $ contract l1
#eval eval $ contract (l1 * l2)
#eval eval $ l1 + l2 - l2
#eval eval $ l1 * l2 - l2

#eval eval $ m1
#eval eval $ m1 * m1
#eval eval $ m1 + m1
#eval eval $ SStream.map contract $ m1 + m1
#eval eval $ contract $ SStream.map contract $ m1 + m1
#eval eval $ m1 - m1

def b1 := stream #[(1, true), (2, true), (5, true)]
def b2 := stream #[(1, true), (5, true)]

instance : Zero Bool := ⟨false⟩
instance : Add Bool := ⟨or⟩
instance : Mul Bool := ⟨and⟩

#eval eval $ b1 * b2
#eval eval $ contract $ b1

end tests

end Etch.Verification.SStream
