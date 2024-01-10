import Etch.Verification.Semantics.SkipStream
import Etch.Verification.Semantics.Mul
import Etch.Verification.Semantics.Add
import Etch.Verification.Semantics.Contract

import Mathlib.Tactic

def Array.toSet (arr : Array α) := arr.map fun n => (n, true)

namespace Etch.Verification

section
variable (s : Stream ι α) [DecidablePred s.ready] [DecidablePred s.valid]
-- @[macro_inline] def Stream.next' (q : s.σ) (h : s.valid q) : s.σ := s.skip q h (s.index q h, s.ready q)
@[macro_inline]
def Stream.next'' (q : s.σ) (h : decide (s.valid q) = true) : s.σ := s.skip q (by simpa using h) (s.index q (by simpa using h), s.ready q)
end

-- stream plus a state
structure SStream (ι : Type) (α : Type u) extends Stream ι α where
  q : σ
  weaken : ∀ {q : σ}, ready q → valid q
  dec_ready : DecidablePred ready
  dec_valid : DecidablePred valid
  -- todo: try constructor with autoparam inferInstance for dec fields?

attribute [instance] SStream.dec_valid SStream.dec_ready
--attribute [inline]   SStream.dec_ready SStream.dec_valid

namespace SStream

variable
{ι : Type}
[LinearOrder ι]
{α : Type u}
(s t : SStream ι α)

@[macro_inline, specialize]
def map (f : α → β) (s : SStream ι α) : SStream ι β :=
  { s with value := fun q hq => f (s.value q hq) }

variable [Inhabited ι]

def SStream.zero : SStream ι α where
  q := ()
  valid _ := False
  ready _ := False
  skip _ _ _ := ()
  index _ := default
  value _ := (nomatch .)
  weaken := id
  dec_ready := inferInstance
  dec_valid := inferInstance

instance : Zero (SStream ι α) := ⟨SStream.zero⟩

variable (l : Array (ι × α))

/- todo fix of/to mismatch -/

@[macro_inline]
def ofArray (l : Array (ℕ × α)) : SStream ℕ α where
  σ := ℕ
  q := 0
  valid q := q < l.size
  ready q := q < l.size
  index k h := (l[k]'h).1
  value k h := (l[k]'h).2
  skip q hq := fun ⟨j, r⟩ =>
    let i := (l[q]'hq).fst
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q
  weaken := id
  dec_valid := inferInstance
  dec_ready := inferInstance

@[macro_inline]
def ofArrayPair (is : Array ℕ) (vs : Array α) (heq : is.size = vs.size) : SStream ℕ α where
  σ := ℕ
  q := 0
  valid q := q < is.size
  ready q := q < is.size
  index k h := (is[k]'h)
  value k h := (vs[k]'(heq ▸ h))
  skip q hq := fun ⟨j, r⟩ =>
    let i := (is[q]'hq)
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q
  weaken := id
  dec_valid := inferInstance
  dec_ready := inferInstance


--def ofFloatArray (is : Array ι) (vs : FloatArray) (eq : is.size = vs.size) : SStream ι Float where
--  σ := ℕ
--  q := 0
--  valid q := q < is.size
--  ready q := q < is.size
--  index k h := (is[k]'h)
--  value k h := (vs[k]'(eq ▸ h))
--  skip q hq := fun ⟨j, r⟩ =>
--    let i := is[q]'hq
--    if r then if i ≤ j then q+1 else q
--         else if i < j then q+1 else q
--  weaken := id
--  dec_valid := inferInstance
--  dec_ready := inferInstance

#check IsBounded

-- todo, use IsBounded
partial def toArray_aux (acc : Array (ι × α)) (q : s.σ) : Array (ι × α) :=
  if hv : s.valid q
  then if hr : s.ready q
       then toArray_aux (acc.push (s.index q hv, s.value q hr)) (s.next q)
       else toArray_aux acc (s.next q)
  else acc

-- for summing an (SStream Unit α) into a scalar
--partial def toArray_aux' [Add α] (acc : α) (q : s.σ) : α :=
--  if s.valid q
--  then if hr : s.ready q
--       then toArray_aux' (acc + s.value q hr) (s.next q)
--       else toArray_aux' acc (s.next q)
--  else acc

--def Stream.next' (q : s.σ) (h : s.valid q) : s.σ := s.skip q h (s.index q h, s.ready q)

@[inline] partial def toArray_aux' [hadd : Add α] (s : SStream ι α) (acc : α) (q : s.σ) : α :=
  -- we need valid/ready functions to be inlined here
  let rec @[specialize] go add (valid : s.σ → Bool) (ready : s.σ → Bool) (value : (x : s.σ) → ready x → α) (next : (x : s.σ) → valid x → s.σ) (acc : α) q :=
    if hv : valid q then
      let q' := (next q hv)
      if hr : ready q
           then go add valid ready value next (add acc $ value q hr) q'
           else go add valid ready value next acc q'
    else acc
  go hadd.add s.valid s.ready (fun x h => s.value x (by simpa using h)) s.next'' acc q

def toArray := s.toArray_aux #[] s.q

class ToStream (α : Type u) (β : outParam $ Type v) where
  stream : α → β

instance [ToStream β β'] : ToStream  (Array (ℕ × β)) (SStream ℕ β') where
  stream := map ToStream.stream ∘ ofArray

def Vec α n := { x : Array α // x.size = n }

instance [ToStream β β'] : ToStream  (Vec ℕ n × Vec β n) (SStream ℕ β') where
  stream := map ToStream.stream ∘ (fun (a, b) => ofArrayPair a.1 b.1 (a.property.trans b.property.symm))

class OfStream (α : Type u) (β : outParam $ Type v) where
  eval : α → β

instance [OfStream β β'] : OfStream (SStream ι β) (Array (ι × β')) where
  eval := toArray ∘ map OfStream.eval

-- todo avoid overlapping instances?
instance [OfStream β β'] [Add β'] [Zero β'] : OfStream (SStream Unit β) β' where
  eval := (fun s => s.toArray_aux' 0 s.q) ∘ map OfStream.eval

-- maybe faster
instance : OfStream (SStream ι Nat) (Array (ι × Nat)) where
  eval := toArray

instance : OfStream (SStream Unit Nat) Nat where
  eval := fun s => s.toArray_aux' 0 s.q

class Scalar (α : Type u)
instance : Scalar ℕ := ⟨⟩
instance : Scalar Bool := ⟨⟩

--instance [Scalar α] : OfStream α α := ⟨id⟩
instance [Scalar α] : ToStream α α := ⟨id⟩

variable
(a b : Stream ι α) (q : a.σ × b.σ)
[DecidablePred a.valid] [DecidablePred a.ready]
[DecidablePred b.valid] [DecidablePred b.ready]

instance : DecidablePred (Stream.mul.Ready a b)
| _ => decidable_of_iff _ (Stream.mul.Ready_iff _ _ _).symm

variable [Mul α]

@[macro_inline]
def mul (a b : SStream ι α) : SStream ι α := {
  a.toStream.mul b.toStream with
  q := (a.q, b.q)
  weaken := fun h => ⟨h.v₁, h.v₂⟩
  -- todo: change this back to inferInstance?
  dec_valid := fun p =>
   match a.dec_valid p.1 with
   | isFalse fa => isFalse fun p => fa p.1
   | isTrue ta => match b.dec_valid p.2 with
     | isFalse fb => isFalse fun p => fb p.2
     | isTrue tb => isTrue ⟨ta, tb⟩
   -- by dsimp only [Stream.mul, Stream.ready]; exact inferInstance
  dec_ready := by dsimp only [Stream.mul, Stream.ready]; exact inferInstance
}

instance : Mul (SStream ι α) := ⟨mul⟩

instance [HMul α β γ] : HMul (ι → α) (SStream ι β) (SStream ι γ) where
  hMul f x := { x with value := fun s h => f (x.index s $ x.weaken h) * x.value s h }

instance [HMul α β γ] : HMul (SStream ι α) (ι → β) (SStream ι γ) where
  hMul x f := { x with value := fun s h => x.value s h * f (x.index s $ x.weaken h) }

def exp (a : SStream ι' α) : ι → SStream ι' α := fun _ => a

@[macro_inline]
def contract (a : SStream ι α) : SStream Unit α := {
  a.toStream.contract with
  q := a.q
  weaken := a.weaken
  dec_ready := by
    dsimp only [Stream.contract]
    exact inferInstance
  dec_valid := by
    dsimp only [Stream.contract]
    exact inferInstance
}

/- New operation: fused saturating subtraction.
   applicable to semirings like ℕ, Bool that lack additive inverses
   and have the property 0 - x = 0.
-/
section sub

variable [Zero α] [Sub α]
variable (sa sb : SStream ι α)

variable
(a b : Stream ι α) (qa : a.σ) (qb : b.σ)
[DecidablePred a.valid] [DecidablePred a.ready]
[DecidablePred b.valid] [DecidablePred b.ready]

@[mk_iff]
structure Stream.sub.Ready : Prop where
  valid : a.valid qa
  ready : a.ready qa
  le : a.toOrder' qa ≤ b.toOrder' qb

instance : Decidable (Stream.sub.Ready a b qa qb) :=
decidable_of_iff _ (Stream.sub.Ready_iff _ _ _ _).symm

def sub : SStream ι α where
  σ := sa.σ × sb.σ
  valid s := sa.valid s.1
  ready q := Stream.sub.Ready sa.toStream sb.toStream q.1 q.2
  skip p hp i := (sa.skip p.1 hp i, sb.skip' p.2 i)
  index s h := sa.index s.1 h
  value s h :=
    (sa.value s.1 h.ready) -
      if valid : sb.valid s.2
      then if eq : sa.toOrder s.1 h.valid = sb.toOrder s.2 valid
           then sb.value s.2 $ by cases h; dsimp at *; simpa [Stream.toOrder, *] using congr_arg Prod.snd eq
           else 0
      else 0
  q := (sa.q, sb.q)
  weaken := fun h => h.valid
  dec_valid := inferInstance
  dec_ready := inferInstance

instance : Sub (SStream ι α) := ⟨sub⟩

end sub

section add
variable [Zero α] [Add α] (sa sb : SStream ι α)

def add : SStream ι α := {
  sa.toStream.add sb.toStream with
  q := (sa.q, sb.q)
  weaken := fun
    | Or.inl h => Or.inl $ sa.weaken h.2
    | Or.inr h => Or.inr $ sb.weaken h.2
  dec_valid := by dsimp only [Stream.add, Stream.ready]; exact inferInstance
  dec_ready := by dsimp only [Stream.add, Stream.ready]; exact inferInstance
}

instance : Add (SStream ι α) := ⟨add⟩
end add

infixr:10 " →ₛ " => SStream
abbrev NN (α) := ℕ →ₛ ℕ →ₛ α
abbrev UU (α) := Unit →ₛ Unit →ₛ α
@[macro_inline]
def contract2 : NN α → UU α := contract ∘ SStream.map contract

end Etch.Verification.SStream

open Etch.Verification.SStream
open OfStream ToStream

@[macro_inline]
def defer (m : IO Unit) : Unit → IO Unit := fun _ => m

def time (s : String) (m : Unit → IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← m ()
  let t1 ← IO.monoMsNow
  IO.println s!"[{s}] time: {t1-t0}"
  pure v

#check FloatArray

def data num := Array.range num
@[inline]
def vecStream (num : Nat) := stream $ Array.range num |>.map fun n => (n,n)
@[inline]
def vecStream' (num : Nat) :=
  let v : Vec ℕ num := ⟨Array.range num, by sorry⟩
  stream $ (v, v)

#eval (Array.range 5 |>.map fun n => (n,n))
--#eval
--  let s := stream (Array.range 5 |>.map fun n => (n,n))
--  eval $ contract $ s * s

def doTest' [ToString α] label (s : Unit → α) := do
  let v ← time label (fun x => pure (s x))
  IO.println s!"result: {v}"

def doTest [OfStream α ℕ] label (s : α) := do
  let v ← time label (fun _ => pure $ eval s)
  IO.println s!"result: {v}"

@[inline] unsafe def myArrayLoop {β : Type v} [Add β] (as : Array β) (b : β) : β :=
  let sz := USize.ofNat as.size
  let rec @[specialize] loop (i : USize) (b : β) : β :=
    if i < sz then
      let a := as.uget i lcProof
      loop (i+1) (b + a)
    else
      b
  loop 0 b

section compiler_trace
def str1 := vecStream 10
--set_option trace.compiler.inline true
--set_option trace.compiler.specialize true
set_option trace.compiler.stage2 true
def thetest := eval (contract (vecStream 10)) --
def thetest' := eval (contract (vecStream' 10)) -- !!!
def multest := eval (contract (str1 * str1)) --
unsafe example := myArrayLoop #[] 0
end compiler_trace

def test1 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let arr_ := Array.range num
  --let arr := arr_ |>.map fun n => (n,n)
  time "lean forIn" fun _ =>
    for _ in [0:10] do
      let mut m := 0
      for i in arr_ do
        m := m + i
      IO.println s!"result: {m}"

--unsafe def test2 (num : Nat) : IO Unit := do
--  IO.println "-----------"
--  let arr := Array.range num
--  time "myForIn" fun _ =>
--    for _ in [0:10] do
--      let x := myArrayLoop arr 0
--      IO.println s!"{x}"

def test3 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := contract $ vecStream num
  time "stream" fun _ =>
    for _ in [0:10] do
      let x := eval s
      IO.println s!"{x}"

def test3' (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := contract $ vecStream' num
  time "stream (ofPair)" fun _ =>
    for _ in [0:10] do
      let x := eval s
      IO.println s!"{x}"

def mulTest (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream' num
  let s := contract $ v * v
  time "stream mul" fun _ =>
    for _ in [0:1] do
      let x := eval s
      IO.println s!"{x}"
  pure ()

@[macro_inline]
def mat (num : Nat) :=
  let m1 : Array (ℕ × Array (ℕ × ℕ)) :=
    Array.range (2*num).sqrt |>.map (.+1) |>.map $ fun n =>
      (n, Array.range n |>.map fun m => (m, m+10))
  stream m1

def matTest1 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := contract2 $ mat num
  time "matrix sum" fun _ =>
    for _ in [0:10] do
      let x := eval s
      IO.println s!"{x}"

def matTest2 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let m := mat num
  let s := contract2 $ m * m
  time "matrix prod sum" fun _ =>
    for _ in [0:1] do
      let x := eval s
      IO.println s!"{x}"

unsafe def main (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 100
  IO.println s!"test of size {num}"
  /-
  let t1 (_ : Unit) := do
    let x := eval $ contract (l3 * l3)
    IO.println s!"result: {x}"
  let t3 := do
    let x := eval $ m2
    IO.println s!"result: {x.size}"
  let arr' := arr.map fun n => (n, n)
  -/
  IO.println "starting"
  --doTest "contraction s" $ contract (stream arr' : ℕ →ₛ ℕ)
  --doTest "contraction **2" (contract $ l3 * l3)
  --time "loop" $ tl3 num

  test1 num
  --test2 num
  --test3 num
  test3' num
  mulTest num
  matTest1 num
  matTest2 num

  --doTest' "loop myForIn" $ (fun _ => myArrayLoop arr 0)
  --time "contraction" t0
  --time "contraction ** 2" t1
  pure ()

-- contribution? no bounds checking
-- sub relation to left join?


/-
def SStream.fun (v : ι → α) (min : ι) : SStream ι α where
  σ := ι
  q := min
  valid _ := True
  ready _ := True
  skip _ _ p := p.1 -- ignores p.2; this makes the stream not strictly monotonic
  index i _ := i
  value i _ := v i
  dec_ready := inferInstance
  dec_valid := inferInstance

-/
--inductive TypedStream (α : Type) : List Type → Type 1
--| base {σ : Type} (v : σ → α) : TypedStream α []
--| level (l : SStream ι (TypedStream α is)) : TypedStream α (i :: is)
