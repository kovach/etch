/-
This file implements a prototype of indexed stream fusion,
  an optimization to speed up programs that manipulate (nested) associative arrays.

Authors: Scott Kovach
-/

/- Vs SkipStream, we redefine valid/ready to return Bool; this is easier to work with for now -/
--import Etch.Verification.Semantics.SkipStream
--import Etch.Verification.Semantics.Mul
--import Etch.Verification.Semantics.Add
--import Etch.Verification.Semantics.Contract

/- General notes:

See Stream.mul for the key motivation for the stream interface

A key function is Stream.fold (previously called toArray_aux)
  This generates the top-level loop
  We want this to include no calls to lean_apply_[n] and minimal allocations
    (so far there may still some tuples allocated for multiplication states)

Performance is sensitive to the particular classes used.
We need to be careful to redefine any instances to add @[inline]

The choice of inline vs macro_inline is not intentional anywhere except for `Stream.next`, where macro_inline seems to be necessary
-/

/- todo:
  do manual loop with rbmap
  stream for rbmap

  vecMulSum3

  prove (Array.range n).size = n
-/

import Mathlib.Data.Prod.Lex
import Std.Data.RBMap

open Std (RBMap)

namespace Etch.Verification

structure Stream (ι : Type) (α : Type u) : Type max 1 u where
  σ : Type
  valid : σ → Bool
  ready : σ → Bool
  skip : ∀ x, valid x → ι ×ₗ Bool → σ
  index : ∀ x : σ, valid x → ι
  value : ∀ x : σ, ready x → α

namespace Stream
variable {ι : Type} {α : Type _}
variable [Mul α]
[LinearOrder ι] -- this is ok
--[h : LE ι] [DecidableRel h.le] [DecidableEq ι]

variable (s : Stream ι α)

-- hack: redefine these instances to ensure they are inlined
--  see: instDecidableLeToLEToPreorderToPartialOrder
section
variable [LinearOrder α]
@[inline] instance (a b : α) : Decidable (a < b) := LinearOrder.decidableLT a b
@[inline] instance (a b : α) : Decidable (a ≤ b) := LinearOrder.decidableLE a b
@[inline] instance (a b : α) : Decidable (a = b) := LinearOrder.decidableEq a b
end

@[simps, macro_inline]
def contract (s : Stream ι α) : Stream Unit α where
  σ := s.σ
  valid := s.valid
  ready := s.ready
  index := default
  value := s.value
  skip q hq i := s.skip q hq (s.index q hq, i.2)

end Stream

section Mul
@[unbox] inductive Prod (α β : Type) | mk : α → β → Prod α β

variable [Mul α]
--[LinearOrder ι] -- the generated code is about 2x slower
[h : LE ι] [DecidableRel h.le] [DecidableEq ι]

/- This combinator is a primary motivation for Stream -/
@[macro_inline]
def Stream.mul [HMul α β γ] (a : Stream ι α) (b : Stream ι β) : Stream ι γ where
  σ := a.σ × b.σ
  valid p := a.valid p.1 && b.valid p.2
  ready p :=
  /- for experimentation: -/
  --true
  --a.index p.1 sorry = b.index p.2 sorry
  if hv : a.valid p.1 && b.valid p.2
    then a.ready p.1 && b.ready p.2 &&
         a.index p.1 (by simp at hv; exact hv.1) = b.index p.2 (by simp at hv; exact hv.2)
    else false
  index p hv :=
    let ai := (a.index p.1 (by simp at hv; exact hv.1))
    let bi := (b.index p.2 (by simp at hv; exact hv.2))
    if ai ≤ bi then bi else ai
    --if ai = bi then ai else bi -- substantially faster than ≤; maybe still some performance to find
  value p hr := by
    dsimp at hr
    split_ifs at hr with h
    simp at hr
    exact a.value p.1 hr.1.1 * b.value p.2 hr.1.2
  --value p _ := a.value p.1 sorry * b.value p.2 sorry
  skip p hp i :=
    let p1 := a.skip p.1 (by simp at hp; exact hp.1) i
    let p2 := b.skip p.2 (by simp at hp; exact hp.2) i
    ⟨p1, p2⟩

end Mul

-- stream plus a state
structure SStream (ι : Type) (α : Type u) extends Stream ι α where
  q : σ
  weaken : ∀ {q : σ}, ready q → valid q

-- for some reason, this definition *definitely* needs to be macro_inline for performance
-- everything else is probably safe at @[inline]
@[macro_inline]
def Stream.next (s : Stream ι α) (q : s.σ) (h : (s.valid q) = true) (ready : Bool) : s.σ := s.skip q h (s.index q h, ready)

namespace SStream

variable
{ι : Type} [LinearOrder ι] {α : Type u}

@[macro_inline, specialize]
def map (f : α → β) (s : SStream ι α) : SStream ι β :=
  { s with value := fun q hq => f (s.value q hq) }

variable [Inhabited ι]

/- Converting data into a SStream -/
def SStream.zero : SStream ι α where
  q := (); valid _ := False; ready _ := False;
  index _ := default; value _ := (nomatch .);
  skip _ _ _ := ();
  weaken := id

instance : Zero (SStream ι α) := ⟨SStream.zero⟩

-- deprecated
@[macro_inline]
def ofArray (l : Array (ℕ × α)) : SStream ℕ α where
  σ := ℕ
  q := 0
  valid q := q < l.size
  ready q := q < l.size
  index k h := (l[k]'(by simpa using h)).1
  value k h := (l[k]'(by simpa using h)).2
  skip q hq := fun ⟨j, r⟩ =>
    let i := (l[q]'(by simpa using hq)).fst
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q
  weaken := id

@[macro_inline]
def ofArrayPair (is : Array ι) (vs : Array α) (eq : is.size = vs.size) : SStream ι α where
  σ := ℕ
  q := 0
  valid q := q < is.size
  ready q := q < is.size
  index k h := (is[k]'(by simpa using h))
  value k h := (vs[k]'(eq ▸ (by simpa using h)))
  skip q hq := fun ⟨j, r⟩ =>
    let i := (is[q]'(by simpa using hq))
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q
  weaken := id

-- not tested yet
@[macro_inline]
def ofFloatArray (is : Array ι) (vs : FloatArray) (eq : is.size = vs.size) : SStream ι Float where
  σ := ℕ
  q := 0
  valid q := q < is.size
  ready q := q < is.size
  index k h := (is[k]'(by simpa using h))
  value k h := (vs[k]'(eq ▸ (by simpa using h)))
  skip q hq := fun ⟨j, r⟩ =>
    let i := is[q]'(by simpa using hq)
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q
  weaken := id

class ToStream (α : Type u) (β : outParam $ Type v) where
  stream : α → β

instance [ToStream β β'] : ToStream  (Array (ℕ × β)) (SStream ℕ β') where
  stream := map ToStream.stream ∘ ofArray

def Vec α n := { x : Array α // x.size = n }

structure Level (ι α : Type) (n : ℕ) where
  is : Vec ι n
  vs : Vec α n

def FloatVec n := { x : FloatArray // x.size = n }

instance [ToStream β β'] : ToStream  (Level ι β n) (SStream ι β') where
  stream := map ToStream.stream ∘ (fun ⟨is, vs⟩ => ofArrayPair is.val vs.val (by simp [is.2, vs.2]))

--def Search (α : Type) := α
--instance [ToStream β β'] : ToStream (Search (Vec ℕ n × Vec β n)) (SStream ℕ β') where
--  stream := map ToStream.stream ∘ (fun (a, b) => searchStreamOfArrayPair a.1 b.1 (a.property.trans b.property.symm))

instance : ToStream  (Vec ℕ n × FloatVec n) (SStream ℕ Float) where
  stream := fun (a, b) => ofFloatArray a.1 b.1 (a.property.trans b.property.symm)

/- Converting a Stream into Data -/
-- this definition follows the same inline/specialize pattern as Array.forInUnsafe
@[inline] partial def _root_.Etch.Verification.Stream.fold (add : β → ι → α → β) (s : Stream ι α) (acc : β) (q : s.σ) : β :=
  let rec @[specialize] go add (valid : s.σ → Bool) (ready : s.σ → Bool)
    (index : (x : s.σ) → valid x → ι) (value : (x : s.σ) → ready x → α)
    (next : (x : s.σ) → valid x → Bool → s.σ) (acc : β) q :=
    if hv : valid q then
      if hr : ready q
           then go add valid ready index value next (add acc (index q hv) $ value q hr) (next q hv true)
           else go add valid ready index value next acc (next q hv false)
    else acc
  go add s.valid s.ready s.index (fun x h => s.value x (by simpa using h)) s.next acc q

@[inline] def toArrayPair (s : SStream ι α) : Array ι × Array α :=
  s.fold (fun (is, vs) i v => (is.push i, vs.push v)) (#[], #[]) s.q

-- outParam not ultimately desirable, but simplifies testing for now
class OfStream (α : Type u) (β : outParam $ Type v) where
  eval : α → β

instance [OfStream β β'] [Add β'] [Zero β'] : OfStream (SStream Unit β) β' where
  eval := (fun s => s.fold (fun a _ b => a + b) 0 s.q) ∘ map OfStream.eval

instance [OfStream β β'] : OfStream (SStream ι β) (Array ι × Array β') where
  eval := toArrayPair ∘ map OfStream.eval

class Scalar (α : Type u)
instance : Scalar ℕ := ⟨⟩
instance : Scalar Float := ⟨⟩
instance : Scalar Bool := ⟨⟩

instance [Scalar α] : OfStream α α := ⟨id⟩
instance [Scalar α] : ToStream α α := ⟨id⟩

/- various shortcuts/alternatives, probably no longer needed -/
-- maybe faster
--instance : OfStream (SStream ι Nat) (Array (ι × Nat)) where
--  eval := toArray
--instance : OfStream (SStream ι Nat) (Array ι × Array Nat) where
--  eval s := (toArrayPair_aux s (#[], #[]) s.q)
-- todo: without this shortcut, memory usage explodes
--instance [Zero α] [Add α] [Scalar α] : OfStream (SStream Unit α) α where
--  eval := fun s => s.toArray_aux' (fun a _ b => a + b) 0 s.q
--@[inline] partial def toArray_aux (s : SStream ι α) (acc : Array (ι × α)) (q : s.σ) := toArray_aux' (fun arr i v => arr.push (i,v)) s acc q
--@[inline] def toArray := s.toArray_aux #[] s.q
--instance [OfStream β β'] : OfStream (SStream ι β) (Array (ι × β')) where
--  eval := toArray ∘ map OfStream.eval

@[macro_inline]
def mul [HMul α β γ] (a : SStream ι α) (b : SStream ι β) : SStream ι γ := {
  a.toStream.mul b.toStream with
  q := ⟨a.q, b.q⟩
  weaken := fun h => by simp [Stream.mul] at *; split_ifs at h; assumption
}

infixr:25 " →ₛ " => SStream

@[macro_inline]
instance [HMul α β γ] : HMul (ℕ →ₛ α) (ℕ →ₛ β) (ℕ →ₛ γ) := ⟨mul⟩

@[macro_inline]
instance [HMul α β γ] : HMul (ι → α) (ι →ₛ β) (ι →ₛ γ) where
  hMul f x := { x with value := fun s h => f (x.index s $ x.weaken h) * x.value s h }

@[macro_inline]
instance [HMul α β γ] : HMul (ι →ₛ α) (ι → β) (ι →ₛ γ) where
  hMul x f := { x with value := fun s h => x.value s h * f (x.index s $ x.weaken h) }

@[macro_inline]
def expand (a : α) : ι → α := fun _ => a

@[inline]
def _root_.Std.RBMap.toFn [Zero α] (map : RBMap ι α Ord.compare) : ι → α := fun i => map.find? i |>.getD 0

@[macro_inline]
def contract (a : SStream ι α) : SStream Unit α := {
  a.toStream.contract with
  q := a.q
  weaken := a.weaken
}

abbrev NN (α) := ℕ →ₛ ℕ →ₛ α
abbrev UU (α) := Unit →ₛ Unit →ₛ α

@[macro_inline]
def contract2 : NN α → UU α := contract ∘ SStream.map contract

end SStream

open Etch.Verification.SStream
open OfStream ToStream

def time (s : String) (m : Unit → IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← m ()
  let t1 ← IO.monoMsNow
  IO.println s!"[{s}] time: {t1-t0}"
  pure v

@[inline] def vecStream (num : Nat) := stream $ Array.range num |>.map fun n => (n,n)
@[inline] def vecStream' (num : Nat) :=
  let v : Vec ℕ num := ⟨Array.range num, by sorry⟩
  stream $ Level.mk v v

@[inline] def floatVecStream (num : Nat) :=
  let is : Vec ℕ num := ⟨Array.range num, by sorry⟩
  let vs : FloatVec num := ⟨Array.range num |>.toList.map (fun x => x.toFloat) |>.toFloatArray, by sorry⟩
  stream $ (is, vs)

-- adjusts size so that there are ~num non-zero entries
@[macro_inline]
def mat (num : Nat) :=
  let m1 : Array (ℕ × Array (ℕ × ℕ)) :=
    Array.range (2*num).sqrt |>.map (.+1) |>.map $ fun n =>
      (n, Array.range n |>.map fun m => (m, m+10))
  stream m1

@[macro_inline]
def mat' (num : Nat) :=
  let m1 : Array (ℕ × Array (ℕ × ℕ)) :=
    Array.range num |>.map (.+1) |>.map $ fun n =>
      (n, Array.range n |>.map fun m => (m, m+10))
  stream m1

-- these tests need to be separate defs for profile legibility
namespace test
def baseline (num : Nat) : IO Unit := do
  IO.println "-----------"
  let arr_ := Array.range num
  --let arr := arr_ |>.map fun n => (n,n)
  time "baseline (forIn) vec sum" fun _ =>
    for _ in [0:10] do
      let mut m := 0
      for i in arr_ do
        m := m + i
      IO.println s!"{m}"

def baselineRB (num : Nat) : IO Unit := do
  IO.println "-----------"
  let arr_ := Array.range num
  let map := RBMap.ofList (arr_.toList.map fun i => (i, 1)) Ord.compare
  --let arr := arr_ |>.map fun n => (n,n)
  let test map := do
    time "forIn vec * rbmap sum" fun _ => -- about 10x slower than vecMulSum
      for _ in [0:10] do
        let mut m := 0
        for i in arr_ do
          m := m + i * (map.toFn i)
        IO.println s!"{m}"
    time "forIn rbmap * vec sum" fun _ => -- about 5x slower than vecMulSum
      for _ in [0:10] do
        let mut m := 0
        for (i,v) in map do
          m := m + arr_.get! i * v
        IO.println s!"{m}"
  test map

def vecSum_slow (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := contract $ vecStream num
  time "vec sum (slower)" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval s
      IO.println s!"{x}"

def vecSum (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := contract $ vecStream' num
  time "vec sum" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval s
      IO.println s!"{x}"

def testFloat (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := contract $ floatVecStream num
  time "float stream" fun _ =>
    for _ in [0:10] do
      let x : Float := eval s
      IO.println s!"{x}"

--def vecMul_slow (num : Nat) : IO Unit := do
--  IO.println "-----------"
--  let v := vecStream' num
--  let v' := vecStream' num |>.map fun _ => 1
--  let s := v * v'
--  time "vec mul (slower)" fun _ =>
--    for _ in [0:10] do
--      let x : Array (ℕ × ℕ) := eval s
--      IO.println s!"{x.size}"
--  pure ()

def vecMul (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream' num
  let v' := vecStream' num |>.map fun _ => 1
  let s := v * v'
  time "vec mul" fun _ =>
    for _ in [0:10] do
      let x : Array ℕ × Array ℕ := eval s
      IO.println s!"{x.1.size}"
  pure ()

def vecMulSum (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream' num
  let v' := vecStream' num |>.map fun _ => 1
  let s := contract $ v * v'
  time "vec mul sum" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval s
      IO.println s!"{x}"
  pure ()

-- todo: this has allocation and other perf issues
def vecMulSum3 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream' num
  let v' := vecStream' num |>.map fun _ => 1
  let s := contract $ v * v' * v'
  time "vec mul 3 sum" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval s
      IO.println s!"{x}"
  pure ()

def matSum (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := contract2 $ mat num
  time "matrix sum" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval s
      IO.println s!"{x}"

def matProdSum (num : Nat) : IO Unit := do
  IO.println "-----------"
  let m := mat num
  let s := contract2 $ m * m
  time "matrix prod sum" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval s
      IO.println s!"{x}"

def _root_.Nat.cubeRoot (n : Nat) : Nat :=
  if n ≤ 1 then n else
  iter n (n / 2)
where
  /-- Auxiliary for `sqrt`. If `guess` is greater than the integer square root of `n`,
  returns the integer square root of `n`. -/
  iter (n guess : Nat) : Nat :=
    let next := (2*guess + n / (guess * guess)) / 3
    if _h : next < guess then
      iter n next
    else
      guess
termination_by iter guess => guess

@[macro_inline]
def aMatMul (n : Nat) : ℕ →ₛ ℕ →ₛ Unit →ₛ ℕ :=
  let m := mat' (4*n).cubeRoot;
  let m1 : ℕ →ₛ ℕ →  ℕ →ₛ ℕ := map expand m
  let m2 : ℕ →ₛ ℕ →ₛ ℕ → ℕ := map (map expand) m
  let s  : ℕ →ₛ ℕ →ₛ ℕ →ₛ ℕ := m1 * m2
  map (map contract) $ s

def matMultiplySum (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := contract2 $ aMatMul num
  time "matrix multiply (inner-product) sum" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval s
      IO.println s!"{x}"

def matMultiply (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := aMatMul num
  time "matrix multiply (inner-product)" fun _ =>
    for _ in [0:10] do
      let x := eval s
      --let x : (Array ℕ × (Array ℕ × Array ℕ)) := eval s
      IO.println s!"{x.1.size}"

end test

end Etch.Verification

open Etch.Verification
open Etch.Verification.SStream
open OfStream ToStream

-- !!
unsafe def _root_.main (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"

  test.baseline num
  test.vecSum num
  --test.baselineRB num
  test.vecMulSum num      -- ideally about 2x vecSum
  test.vecMulSum3 num      -- ideally about 2x vecSum
  --test.vecMulSumSearch num
  --test.vecMul num         -- ideally about 1x vecMulSum (currently 3x slower, but that's almost all Array.push. try pre-allocating?)
  test.matSum num         -- ideally about 1x vecSum
  --test.matProdSum num     -- ... 2x matSum
  test.matMultiplySum num
  --test.matMultiply num

section appendix
-- simple inline/specialize example
@[inline] unsafe def myArrayLoop {β : Type v} [Add β] (as : Array β) (b : β) : β :=
  let sz := USize.ofNat as.size
  let rec @[specialize] loop (i : USize) (b : β) : β :=
    if i < sz then
      let a := as.uget i lcProof
      loop (i+1) (b + a)
    else
      b
  loop 0 b

def test1Floats (num : Nat) : IO Unit := do
  IO.println "-----------"
  let arr_ := Array.range num |>.map Nat.toFloat |>.toList.toFloatArray
  --let arr := arr_ |>.map fun n => (n,n)
  time "lean forIn FloatArray" fun _ =>
    for _ in [0:10] do
      let mut m := 0
      for i in arr_ do
        m := m + i
      IO.println s!"{m}"

unsafe def test2 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let arr := Array.range num
  time "myForIn" fun _ =>
    for _ in [0:10] do
      let x := myArrayLoop arr 0
      IO.println s!"{x}"

-- IR playground
section compiler_trace
@[inline]
def str1 := vecStream 10
--set_option trace.compiler.inline true
--set_option trace.compiler.specialize true
--set_option trace.compiler.stage2 true
--def thetest' : ℕ := eval (contract (vecStream' 10)) --
@[noinline]
def dup (x : α) := (x, x)
example (x : ℕ) := let (a, _) := dup x; a
--def multest_ := let str1 := vecStream' 10; eval (contract (str1 * str1)) -- !!
--def foo (n : ℕ) := let s := contract2 (mat n); eval s --!!!
unsafe example := myArrayLoop #[] 0
end compiler_trace

end appendix
