/-
This file implements a prototype of indexed stream fusion,
  an optimization to speed up programs that manipulate (nested) associative arrays.

Authors: Scott Kovach
-/

/- Ideally we would use the same Stream definition from SkipStream, which doesn't critically use Classical.
   For now, we redefine valid/ready to return Bool -/
--import Etch.Verification.Semantics.SkipStream
--import Etch.Verification.Semantics.Mul
--import Etch.Verification.Semantics.Add
--import Etch.Verification.Semantics.Contract

/- General notes:
  Stream.fold generates the top-level loop.
    For performance, we want this to include no calls to lean_apply_[n] and minimal allocations
      (so far there are still some tuples allocated for multiplication states)
    Some care is needed to ensure everything is inlined.

  Stream.mul is the key combinator. it multiplies the non-zero values of two streams.

  The choice of inline vs macro_inline is not intentional anywhere except for `Stream.next`, where macro_inline seems to be necessary
-/

/- TODOs: see paper draft
  easy:
    make a stream of type String →ₛ ℕ
-/

import Mathlib.Data.Prod.Lex
import Init.Data.Array.Basic
import Std.Data.RBMap
import Std.Data.HashMap
import Etch.StreamFusion.Traversals

open Std (RBMap HashMap)

namespace Std

@[inline]
def HashMap.modifyD [BEq α] [Hashable α] [Zero β] (self : HashMap α β) (a : α) (f : β → β) : HashMap α β :=
  self.insert a (f $ self.findD a 0)

@[inline]
def HashMap.modifyD' [BEq α] [Hashable α] [Zero β] (self : HashMap α β) (a : α) (f : β → β) : HashMap α β :=
  if self.contains a then self.modify a (fun _ => f) else self.insert a (f 0)

@[inline]
def RBMap.modifyD [Zero β] (self : RBMap α β h) (a : α) (f : β → β) : RBMap α β h :=
  self.alter a (fun | none => some 0 | some a => some (f a))
end Std

namespace Etch.Verification


namespace Exposition
-- In analogy with streams representing sequences, we define the type of streams
-- representing sequences of (ι × α) pairs, ordered by ι,
-- which admit efficient `seek` up to or past a given index.

-- This pair of definitions is not used, but they are one logical step between "Stream Fusion" and Stream below
inductive StreamStep (ι : Type) (α : Type u) where
| done
| ready : σ → ι → α → StreamStep ι α
| skip  : σ → ι → StreamStep ι α

structure StreamAlt (ι : Type) (α : Type u) where
  σ : Type
  seek : (x : σ) → ι → Bool → StreamStep ι α
  q : σ
end Exposition

structure Stream (ι : Type) (α : Type u) where
  σ : Type
  valid : σ → Bool
  ready : σ → Bool
  seek  : (x : σ) → valid x → ι ×ₗ Bool → σ
  index : (x : σ) → valid x → ι
  value : (x : σ) → ready x → α

-- stream plus a state
structure SStream (ι : Type) (α : Type u) extends Stream ι α where
  q : σ
  weaken : ∀ {q : σ}, ready q → valid q

infixr:25 " →ₛ " => SStream

namespace Stream
variable {ι : Type} {α : Type _} [Mul α] [LinearOrder ι]
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
  seek q hq i := s.seek q hq (s.index q hq, i.2)

end Stream

section Mul

variable [Mul α] [LinearOrder ι]
--[h : LE ι] [DecidableRel h.le] [DecidableEq ι] -- todo: is the generated code different here?

/- This combinator is a primary motivation for Stream -/
@[macro_inline]
def Stream.mul [HMul α β γ] (a : Stream ι α) (b : Stream ι β) : Stream ι γ where
  σ := a.σ × b.σ
  valid p := a.valid p.1 && b.valid p.2
  ready p :=
    if hv : a.valid p.1 && b.valid p.2
      then a.ready p.1 && b.ready p.2 &&
           a.index p.1 (by simp at hv; exact hv.1) = b.index p.2 (by simp at hv; exact hv.2)
      else false
  index p hv :=
    let ai := (a.index p.1 (by simp at hv; exact hv.1))
    let bi := (b.index p.2 (by simp at hv; exact hv.2))
    if ai ≤ bi then bi else ai
    -- todo: check max performance
    -- if ai = bi then ai else bi -- substantially faster than ≤; maybe still some performance to find
  value p hr := by -- todo; refactor this proof to be safe?
    dsimp at hr
    split_ifs at hr
    simp at hr
    exact a.value p.1 hr.1.1 * b.value p.2 hr.1.2
  seek p hp i :=
    let p1 := a.seek p.1 (by simp at hp; exact hp.1) i
    let p2 := b.seek p.2 (by simp at hp; exact hp.2) i
    ⟨p1, p2⟩

end Mul

-- For some reason, this definition *definitely* needs to be macro_inline for performance.
-- Everything else I have checked is safe at @[inline].
@[macro_inline]
def Stream.next (s : Stream ι α) (q : s.σ) (h : s.valid q = true) (ready : Bool) : s.σ :=
  s.seek q h (s.index q h, ready)

namespace SStream

variable {ι : Type} [LinearOrder ι] {α : Type u}

@[inline]
def map (f : α → β) (s : SStream ι α) : SStream ι β :=
  { s with value := fun q => f ∘ s.value q }

variable [Inhabited ι]

/- Converting data into a SStream -/
def SStream.zero : SStream ι α where
  q := (); valid _ := False; ready _ := False;
  index _ := default; value _ := (nomatch .);
  seek _ _ _ := ();
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
  seek q hq := fun ⟨j, r⟩ =>
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
  seek q hq := fun ⟨j, r⟩ =>
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
  seek q hq := fun ⟨j, r⟩ =>
    let i := is[q]'(by simpa using hq)
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q
  weaken := id

class Scalar (α : Type u)
instance : Scalar ℕ := ⟨⟩
instance : Scalar Float := ⟨⟩
instance : Scalar Bool := ⟨⟩

class ToStream (α : Type u) (β : outParam $ Type v) where
  stream : α → β

instance [Scalar α] : ToStream α α := ⟨id⟩

instance [ToStream β β'] : ToStream  (Array (ℕ × β)) (SStream ℕ β') where
  stream := map ToStream.stream ∘ ofArray

def Vec α n := { x : Array α // x.size = n }
def Vec.map (v : Vec α n) (f : α → β) : Vec β n := ⟨v.1.map f, by have := Array.size_map f v.1; simp [*, v.2]⟩
def Vec.push (l : Vec α n) (v : α) : Vec α (n+1) :=
  ⟨l.1.push v, by have := Array.size_push l.1 v; simp only [this, l.2]⟩

structure Level (ι : Type) (α : Type u) (n : ℕ) where
  is : Vec ι n
  vs : Vec α n

def Level.push (l : Level ι α n) (i : ι) (v : α) : Level ι α (n+1) :=
  ⟨l.is.push i, l.vs.push v⟩

def FloatVec n := { x : FloatArray // x.size = n }

instance [ToStream β β'] : ToStream  (Level ι β n) (SStream ι β') where
  stream := map ToStream.stream ∘ (fun ⟨is, vs⟩ => ofArrayPair is.val vs.val (by simp [is.2, vs.2]))

instance : ToStream  (Vec ι n × FloatVec n) (SStream ι Float) where
  stream := fun (a, b) => ofFloatArray a.1 b.1 (a.property.trans b.property.symm)


/- Converting a Stream into Data -/
-- this definition follows the same inline/specialize pattern as Array.forInUnsafe
@[inline] partial def _root_.Etch.Verification.Stream.fold (f : β → ι → α → β) (s : Stream ι α) (q : s.σ) (acc : β) : β :=
  let rec @[specialize] go f (valid : s.σ → Bool) (ready : s.σ → Bool)
      (index : (x : s.σ) → valid x → ι) (value : (x : s.σ) → ready x → α)
      (next : (x : s.σ) → valid x → Bool → s.σ) (acc : β) q :=
    if hv : valid q then
      if hr : ready q
           then go f valid ready index value next (f acc (index q hv) $ value q hr) (next q hv true)
           else go f valid ready index value next acc (next q hv false)
    else acc
  go f s.valid s.ready s.index s.value s.next acc q

@[inline] def fold (f : β → ι → α → β) (s : SStream ι α) (acc : β) : β := s.toStream.fold f s.q acc

@[inline] def toArrayPair (s : SStream ι α) : Array ι × Array α → Array ι × Array α :=
  s.fold (fun (a,b) i v => ⟨a.push i, b.push v⟩)

-- not used yet
--@[inline] def toLevel (s : SStream ι α) : (n : ℕ) × (Level ι α n) :=
--  s.fold (fun ⟨_, l⟩ i v => ⟨_, l.push i v⟩) s.q ⟨0, ⟨⟨#[], rfl⟩, ⟨#[], rfl⟩⟩⟩
--@[inline] def toArrayPair (s : SStream ι α) : Array ι × Array α :=
--  let ⟨_, l⟩ : (n : _) × Level ι α n := s.fold (fun ⟨_, l⟩ i v => ⟨_, l.push i v⟩) ⟨0, ⟨⟨#[], rfl⟩, ⟨#[], rfl⟩⟩⟩ s.q
--  (l.1.1, l.2.1)

class OfStream (α : Type u) (β : Type v) where
  eval : α → β → β

instance [Scalar α] [Add α] : OfStream α α := ⟨(.+.)⟩

instance [OfStream β β'] : OfStream (SStream Unit β) β' where
  eval := fold (fun a _ b => OfStream.eval b a)

-- Doesn't support update of previous indices; assumes fully formed value is
--   inserted at each step (so pass 0 to recursive eval)
instance [OfStream β β'] [Zero β']: OfStream (SStream ι β) (Array ι × Array β') where
  eval := toArrayPair ∘ map (OfStream.eval . 0)

-- BEq issue without @HashMap
instance [BEq ι] [Hashable ι] [OfStream α β] [Zero β] : OfStream (ι →ₛ α) (@HashMap ι β inferInstance inferInstance) where
  eval := fold (fun m k v => m.modifyD k (OfStream.eval v))

instance [OfStream α β] [Zero β] : OfStream (ι →ₛ α) (RBMap ι β Ord.compare) where
  eval := fold (fun m k v => m.modifyD k (OfStream.eval v))

@[macro_inline]
def mul [HMul α β γ] (a : SStream ι α) (b : SStream ι β) : SStream ι γ := {
  a.toStream.mul b.toStream with
  q := ⟨a.q, b.q⟩
  weaken := fun h => by simp [Stream.mul] at *; split_ifs at h; assumption
}

@[macro_inline]
instance [HMul α β γ] : HMul (ℕ →ₛ α) (ℕ →ₛ β) (ℕ →ₛ γ) := ⟨mul⟩

@[macro_inline]
instance [HMul α β γ] : HMul (ι → α) (ι →ₛ β) (ι →ₛ γ) where
  hMul f x := { x with value := fun s h => f (x.index s $ x.weaken h) * x.value s h }

@[macro_inline]
instance [HMul α β γ] : HMul (ι →ₛ α) (ι → β) (ι →ₛ γ) where
  hMul x f := { x with value := fun s h => x.value s h * f (x.index s $ x.weaken h) }

@[macro_inline] def expand (a : α) : ι → α := fun _ => a

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
open ToStream

@[inline] def eval [Zero β] [OfStream α β] : α → β := (OfStream.eval . 0)

def time (s : String) (m : Unit → IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← m ()
  let t1 ← IO.monoMsNow
  IO.println s!"[{s}] time: {t1-t0}"
  pure v

-- deprecated
@[inline] def vecStream' (num : Nat) := stream $ Array.range num |>.map fun n => (n,n)

@[inline] def vecStream (num : Nat) :=
  let v : Vec ℕ num := ⟨Array.range num, Array.size_range⟩
  stream $ Level.mk v v

@[inline] def floatVecStream (num : Nat) :=
  let is : Vec ℕ num := ⟨Array.range num, Array.size_range⟩
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
  let map' : Tree' ℕ ℕ := map.1.map fun (i,v) => (i, Side.no, v)
  let test (map : RBMap ℕ ℕ Ord.compare) := do
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
    time "RBMap.map" fun _ => do -- baseline
      let mut map := map.1
      for _ in [0:10] do
        map := map.map fun x => (x.1, x.2 * 2)
        IO.println s!"{map.look}"
    -- about 1.8x slower than baseline. no stack. allocation
    time "tmap" fun _ => do
      let mut map := map.1
      for _ in [0:10] do
        map := tmap (t := map) fun b => b*2
        IO.println s!"{map.look}"
    -- about 1.5x slower than baseline. no stack. no allocation
    time "tmap fbip" fun _ => do
      let mut map : Tree' ℕ ℕ := map'
      for _ in [0:10] do
        map := tmap' (t := map) fun b => b*2
        IO.println s!"{let (i, _, x) := map.look; (i,x)}"
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
  let s := contract $ vecStream num
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

instance : EmptyCollection (Array α × Array β) := ⟨#[], #[]⟩
instance [EmptyCollection α] : Zero α := ⟨{}⟩

def vecMul (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream num
  let v' := vecStream num |>.map fun _ => 1
  let s := v * v'
  time "vec mul" fun _ =>
    for _ in [0:10] do
      let x : Array ℕ × Array ℕ := eval s
      IO.println s!"{x.1.size}"
  pure ()

abbrev Map a [Ord a] b := RBMap a b Ord.compare

def vecMul_rb (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream num
  let v' := vecStream num |>.map fun _ => 1
  let s := v * v'
  time "vec mul rb" fun _ =>
    for _ in [0:10] do
      let x : RBMap ℕ ℕ Ord.compare := eval s
      IO.println s!"{x.1.size}"
  pure ()

def vecMul_hash (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream num
  let v' := vecStream num |>.map fun _ => 1
  let s := v * v'
  time "vec mul hash" fun _ =>
    for _ in [0:10] do
      let x : HashMap ℕ ℕ := eval s
      IO.println s!"{x.1.size}"
  pure ()

def vecMulSum (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream num
  let v' := vecStream num |>.map fun _ => 1
  let s := contract $ v * v'
  time "vec mul sum" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval s
      IO.println s!"{x}"
  pure ()

-- todo: this has allocation and other perf issues
def vecMulSum3 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream num
  let v₁ := vecStream num |>.map fun _ => 1
  let v₂ := vecStream num |>.map fun _ => 1
  let s := contract $ v * v₁ * v₂
  time "vec mul 3 sum slow?" fun _ =>
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
  let m' := mat' (4*n).cubeRoot;
  let m1 : ℕ →ₛ ℕ →  ℕ →ₛ ℕ := map expand m
  let m2 : ℕ →ₛ ℕ →ₛ ℕ → ℕ := map (map expand) m'
  let s  : ℕ →ₛ ℕ →ₛ ℕ →ₛ ℕ := m1 * m2
  map (map contract) $ s

def matMultiplySum (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := contract2 $ aMatMul num
  time "matrix multiply (inner-product) sum" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval s
      IO.println s!"{x}"

def matMultiply1 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := aMatMul num
  time "matrix multiply (inner-product) arrays" fun _ =>
    for _ in [0:10] do
      let x : Array ℕ × Array (Array ℕ × Array ℕ) := eval s
      IO.println s!"{x.1.size}"

-- todo: this isn't being inlined correctly
def matMultiply2 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := aMatMul num
  time "matrix multiply (inner-product) array hashmap" fun _ =>
    for _ in [0:10] do
      let y : Array ℕ × Array (HashMap ℕ ℕ) := eval s
      IO.println s!"{y.2.size}"

def matMultiply3 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let s := aMatMul num
  time "matrix multiply (inner-product) array rbmap" fun _ =>
    for _ in [0:10] do
      let y : Array ℕ × Array (RBMap ℕ ℕ Ord.compare) := eval s
      IO.println s!"{y.2.size}"

end test

end Etch.Verification

open Etch.Verification
open SStream
open OfStream ToStream

unsafe def testRB (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"

  test.baselineRB num

unsafe def testAll (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"

  test.baseline num
  test.vecSum num
  test.vecMulSum num      -- ideally about 2x vecSum
  test.vecMulSum3 num      -- ideally about 2x vecSum
  test.vecMul num         -- ideally about 1x vecMulSum (currently 3x slower, but that's almost all Array.push. try pre-allocating?)
  test.matSum num         -- ideally about 1x vecSum
  test.matProdSum num     -- ... 2x matSum
  test.matMultiplySum num
  test.matMultiply1 num
  test.matMultiply2 num
  test.matMultiply3 num

unsafe def testSome (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"

  test.baseline num
  test.vecSum num
  test.vecMulSum num
  test.vecMul_hash num
  test.matMultiply1 num
  test.matMultiply3 num

unsafe def _root_.main := testSome

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
@[noinline] def dup (x : α) := (x, x) example (x : ℕ) := let (a, _) := dup x; a
--def multest_ := let str1 := vecStream' 10; eval (contract (str1 * str1))
--def foo (n : ℕ) := let s := contract2 (mat n); eval s
unsafe example := myArrayLoop #[] 0
end compiler_trace

end appendix
