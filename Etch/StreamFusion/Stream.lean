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
import Mathlib.Data.ByteArray

open Std (RBMap HashMap)

/- hack: redefine these instances to ensure they are inlined (see instDecidableLeToLEToPreorderToPartialOrder)
-/
section
variable [LinearOrder α]
@[inline] instance (a b : α) : Decidable (a < b) := LinearOrder.decidableLT a b
@[inline] instance (a b : α) : Decidable (a ≤ b) := LinearOrder.decidableLE a b
@[inline] instance (a b : α) : Decidable (a = b) := LinearOrder.decidableEq a b
end

namespace Std

@[inline]
def RBMap.toFn [Ord ι] [Zero α] (map : RBMap ι α Ord.compare) : ι → α := fun i => map.find? i |>.getD 0

@[inline]
def HashMap.modifyD [BEq α] [Hashable α] [Zero β] (self : HashMap α β) (a : α) (f : β → β) : HashMap α β :=
  self.insert a (f $ self.findD a 0)

@[inline]
def HashMap.modifyD' [BEq α] [Hashable α] [Zero β] (self : HashMap α β) (a : α) (f : β → β) : HashMap α β :=
  if self.contains a then self.modify a (fun _ => f) else self.insert a (f 0)

@[inline]
def RBMap.modifyD [Zero β] (self : RBMap α β h) (a : α) (f : β → β) : RBMap α β h :=
  self.insert a (f $ self.findD a 0)
  --self.alter a (fun | none => some 0 | some a => some (f a))
end Std

namespace Etch.Verification

structure Stream (ι : Type) (α : Type u) where
  σ : Type
  valid : σ → Bool
  ready : {x // valid x} → Bool
  seek  : {x // valid x} → ι ×ₗ Bool → σ
  index : {x // valid x} → ι
  value : {x // ready x} → α

-- stream plus a state
structure SStream (ι : Type) (α : Type u) extends Stream ι α where
  q : σ
  --weaken : ∀ {q : σ}, ready q → valid q

infixr:25 " →ₛ " => SStream

namespace Stream
variable {ι : Type} {α : Type _} [Mul α] [LinearOrder ι]
variable (s : Stream ι α)

section Mul
variable [Mul α]
--[h : LE ι] [DecidableRel h.le] [DecidableEq ι] -- todo: is the generated code different here?


@[inline]
def mul.valid.fst {a : Stream ι α} {b : Stream ι β} (p : {q : a.σ × b.σ // a.valid q.1 && b.valid q.2}) : {x // a.valid x} :=
  let ⟨q, hv⟩ := p; ⟨q.1, (Bool.and_eq_true _ _ ▸ hv).1⟩

@[inline]
def mul.valid.snd {a : Stream ι α} {b : Stream ι β} (p : {q : a.σ × b.σ // a.valid q.1 && b.valid q.2}) : {x // b.valid x} :=
  let ⟨q, hv⟩ := p; ⟨q.2, (Bool.and_eq_true _ _ ▸ hv).2⟩

@[inline]
def mul.ready {a : Stream ι α} {b : Stream ι β} (q : {p : a.σ × b.σ // a.valid p.1 && b.valid p.2}) : Bool :=
    let qa := mul.valid.fst q; let qb := mul.valid.snd q
    a.ready qa && b.ready qb && a.index qa = b.index qb

@[inline]
def mul.ready.fst [HMul α β γ] {a : Stream ι α} {b : Stream ι β} (q : {x : {p : a.σ × b.σ // a.valid p.1 && b.valid p.2} // mul.ready x}) : {x // a.ready x} :=
  let ⟨⟨q, v⟩, r⟩ := q;
  ⟨⟨q.1, (Bool.and_eq_true _ _ ▸ v).1⟩,
    by unfold mul.ready at r; simp_rw [Bool.and_eq_true] at r; exact r.1.1⟩

@[inline]
def mul.ready.snd [HMul α β γ] {a : Stream ι α} {b : Stream ι β} (q : {x : {p : a.σ × b.σ // a.valid p.1 && b.valid p.2} // mul.ready x}) : {x // b.ready x} :=
  let ⟨⟨q, v⟩, r⟩ := q;
  ⟨⟨q.2, (Bool.and_eq_true _ _ ▸ v).2⟩,
    by unfold mul.ready at r; simp_rw [Bool.and_eq_true] at r; exact r.1.2⟩


/- This combinator is a primary motivation for Stream -/
@[macro_inline]
def mul [HMul α β γ] (a : Stream ι α) (b : Stream ι β) : Stream ι γ where
  σ := a.σ × b.σ
  valid q := a.valid q.1 && b.valid q.2
  ready q :=
    let qa := mul.valid.fst q; let qb := mul.valid.snd q
    a.ready qa && b.ready qb && a.index qa = b.index qb
  index q := max (a.index (mul.valid.fst q)) (b.index (mul.valid.snd q))
  value q := a.value (mul.ready.fst q) * b.value (mul.ready.snd q)
  seek q i :=
    let p1 := a.seek (mul.valid.fst q) i
    let p2 := b.seek (mul.valid.snd q) i
    ⟨p1, p2⟩

end Mul

@[simps, macro_inline]
def contract (s : Stream ι α) : Stream Unit α where
  σ := s.σ
  valid := s.valid
  ready := s.ready
  index := default
  value := s.value
  seek q := fun ((), r) => s.seek q (s.index q, r)

-- For some reason, this definition *definitely* needs to be macro_inline for performance.
-- Everything else I have checked is safe at @[inline].
@[macro_inline]
def next (s : Stream ι α) (q : s.σ) (h : s.valid q = true) (ready : Bool) : s.σ :=
  let q := ⟨q, h⟩; s.seek q (s.index q, ready)

/- (Important def) Converting a Stream into data
   This definition follows the same inline/specialize pattern as Array.forInUnsafe
-/
@[inline] partial def fold (f : β → ι → α → β) (s : Stream ι α) (q : s.σ) (acc : β) : β :=
  let rec @[specialize] go f (valid : s.σ → Bool) (ready : (x : s.σ) → valid x → Bool)
      (index : (x : s.σ) → valid x → ι) (value : (x : s.σ) → (h : valid x) → ready x h → α)
      (next : (x : s.σ) → valid x → Bool → s.σ) (acc : β) q :=
    if hv : valid q then
      if hr : ready q hv
           then go f valid ready index value next (f acc (index q hv) (value q hv hr)) (next q hv true)
           else go f valid ready index value next acc (next q hv false)
    else acc
  go f s.valid (fun q h => s.ready ⟨q,h⟩) (fun q h => s.index ⟨q,h⟩) (fun q v r => s.value ⟨⟨q,v⟩,r⟩) s.next acc q

end Stream

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

namespace SStream

variable {ι : Type} [LinearOrder ι] {α : Type u}

@[inline]
def map (f : α → β) (s : SStream ι α) : SStream ι β := { s with value := f ∘ s.value}

variable [Inhabited ι]

/- Converting data into a SStream -/
def zero : SStream ι α where
  σ := Unit; q := (); valid _ := false; ready _ := false;
  index _ := default; value := fun ⟨_, h⟩ => nomatch h;
  seek _ _ := ();
  --weaken := id

instance : Zero (SStream ι α) := ⟨SStream.zero⟩

-- deprecated
@[macro_inline]
def ofArray (l : Array (ℕ × α)) : SStream ℕ α where
  σ := ℕ
  q := 0
  valid q := q < l.size
  ready q := True
  index := fun q => (l[q.1]'(by simpa using q.2)).1
  value := fun ⟨q, _⟩ => (l[q.1]'(by simpa using q.2)).2
  seek q := fun ⟨j, r⟩ =>
    let i := (l[q.1]'(by simpa using q.2)).fst
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q
  --weaken := id

@[macro_inline]
def ofArrayPair (is : Array ι) (vs : Array α) (eq : is.size = vs.size) : SStream ι α where
  σ := ℕ
  q := 0
  valid q := q < is.size
  ready q := true
  index q := (is[q.1]'(by simpa using q.2))
  value := fun ⟨q, _⟩ => (vs[q.1]'(eq ▸ (by simpa using q.2)))
  seek q := fun ⟨j, r⟩ =>
    let i := (is[q.1]'(by simpa using q.2))
    if r then if i ≤ j then q+1 else q
         else if i < j then q+1 else q
  --weaken := id

-- not tested yet
--@[macro_inline]
--def ofFloatArray (is : Array ι) (vs : FloatArray) (eq : is.size = vs.size) : SStream ι Float where
--  σ := ℕ
--  q := 0
--  valid q := q < is.size
--  ready q := q < is.size
--  index k h := (is[k]'(by simpa using h))
--  value k h := (vs[k]'(eq ▸ (by simpa using h)))
--  seek q hq := fun ⟨j, r⟩ =>
--    let i := is[q]'(by simpa using hq)
--    if r then if i ≤ j then q+1 else q
--         else if i < j then q+1 else q
--  --weaken := id

-- Used as a base case for ToStream/OfStream
class Scalar (α : Type u)
instance : Scalar ℕ := ⟨⟩
instance : Scalar Float := ⟨⟩
instance : Scalar Bool := ⟨⟩

class ToStream (α : Type u) (β : outParam $ Type v) where
  stream : α → β

instance [Scalar α] : ToStream α α := ⟨id⟩

instance [ToStream β β'] : ToStream  (Array (ℕ × β)) (SStream ℕ β') where
  stream := map ToStream.stream ∘ ofArray

instance [ToStream β β'] : ToStream  (Level ι β n) (SStream ι β') where
  stream := map ToStream.stream ∘ (fun ⟨⟨is, _⟩, ⟨vs, _⟩⟩ => ofArrayPair is vs (by simp [*]))

--instance : ToStream  (Vec ι n × FloatVec n) (SStream ι Float) where
--  stream := fun (a, b) => ofFloatArray a.1 b.1 (a.property.trans b.property.symm)

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
  eval := SStream.fold (fun a _ b => OfStream.eval b a)

-- Doesn't support update of previous indices; assumes fully formed value is
--   inserted at each step (so pass 0 to recursive eval)
instance [OfStream β β'] [Zero β']: OfStream (SStream ι β) (Array ι × Array β') where
  eval := toArrayPair ∘ map (OfStream.eval . 0)

-- BEq issue without @HashMap
instance [BEq ι] [Hashable ι] [OfStream α β] [Zero β] : OfStream (ι →ₛ α) (@HashMap ι β inferInstance inferInstance) where
  eval := SStream.fold (fun m k v => m.modifyD k (OfStream.eval v))

instance [OfStream α β] [Zero β] : OfStream (ι →ₛ α) (RBMap ι β Ord.compare) where
  eval := SStream.fold (fun m k v => m.modifyD k (OfStream.eval v))

@[macro_inline]
def mul [HMul α β γ] (a : SStream ι α) (b : SStream ι β) : SStream ι γ := {
  a.toStream.mul b.toStream with
  q := ⟨a.q, b.q⟩
  --weaken := fun h => by simp [Stream.mul] at *; split_ifs at h; assumption
}

@[macro_inline]
instance [HMul α β γ] : HMul (ℕ →ₛ α) (ℕ →ₛ β) (ℕ →ₛ γ) := ⟨mul⟩

@[macro_inline]
instance [HMul α β γ] : HMul (ι → α) (ι →ₛ β) (ι →ₛ γ) where
  hMul f x := { x with value := fun q => f (x.index q) * x.value q}

@[macro_inline]
instance [HMul α β γ] : HMul (ι →ₛ α) (ι → β) (ι →ₛ γ) where
  hMul x f := { x with value := fun q => x.value q * f (x.index q) }

@[macro_inline] def expand (a : α) : ι → α := fun _ => a

@[macro_inline]
def contract (a : SStream ι α) : SStream Unit α := {
  a.toStream.contract with
  q := a.q
  --weaken := a.weaken
}

@[macro_inline]
def contract2 : (ℕ →ₛ ℕ →ₛ α) → Unit →ₛ Unit →ₛ α := contract ∘ SStream.map contract

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

--@[inline] def floatVecStream (num : Nat) :=
--  let is : Vec ℕ num := ⟨Array.range num, Array.size_range⟩
--  let vs : FloatVec num := ⟨Array.range num |>.toList.map (fun x => x.toFloat) |>.toFloatArray, by sorry⟩
--  stream $ (is, vs)

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

--def testFloat (num : Nat) : IO Unit := do
--  IO.println "-----------"
--  let s := contract $ floatVecStream num
--  time "float stream" fun _ =>
--    for _ in [0:10] do
--      let x : Float := eval s
--      IO.println s!"{x}"

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
  let s := v * (v.map fun _ => 1)
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

-- todo: not inlining!
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
  test.vecMulSum3 num
  test.vecMul num

  --test.matProdSum num

  --test.vecMul_rb num
  test.matMultiply1 num
  --test.matMultiply3 num

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
