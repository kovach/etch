import Std.Data.RBMap
import Std.Data.HashMap

import Etch.StreamFusion.Stream
import Etch.StreamFusion.Multiply
import Etch.StreamFusion.Traversals

open Std (RBMap RBSet HashMap)
open Etch.Verification
open SStream
open OfStream ToStream


-- deprecated
--@[inline] def vecStream' (num : Nat) := stream $ Array.range num |>.map fun n => (n,n)

@[inline] def vecStream (num : Nat) :=
  let v : Vec ℕ num := ⟨Array.range num, Array.size_range⟩
  stream $ Level.mk v v

@[inline] def boolStream (num : Nat) : ℕ →ₛ Bool:=
  stream $ Array.range num

--@[inline] def floatVecStream (num : Nat) :=
--  let is : Vec ℕ num := ⟨Array.range num, Array.size_range⟩
--  let vs : FloatVec num := ⟨Array.range num |>.toList.map (fun x => x.toFloat) |>.toFloatArray, by sorry⟩
--  stream $ (is, vs)

def time (s : String) (m : Unit → IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← m ()
  let t1 ← IO.monoMsNow
  IO.println s!"[{s}] time: {t1-t0}"
  pure v

namespace test

-- todo investigate perf differences
@[specialize]
def genCase [OfStream α β] [Zero β] (label : String) (setup : ℕ → α) [ToString β'] (print : β → β') (num : Nat) (reps := 10) : IO Unit := do
  IO.println "-----------"
  let s := setup num
  time label fun _ =>
    for _ in [0:reps] do
      let x := SStream.eval s
      IO.println s!"{print x}"

-- these tests need to be separate defs for profile legibility
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

set_option trace.compiler.ir.reset_reuse true in
def vecSum : ℕ → IO Unit :=
  genCase "vec sum"
    (setup := fun num => contract $ vecStream num)
    (print := fun x : ℕ => toString x)

@[inline] def filt : ℕ → Bool := fun i => i > 50

def vecBoolMul : Nat → IO Unit := genCase
  "vec mul filter 2"
  (setup := fun num => do
    let b := boolStream num
    b * (vecStream num))
  (print := fun x : ArrayMap ℕ ℕ => s!"{x.1.size}")

def vecBoolMul3 : Nat → IO Unit := genCase
  "vec mul filter 3"
  (setup := fun num => do
    let b := boolStream num
    b * (b * vecStream num))
  (print := fun x : ArrayMap ℕ ℕ => x.1.size)

--def testFloat (num : Nat) : IO Unit := do
--  IO.println "-----------"
--  let s := contract $ floatVecStream num
--  time "float stream" fun _ =>
--    for _ in [0:10] do
--      let x : Float := eval s
--      IO.println s!"{x}"

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

--set_option trace.compiler.ir.reset_reuse true in
def vecMulSum : ℕ → IO Unit := genCase "vec mul sum"
  (fun num =>
    let v := vecStream num
    let v' := vecStream num |>.map fun _ => 1
    contract $ v * v')
  (fun x : ℕ => x)

-- todo: vecMul' performs additional allocation in the inner loop
--set_option trace.compiler.ir.reset_reuse true in
def vecMul : ℕ → IO Unit := genCase "vec mul"
    (fun num =>
      let v := vecStream num;
      let v' := vecStream num |>.map fun _ => 1;
      v * v')
    (fun x : ArrayMap ℕ ℕ => x.1.size)

--set_option trace.compiler.ir.reset_reuse true in
--set_option trace.compiler.stage2 true in
def vecMulSum3 : ℕ → IO Unit := genCase "vec mul 3 sum"
  (fun num =>
    let v  := vecStream num
    let v₁ := vecStream num |>.map fun _ => 1
    let v₂ := vecStream num |>.map fun _ => 1
    contract $ v * (v₁ * v₂))
  (fun x : ℕ => x)

def vecMul' (num : Nat) : IO Unit := do
  IO.println "-----------"
  let v := vecStream num
  let v' := vecStream num |>.map fun _ => 1
  let s := v * v'
  time "vec mul" fun _ =>
    for _ in [0:10] do
      let x : Array ℕ × Array ℕ := eval s
      IO.println s!"{x.1.size}"
  pure ()

def vecMul3 : ℕ → IO Unit := genCase "vec mul 3"
  (fun num =>
    let v  := vecStream num
    let v₁ := vecStream num |>.map fun _ => 1
    let v₂ := vecStream num |>.map fun _ => 1
    v * (v₁ * v₂))
  (fun x : ArrayMap ℕ ℕ => x.1.size)

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

unsafe def testRB (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"

  test.baselineRB num

end test

unsafe def tests (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"

  test.baseline num
  test.vecSum num
  --test.vecBoolMul num
  --test.vecBoolMul3 num
  test.vecMulSum num
  test.vecMul num
  test.vecMul3 num
  --test.vecMulSum3 num

unsafe def _root_.main := tests

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
