import Std.Data.RBMap
import Std.Data.HashMap

import Etch.StreamFusion.Stream
import Etch.StreamFusion.Multiply
import Etch.StreamFusion.Traversals

open Std (RBMap HashMap)
open Etch.Verification
open SStream
open OfStream ToStream

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

def time (s : String) (m : Unit → IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← m ()
  let t1 ← IO.monoMsNow
  IO.println s!"[{s}] time: {t1-t0}"
  pure v

namespace test
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
