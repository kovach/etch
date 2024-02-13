import Std.Data.RBMap
import Std.Data.HashMap

import Etch.StreamFusion.Stream
import Etch.StreamFusion.Multiply
import Etch.StreamFusion.Traversals

open Std (RBMap HashMap)
open Etch.Verification
open SStream
open OfStream ToStream

@[inline]
def SStream.ofMat [Scalar α] (is : Array (ℕ × Array ℕ)) (vs : ℕ → ℕ → α) : ℕ →ₛ ℕ →ₛ α :=
  let x := is.map fun (row, cs) => (row, cs.map fun col => (col, vs row col))
  stream x

-- adjusts size so that there are ~num non-zero entries
-- macro_inline needed!
@[macro_inline]
def mat (num : Nat) :=
  let is : Array (ℕ × Array ℕ) :=
    Array.range (2*num).sqrt |>.map (.+1) |>.map $ fun n => (n, Array.range n)
  SStream.ofMat is fun _ m => m+10

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

def matSum (num : Nat) : IO Unit := do
  IO.println "-----------"
  let x := mat num
  let s := contract2 x
  time "matrix sum" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval s
      IO.println s!"{x}"

-- todo: not inlining!
def matProdSum (num : Nat) : IO Unit := do
  IO.println "-----------"
  let m := mat num
  let m' := mat num
  let s := contract2 $ m * m'
  time "matrix prod sum" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval s
      IO.println s!"{x}"

def matId (num : Nat) : IO Unit := do
  IO.println "-----------"
  let is : Array (ℕ × Array ℕ) := Array.range (2*num).sqrt |>.map (.+1) |>.map $ fun n => (n, Array.range n)
  let x := is.map fun (row, cs) => (row, cs.map fun col => (col, 1))
  let s := (stream x)
  time "matrix id" fun _ =>
    for _ in [0:10] do
      let x : ArrayMap ℕ (ArrayMap ℕ ℕ) := eval s
      IO.println s!"{x.1.size}"

def matId_RB (num : Nat) : IO Unit := do
  IO.println "-----------"
  let is : Array (ℕ × Array ℕ) := Array.range (2*num).sqrt |>.map (.+1) |>.map $ fun n => (n, Array.range n)
  let x := is.map fun (row, cs) => (row, cs.map fun col => (col, 1))
  let s := (stream x)
  time "matrix id rb" fun _ =>
    for _ in [0:10] do
      let x : Map ℕ (Map ℕ ℕ) := eval s
      IO.println s!"{x.1.size}"

def matId_RB_s1 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let is : Array (ℕ × Array ℕ) := Array.range (2*num).sqrt |>.map (.+1) |>.map $ fun n => (n, Array.range n)
  let x := is.map fun (row, cs) => (row, cs.map fun col => (col, 1))
  let s := contract (stream x)
  time "matrix s1 rb" fun _ =>
    for _ in [0:10] do
      let x : (Map ℕ ℕ) := eval s
      IO.println s!"{x.1.size}"

def matId_RB_s2 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let is : Array (ℕ × Array ℕ) := Array.range (2*num).sqrt |>.map (.+1) |>.map $ fun n => (n, Array.range n)
  let x := is.map fun (row, cs) => (row, cs.map fun col => (col, 1))
  let s := map contract (stream x)
  time "matrix s2 rb" fun _ =>
    for _ in [0:10] do
      let x : (Map ℕ ℕ) := eval s
      IO.println s!"{x.1.size}"

def matId_hash_s1 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let is : Array (ℕ × Array ℕ) := Array.range (2*num).sqrt |>.map (.+1) |>.map $ fun n => (n, Array.range n)
  let x := is.map fun (row, cs) => (row, cs.map fun col => (col, 1))
  let s := contract (stream x)
  time "matrix s1 hash" fun _ =>
    for _ in [0:10] do
      let x : (HashMap ℕ ℕ) := eval s
      IO.println s!"{x.1.size}"

def matId_hash_s2 (num : Nat) : IO Unit := do
  IO.println "-----------"
  let is : Array (ℕ × Array ℕ) := Array.range (2*num).sqrt |>.map (.+1) |>.map $ fun n => (n, Array.range n)
  let x := is.map fun (row, cs) => (row, cs.map fun col => (col, 1))
  let s := map contract (stream x)
  time "matrix s2 hash" fun _ =>
    for _ in [0:10] do
      let x : (HashMap ℕ ℕ) := eval s
      IO.println s!"{x.1.size}"

--@[inline]
--def ones (i j : Nat) :=
--  let is := Array.range i |>.map fun _ => (i, Array.range j)
--  SStream.ofMat' is fun _ _ => 1

--def matSum1 (num : Nat) : IO Unit := do
--  IO.println "-----------"
--  let num := num.sqrt
--  let i := 0; let j := 1; let k := 2
--  let ij := [(0, ℕ), (1, ℕ)]
--  let m1 := ones num num
--  let s := contract2 $ {ij | m1(i,j)}
--  time "matrix sum (ones)" fun _ =>
--    for _ in [0:10] do
--      let x : ℕ := eval s
--      IO.println s!"{x}"

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

@[inline]
def aMatMul (n : Nat) : ℕ →ₛ ℕ →ₛ Unit →ₛ ℕ :=
  let m  := mat (4*n).cubeRoot
  let m' := mat (4*n).cubeRoot
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

  test.matSum num
  test.matId num
  --test.matId_RB num
  --test.matId_RB_s1 num
  --test.matId_RB_s2 num
  --test.matId_hash_s1 num
  --test.matId_hash_s2 num
  test.matProdSum num     -- ... 2x matSum

unsafe def _root_.main := testSome
