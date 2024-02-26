import Std.Data.RBMap
import Std.Data.HashMap

import Etch.StreamFusion.Stream
import Etch.StreamFusion.Multiply
import Etch.StreamFusion.Expand
import Etch.StreamFusion.Traversals
import Etch.StreamFusion.TestUtil

open Std (RBMap RBSet HashMap)
open Etch.Verification
open SStream
open OfStream ToStream

namespace test

-- todo investigate perf differences
@[specialize]
def genCase [OfStream α β] [Zero β] (label : String) (setup : init → α) [ToString β'] (print : β → β') (num : init) (reps := 10) : IO Unit := do
  IO.println s!"reps: {reps}-----"
  let s := setup num
  time label fun _ => do
    for i in [0:reps] do
      let x := SStream.eval s
      if i % 1000000 = 0 then
        IO.println s!"{print x}"

@[specialize]
def genCase' [Zero β] (label : String) (setup : init → α) (op : α → β) [ToString β'] (print : β → β') (num : init) (reps := 10) : IO Unit := do
  IO.println s!"reps: {reps}-----"
  let s := setup num
  time label fun _ => do
    for i in [0:reps] do
      let x := op s
      if i % 1000000 = 0 then
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

/-
def vecBoolMul : Nat → IO Unit := genCase
  "vec mul filter 2"
  (setup := fun num => do
    let b := boolStream num
    b * (vecStream num))
  (print := fun x : SparseArray ℕ ℕ => s!"{x.1.size}")

def vecBoolMul3 : Nat → IO Unit := genCase
  "vec mul filter 3"
  (setup := fun num => do
    let b := boolStream num
    b * (b * vecStream num))
  (print := fun x : SparseArray ℕ ℕ => x.1.size)
-/

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

--set_option trace.compiler.ir.result true in
--set_option trace.compiler.stage2 true in
def vecSum' : ℕ → IO Unit := genCase "vec sum"
    (fun num => let v := vecStream num; contract v)
    (fun x : ℕ => x)

def vecSum := genCase "vec sum"
    (fun (vec : SparseArray ℕ ℕ) => contract $ stream vec)
    (fun x : ℕ => x)

def vecCopy : ℕ → IO Unit := genCase "vec copy"
    (fun num => let v := vecStream num; v)
    (fun x : F ℕ ℕ => x.1.size)

def_index_enum_group i, j

def matSum := genCase "matrix sum"
    (fun (mat : SparseArrayMat ℕ ℕ ℕ) => Σ 0 1 => mat(0,1))
    (fun x : ℕ => x)

open RB

def rbVecSumBaseline := genCase' "baseline rb sum"
    (fun (mat : TreeMap ℕ ℕ) => mat)
    (op := fun mat => mat.foldl (fun acc v => acc + v.value) 0)
    (fun x : ℕ => x)

def rbVecSum := genCase "rbVec sum"
    (fun (mat : TreeMap ℕ ℕ) => Σ 0 => mat(0))
    (fun x : ℕ => x)

--set_option trace.compiler.ir.reset_reuse true in
def vecMulSum : ℕ → IO Unit := genCase "vec mul sum"
  (fun num =>
    let v := vecStream num
    let v' := vecStream num |>.map fun _ => 1
    contract $ v * v')
  (fun x : ℕ => x)

-- todo: vecMul' performs additional allocation in the inner loop
--set_option trace.compiler.ir.result true in
def vecMul : ℕ → IO Unit := genCase "vec mul"
    (fun num =>
      let v := vecStream num;
      let v' := vecStream num |>.map fun _ => 1;
      v * v')
    (fun x : F ℕ ℕ => x.1.size)

--set_option trace.compiler.ir.reset_reuse true in
--set_option trace.compiler.stage2 true in
def vecMulSum3 : ℕ → IO Unit := genCase "vec mul 3 sum"
  (fun num =>
    let v  := vecStream num
    let v₁ := vecStream num |>.map fun _ => 1
    let v₂ := vecStream num |>.map fun _ => 1
    contract $ v * (v₁ * v₂))
  (fun x : ℕ => x)

--def vecMul' (num : Nat) : IO Unit := do
--  IO.println "-----------"
--  let v := vecStream num
--  let v' := vecStream num |>.map fun _ => 1
--  let s := v * v'
--  time "vec mul" fun _ =>
--    for _ in [0:10] do
--      let x : SparseArray ℕ ℕ := eval s
--      IO.println s!"{x.1.size}"
--  pure ()

--set_option trace.compiler.ir.reset_reuse true in
def vecMul3 : ℕ → IO Unit := genCase "vec mul 3"
  (fun num =>
    let v  := vecStream num
    let v₁ := vecStream num |>.map fun _ => 1
    let v₂ := vecStream num |>.map fun _ => 1
    v * (v₁ * v₂))
  (fun x : F ℕ ℕ => x.1.size)

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

end test

unsafe def tests (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"

  let v := sparseVec num
  let v1 := sparseVecRB num
  let v2 := sparseVecRB num
  let m := sparseMat num.sqrt

  test.baseline num
  test.vecSum v
  test.rbVecSum v1 -- about 10x slower
  test.rbVecSumBaseline v2
  --test.vecCopy num
  test.matSum m
  ----test.vecBoolMul num
  ----test.vecBoolMul3 num
  --test.vecMulSum num
  --test.vecMul num
  --test.vecMul3 num
  ----test.vecMulSum3 num

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

-- IR option examples
section compiler_trace
@[inline]
def str1 := vecStream 10
--set_option trace.compiler.inline true
--set_option trace.compiler.specialize true
--set_option trace.compiler.stage2 true
--set_option trace.compiler.ir.reset_reuse true in
--set_option trace.compiler.ir.result true in
--def thetest' : ℕ := eval (contract (vecStream' 10)) --
@[noinline] def dup (x : α) := (x, x) example (x : ℕ) := let (a, _) := dup x; a
--def multest_ := let str1 := vecStream' 10; eval (contract (str1 * str1))
--def foo (n : ℕ) := let s := contract2 (mat n); eval s
unsafe example := myArrayLoop #[] 0
end compiler_trace

end appendix
