/- very WIP tutorial for the library -/

import Etch.StreamFusion.Stream
import Etch.StreamFusion.Expand
import Etch.StreamFusion.TestUtil

namespace Etch.Verification.SStream

variable {I J K L α β : Type}
[LinearOrder I] [LinearOrder J] [LinearOrder K] [LinearOrder L]
[Scalar α] [Mul α] [Zero α] [Add α]

abbrev i : ℕ := 0
abbrev j : ℕ := 1
abbrev k : ℕ := 2
abbrev l : ℕ := 3

/- Some examples of `{ shape | collection(indices) }` notation

  notes:
    - a shape is a list of (Nat, Type) pairs
    - a collection needs to have a ToStream instance
    - indices are index names encoded as natural numbers for now
-/

@[inline] def vecSum [ToStream t (I →ₛ α)] (v : t)      := Σ i, { [(i,I)] | v(i) }
@[inline] def matSum [ToStream t (I →ₛ J →ₛ α)] (m : t) := Σ i, Σ j, { [(i,I), (j,J)] | m(i, j) }

@[inline]
def matMul_ijjk [ToStream t (I →ₛ J →ₛ α)] [ToStream t' (J →ₛ K →ₛ α)] (a : t) (b : t')
    : i//I →ₛ Unit →ₛ k//K →ₛ α :=
  let ijk := [(i,I),(j,J),(k,K)]
  let m1 := { ijk | a(i,j) }
  let m2 := { ijk | b(j,k) }
  let m  := m1 * m2
  Σ j, m

#synth  OfStream (K →ₛ α) ((ArrayMap K α))

-- todo: investigate these definitions and other approaches
@[inline] def ABC
  [ToStream t1 (I →ₛ J →ₛ α)]
  [ToStream t2 (J →ₛ K →ₛ α)]
  [ToStream t3 (K →ₛ L →ₛ α)]
   (a : t1) (b : t2) (c : t3) : i//I →ₛ Unit →ₛ l//L →ₛ α :=
  let S1 := [(i,I),(j,J),(k,K)]
  let S2 := [(i,I),(k,K),(l,L)]
  let m1 := { S1 | a(i,j) }
  let m2 := { S1 | b(j,k) }
  let m3 := { S2 | c(k,l) }
  let x : ArrayMap I (ArrayMap K α) := eval $ Σ j, m1 * m2
  let m  := {S2| x(i,k)} * m3
  Σ k, m

@[inline] def ABC' [ToStream t1 (I →ₛ J →ₛ α)] [ToStream t2 (J →ₛ K →ₛ α)] [ToStream t3 (K →ₛ L →ₛ α)]
   (a : t1) (b : t2) (c : t3) : i//I →ₛ Unit →ₛ l//L →ₛ α :=
  let jk := [(j,J),(k,K)]
  let ijk := [(i,I),(j,J),(k,K)]
  let ikl := [(i,I),(k,K),(l,L)]
  let m1 := { ijk | a(i,j) }
  let m3 := {ikl| c(k,l) }
  let m : i//I →ₛ k//K →ₛ α := m1.map fun (row : j//J →ₛ k//K → α) =>
             memo (ArrayMap K α) (Σ j: row * { jk | b(j,k) })
  let m  := ikl ⇑ m * m3
  Σ k, m

/- Exercise: write out the types for a and b and fill in the body;
   It should compute a(i,k) * b(j,k) and mirror the definition of matMul_ijjk
-/
@[inline]
def matMul_ikjk (a : sorry) (b : sorry) : I →ₛ J →ₛ Unit →ₛ α := sorry

def matMul1 (num : ℕ) : IO Unit := do
  let m := mat' num
  let x := matMul_ijjk m m
  time "matrix 1'" fun _ =>
    for _ in [0:10] do
      let x : HMap ℕ (HMap ℕ ℕ) := eval x
      IO.println s!"{x.1.size}"

def matMul1' (num : ℕ) : IO Unit := do
  let m := mat' num
  let x := Σ i, Σ k, matMul_ijjk m m
  time "matrix 1'" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval x
      IO.println s!"{x}"

def testABC (num : ℕ) : IO Unit := do
  let m := mat' num
  time "matrix abc" fun _ =>
    for _ in [0:10] do
      let x : ArrayMap ℕ (HMap ℕ ℕ) := eval $ ABC m m m
      IO.println s!"{x.1.size}"

def testABC' (num : ℕ) : IO Unit := do
  let m := mat' num
  time "matrix abc'" fun _ =>
    for _ in [0:10] do
      let x : ArrayMap ℕ (HMap ℕ ℕ) := eval $ ABC' m m m
      IO.println s!"{x.1.size}"

/- Exercise: add a test that invokes matMul_ikjk, otherwise identical to matMul1 -/
def matMul2 (num : ℕ) : IO Unit := sorry

/- Exercise: add a test that invokes vecSum -/

def _root_.main (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"
  --matMul1 num
  --matMul1' num
  testABC num
  testABC' num

end Etch.Verification.SStream
