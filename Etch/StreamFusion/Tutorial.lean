/- very WIP tutorial for the library -/

import Etch.StreamFusion.Stream
import Etch.StreamFusion.Expand
import Etch.StreamFusion.TestUtil

namespace Etch.Verification.SStream

variable {I J K α β : Type}
[LinearOrder I] [LinearOrder J] [LinearOrder K]
[Scalar α] [Mul α] [Mul β]

abbrev i : ℕ := 0
abbrev j : ℕ := 1
abbrev k : ℕ := 2

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
    : i~I →ₛ Unit →ₛ k~K →ₛ α :=
  let ijk := [(i,I),(j,J),(k,K)]
  let m1 := { ijk | a(i,j) }
  let m2 := { ijk | b(j,k) }
  let m  := m1 * m2
  Σ j, m

/- Exercise: write out the types for a and b and fill in the body;
   It should compute a(i,k) * b(j,k) and mirror the definition of matMul_ijjk
-/
@[inline]
def matMul_ikjk (a : sorry) (b : sorry) : I →ₛ J →ₛ Unit →ₛ α := sorry

def matMul1 (num : Nat) : IO Unit := do
  let m := mat' num
  let x := matMul_ijjk m m
  time "matrix 1'" fun _ =>
    for _ in [0:10] do
      let x : HMap ℕ (HMap ℕ ℕ) := eval x
      IO.println s!"{x.1.size}"

def matMul1' (num : Nat) : IO Unit := do
  let m := mat' num
  let x := Σ i, Σ k, matMul_ijjk m m
  time "matrix 1'" fun _ =>
    for _ in [0:10] do
      let x : ℕ := eval x
      IO.println s!"{x}"

/- Exercise: add a test that invokes matMul_ikjk, otherwise identical to matMul1 -/
def matMul2 (num : Nat) : IO Unit := sorry

/- Exercise: add a test that invokes vecSum -/

def _root_.main (args : List String) : IO Unit := do
  let num := (args[0]!).toNat?.getD 1000
  IO.println s!"test of size {num}"
  IO.println "starting"
  matMul1 num
  matMul1' num
  --matMul2 num -- uncomment after exercise is done

end Etch.Verification.SStream
