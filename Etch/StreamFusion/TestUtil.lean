import Etch.StreamFusion.Stream
import Etch.StreamFusion.Traversals

def time (s : String) (m : Unit → IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← m ()
  let t1 ← IO.monoMsNow
  IO.println s!"[{s}] time: {t1-t0}"
  pure v

open Etch.Verification
open SStream
open OfStream ToStream

variable
{ι ι' : Type}
[LinearOrder ι] [LinearOrder ι']

@[inline] def sparseVec (num : Nat) :=
  let v  : Vec ℕ num := ⟨Array.range num, Array.size_range⟩
  SparseArray.mk v v

@[inline] def sparseVecRB (num : Nat) :=
  RB.TreeMap.ofList $ (List.range num).map fun n => (n,n)

@[inline] def vecStream (num : Nat) :=
  let v  : Vec ℕ num := ⟨Array.range num, Array.size_range⟩
  stream $ SparseArray.mk v v

@[inline]
def SparseArray.range (num : Nat) : SparseArray ℕ ℕ :=
  let v := Vec.range num; SparseArray.mk v v

@[inline] def sparseMat (num : Nat) :=
  let v := SparseArray.range num
  v.mapVals fun _ => SparseArray.range num

@[inline] def boolStream (num : Nat) : ℕ →ₛ Bool:=
  stream $ Array.range num
