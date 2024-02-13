import Etch.StreamFusion.Stream

def time (s : String) (m : Unit → IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← m ()
  let t1 ← IO.monoMsNow
  IO.println s!"[{s}] time: {t1-t0}"
  pure v

open Etch.Verification.SStream
open OfStream ToStream

@[inline]
def SStream.ofMat [Scalar α] (is : Array (ℕ × Array ℕ)) (vs : ℕ → ℕ → α) : ℕ →ₛ ℕ →ₛ α :=
  let x := is.map fun (row, cs) => (row, cs.map fun col => (col, vs row col))
  stream x

@[inline]
def SStream.ofMat' [Scalar α] (is : Array (ℕ × Array ℕ)) (vs : ℕ → ℕ → α) :=
  is.map fun (row, cs) => (row, cs.map fun col => (col, vs row col))

-- adjusts size so that there are ~num non-zero entries
-- macro_inline needed!
@[macro_inline]
def mat (num : Nat) :=
  let is : Array (ℕ × Array ℕ) :=
    Array.range (2*num).sqrt |>.map (.+1) |>.map $ fun n => (n, Array.range n)
  SStream.ofMat is fun _ m => m+10

-- macro_inline needed!
@[macro_inline]
def mat' (num : Nat) :=
  let is : Array (ℕ × Array ℕ) :=
    Array.range (2*num).sqrt |>.map (.+1) |>.map $ fun n => (n, Array.range n)
  SStream.ofMat' is fun _ m => m+10
