import Etch.StreamFusion.Stream
import Etch.StreamFusion.Expand
import Etch.StreamFusion.TestUtil
namespace Etch.Verification.SStream

variable {I J K α β : Type}

abbrev PID := ℕ -- Person ID
abbrev MID := ℕ -- Movie ID

variable {I : Type}
[LinearOrder I]

abbrev pid : ℕ := 0
abbrev mid : ℕ := 1
abbrev i   : ℕ := 2

@[inline]
def peopleMovieDistance
    [ToStream P (PID →ₛ I →ₛ Float)]
    [ToStream M (MID →ₛ I →ₛ Float)]
    [ToStream R (PID →ₛ MID →ₛ Bool)]
    (personStream  : P)
    (movieStream   : M)
    (requestStream : R)
    : ℕ :=
  let shape := [ (pid,PID),(mid,MID),(i,I) ]
  let persons  := { shape | personStream(pid,i) }
  let movies   := { shape | movieStream(mid,i) }
  let requests := { shape | requestStream(pid,mid) }
  let result := Σ i, requests * persons * movies
  42

end Etch.Verification.SStream
