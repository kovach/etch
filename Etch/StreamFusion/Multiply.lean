import Etch.StreamFusion.Stream
import Std.Data.RBMap

open Std (RBMap HashMap)

namespace Etch.Verification.Stream


section
variable {ι : Type} {α : Type _} [Mul α] [LinearOrder ι]
variable (s : Stream ι α)
--[h : LE ι] [DecidableRel h.le] [DecidableEq ι] -- todo: is the generated code different here?

@[inline, reducible] -- reducible needed for aesop proof below
def mul.valid (a : Stream ι α) (b : Stream ι β) (q : a.σ × b.σ) : Bool := a.valid q.1 && b.valid q.2

@[inline]
def mul.valid.fst {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) : {x // a.valid x} :=
  ⟨q.1.1, by aesop⟩

@[inline]
def mul.valid.snd {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) : {x // b.valid x} :=
  ⟨q.1.2, by aesop⟩

@[inline, reducible] -- reducible needed for aesop proof below
def mul.ready {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) : Bool :=
    let q₁ := mul.valid.fst q; let q₂ := mul.valid.snd q
    a.ready q₁ && b.ready q₂ && a.index q₁ = b.index q₂

@[inline]
def mul.ready.fst [HMul α β γ] {a : Stream ι α} {b : Stream ι β} (q : {x : {p // mul.valid a b p} // mul.ready x}) : {x // a.ready x} :=
  ⟨mul.valid.fst q.1, by aesop⟩

@[inline]
def mul.ready.snd [HMul α β γ] {a : Stream ι α} {b : Stream ι β} (q : {x : {p // mul.valid a b p} // mul.ready x}) : {x // b.ready x} :=
  ⟨mul.valid.snd q.1, by aesop⟩

/- This combinator is a primary motivation for Stream -/
@[inline]
def mul [HMul α β γ] (a : Stream ι α) (b : Stream ι β) : Stream ι γ where
  σ         := a.σ × b.σ
  valid q   := a.valid q.1 && b.valid q.2
  ready q   := let q₁ := mul.valid.fst q; let q₂ := mul.valid.snd q
               a.ready q₁ && b.ready q₂ && a.index q₁ = b.index q₂
  index q   := max (a.index (mul.valid.fst q)) (b.index (mul.valid.snd q))
  value q   := a.value (mul.ready.fst q) * b.value (mul.ready.snd q)
  seek  q i := ⟨a.seek (mul.valid.fst q) i, b.seek (mul.valid.snd q) i⟩

end
end Stream

namespace SStream

section
variable {ι : Type} [LinearOrder ι] {α : Type u}

@[inline]
def mul [HMul α β γ] (a : SStream ι α) (b : SStream ι β) : SStream ι γ := {
  a.toStream.mul b.toStream with
  q := ⟨a.q, b.q⟩
}
end

@[inline] instance [LinearOrder ι] [HMul α β γ] : HMul (ι →ₛ α) (ι →ₛ β) (ι →ₛ γ) := ⟨mul⟩
@[inline] instance [HMul α β γ] : HMul (ι → α) (ι →ₛ β) (ι →ₛ γ) where
  hMul f x := { x with value := fun q => f (x.index q) * x.value q}
@[inline] instance [HMul α β γ] : HMul (ι →ₛ α) (ι → β) (ι →ₛ γ) where
  hMul x f := { x with value := fun q => x.value q * f (x.index q) }

end Etch.Verification.SStream
