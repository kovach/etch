import Etch.StreamFusion.Stream

namespace Etch.Verification.Stream

section
variable {ι : Type} {α : Type _} [Mul α]
[LE ι] [DecidableRel (. ≤ . : ι → ι → Prop)]
[LT ι] [DecidableRel (. < . : ι → ι → Prop)]
[DecidableEq ι] [Max ι]

variable (s : Stream ι α)

@[inline, reducible] -- reducible helps aesop proof below
def mul.valid (a : Stream ι α) (b : Stream ι β) (q : a.σ × b.σ) : Bool := a.valid q.1 && b.valid q.2

@[inline]
def mul.valid.fst {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) : {x // a.valid x} :=
  ⟨q.val.fst, by aesop⟩

@[inline]
def mul.valid.snd {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) : {x // b.valid x} :=
  ⟨q.val.snd, by aesop⟩

@[inline]
def mul.valid.cases {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) : {x // a.valid x} × {x // b.valid x} :=
  (mul.valid.fst q, mul.valid.snd q)

@[inline, reducible] -- reducible helps aesop proof below
def mul.ready (a : Stream ι α) (b : Stream ι β) (q : {p // mul.valid a b p}) : Bool :=
    let q₁ := mul.valid.fst q; let q₂ := mul.valid.snd q
    a.ready q₁ && b.ready q₂ && a.index q₁ = b.index q₂

@[inline]
def mul.ready.fst {a : Stream ι α} {b : Stream ι β} (q : {x // mul.ready a b x}) : {x // a.ready x} :=
  ⟨mul.valid.fst q.val, by aesop⟩

@[inline]
def mul.ready.snd {a : Stream ι α} {b : Stream ι β} (q : {x // mul.ready a b x}) : {x // b.ready x} :=
  ⟨mul.valid.snd q.val, by aesop⟩

@[inline]
def mul.ready.cases {a : Stream ι α} {b : Stream ι β} (q : {p // mul.ready a b p}) : {x // a.ready x} × {x // b.ready x} :=
  (mul.ready.fst q, mul.ready.snd q)

@[inline]
def mul [HMul α β γ] (a : Stream ι α) (b : Stream ι β) : Stream ι γ where
  σ         := a.σ × b.σ
  valid q   := a.valid q.1 && b.valid q.2
  ready q   := let (qa, qb) := mul.valid.cases q
               a.ready qa && b.ready qb && a.index qa = b.index qb
  index q   := let (qa, qb) := mul.valid.cases q
               max (a.index qa) (b.index qb)
  seek  q i := let (qa, qb) := mul.valid.cases q
               ⟨a.seek qa i, b.seek qb i⟩
  value q   := let (qa, qb) := mul.ready.cases q
               a.value qa * b.value qb

end
end Stream

namespace SStream

section
variable {ι : Type} {α : Type u}

[LE ι] [DecidableRel (. ≤ . : ι → ι → Prop)]
[LT ι] [DecidableRel (. < . : ι → ι → Prop)]
[DecidableEq ι] [Max ι]

@[inline]
def mul [HMul α β γ] (a : SStream ι α) (b : SStream ι β) : SStream ι γ := {
  Stream.mul a.toStream b.toStream with
  q := ⟨a.q, b.q⟩
}

@[inline] instance [HMul α β γ] : HMul (ι →ₛ α) (ι →ₛ β) (ι →ₛ γ) := ⟨mul⟩

end

-- These don't require ordering on ι
@[inline] instance [HMul α β γ] : HMul (ι → α) (ι →ₛ β) (ι →ₛ γ) where
  hMul f x := { x with value := fun q => f (x.index q) * x.value q}
@[inline] instance [HMul α β γ] : HMul (ι →ₛ α) (ι → β) (ι →ₛ γ) where
  hMul x f := { x with value := fun q => x.value q * f (x.index q) }
@[inline] instance [HMul α β γ] {ι : Type} : HMul (ι → α) (ι → β) (ι → γ) where
  hMul f g x := f x * g x

end Etch.Verification.SStream
