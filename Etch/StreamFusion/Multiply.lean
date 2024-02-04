import Etch.StreamFusion.Stream

namespace Etch.Verification.Stream

variable {ι : Type} {α : Type _} [Mul α] [LinearOrder ι]
variable (s : Stream ι α)
--[h : LE ι] [DecidableRel h.le] [DecidableEq ι] -- todo: is the generated code different here?


@[inline]
def mul.valid.fst {a : Stream ι α} {b : Stream ι β} (p : {q : a.σ × b.σ // a.valid q.1 && b.valid q.2}) : {x // a.valid x} :=
  let ⟨q, hv⟩ := p; ⟨q.1, (Bool.and_eq_true _ _ ▸ hv).1⟩

@[inline]
def mul.valid.snd {a : Stream ι α} {b : Stream ι β} (p : {q : a.σ × b.σ // a.valid q.1 && b.valid q.2}) : {x // b.valid x} :=
  let ⟨q, hv⟩ := p; ⟨q.2, (Bool.and_eq_true _ _ ▸ hv).2⟩

@[inline]
def mul.ready {a : Stream ι α} {b : Stream ι β} (q : {p : a.σ × b.σ // a.valid p.1 && b.valid p.2}) : Bool :=
    let qa := mul.valid.fst q; let qb := mul.valid.snd q
    a.ready qa && b.ready qb && a.index qa = b.index qb

@[inline]
def mul.ready.fst [HMul α β γ] {a : Stream ι α} {b : Stream ι β} (q : {x : {p : a.σ × b.σ // a.valid p.1 && b.valid p.2} // mul.ready x}) : {x // a.ready x} :=
  let ⟨⟨q, v⟩, r⟩ := q;
  ⟨⟨q.1, (Bool.and_eq_true _ _ ▸ v).1⟩,
    by unfold mul.ready at r; simp_rw [Bool.and_eq_true] at r; exact r.1.1⟩

@[inline]
def mul.ready.snd [HMul α β γ] {a : Stream ι α} {b : Stream ι β} (q : {x : {p : a.σ × b.σ // a.valid p.1 && b.valid p.2} // mul.ready x}) : {x // b.ready x} :=
  let ⟨⟨q, v⟩, r⟩ := q;
  ⟨⟨q.2, (Bool.and_eq_true _ _ ▸ v).2⟩,
    by unfold mul.ready at r; simp_rw [Bool.and_eq_true] at r; exact r.1.2⟩


/- This combinator is a primary motivation for Stream -/
@[inline]
def mul [HMul α β γ] (a : Stream ι α) (b : Stream ι β) : Stream ι γ where
  σ         := a.σ × b.σ
  valid q   := a.valid q.1 && b.valid q.2
  ready q   := let qa := mul.valid.fst q; let qb := mul.valid.snd q
               a.ready qa && b.ready qb && a.index qa = b.index qb
  index q   := max (a.index (mul.valid.fst q)) (b.index (mul.valid.snd q))
  value q   := a.value (mul.ready.fst q) * b.value (mul.ready.snd q)
  seek  q i := ⟨a.seek (mul.valid.fst q) i, b.seek (mul.valid.snd q) i⟩

end Stream

namespace SStream

variable {ι : Type} [LinearOrder ι] {α : Type u}

@[macro_inline]
def mul [HMul α β γ] (a : SStream ι α) (b : SStream ι β) : SStream ι γ := {
  a.toStream.mul b.toStream with
  q := ⟨a.q, b.q⟩
  --weaken := fun h => by simp [Stream.mul] at *; split_ifs at h; assumption
}

@[macro_inline]
instance [HMul α β γ] : HMul (ℕ →ₛ α) (ℕ →ₛ β) (ℕ →ₛ γ) := ⟨mul⟩

@[macro_inline]
instance [HMul α β γ] : HMul (ι → α) (ι →ₛ β) (ι →ₛ γ) where
  hMul f x := { x with value := fun q => f (x.index q) * x.value q}

@[macro_inline]
instance [HMul α β γ] : HMul (ι →ₛ α) (ι → β) (ι →ₛ γ) where
  hMul x f := { x with value := fun q => x.value q * f (x.index q) }

end Etch.Verification.SStream
