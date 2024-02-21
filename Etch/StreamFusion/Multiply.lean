import Etch.StreamFusion.Stream

namespace Etch.Verification.Stream

-- todo: experiment in simplifying control flow for `fold`
@[inline] def bothand (x y : Bool) : Bool :=
  x.toNat.land y.toNat = 1
@[simp] theorem bothand_spec : ∀ x y, bothand x y = and x y := by decide

infixl:35 " &' " => and

section
variable {ι : Type} [LinearOrder ι] {α : Type _} [Mul α]

variable (s : Stream ι α)

@[inline]
def mul.valid (a : Stream ι α) (b : Stream ι β) (q : a.σ × b.σ) : Bool := a.valid q.1 &' b.valid q.2

attribute [simp] mul.valid -- simp helps aesop proof below

@[inline]
def mul.valid.fst {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) : {x // a.valid x} :=
  ⟨q.val.fst, by aesop⟩

@[simp] lemma coe_mul_valid_fst {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) : (mul.valid.fst q : a.σ) = q.val.fst := rfl

@[inline]
def mul.valid.snd {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) : {x // b.valid x} :=
  ⟨q.val.snd, by aesop⟩

@[simp] lemma coe_mul_valid_snd {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) : (mul.valid.snd q : b.σ) = q.val.snd := rfl

@[inline]
def mul.valid.cases {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) : {x // a.valid x} × {x // b.valid x} :=
  match h : q.val with
  | (qa, qb) => (⟨qa, by aesop⟩, ⟨qb, by aesop⟩)
  -- mul.valid.fst q, mul.valid.snd q)

@[simp] lemma mul_valid_cases_eq {a : Stream ι α} {b : Stream ι β} (q : {p // mul.valid a b p}) :
    mul.valid.cases q = (mul.valid.fst q, mul.valid.snd q) := rfl

@[inline]
def mul.ready (a : Stream ι α) (b : Stream ι β) (q : {p // mul.valid a b p}) : Bool :=
match mul.valid.cases q with
| (q₁, q₂) => a.ready q₁ &' b.ready q₂ &' a.index q₁ = b.index q₂
    --let q₁ := mul.valid.fst q; let q₂ := mul.valid.snd q
    --a.ready q₁ &' b.ready q₂ &' a.index q₁ = b.index q₂

--todo
attribute [simp] mul.ready -- simp helps aesop proof below

@[inline]
def mul.ready.fst {a : Stream ι α} {b : Stream ι β} (q : {x // mul.ready a b x}) : {x // a.ready x} :=
  ⟨mul.valid.fst q.val, by aesop⟩

@[inline]
def mul.ready.snd {a : Stream ι α} {b : Stream ι β} (q : {x // mul.ready a b x}) : {x // b.ready x} :=
  ⟨mul.valid.snd q.val, by aesop⟩

@[inline]
def mul.ready.cases {a : Stream ι α} {b : Stream ι β} (q : {p // mul.ready a b p}) : {x // a.ready x} × {x // b.ready x} :=
match h : mul.valid.cases q.val with
| ⟨qa, qb⟩ =>
  (⟨qa, by aesop⟩, ⟨qb, by aesop⟩)
  --(mul.ready.fst q, mul.ready.snd q)

@[simp] lemma mul_ready_cases_eq {a : Stream ι α} {b : Stream ι β} (q : {p // mul.ready a b p}) :
    mul.ready.cases q = (mul.ready.fst q, mul.ready.snd q) := rfl

@[inline, simps (config := { simpRhs := true })]
def mul [HMul α β γ] (a : Stream ι α) (b : Stream ι β) : Stream ι γ where
  σ         := a.σ × b.σ
  valid q   := let (qa, qb) := q; a.valid qa &' b.valid qb
  ready q   := let (qa, qb) := mul.valid.cases q
               a.ready qa &' b.ready qb &' (a.index qa = b.index qb)
  index q   := let (qa, qb) := mul.valid.cases q
               max (a.index qa) (b.index qb)
  seek  q i := let (qa, qb) := mul.valid.cases q
               ⟨a.seek qa i, b.seek qb i⟩
  value q   := let (qa, qb) := mul.ready.cases q
               a.value qa * b.value qb

/-- Make a valid state given two valid states -/
def mul.valid_mk {a : Stream ι α} {b : Stream ι β} (qa : {x // a.valid x}) (qb : {x // b.valid x}) : {x // mul.valid a b x} :=
  ⟨(qa.val, qb.val), by aesop⟩

/-- Make a ready state given two ready states at the same index -/
def mul.ready_mk {a : Stream ι α} {b : Stream ι β} (qa : {x // a.ready x}) (qb : {x // b.ready x}) (h : a.index qa = b.index qb) : {x // mul.ready a b x} :=
  ⟨mul.valid_mk qa.val qb.val, by aesop⟩

end
end Stream

namespace SStream

section
variable {ι : Type} {α : Type u}
[LinearOrder ι]

--[LE ι] [DecidableRel (. ≤ . : ι → ι → Prop)]
--[LT ι] [DecidableRel (. < . : ι → ι → Prop)]
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

section boolean

instance [Zero α] [Scalar α] : HMul Bool α α where
  hMul b x := if b then x else 0

instance : Zero Bool := ⟨false⟩

instance [Zero α] : HMul (ι → Bool) (ι →ₛ α) (ι →ₛ α) where
  hMul b s := { s with
    ready := fun q => if b (s.index q) then s.ready q else false,
    seek  := fun q i => if s.ready q && not (b (s.index q))
                        then s.seek q ⟨i.1, true⟩ else s.seek q i
    value := fun q => s.value ⟨q.1, by
      cases q with | _ a b =>
      dsimp at b; split at b;
      . exact b;
      . contradiction; ⟩
  }

end boolean

end Etch.Verification.SStream
