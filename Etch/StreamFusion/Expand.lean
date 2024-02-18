import Etch.StreamFusion.Stream
import Etch.StreamFusion.Multiply

namespace Etch.Verification.SStream

def LabeledIndex (n : Label) (ι : Type) := ι
def LabeledIndex.mk (n : Label) (i : ι) : LabeledIndex n ι := i

-- todo: decide on a nicer notation
notation n:30 "~" i:30 => LabeledIndex n i
notation n:30 "//" i:30 => LabeledIndex n i
--notation n:30 "/" i:30 => LabeledIndex n i
--macro_rules | `($label / $type)   => `(LabeledIndex $label $type)

@[inline] instance [LinearOrder ι] : LinearOrder (i//ι) := by unfold LabeledIndex; exact inferInstance
@[inline] instance [Inhabited ι] : Inhabited (i//ι) := by unfold LabeledIndex; exact inferInstance

class Label (σ : List ℕ) (α : Type*) (β : outParam Type*) where
  label : α → β
instance [Scalar α]     : Label [] α α := ⟨id⟩
instance [Label is α β] : Label (i::is) (ι →ₛ α) (i//ι →ₛ β) := ⟨map (Label.label is)⟩
instance [Label is α β] : Label (i::is) (ι → α) (i//ι → β) := ⟨(Label.label is ∘ .)⟩

class NatLt (m n : ℕ) where proof : m < n
instance NatLt.one (n : ℕ) : NatLt 0 n.succ := ⟨Nat.succ_pos _⟩
instance NatLt.step (m n : ℕ) [h : NatLt m n] : NatLt (m+1) (n+1) := ⟨Nat.succ_lt_succ h.proof⟩

class Contract (σ : ℕ) (α : Type*) (β : outParam Type*) where
  contract : α → β
instance : Contract i (i//ι →ₛ α) (Unit →ₛ α) := ⟨fun s => contract s⟩
instance [Contract j α β] [NatLt i j] : Contract j (i//ι →ₛ α) (i//ι →ₛ β) := ⟨map (Contract.contract j)⟩
instance [Contract j α β]  : Contract j (Unit →ₛ α) (Unit →ₛ β) := ⟨map (Contract.contract j)⟩

notation "Σ " j ", " t => Contract.contract j t
notation "Σ " j ": " t => Contract.contract j t

class Expand (σ : List (ℕ × Type)) (α : Type*) (β : outParam Type*) where
  expand : α → β

instance expBase                                                              : Expand [] α α                                 := ⟨id⟩
instance expScalar {ι : Type}   {i : ℕ} [Scalar α]  [Expand σ α β]            : Expand ((i,ι) :: σ) α           (i//ι → β)    := ⟨fun v _ => Expand.expand σ v⟩
instance expLt     {ι : Type} {i j : ℕ} [NatLt i j] [Expand σ (j//ι' →ₛ α) β] : Expand ((i,ι) :: σ) (j//ι' →ₛ α) (i//ι → β)   := ⟨fun v _ => Expand.expand σ v⟩
instance expGt     {ι : Type} {i j : ℕ} [NatLt j i] [Expand ((i,ι) :: σ) α β] : Expand ((i,ι) :: σ) (j//ι' →ₛ α) (j//ι' →ₛ β) := ⟨fun v => map (Expand.expand ((i,ι)::σ)) v⟩
instance expEq     {ι : Type}   {i : ℕ}             [Expand σ α β]            : Expand ((i,ι) :: σ) (i//ι  →ₛ α) (i//ι →ₛ β)  := ⟨fun v => map (Expand.expand σ) v⟩
instance expEqFun  {ι : Type}   {i : ℕ}             [Expand σ α β]            : Expand ((i,ι) :: σ) (i//ι  → α)  (i//ι → β)   := ⟨fun v => (Expand.expand σ) ∘ v⟩

instance [LinearOrder ι] [HMul α β γ] : HMul (i//ι →ₛ α) (i//ι →ₛ β) (i//ι →ₛ γ) := ⟨mul⟩
instance [HMul α β γ] : HMul (i//ι → α) (i//ι →ₛ β) (i//ι →ₛ γ) where
  hMul f x := { x with value := fun q => f (x.index q) * x.value q}
instance [HMul α β γ] : HMul (i//ι →ₛ α) (i//ι → β) (i//ι →ₛ γ) where
  hMul x f := { x with value := fun q => x.value q * f (x.index q) }

notation s:80 "⇑" x:80 => Expand.expand s x

@[inline]
def streamify (S : List (ℕ × Type)) (s : List ℕ) [ToStream α β] [Label s β γ] [Expand S γ δ] : α → δ :=
  Expand.expand S ∘ Label.label s ∘ ToStream.stream

syntax "{" term "|" term noWs "(" term,* ")" "}" : term
macro_rules
| `({$S | $t($ss,*) }) => `(streamify $S [$ss,*] $t)

instance [OfStream (ι →ₛ α) β] : OfStream (i//ι →ₛ α) β := ⟨fun x : ι →ₛ α => OfStream.eval x⟩

end Etch.Verification.SStream

-- not working
syntax "!_aux(" num ", " num ")" : term
syntax "!(" num ")" : term
open Lean in
macro_rules
| `(!_aux($count, $limit)) => do
  let count' := count.getNat + 1
  if count' < limit.getNat
  then `((($count : Nat), !_aux($(quote count'), $limit)))
  else `($count)
| `(!($limit)) => `(!_aux($(quote 0), $limit))
