/- TODO: make "indexed functor" class and generalize Expand; remove this file -/
/- This is largely duplicated from Expand! Please ensure any changes stay in sync. -/
import Etch.StreamFusion.SequentialStream
import Etch.Util.ExpressionTree

open Etch.ExpressionTree

namespace Etch.Verification.SequentialStream

section

local infixr:25 " →ₛ " => SequentialStream

-- todo: decide on a nicer notation
local notation n:30 "~" i:30 => LabeledIndex n i

variable (i : ℕ) (ι : Type)
@[inline] instance [LinearOrder ι] : LinearOrder (i~ι) := by change LinearOrder ι; exact inferInstance
@[inline] instance [Inhabited ι] : Inhabited (i~ι) := by change Inhabited ι; exact inferInstance

instance : TypeHasIndex (i~ι →ₛ β) i ι β where
instance : TypeHasIndex (i~ι → β) i ι β where

instance [Scalar α]     : Label [] α α := ⟨id⟩
instance [Label is α β] : Label (i::is) (ι →ₛ α) (i~ι →ₛ β) := ⟨map (Label.label is)⟩
instance [Label is α β] : Label (i::is) (ι → α) (i~ι → β) := ⟨(Label.label is ∘ .)⟩
instance [Label is α β] : Label (i::is) (i'~ι →ₛ α) (i~ι →ₛ β) := ⟨map (Label.label is)⟩
instance [Label is α β] : Label (i::is) (i'~ι → α) (i~ι → β) := ⟨(Label.label is ∘ .)⟩

def idx (x : α) (shape : List ℕ) [Label shape α β] := Label.label shape x

instance (I : Type) : MapIndex i α β (i~I →ₛ α) (i~I →ₛ β)where
  map f s := s.map f

instance (J : Type) [NatLt j i] [MapIndex i a b a' b'] : MapIndex i a b (j~J →ₛ a') (j~J →ₛ b') where
  map f s := s.map (MapIndex.map i f)

instance : Contract i (i~ι →ₛ α) (i~Unit →ₛ α) := ⟨fun s => contract s⟩
instance [Contract j α β] [NatLt i j] : Contract j (i~ι →ₛ α) (i~ι →ₛ β) := ⟨map (Contract.contract j)⟩
instance [Contract j α β]  : Contract j (Unit →ₛ α) (Unit →ₛ β) := ⟨map (Contract.contract j)⟩

--notation "Σ " j ", " t => Contract.contract j t
--notation "Σ " j ": " t => Contract.contract j t

variable {σ : List (Nat × Type)}

section
variable {α β : Type*}
instance expBase                                                              : Expand [] α α                               := ⟨id⟩
instance expScalar {ι : Type}   {i : ℕ} [Scalar α]  [Expand σ α β]            : Expand ((i,ι) :: σ) α           (i~ι → β)   := ⟨fun v _ => Expand.expand σ v⟩
instance expLt     {ι : Type} {i j : ℕ} [NatLt i j] [Expand σ (j~ι' →ₛ α) β]  : Expand ((i,ι) :: σ) (j~ι' →ₛ α) (i~ι → β)   := ⟨fun v _ => Expand.expand σ v⟩
instance expGt     {ι : Type} {i j : ℕ} [NatLt j i] [Expand ((i,ι) :: σ) α β] : Expand ((i,ι) :: σ) (j~ι' →ₛ α) (j~ι' →ₛ β) := ⟨fun v => map (Expand.expand ((i,ι)::σ)) v⟩
instance expEq     {ι : Type}   {i : ℕ}             [Expand σ α β]            : Expand ((i,ι) :: σ) (i~ι  →ₛ α) (i~ι →ₛ β)  := ⟨fun v => map (Expand.expand σ) v⟩

instance expLtFun  {ι : Type} {i j : ℕ} [NatLt i j] [Expand σ (j~ι' → α) β]   : Expand ((i,ι) :: σ) (j~ι' → α) (i~ι → β)    := ⟨fun v _ => Expand.expand σ v⟩
instance expGtFun  {ι : Type} {i j : ℕ} [NatLt j i] [Expand ((i,ι) :: σ) α β] : Expand ((i,ι) :: σ) (j~ι' → α) (j~ι' → β)   := ⟨fun v => Expand.expand ((i,ι)::σ) ∘ v⟩
instance expEqFun  {ι : Type}   {i : ℕ}             [Expand σ α β]            : Expand ((i,ι) :: σ) (i~ι  → α)  (i~ι → β)   := ⟨fun v => (Expand.expand σ) ∘ v⟩
end

-- Ignoring `base` for now. It should be used for a coercion.
instance [Expand σ α β] : EnsureBroadcast σ base α β where
  broadcast := Expand.expand σ

end

end Etch.Verification.SequentialStream
