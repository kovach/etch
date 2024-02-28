import Etch.StreamFusion.Proofs.StreamProof

namespace Etch.Verification.Stream

section bdd_stream

variable (ι : Type) [Preorder ι]

structure BddSStream (α : Type) extends SStream ι α :=
  (bdd : IsBounded toStream)

attribute [instance] BddSStream.bdd

infixr:25 " →ₛb " => BddSStream

variable {ι}

@[macro_inline] def BddSStream.map {α β : Type} (f : α → β) (s : ι →ₛb α) : ι →ₛb β :=
  { s with
    value := f ∘ s.value
    bdd := ⟨s.bdd.out⟩ }

@[simp] lemma BddSStream.map_eq_map {α β : Type} (f : α → β) (s : ι →ₛb α) :
    (BddSStream.map f s).toSStream = s.toSStream.map f := rfl

@[inline, simp] def BddSStream.fold {α : Type} (f : β → ι → α → β) (s : ι →ₛb α) (b : β) : β :=
  s.toStream.fold_wf f s.q b

noncomputable def BddSStream.eval [AddZeroClass α] (s : ι →ₛb α) : ι →₀ α :=
  s.toStream.eval s.q

instance : Zero (ι →ₛb α) where
  zero := { toSStream := 0, bdd := inferInstanceAs (IsBounded 0) }

@[simp] lemma zero_toStream : (0 : ι →ₛb α).toStream = 0 := rfl
@[simp] lemma zero_state : (0 : ι →ₛb α).q = () := rfl

end bdd_stream

class EvalToFinsupp (α : Type*) (β : outParam (Type*)) [Zero α] [Zero β] where
  evalFinsupp : ZeroHom α β

open EvalToFinsupp

@[simps]
instance [Scalar α] [AddZeroClass α] : EvalToFinsupp α α where
  evalFinsupp := ⟨id, rfl⟩

@[simps]
noncomputable instance [LinearOrder ι] [Zero α] [AddZeroClass β] [EvalToFinsupp α β] : EvalToFinsupp (ι →ₛb α) (ι →₀ β) where
  evalFinsupp := ⟨fun f => (f.map evalFinsupp).eval, by
    change (0 : ι →ₛb β).eval = 0
    dsimp [BddSStream.eval]
    simp
  ⟩

end Etch.Verification.Stream
