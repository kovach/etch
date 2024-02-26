import Etch.StreamFusion.Stream
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

@[inline] def BddSStream.fold {α : Type} (f : β → ι → α → β) (s : ι →ₛb α) (b : β) : β :=
  s.toStream.fold_wf f s.q b

end bdd_stream

section eval
open SStream (Scalar)

variable {ι : Type} [LinearOrder ι]

/- Note!! recursive application of `eval` needs to occur outside of any enclosing functions to achieve full inlining
   (see bad examples below)
-/

instance [OfStream α β] : OfStream (Unit →ₛb α) β where
  eval := BddSStream.fold (fun (a : β) _ (b : β → β) => b a) ∘ BddSStream.map OfStream.eval

instance [OfStream α β] [Modifiable ι β m] : OfStream (ι →ₛb α) m where
  eval := BddSStream.fold Modifiable.update ∘ BddSStream.map OfStream.eval

variable {α : Type} [AddCommMonoid α] [Scalar α]

class LawfulModifiable (α β : outParam Type*) (m : Type*) [Zero β] [Zero m] extends Modifiable α β m where
  get : m → α → β
  get_update : ∀ (m : m) (x : α) (v : β → β), get (update m x v) x = v (get m x)
  get_update_ne : ∀ (m : m) (x y : α) (v : β → β), x ≠ y → get (update m x v) y = get m y
  get_zero : ∀ (x : α), get 0 x = 0

attribute [simp] LawfulModifiable.get_update

theorem LawfulModifiable.get_eq_eval (s : ι →ₛb α) (x : ι) [Zero m] [LawfulModifiable ι α m] :
    LawfulModifiable.get (OfStream.eval s 0 : m) x = s.toStream.eval s.q x := by
  sorry

-- theorem rbmap_eval (s : ι →ₛb α) (x : ι) :
--     (OfStream.eval s 0 : Map ι α).findD x 0 = s.toStream.eval s.q x :=
--   by

--     sorry


end eval

end Etch.Verification.Stream
