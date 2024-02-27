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

@[simp] lemma BddSStream.map_eq_map {α β : Type} (f : α → β) (s : ι →ₛb α) :
    (BddSStream.map f s).toSStream = s.toSStream.map f := rfl

@[inline, simp] def BddSStream.fold {α : Type} (f : β → ι → α → β) (s : ι →ₛb α) (b : β) : β :=
  s.toStream.fold_wf f s.q b

end bdd_stream

section eval
variable {ι : Type} [LinearOrder ι]

/- Note!! recursive application of `eval` needs to occur outside of any enclosing functions to achieve full inlining
   (see bad examples below)
-/

@[simp] lemma OfStream.eval_scalar [Scalar α] [Add α] (x y : α) :
    OfStream.eval x y = x + y := rfl

@[simps]
instance [OfStream α β] : OfStream (Unit →ₛb α) β where
  eval := BddSStream.fold (fun (a : β) _ (b : β → β) => b a) ∘ BddSStream.map OfStream.eval

@[simps]
instance [OfStream α β] [Modifiable ι β m] : OfStream (ι →ₛb α) m where
  eval := BddSStream.fold Modifiable.update ∘ BddSStream.map OfStream.eval

class LawfulModifiable (α β : outParam Type*) (m : Type*) [Zero β] [Zero m] extends Modifiable α β m, Readable α β m where
  get_update : ∀ (m : m) (x : α) (v : β → β), get (update m x v) x = v (get m x)
  get_update_ne : ∀ (m : m) (x y : α) (v : β → β), x ≠ y → get (update m x v) y = get m y
  get_zero : ∀ (x : α), get 0 x = 0

attribute [simp] LawfulModifiable.get_update LawfulModifiable.get_zero

section lawful_mod
open Std

-- lemma _root_.RBMap.find?_insert_of_eq {v' v : α} {cmp : α → α → Ordering} [TransCmp cmp] (t : RBMap α β cmp)
--     (h : cmp v' v = Ordering.eq) (x : β) :
--     (t.insert v x).find? v' = some x := by
--   dsimp [RBMap.find?, RBMap.findEntry?]
  -- apply RBSet.find?_insert_of_eq

instance [Zero β] : LawfulModifiable ι β (Std.RBMap ι β Ord.compare) where
  get := fun m i => m.findD i 0
  get_update := sorry
  get_update_ne := sorry
  get_zero := sorry


end lawful_mod

lemma LawfulModifiable.get_update' [Zero β] [Zero m] [DecidableEq α] (m₀ : m) (x t : α) (v : β → β) [LawfulModifiable α β m] :
    Readable.get (Modifiable.update m₀ x v) t = if x = t then v (Readable.get m₀ t) else Readable.get m₀ t := by
  split_ifs with h
  · rw [← h, LawfulModifiable.get_update]
  · rw [LawfulModifiable.get_update_ne _ _ _ _ h]

theorem LawfulModifiable.get_eq_eval [AddCommMonoid α] [Scalar α] (s : ι →ₛb α) (x : ι) [Zero m] [LawfulModifiable ι α m] :
    Readable.get (OfStream.eval s 0 : m) x = s.toStream.eval s.q x := by
  rcases s with ⟨⟨s, q⟩, bdd⟩; dsimp at bdd ⊢
  suffices :
    ∀ (m₀ : m), Readable.get ((s.map OfStream.eval).fold_wf Modifiable.update q m₀) x =
      (Readable.get m₀ x) + s.eval q x
  · simpa using this 0
  apply s.wf.induction q; clear q
  intro q ih m₀
  by_cases hv : s.valid q
  · -- TODO: can induction tactic do this?
    revert ih; refine Subtype.with_prop (fun t => s.valid t) q hv ?_; clear q hv
    intro q ih
    rw [Stream.fold_wf_spec, Stream.eval_valid, Stream.eval₀]
    dsimp only [map_σ, map_valid, map_ready, map_index, map_value, Finsupp.coe_add, Pi.add_apply]
    simp only [advance_val, map_seek, map_toOrder]
    rw [ih]
    split_ifs with hr
    · rw [Finsupp.single_apply, LawfulModifiable.get_update']
      split_ifs with heq
      · simp [← add_assoc, add_comm]
      · simp
    · simp
    · exact s.progress rfl.le
  · rw [Stream.fold_wf_invalid, Stream.eval_invalid (h := hv)]; swap; exact hv
    simp

theorem LawfulModifiable.get_eq_eval'  [OfStream α β] [Modifiable ι β m] (s : ι →ₛb α) [Zero β] [Zero m] [LawfulModifiable ι β m]
    [AddCommMonoid γ] {F} [ZeroHomClass F β γ] (tr : F)
    -- (htr : ∀ (i : ι) (s' : β), tr (OfStream.eval s' )) some additional assumption needed
    (x : ι) :
    tr (Readable.get (OfStream.eval s 0 : m) x) =
      (s.map fun a => tr (OfStream.eval a 0)).toStream.eval s.q x := by
  rcases s with ⟨⟨s, q⟩, bdd⟩; dsimp at bdd ⊢
  suffices :
    ∀ (m₀ : m), tr (Readable.get ((s.map OfStream.eval).fold_wf Modifiable.update q m₀) x) =
      tr (Readable.get m₀ x) + (s.map fun a => tr (OfStream.eval a 0)).eval q x
  · simpa using this 0
  · sorry


#check SStream.map

end eval

end Etch.Verification.Stream
