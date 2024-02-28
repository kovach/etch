import Etch.StreamFusion.Stream
import Etch.StreamFusion.Proofs.StreamProof
import Etch.StreamFusion.Proofs.NestedEval

namespace Etch.Verification.Stream

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
  supp_finite : ∀ (m : m), Set.Finite (Function.support <| get m)

attribute [simp] LawfulModifiable.get_update LawfulModifiable.get_zero

noncomputable def LawfulModifiable.getAsFinsupp [Zero β] [Zero m] [LawfulModifiable ι β m] : ZeroHom m (ι →₀ β) where
  toFun := fun m => Finsupp.ofSupportFinite (Readable.get m) (LawfulModifiable.supp_finite m)
  map_zero' := by ext; exact LawfulModifiable.get_zero _

open EvalToFinsupp LawfulModifiable

@[simp] lemma LawfulModifiable.getAsFinsupp_apply [Zero β] [Zero m] [LawfulModifiable ι β m] (m : m) (i : ι) :
    (getAsFinsupp m : ι →₀ β) i = Readable.get m i := rfl

@[simps]
noncomputable instance LawfulModifiable.instEvalToFinsupp [Zero α] [Zero β] [Zero m] [LawfulModifiable ι α m] [EvalToFinsupp α β]  :
    EvalToFinsupp m (ι →₀ β) where
  evalFinsupp := ZeroHom.comp (Finsupp.mapRange.zeroHom (α := ι) (evalFinsupp : ZeroHom α β)) (getAsFinsupp (ι := ι) (β := α) (m := m))

class LawfulOfStream (α β γ : Type*) [Zero α] [Zero β] [AddZeroClass γ] [EvalToFinsupp α γ] [EvalToFinsupp β γ] extends OfStream α β where
  eval_of_stream : ∀ (s : α) (b : β), (evalFinsupp (eval s b) : γ) = evalFinsupp b + evalFinsupp s

class LawfulToStream (α : Type*) (β γ : outParam Type*) [Zero α] [Zero β] [Zero γ] [EvalToFinsupp α γ] [EvalToFinsupp β γ] extends ToStream α β where
  to_stream_eval : ∀ (d : α), (evalFinsupp (stream d) : γ) = evalFinsupp d

instance [AddCommMonoid α] [Scalar α] : LawfulOfStream α α α where
  eval_of_stream := fun s b => by simp [add_comm]

-- class LawfulToStream (ι α β γ : outParam Type) [Preorder ι] [Readable ι β m]
--     [EvalToFinsupp α γ] [EvalToFinsupp β γ] [ToStream m (ι →ₛb α)] [AddZeroClass γ] where
--   to_stream_eval : ∀ (d : m) (x : ι), (((ToStream.stream d).map evalFinsupp).eval : ι →₀ γ) x = evalFinsupp (Readable.get d x : β)

lemma LawfulModifiable.get_update' [Zero β] [Zero m] [DecidableEq α] (m₀ : m) (x t : α) (v : β → β) [LawfulModifiable α β m] :
    Readable.get (Modifiable.update m₀ x v) t = if x = t then v (Readable.get m₀ t) else Readable.get m₀ t := by
  split_ifs with h
  · rw [← h, LawfulModifiable.get_update]
  · rw [LawfulModifiable.get_update_ne _ _ _ _ h]

theorem LawfulOfStream.get_fold [Zero α] [Zero β] [Zero m] [AddCommMonoid γ]
    [EvalToFinsupp α γ] [EvalToFinsupp β γ]
    [LawfulOfStream α β γ] [LawfulModifiable ι β m] (s : Stream ι α) [IsBounded s] (q : s.σ) (i : ι) :
    ∀ (b : m), evalFinsupp (Readable.get (fold_wf Modifiable.update (map OfStream.eval s) q b) i) =
      evalFinsupp (Readable.get b i) + (eval (map (⇑evalFinsupp) s) q) i := by
  apply s.wf.induction q; clear q
  intro q ih b
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
      · rw [← add_assoc]
        rw [LawfulOfStream.eval_of_stream]
      · simp
    · simp
    · exact s.progress rfl.le
  · rw [Stream.fold_wf_invalid, Stream.eval_invalid]; all_goals (try exact hv)
    simp

instance [Zero α] [Zero β] [Zero m] [AddCommMonoid γ]
    [EvalToFinsupp α γ] [EvalToFinsupp β γ]
    [LawfulOfStream α β γ] [LawfulModifiable ι β m] : LawfulOfStream (ι →ₛb α) m (ι →₀ γ) where
  eval_of_stream := by
    rintro ⟨⟨s, q⟩, bdd⟩ b
    ext i
    exact LawfulOfStream.get_fold s q i b

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
  supp_finite := sorry


end lawful_mod

-- theorem LawfulModifiable.get_eq_eval [AddCommMonoid α] [Scalar α] (s : ι →ₛb α) (x : ι) [Zero m] [LawfulModifiable ι α m] :
--     Readable.get (OfStream.eval s 0 : m) x = s.toStream.eval s.q x := by
--   rcases s with ⟨⟨s, q⟩, bdd⟩; dsimp at bdd ⊢
--   suffices :
--     ∀ (m₀ : m), Readable.get ((s.map OfStream.eval).fold_wf Modifiable.update q m₀) x =
--       (Readable.get m₀ x) + s.eval q x
--   · simpa using this 0
--   apply s.wf.induction q; clear q
--   intro q ih m₀
--   by_cases hv : s.valid q
--   · -- TODO: can induction tactic do this?
--     revert ih; refine Subtype.with_prop (fun t => s.valid t) q hv ?_; clear q hv
--     intro q ih
--     rw [Stream.fold_wf_spec, Stream.eval_valid, Stream.eval₀]
--     dsimp only [map_σ, map_valid, map_ready, map_index, map_value, Finsupp.coe_add, Pi.add_apply]
--     simp only [advance_val, map_seek, map_toOrder]
--     rw [ih]
--     split_ifs with hr
--     · rw [Finsupp.single_apply, LawfulModifiable.get_update']
--       split_ifs with heq
--       · simp [← add_assoc, add_comm]
--       · simp
--     · simp
--     · exact s.progress rfl.le
--   · rw [Stream.fold_wf_invalid, Stream.eval_invalid (h := hv)]; swap; exact hv
--     simp

-- theorem LawfulModifiable.get_eq_eval'  [OfStream α β] [Modifiable ι β m] (s : ι →ₛb α) [Zero β] [Zero m] [LawfulModifiable ι β m]
--     [AddCommMonoid γ] {F} [ZeroHomClass F β γ] (tr : F)
--     -- (htr : ∀ (i : ι) (s' : β), tr (OfStream.eval s' )) some additional assumption needed
--     (x : ι) :
--     tr (Readable.get (OfStream.eval s 0 : m) x) =
--       (s.map fun a => tr (OfStream.eval a 0)).toStream.eval s.q x := by
--   rcases s with ⟨⟨s, q⟩, bdd⟩; dsimp at bdd ⊢
--   suffices :
--     ∀ (m₀ : m), tr (Readable.get ((s.map OfStream.eval).fold_wf Modifiable.update q m₀) x) =
--       tr (Readable.get m₀ x) + (s.map fun a => tr (OfStream.eval a 0)).eval q x
--   · simpa using this 0
--   · sorry

end eval

end Etch.Verification.Stream
