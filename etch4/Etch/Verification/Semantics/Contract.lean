import Etch.Verification.Semantics.SkipStream

/-!
# Contraction of indexed streams

In this file, we define the contraction of indexed streams `Stream.contract`.
This replaces the indexing axis with `() : Unit`, implicitly summing over the
values of the stream.

## Main results
  - `contract_eval`: Correctness for `contract`; evaluating `contract s` results in
    the sum of the values of `s`
  - `is_lawful (Stream.contract s)`: `s.contract` is lawful assuming `s` is

-/

namespace Etch.Verification

variable {ι : Type} {α : Type _}

@[simps]
def Stream.contract (s : Stream ι α) : Stream Unit α
    where
  σ := s.σ
  valid := s.valid
  Ready := s.Ready
  skip q hq i := s.skip q hq (s.index q hq, i.2)
  index := default
  value := s.value
#align Stream.contract Etch.Verification.Stream.contract

variable [LinearOrder ι]

section IndexLemmas

instance (s : Stream ι α) [IsBounded s] : IsBounded (Stream.contract s) :=
  ⟨⟨s.WfRel, s.wf, fun q hq => by
      rintro ⟨⟨⟩, b⟩
      simp only [Stream.contract_skip]
      refine' (s.wf_valid q hq (s.index q hq, b)).imp_right (And.imp_left _)
      simp [Stream.toOrder]; exact id⟩⟩

@[simp]
theorem contract_next (s : Stream ι α) (q : s.σ) : (Stream.contract s).next q = s.next q :=
  rfl
#align contract_next Etch.Verification.contract_next

theorem contract_map {β : Type _} (f : α → β) (s : Stream ι α) :
    (s.map f).contract = s.contract.map f :=
  rfl
#align contract_map Etch.Verification.contract_map

end IndexLemmas

section ValueLemmas

variable [AddCommMonoid α]

theorem contract_eval₀ (s : Stream ι α) (q : s.σ) (hq : s.valid q) :
    (Stream.contract s).eval₀ q hq () = Finsupp.sumRange (s.eval₀ q hq) :=
  by
  simp only [Stream.eval₀]
  dsimp
  split_ifs with hr <;> simp
#align contract_eval₀ Etch.Verification.contract_eval₀

theorem contract_eval (s : Stream ι α) [IsBounded s] [AddCommMonoid α] (q : s.σ) :
    (Stream.contract s).eval q () = Finsupp.sumRange (s.eval q) :=
  by
  refine' @WellFounded.induction _ (Stream.contract s).WfRel (Stream.contract s).wf _ q _
  clear q; intro q ih
  by_cases hq : s.valid q; swap; · simp [hq]
  simp only [s.eval_valid _ hq, (Stream.contract s).eval_valid _ hq, Finsupp.coe_add, Pi.add_apply,
    map_add, ih _ ((Stream.contract s).next_wf q hq)]
  rw [contract_next, contract_eval₀]
#align contract_eval Etch.Verification.contract_eval

theorem contract_mono (s : Stream ι α) : (Stream.contract s).IsMonotonic := fun q hq i =>
  by
  rw [Stream.index'_val hq, PUnit.eq_punit ((Stream.contract s).index q hq)]
  exact bot_le
#align contract_mono Etch.Verification.contract_mono

instance (s : Stream ι α) [IsLawful s] : IsLawful (Stream.contract s)
    where
  mono := contract_mono s
  skip_spec q hq i j hj := by
    cases j
    obtain rfl : i = ((), ff) := le_bot_iff.mp hj
    simp only [Stream.contract_skip, contract_eval, Stream.eval_skip_eq_of_false]

end ValueLemmas

end Etch.Verification
