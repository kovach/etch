import Mathlib.Tactic.Linarith

import Etch.StreamFusion.Stream
import Etch.Verification.FinsuppLemmas
import Etch.Verification.Misc

namespace Etch.Verification

section StreamDefs

/- In this section we give many simple, auxiliary definitions related to streams.
  Many of these simply give default values to partial functions e.g. `index'` gives the default value `⊤` when
  the stream has terminated (is invalid). -/
variable {ι : Type} {α : Type _}

variable (a b : Stream ι α)

variable (s : Stream ι α)

/--
Abbreviation for `ι × bool` with the lexicographic ordering (an index with a strictness indicator) -/
@[reducible]
def StreamOrder (ι : Type) : Type :=
  ι ×ₗ Bool

/-- The current emmited value; if ready, this is `index ↦ value`, otherwise it is 0.
  This is denoted `index(r) ↦ −→ ready(r) · ⟦value(r)⟧` in the paper. -/
noncomputable def Stream.eval₀ [Zero α]  (σ₀ : {q // s.valid q}) : ι →₀ α :=
  if h₂ : s.ready σ₀ then Finsupp.single (s.index σ₀) (s.value ⟨σ₀, h₂⟩) else 0

/-- The current `(index, ready)` value of the stream -/
@[simps]
def Stream.toOrder (q : {q // s.valid q}) : StreamOrder ι :=
  (s.index q, s.ready q)

/-- The index with a default value of `⊤` if the state `x` is not valid -/
def Stream.index' (x : s.σ) : WithTop ι :=
  if h : s.valid x then s.index ⟨x, h⟩ else ⊤

/-- Whether the stream is valid *and* ready -/
def Stream.ready' (x : s.σ) : Prop :=
  ∃ h : s.valid x, s.ready ⟨x, h⟩

instance : DecidablePred s.ready' :=
  fun x => inferInstanceAs (Decidable (∃ h, s.ready ⟨x, h⟩))

@[simp] lemma Stream.ready'_val (x : {q // s.valid q}) : s.ready' x ↔ s.ready x :=
  by simp [Stream.ready', x.prop]

/-- The current `(index', valid ∧ ready)` value of the stream -/
def Stream.toOrder' (q : s.σ) : WithTop ι ×ₗ Bool :=
  (s.index' q, decide (s.ready' q))

/-- The value, with a default value of `0` if the stream is not ready -/
def Stream.value' [Zero α] (x : s.σ) : α :=
  if h : s.ready' x then s.value ⟨⟨x, h.1⟩, h.2⟩
  else 0

def Stream.advance (q : s.σ) : s.σ :=
  if h : s.valid q then s.seek ⟨q, h⟩ (s.toOrder ⟨q, h⟩) else q

/-- Skips to `i` from `q`, or stays at the same state if the stream has terminated -/
def Stream.seek' (q : s.σ) (i : StreamOrder ι) : s.σ :=
  if h : s.valid q then s.seek ⟨q, h⟩ i else q

section order
/--
Order injection from `stream_order ι` to `(with_top ι) ×ₗ bool` by coercing the first argument -/
abbrev coeLex (x : StreamOrder ι) : WithTop ι ×ₗ Bool :=
  (↑x.1, x.2)


@[simp]
theorem coeLex_le_iff [Preorder ι] {x y : StreamOrder ι} : coeLex x ≤ coeLex y ↔ x ≤ y := by
  simp [Prod.Lex.le_iff']

@[simp]
theorem coeLex_lt_iff [Preorder ι] {x y : StreamOrder ι} : coeLex x < coeLex y ↔ x < y := by
  simp [Prod.Lex.lt_iff']

theorem coeLex_injective : Function.Injective (@coeLex ι)
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => by
    rw [Prod.mk.injEq .., Prod.mk.injEq ..]
    simp

@[simp]
theorem coeLex_inj (x y : StreamOrder ι) : coeLex x = coeLex y ↔ x = y :=
  coeLex_injective.eq_iff
end order

variable {s}

@[simp]
theorem Stream.index'_val (x : {q // s.valid q}) : s.index' x = s.index x :=
  dif_pos x.prop

theorem Stream.index'_val' (x : s.σ) (h : s.valid x) : s.index' x = s.index ⟨x, h⟩ :=
  Stream.index'_val ⟨x, h⟩

@[simp]
theorem Stream.index'_invalid {x : s.σ} (h : s.valid x = false) : s.index' x = ⊤ :=
  dif_neg (by simpa)


@[simp]
theorem Stream.value'_val [Zero α] (x : {q // s.ready' q}) :
    s.value' x = s.value ⟨⟨x, x.prop.1⟩, x.prop.2⟩ :=
  dif_pos x.prop

@[simp]
theorem Stream.advance_val (x : {q // s.valid q}) :
    s.advance x = s.seek x (s.toOrder x) :=
  dif_pos x.prop

@[simp]
theorem Stream.advance_invalid {x : s.σ} (h : ¬s.valid x) : s.advance x = x :=
  dif_neg h

variable (s)
@[simp]
theorem Stream.toOrder'_fst (q : s.σ) : (s.toOrder' q).1 = s.index' q :=
  rfl

variable {s}
@[simp]
theorem Stream.seek'_val {q : s.σ} (hq : s.valid q) (i : ι ×ₗ Bool) :
    s.seek' q i = s.seek ⟨q, hq⟩ i :=
  dif_pos hq

@[simp]
theorem Stream.seek'_invalid {q : s.σ} (hq : ¬s.valid q) (i : ι ×ₗ Bool) :
    s.seek' q i = q :=
  dif_neg hq

theorem Stream.toOrder'_val (q : {q // s.valid q}) :
    s.toOrder' q = (s.index' q, s.ready q) := by simp [Stream.toOrder']

theorem Stream.coeLex_toOrder (q : {q // s.valid q}) :
    s.toOrder' q = coeLex (s.toOrder q) := by
  simp [coeLex, Stream.toOrder'_val]

@[simp]
theorem Stream.toOrder'_val_snd (q : {q // s.valid q}) :
    (s.toOrder' q).2 = s.ready q := by simp [Stream.toOrder'_val]


@[simp]
theorem Stream.index'_lt_top_iff [Preorder ι] {q : s.σ} :
    s.index' q < ⊤ ↔ s.valid q := by
  rw [Stream.index']
  split_ifs
  · simpa [WithTop.coe_lt_top]
  · simp [*]

@[simp]
theorem Stream.get_index' [PartialOrder ι] {x : s.σ} (h : (s.index' x).isSome) :
    (s.index' x).get h = s.index ⟨x, (by simpa using h)⟩ := by
  generalize_proofs hq
  simp_rw [Stream.index', hq, Option.get]

-- We use this notation so that we can explicitly ask Lean to use lexicographic comparison (rather than pointwise comparison)
scoped[Streams] notation:50 a " <ₗ " b => @LT.lt (Etch.Verification.StreamOrder _) _ a b
scoped[Streams] notation:50 a " ≤ₗ " b => @LE.le (Etch.Verification.StreamOrder _) _ a b

open Streams

variable (s)

section well_founded
variable [Preorder ι]
/-- The stream is bounded if there is a well-founded relation `≺` on states such that
    a) whenever we are asked to skip past an index `i` past the current index (i.e. `i ≥ s.to_order q`),
        we strictly make progress (`s.skip q hq i ≺ q`)
    b) We always either make progress or remain at the same state
  These properties ensure that evaluation terminates. -/
@[mk_iff]
class IsBounded : Prop where
  out :
    ∃ wf_rel : WellFoundedRelation s.σ,
      ∀ q i, wf_rel.rel (s.seek q i) q ∨ (i <ₗ s.toOrder q) ∧ s.seek q i = q

/-- Extract the well-founded relation on a bounded stream -/
noncomputable def Stream.wfRel [IsBounded s] : WellFoundedRelation s.σ :=
  ‹IsBounded s›.out.choose

/-- Extract the well-founded relation on a bounded stream -/
def Stream.WfRel [IsBounded s] : s.σ → s.σ → Prop :=
  s.wfRel.rel

scoped notation:50 a " ≺ " b => Etch.Verification.Stream.WfRel _ a b

theorem Stream.wf [LT ι] [IsBounded s] : WellFounded s.WfRel :=
  s.wfRel.wf

theorem Stream.wf_valid [IsBounded s] :
    ∀ q i, (s.seek q i ≺ q) ∨ (i <ₗ s.toOrder q) ∧ s.seek q i = q :=
  ‹IsBounded s›.out.choose_spec

theorem wf_valid_iff (wf_rel : s.σ → s.σ → Prop) (q i) :
    wf_rel (s.seek q i) q ∨ i < s.toOrder q ∧ s.seek q i = q ↔
      wf_rel (s.seek' q i) q ∨ coeLex i < s.toOrder' q ∧ s.seek' q i = q :=
  by simp only [Stream.seek'_val q.prop, Stream.coeLex_toOrder, coeLex_lt_iff]

variable {s}
theorem IsBounded.mk'
    (h :
      ∃ wf_rel : WellFoundedRelation s.σ,
        ∀ q i, wf_rel.rel (s.seek' q i) q ∨ coeLex i < s.toOrder' q ∧ s.seek' q i = q) :
    IsBounded s :=
  ⟨by
    simp only [wf_valid_iff]
    rcases h with ⟨wfr, hr⟩
    exact ⟨wfr, fun q i => hr q i⟩⟩

variable (s)
theorem Stream.wf_valid' [IsBounded s] (q i) :
    (s.seek' q i ≺ q) ∨ coeLex i < s.toOrder' q ∧ s.seek' q i = q :=
  if hq : s.valid q then by
    rw [← wf_valid_iff (q := ⟨q, hq⟩)]
    exact s.wf_valid ⟨q, hq⟩ i
  else by
    right
    constructor
    · rw [Prod.Lex.lt_iff']
      left
      simpa [hq] using WithTop.coe_lt_top _
    · simp [hq]

theorem Stream.progress [IsBounded s] {q i} (h : s.toOrder q ≤ i) :
    s.seek q i ≺ q :=
  (s.wf_valid q i).resolve_right fun H => absurd H.1 h.not_lt

theorem Stream.next_wf [IsBounded s] (q : {q // s.valid q}) : s.advance q ≺ q := by
  rw [Stream.advance_val]
  exact s.progress rfl.le

theorem Stream.no_backward [IsBounded s] (q i) :
    (s.seek q i ≺ q) ∨ s.seek q i = q :=
  (s.wf_valid q i).imp_right And.right

/-- Evaluates `∑_{q →* r} eval₀ r`, which is well-defined for bounded streams. -/
noncomputable def Stream.eval [AddZeroClass α] (s : Stream ι α) [IsBounded s]
    : s.σ → ι →₀ α
  | q =>
    if h : s.valid q then
      have : s.WfRel (s.advance q) q := s.next_wf ⟨q, h⟩
      s.eval₀ ⟨q, h⟩ + s.eval (s.advance q)
    else 0
termination_by _ x => s.wf.wrap x
end well_founded

@[inline] def Stream.fold_wf [Preorder ι] (f : β → ι → α → β) (s : Stream ι α) [IsBounded s]
    (q : s.σ) (acc : β) : β :=
  let rec @[specialize] go [Preorder ι] [IsBounded s] f
      (valid : s.σ → Bool) (ready : (x : s.σ) → valid x → Bool)
      (index : (x : s.σ) → valid x → ι) (value : (x : s.σ) → (h : valid x) → ready x h → α)
      (next : (x : s.σ) → valid x → Bool → s.σ)
      (h : ∀ (q : s.σ) (hv : valid q), next q hv (ready q hv) ≺ q)
      (acc : β) (q : s.σ) : β :=
        if hv : valid q then
          let i := index q hv
          let hr := ready q hv
          let q' := next q hv hr
          let acc' := if hr : hr then f acc i (value q hv hr) else acc
          go f valid ready index value next h acc' q'
        else acc
  go f s.valid (fun q h => s.ready ⟨q,h⟩) (fun q h => s.index ⟨q,h⟩) (fun q v r => s.value ⟨⟨q,v⟩,r⟩) s.next
    (fun q hv => s.progress rfl.le) acc q
termination_by _ => s.wf.wrap q
decreasing_by exact h q hv


variable [PartialOrder ι]

@[simp]
theorem Stream.eval_invalid [AddZeroClass α]
  (s : Stream ι α) [IsBounded s] (q : s.σ)
  (h : ¬s.valid q) : s.eval q = 0 := by rwa [Stream.eval, dif_neg]

@[simp]
theorem Stream.eval_valid [AddZeroClass α]
    (s : Stream ι α) [IsBounded s] (q : {q // s.valid q}) :
  s.eval q = s.eval₀ q + s.eval (s.advance q) := by rw [Stream.eval, dif_pos]


theorem Stream.eval₀_support [Zero α]
    (s : Stream ι α) [IsBounded s]
    (x : {q // s.valid q}) :
    (s.eval₀ x).support ⊆ {s.index x} := by
  rw [Stream.eval₀]
  split_ifs
  · exact Finsupp.support_single_subset
  · simp

/-- If the evaluation is nonzero at i, then `i` is the current index and `ready` is true -/
theorem Stream.eval₀_support' [Zero α]
    (s : Stream ι α) [IsBounded s]
    (x : {q // s.valid q}) {i : ι}
    (h₂ : s.eval₀ x i ≠ 0) : s.toOrder x = (i, true) := by
  obtain rfl := Finset.eq_of_mem_singleton (s.eval₀_support x (Finsupp.mem_support_iff.mpr h₂))
  rw [Stream.eval₀] at h₂
  split_ifs at h₂ with hr
  · simp [Stream.toOrder, hr]
  · simp at h₂


end StreamDefs

section Mono
open Streams

variable [LinearOrder ι]

/-- A stream is monotonic if the index does not decrease after `skip` is called. -/
def Stream.IsMonotonic (s : Stream ι α) : Prop :=
  ∀ (q : {q // s.valid q}) i, s.index' q ≤ s.index' (s.seek q i)

/-- A stream is strictly monotonic if it is monotonic and strictly advances its
  index when (non-trivially) skipped from a ready state. -/
def Stream.IsStrictMono (s : Stream ι α) : Prop :=
  s.IsMonotonic ∧ ∀ q i, s.toOrder q ≤ i → s.ready q → s.index' q ≠ s.index' (s.seek q i)

theorem Stream.isMonotonic_iff {s : Stream ι α} :
    s.IsMonotonic ↔ ∀ q i hq, s.index q ≤ s.index ⟨s.seek q i, hq⟩ := by
  constructor
  · intro h q i hq
    simpa [index'_val' _ hq] using h q i
  · intro h q i
    by_cases hq' : s.valid (s.seek q i)
    · simpa [index'_val' _ hq'] using h q i hq'
    · rw [Bool.not_eq_true] at hq'
      rw [Stream.index'_invalid hq']
      exact le_top

theorem Stream.IsMonotonic.index_le_index_advance {s : Stream ι α} (h : s.IsMonotonic) (q : s.σ) :
    s.index' q ≤ s.index' (s.advance q) := by
  by_cases H : s.valid q; swap;
  · simp [H]
  · simp only [Stream.advance, H, dif_pos]
    apply h

theorem Stream.IsMonotonic.index_le_of_mem_support [AddZeroClass α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsMonotonic) {q : s.σ} : ∀ i : ι, s.eval q i ≠ 0 → s.index' q ≤ i := by
  classical
  simp only [← Finsupp.mem_support_iff]
  apply s.wf.induction q; clear q
  intro q ih i hi
  by_cases H : s.valid q; swap
  · simp [H] at hi
  · rw [s.eval_valid ⟨_, H⟩] at hi
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with hi | hi
    · rw [Finset.mem_singleton.mp (s.eval₀_support ⟨_, H⟩ hi)]
      exact le_of_eq (Stream.index'_val' _ _)
    · exact (hs.index_le_index_advance q).trans (ih (s.advance q) (s.next_wf ⟨q, H⟩) i hi)

theorem Stream.IsMonotonic.eq_zero_of_lt_index [AddZeroClass α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsMonotonic) {q : s.σ} (i : ι) : ↑i < s.index' q → s.eval q i = 0 := by
  contrapose!
  exact hs.index_le_of_mem_support i

theorem Stream.IsStrictMono.lt {s : Stream ι α} (hs : s.IsStrictMono) (q i)
    (H : s.toOrder q ≤ i) (hr : s.ready q) : s.index' q < s.index' (s.seek q i) :=
  lt_of_le_of_ne (hs.1 _ _) (hs.2 _ _ H hr)

theorem Stream.IsStrictMono.advance_ne {s : Stream ι α} (hs : s.IsStrictMono) (q : {q // s.valid q})
    (hr : s.ready q) : s.index' q ≠ s.index' (s.advance q) := by
  rw [Stream.advance_val]
  exact hs.2 q _ rfl.le hr

theorem Stream.IsStrictMono.spec {s : Stream ι α} (hs : s.IsStrictMono) (q : {q // s.valid q})
    {i} (hi : s.toOrder q ≤ i) : s.toOrder' q ≤ (s.index' (s.seek q i), false) :=
  Prod.Lex.le_iff''.mpr
    ⟨by simpa using hs.1 q i, by
      simp
      contrapose
      simpa using hs.2 q i hi⟩

theorem Stream.IsStrictMono.index_le_of_mem_support [AddZeroClass α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsStrictMono) (q : {q // s.valid q}) {i} (hi : s.toOrder q ≤ i) :
    ∀ j : ι, s.eval (s.seek q i) j ≠ 0 → s.toOrder q ≤ (j, false) := fun j hj =>
  coeLex_le_iff.mp
    (by
      rw [← Stream.coeLex_toOrder]
      refine (hs.spec q hi).trans ?_
      simpa using hs.1.index_le_of_mem_support j hj)

theorem Stream.IsStrictMono.eq_zero_of_lt_index [AddZeroClass α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsStrictMono) (q : {q // s.valid q}) {i} (hi : s.toOrder q ≤ i) (j : ι) :
    ((j, false) <ₗ s.toOrder q) → s.eval (s.seek q i) j = 0 := by
  contrapose
  simpa using hs.index_le_of_mem_support q hi j

theorem fst_lt_of_lt_of_lt {α : Type _} [Preorder α] :
    ∀ {x y z : α ×ₗ Bool}, x < y → y < z → x.1 < z.1
  | x, y, ⟨z, false⟩, h₁, h₂ => Prod.Lex.fst_lt_of_lt_of_le (h₁.trans h₂) (by simp)
  | x, ⟨y, true⟩, ⟨z, true⟩, h₁, h₂ =>
    lt_of_le_of_lt (show x.1 ≤ y from Prod.Lex.fst_le_of_le h₁.le) (by simpa using h₂)
  | x, ⟨y, false⟩, ⟨z, true⟩, h₁, h₂ =>
    lt_of_lt_of_le (show x.1 < y from Prod.Lex.fst_lt_of_lt_of_le h₁ (by simp))
      (Prod.Lex.fst_le_of_le h₂.le)

theorem Stream.IsStrictMono.eval_skip_eq_zero [AddZeroClass α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsStrictMono) (q : {q // s.valid q}) {i : StreamOrder ι} {j : ι}
    (h₁ : (j, false) <ₗ i) (h₂ : i ≤ₗ s.toOrder q) : s.eval (s.seek q i) j = 0 := by
  rcases eq_or_lt_of_le h₂ with h₂ | h₂
  · refine hs.eq_zero_of_lt_index _ h₂.symm.le _ ?_
    rwa [← h₂]
  · apply hs.1.eq_zero_of_lt_index
    refine lt_of_lt_of_le ?_ (hs.1 _ _)
    simpa using fst_lt_of_lt_of_lt h₁ h₂

theorem Stream.IsStrictMono.eval₀_eq_eval_filter [AddCommMonoid α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsStrictMono) (q : {q // s.valid q}) :
    s.eval₀ q = (s.eval q).filter fun i => (i, false) <ₗ s.toOrder q := by
  rw [s.eval_valid, Finsupp.filter_add]
  convert (add_zero (M := ι →₀ α) _).symm
  · rw [Finsupp.filter_eq_self_iff]
    intro i hi
    rw [s.eval₀_support' q hi]
    simp
  · rw [Finsupp.filter_eq_zero_iff]
    intro i hi
    rw [Stream.advance_val]
    exact hs.eq_zero_of_lt_index q rfl.le i hi

section Lawful

/-- A stream is lawful if it is monotonic and satisfies the following property about `skip`:
    Whenever we ask the stream to skip past `i : stream_order ι`, we do not affect the evaluation
    of the stream at any `j ≥ i`, where `j : ι` is interpreted in `stream_order ι` as `(j, ff)`.
    In other words, when we ask to skip past `i`, we do not skip past any `j ≥ i`.

    This also demonstrates the interpretation of the strictness indicator: when `i = (i, ff)`, `skip q _ i` means
    "skip up to (but not past) any ready states with index `i`" (since `(j, ff) ≥ (i, ff) ↔ j ≥ i`). On the other hand, when `i = (i, tt)`,
    this means "skip up to and including states with index `i`, but not anything strictly past `i`".
 -/

class IsLawful {ι : Type} {α : Type _} [LinearOrder ι] [AddZeroClass α] (s : Stream ι α) extends
  IsBounded s where
  mono : s.IsMonotonic
  skip_spec : ∀ q i j, (i ≤ₗ (j, false)) → s.eval (s.seek q i) j = s.eval q j


/-- A stream is strictly lawful if in addition to being lawful, it is strictly monotonic -/
class IsStrictLawful {ι : Type} {α : Type _} [LinearOrder ι] [AddZeroClass α]
  (s : Stream ι α) extends IsLawful s where
  strictMono : s.IsStrictMono
  mono := strictMono.1


variable [AddZeroClass α]

theorem Stream.mono (s : Stream ι α) [IsLawful s] : s.IsMonotonic :=
  ‹IsLawful s›.mono

theorem Stream.strictMono (s : Stream ι α) [IsStrictLawful s] : s.IsStrictMono :=
  ‹IsStrictLawful s›.strictMono

theorem Stream.skip_spec (s : Stream ι α) [IsLawful s] (q : {q // s.valid q})
    (i : StreamOrder ι) :
    ((s.eval (s.seek q i)).filter fun j => i ≤ₗ (j, false)) =
      (s.eval q).filter fun j => i ≤ₗ (j, false) := by
  rw [Finsupp.filter_ext_iff]
  exact IsLawful.skip_spec q i

theorem Stream.skip_lt_toOrder {s : Stream ι α} [IsLawful s] {q : {q // s.valid q}}
    {i : StreamOrder ι} (hi : i < s.toOrder q) : s.eval (s.seek q i) = s.eval q := by
  ext j
  by_cases H : s.toOrder q ≤ (j, true)
  · rw [IsLawful.skip_spec q]
    simpa [Prod.Lex.lt_iff'', Prod.Lex.le_iff''] using lt_of_lt_of_le hi H
  have : ↑j < s.index' q := by
    simpa using fst_lt_of_lt_of_lt (show (j, false) <ₗ (j, true) by simp) (not_le.mp H)
  rw [s.mono.eq_zero_of_lt_index j this,
    s.mono.eq_zero_of_lt_index _ (this.trans_le (s.mono q i))]

theorem Stream.eval_skip_eq_of_false (s : Stream ι α) [IsLawful s] (q : {q // s.valid q}) :
    s.eval (s.seek q (s.index q, false)) = s.eval q := by
  by_cases hr : s.ready q
  · apply Stream.skip_lt_toOrder
    simp [Stream.toOrder, hr]
  . simp [s.eval_valid, Stream.eval₀, hr, Stream.advance_val, Stream.toOrder]


end Lawful

end Mono

end Etch.Verification
