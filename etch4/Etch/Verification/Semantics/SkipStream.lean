import Mathlib.Tactic.Linarith

import Etch.Verification.FinsuppLemmas
import Etch.Verification.Misc

/-!
# Indexed streams

This file defines indexed streams. We introduce `Stream`, the type of
indexed streams with internal state.

## Definitions
  - `Stream ι α`: The type of indexed streams on indexing set `ι` and
    value type `α`. Note that we model higher-order tensors using nested
    streams (e.g. `Stream ι₁ (Stream ι₂ α)`)
  - `is_bounded`: Typeclass asserting that stream evaluation terminates and is well-defined
  - `Stream.eval`: Evaluation of a stream
  - `Stream.is_monotonic`: Predicate that asserts that a stream `s` is monotone 
    (i.e. produces indices in order)
  - `is_lawful`: A lawful stream is one that is monotone and satisfies a certain predicate
    on skip.
  - `is_strict_lawful`: A strictly lawful stream is lawful and strictly monotonic, which
    means that when the stream is ready, it necessarily advances the index.

## References
See *Indexed Streams: A Formal Intermediate Representation for the Fused
Execution of Contraction Operations*
-/

set_option linter.uppercaseLean3 false

open Classical

noncomputable section
namespace Etch.Verification
universe u

/-- An *indexed stream* has the following fields:
  - `σ`: The internal state for the stream
  - `valid`: A predicate which checks if the stream has terminated
  - `ready`: Predicate indicating if the stream will emit a value
  - `skip`: Given a non-terminated `x : σ` and `(i, b)` for `i : ι` and `b : bool`,
      `skip x _ (i, b)` should attempt to advance the stream as far as possible up
      to index `i`, with `b` being a "strictness indicator," indicating whether we want to
      go to `i` or strictly past `i`.
  - `index`: The index of a non-terminated state `x : σ`
  - `value`: The value emitted at a ready state `x : σ`

Note that this contains the data of an indexed stream; when the streams are monotone
and `skip` does what it is supposed to do, we consider it a `lawful_stream`.
-/
structure Stream (ι : Type) (α : Type u) : Type max 1 u where
  σ : Type
  valid : σ → Prop
  ready : σ → Prop
  skip : ∀ x, valid x → ι ×ₗ Bool → σ
  index : ∀ x : σ, valid x → ι
  value : ∀ x : σ, ready x → α
#align Stream Etch.Verification.Stream

@[ext]
theorem Stream.ext {ι α} {s₁ s₂ : Stream ι α} (h₀ : s₁.σ = s₂.σ)
    (h₁ : ∀ x y, HEq x y → (s₁.valid x ↔ s₂.valid y))
    (h₂ : ∀ x y, HEq x y → (s₁.ready x ↔ s₂.ready y))
    (h₃ : ∀ x y H₁ H₂ i, HEq x y → HEq (s₁.skip x H₁ i) (s₂.skip y H₂ i))
    (h₄ : ∀ x y H₁ H₂, HEq x y → HEq (s₁.index x H₁) (s₂.index y H₂))
    (h₅ : ∀ x y H₁ H₂, HEq x y → HEq (s₁.value x H₁) (s₂.value y H₂)) : s₁ = s₂ := by
  rcases s₁ with ⟨σ₁, v₁, r₁, n₁, i₁, l₁⟩
  rcases s₂ with ⟨σ₂, v₂, r₂, n₂, i₂, l₂⟩
  dsimp only at *
  subst h₀; simp only [heq_iff_eq] at *
  obtain rfl : v₁ = v₂ := funext fun x => propext <| h₁ x x rfl
  obtain rfl : r₁ = r₂ := funext fun x => propext <| h₂ x x rfl
  congr
  · ext; apply h₃ _ _ _ _ _ rfl
  · ext; apply h₄ _ _ _ _ rfl
  · ext; apply h₅ _ _ _ _ rfl
#align Stream.ext Etch.Verification.Stream.ext

section StreamDefs

/- In this section we give many simple, auxiliary definitions related to streams. 
  Many of these simply give default values to partial functions e.g. `index'` gives the default value `⊤` when
  the stream has terminated (is invalid). -/
variable {ι : Type} {α : Type _}

/-- The current emmited value; if ready, this is `index ↦ value`, otherwise it is 0.
  This is denoted `index(r) ↦ −→ ready(r) · ⟦value(r)⟧` in the paper. -/
def Stream.eval₀ [Zero α] (s : Stream ι α) (σ₀ : s.σ) (h₁ : s.valid σ₀) : ι →₀ α :=
  if h₂ : s.ready σ₀ then Finsupp.single (s.index _ h₁) (s.value _ h₂) else 0
#align Stream.eval₀ Etch.Verification.Stream.eval₀

/--
Abbreviation for `ι × bool` with the lexicographic ordering (an index with a strictness indicator) -/
@[reducible]
def StreamOrder (ι : Type) : Type :=
  ι ×ₗ Bool
#align stream_order Etch.Verification.StreamOrder

/-- The current `(index, ready)` value of the stream -/
@[simps]
def Stream.toOrder (s : Stream ι α) (q : s.σ) (h : s.valid q) : StreamOrder ι :=
  (s.index q h, s.ready q)
#align Stream.to_order Etch.Verification.Stream.toOrder

/-- The index with a default value of `⊤` if the state `x` is not valid -/
def Stream.index' (s : Stream ι α) (x : s.σ) : WithTop ι :=
  if h : s.valid x then s.index x h else ⊤
#align Stream.index' Etch.Verification.Stream.index'

/-- The current `(index', ready)` value of the stream -/
def Stream.toOrder' (s : Stream ι α) (q : s.σ) : WithTop ι ×ₗ Bool :=
  (s.index' q, s.valid q ∧ s.ready q)
#align Stream.to_order' Etch.Verification.Stream.toOrder'

/-- The value, with a default value of `0` if the stream is not ready -/
def Stream.value' [Zero α] (s : Stream ι α) (x : s.σ) : α :=
  if h : s.ready x then s.value _ h else 0
#align Stream.value' Etch.Verification.Stream.value'

/-- The next state, which is defined as the resulting state from skipping past the current index,
  or the same state if the stream has terminated -/
def Stream.next (s : Stream ι α) (q : s.σ) : s.σ :=
  if h : s.valid q then s.skip q h (s.toOrder q h) else q
#align Stream.next Etch.Verification.Stream.next

/-- Skips to `i` from `q`, or stays at the same state if the stream has terminated -/
def Stream.skip' (s : Stream ι α) (q : s.σ) (i : ι ×ₗ Bool) : s.σ :=
  if h : s.valid q then s.skip q h i else q
#align Stream.skip' Etch.Verification.Stream.skip'

/--
Order injection from `stream_order ι` to `(with_top ι) ×ₗ bool` by coercing the first argument -/
abbrev coeLex (x : StreamOrder ι) : WithTop ι ×ₗ Bool :=
  (↑x.1, x.2)
#align coe_lex Etch.Verification.coeLex

@[simp]
theorem coeLex_le_iff [Preorder ι] {x y : StreamOrder ι} : coeLex x ≤ coeLex y ↔ x ≤ y := by
  simp [Prod.Lex.le_iff']
#align coe_lex_le_iff Etch.Verification.coeLex_le_iff

@[simp]
theorem coeLex_lt_iff [Preorder ι] {x y : StreamOrder ι} : coeLex x < coeLex y ↔ x < y := by
  simp [Prod.Lex.lt_iff']
#align coe_lex_lt_iff Etch.Verification.coeLex_lt_iff

theorem coeLex_injective : Function.Injective (@coeLex ι)
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => by
    rw [Prod.mk.injEq .., Prod.mk.injEq ..]
    simp
#align coe_lex_injective Etch.Verification.coeLex_injective

@[simp]
theorem coeLex_inj (x y : StreamOrder ι) : coeLex x = coeLex y ↔ x = y :=
  coeLex_injective.eq_iff
#align coe_lex_inj Etch.Verification.coeLex_inj

@[simp]
theorem Stream.index'_val {s : Stream ι α} {x : s.σ} (h : s.valid x) : s.index' x = s.index x h :=
  dif_pos h
#align Stream.index'_val Etch.Verification.Stream.index'_val

@[simp]
theorem Stream.index'_invalid {s : Stream ι α} {x : s.σ} (h : ¬s.valid x) : s.index' x = ⊤ :=
  dif_neg h
#align Stream.index'_invalid Etch.Verification.Stream.index'_invalid

@[simp]
theorem Stream.value'_val [Zero α] {s : Stream ι α} {x : s.σ} (h : s.ready x) :
    s.value' x = s.value x h :=
  dif_pos h
#align Stream.value'_val Etch.Verification.Stream.value'_val

@[simp]
theorem Stream.next_val {s : Stream ι α} {x : s.σ} (h : s.valid x) :
    s.next x = s.skip x h (s.toOrder x h) :=
  dif_pos h
#align Stream.next_val Etch.Verification.Stream.next_val

@[simp]
theorem Stream.next_invalid {s : Stream ι α} {x : s.σ} (h : ¬s.valid x) : s.next x = x :=
  dif_neg h
#align Stream.next_invalid Etch.Verification.Stream.next_invalid

@[simp]
theorem Stream.toOrder'_fst (s : Stream ι α) (q : s.σ) : (s.toOrder' q).1 = s.index' q :=
  rfl
#align Stream.to_order'_fst Etch.Verification.Stream.toOrder'_fst

@[simp]
theorem Stream.skip'_val {s : Stream ι α} {q : s.σ} (hq : s.valid q) (i : ι ×ₗ Bool) :
    s.skip' q i = s.skip q hq i :=
  dif_pos hq
#align Stream.skip'_val Etch.Verification.Stream.skip'_val

@[simp]
theorem Stream.skip'_invalid {s : Stream ι α} {q : s.σ} (hq : ¬s.valid q) (i : ι ×ₗ Bool) :
    s.skip' q i = q :=
  dif_neg hq
#align Stream.skip'_invalid Etch.Verification.Stream.skip'_invalid

theorem Stream.toOrder'_val {s : Stream ι α} {q : s.σ} (hq : s.valid q) :
    s.toOrder' q = (s.index' q, decide (s.ready q)) := by simp [Stream.toOrder', hq]
#align Stream.to_order'_val Etch.Verification.Stream.toOrder'_val

@[simp]
theorem Stream.coeLex_toOrder {s : Stream ι α} {q : s.σ} (hq : s.valid q) :
    coeLex (s.toOrder q hq) = s.toOrder' q := by
  simp [coeLex, Stream.toOrder'_val, hq]
#align Stream.coe_lex_to_order Etch.Verification.Stream.coeLex_toOrder

@[simp]
theorem Stream.toOrder'_val_snd {s : Stream ι α} {q : s.σ} (hq : s.valid q) :
    (s.toOrder' q).2 = s.ready q := by simp only [Stream.toOrder'_val hq]
#align Stream.to_order'_val_snd Etch.Verification.Stream.toOrder'_val_snd

@[simp]
theorem Stream.index'_lt_top_iff [Preorder ι] {s : Stream ι α} {q : s.σ} :
    s.index' q < ⊤ ↔ s.valid q := by
  rw [Stream.index']
  split_ifs <;> simpa [WithTop.coe_lt_top]
#align Stream.index'_lt_top_iff Etch.Verification.Stream.index'_lt_top_iff

@[simp]
theorem Stream.get_index' [PartialOrder ι] {s : Stream ι α} {x : s.σ} (h : (s.index' x).isSome) :
    (s.index' x).get h = s.index x (by simpa using h) := by
  generalize_proofs hq
  simp_rw [Stream.index', hq, Option.get]
#align Stream.get_index' Etch.Verification.Stream.get_index'

-- We use this notation so that we can explicitly ask Lean to use lexicographic comparison (rather than pointwise comparison)
scoped[Streams] notation:50 a " <ₗ " b => @LT.lt (Etch.Verification.StreamOrder _) _ a b
scoped[Streams] notation:50 a " ≤ₗ " b => @LE.le (Etch.Verification.StreamOrder _) _ a b

open Streams

/-- The stream is bounded if there is a well-founded relation `≺` on states such that
    a) whenever we are asked to skip past an index `i` past the current index (i.e. `i ≥ s.to_order q`),
        we strictly make progress (`s.skip q hq i ≺ q`)
    b) We always either make progress or remain at the same state
  These properties ensure that evaluation terminates. -/
@[mk_iff]
class IsBounded {ι : Type} {α : Type _} [LinearOrder ι] (s : Stream ι α) : Prop where
  out :
    ∃ wf_rel : s.σ → s.σ → Prop,
      WellFounded wf_rel ∧
        ∀ q hq i, wf_rel (s.skip q hq i) q ∨ (i <ₗ s.toOrder q hq) ∧ s.skip q hq i = q
#align is_bounded Etch.Verification.IsBounded

variable [LinearOrder ι]

/-- Extract the well-founded relation on a bounded stream -/
def Stream.WfRel (s : Stream ι α) [IsBounded s] : s.σ → s.σ → Prop :=
  ‹IsBounded s›.out.choose
#align Stream.wf_rel Etch.Verification.Stream.WfRel

-- mathport name: «expr ≺ »
scoped[Streams] notation:50 a " ≺ " b => Etch.Verification.Stream.WfRel _ a b

theorem Stream.wf (s : Stream ι α) [IsBounded s] : WellFounded s.WfRel :=
  ‹IsBounded s›.out.choose_spec.1
#align Stream.wf Etch.Verification.Stream.wf

/-- Extract the well-founded relation on a bounded stream -/
def Stream.wfRel (s : Stream ι α) [IsBounded s] : WellFoundedRelation s.σ :=
  ⟨s.WfRel, s.wf⟩

theorem Stream.wf_valid (s : Stream ι α) [IsBounded s] :
    ∀ q hq i, (s.skip q hq i ≺ q) ∨ (i <ₗ s.toOrder q hq) ∧ s.skip q hq i = q :=
  ‹IsBounded s›.out.choose_spec.2
#align Stream.wf_valid Etch.Verification.Stream.wf_valid

theorem wf_valid_iff {s : Stream ι α} (wf_rel : s.σ → s.σ → Prop) (q hq i) :
    wf_rel (s.skip q hq i) q ∨ i < s.toOrder q hq ∧ s.skip q hq i = q ↔
      wf_rel (s.skip' q i) q ∨ coeLex i < s.toOrder' q ∧ s.skip' q i = q :=
  by simp only [Stream.skip'_val hq, ← Stream.coeLex_toOrder hq, coeLex_lt_iff]
#align wf_valid_iff Etch.Verification.wf_valid_iff

theorem IsBounded.mk' {s : Stream ι α}
    (h :
      ∃ wf_rel : s.σ → s.σ → Prop,
        WellFounded wf_rel ∧
          ∀ q i, wf_rel (s.skip' q i) q ∨ coeLex i < s.toOrder' q ∧ s.skip' q i = q) :
    IsBounded s :=
  ⟨by
    simp only [wf_valid_iff]
    rcases h with ⟨r, wfr, hr⟩
    exact ⟨r, wfr, fun q _ i => hr q i⟩⟩
#align is_bounded.mk' Etch.Verification.IsBounded.mk'

theorem Stream.wf_valid' (s : Stream ι α) [IsBounded s] (q i) :
    (s.skip' q i ≺ q) ∨ coeLex i < s.toOrder' q ∧ s.skip' q i = q :=
  if hq : s.valid q then by
    rw [← wf_valid_iff]
    exact s.wf_valid q hq i
  else by
    right
    constructor
    · rw [Prod.Lex.lt_iff']
      left
      simpa [hq] using WithTop.coe_lt_top _
    · simp [hq]
#align Stream.wf_valid' Etch.Verification.Stream.wf_valid'

theorem Stream.progress (s : Stream ι α) [IsBounded s] {q hq i} (h : s.toOrder q hq ≤ i) :
    s.skip q hq i ≺ q :=
  (s.wf_valid q hq i).resolve_right fun H => absurd H.1 h.not_lt
#align Stream.progress Etch.Verification.Stream.progress

theorem Stream.next_wf (s : Stream ι α) [IsBounded s] (q) (hq : s.valid q) : s.next q ≺ q := by
  rw [Stream.next_val hq]
  refine s.progress (le_of_eq ?_)
  simp [Stream.toOrder, hq]
#align Stream.next_wf Etch.Verification.Stream.next_wf

theorem Stream.no_backward (s : Stream ι α) [IsBounded s] (q hq i) :
    (s.skip q hq i ≺ q) ∨ s.skip q hq i = q :=
  (s.wf_valid q hq i).imp_right And.right
#align Stream.no_backward Etch.Verification.Stream.no_backward

/-- Evaluates `∑_{q →* r} eval₀ r`, which is well-defined for bounded streams. -/
noncomputable def Stream.eval [AddZeroClass α] (s : Stream ι α) [IsBounded s] : s.σ → ι →₀ α
  | q =>
    if h : s.valid q then
      have : s.WfRel (s.next q) q := s.next_wf _ h
      s.eval₀ q h + s.eval (s.next q)
    else 0
termination_by' ⟨_, s.wf⟩
#align Stream.eval Etch.Verification.Stream.eval

@[simp]
theorem Stream.eval_invalid [AddZeroClass α] (s : Stream ι α) [IsBounded s] (q : s.σ)
    (h : ¬s.valid q) : s.eval q = 0 := by rwa [Stream.eval, dif_neg]
#align Stream.eval_invalid Etch.Verification.Stream.eval_invalid

@[simp]
theorem Stream.eval_valid [AddZeroClass α] (s : Stream ι α) [IsBounded s] (q : s.σ)
    (h : s.valid q) : s.eval q = s.eval₀ q h + s.eval (s.next q) := by rw [Stream.eval, dif_pos]
#align Stream.eval_valid Etch.Verification.Stream.eval_valid

theorem Stream.eval₀_support [Zero α] (s : Stream ι α) (x : s.σ) (h : s.valid x) :
    (s.eval₀ x h).support ⊆ {s.index x h} := by
  rw [Stream.eval₀]
  split_ifs
  · exact Finsupp.support_single_subset
  · simp
#align Stream.eval₀_support Etch.Verification.Stream.eval₀_support

theorem Stream.eval₀_support' [Zero α] (s : Stream ι α) {x : s.σ} (h₁ : s.valid x) {i : ι}
    (h₂ : s.eval₀ x h₁ i ≠ 0) : s.toOrder x h₁ = (i, true) := by
  obtain rfl := Finset.eq_of_mem_singleton (s.eval₀_support x h₁ (Finsupp.mem_support_iff.mpr h₂))
  rw [Stream.eval₀] at h₂
  split_ifs at h₂ with hr
  · simp [Stream.toOrder, Stream.index'_val h₁, hr]
  · simp at h₂
#align Stream.eval₀_support' Etch.Verification.Stream.eval₀_support'

section Mono

/-- A stream is monotonic if the index does not decrease after `skip` is called. -/
def Stream.IsMonotonic (s : Stream ι α) : Prop :=
  ∀ q hq i, s.index' q ≤ s.index' (s.skip q hq i)
#align Stream.is_monotonic Etch.Verification.Stream.IsMonotonic

/-- A stream is strictly monotonic if it is monotonic and strictly advances its
  index when (non-trivially) skipped from a ready state. -/
def Stream.IsStrictMono (s : Stream ι α) : Prop :=
  s.IsMonotonic ∧ ∀ q hq i, s.toOrder q hq ≤ i → s.ready q → s.index' q ≠ s.index' (s.skip q hq i)
#align Stream.is_strict_mono Etch.Verification.Stream.IsStrictMono

theorem Stream.IsMonotonic.skip' {s : Stream ι α} (hs : s.IsMonotonic) (q i) :
    s.index' q ≤ s.index' (s.skip' q i) := by
  by_cases hq : s.valid q
  · rw [Stream.skip'_val hq]
    apply hs
  · rw [Stream.skip'_invalid hq]
#align Stream.is_monotonic.skip' Etch.Verification.Stream.IsMonotonic.skip'

theorem Stream.isMonotonic_iff {s : Stream ι α} :
    s.IsMonotonic ↔ ∀ q hq i hq', s.index q hq ≤ s.index (s.skip q hq i) hq' := by
  constructor
  · intro h q hq i hq'
    specialize h q hq i
    simpa [hq, hq'] using h
  · intro h q hq i
    by_cases hq' : s.valid (s.skip q hq i)
    · simpa [hq, hq'] using h ..
    · rw [Stream.index'_invalid hq']
      exact le_top
#align Stream.is_monotonic_iff Etch.Verification.Stream.isMonotonic_iff

theorem Stream.IsMonotonic.index_le_index_next {s : Stream ι α} (h : s.IsMonotonic) (q : s.σ) :
    s.index' q ≤ s.index' (s.next q) := by
  by_cases H : s.valid q; swap; · simp [H]
  simp only [Stream.next, H, dif_pos]
  apply h
#align Stream.is_monotonic.index_le_index_next Etch.Verification.Stream.IsMonotonic.index_le_index_next

theorem Stream.IsMonotonic.index_le_of_mem_support [AddZeroClass α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsMonotonic) {q : s.σ} : ∀ i : ι, s.eval q i ≠ 0 → s.index' q ≤ i := by
  simp only [← Finsupp.mem_support_iff]
  apply s.wf.induction q
  intro q ih i hi
  by_cases H : s.valid q; swap
  · exfalso
    simp [H] at hi
  · rw [s.eval_valid _ H] at hi
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with hi | hi
    · rw [Finset.mem_singleton.mp (s.eval₀_support _ H hi)]
      exact le_of_eq (Stream.index'_val _)
    · exact _root_.trans (hs.index_le_index_next q) (ih (s.next q) (s.next_wf _ H) i hi)
#align Stream.is_monotonic.index_le_of_mem_support Etch.Verification.Stream.IsMonotonic.index_le_of_mem_support

theorem Stream.IsMonotonic.eq_zero_of_lt_index [AddZeroClass α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsMonotonic) {q : s.σ} (i : ι) : ↑i < s.index' q → s.eval q i = 0 := by
  contrapose!
  exact hs.index_le_of_mem_support i
#align Stream.is_monotonic.eq_zero_of_lt_index Etch.Verification.Stream.IsMonotonic.eq_zero_of_lt_index

theorem Stream.IsStrictMono.lt {s : Stream ι α} (hs : s.IsStrictMono) (q hq i)
    (H : s.toOrder q hq ≤ i) (hr : s.ready q) : s.index' q < s.index' (s.skip q hq i) :=
  lt_of_le_of_ne (hs.1 _ _ _) (hs.2 _ _ _ H hr)
#align Stream.is_strict_mono.lt Etch.Verification.Stream.IsStrictMono.lt

theorem Stream.IsStrictMono.next_ne {s : Stream ι α} (hs : s.IsStrictMono) {q : s.σ}
    (hq : s.valid q) (hr : s.ready q) : s.index' q ≠ s.index' (s.next q) := by
  rw [Stream.next_val hq]
  exact hs.2 q hq _ rfl.le hr
#align Stream.is_strict_mono.next_ne Etch.Verification.Stream.IsStrictMono.next_ne

theorem Stream.IsStrictMono.spec {s : Stream ι α} (hs : s.IsStrictMono) (q : s.σ) (hv : s.valid q)
    {i} (hi : s.toOrder q hv ≤ i) : s.toOrder' q ≤ (s.index' (s.skip q hv i), false) :=
  Prod.Lex.le_iff''.mpr
    ⟨by simpa using hs.1 q hv i, by
      simp
      contrapose
      simpa [hv] using hs.2 q hv i hi⟩
#align Stream.is_strict_mono.spec Etch.Verification.Stream.IsStrictMono.spec

theorem Stream.IsStrictMono.index_le_of_mem_support [AddZeroClass α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsStrictMono) {q : s.σ} (hv) {i} (hi : s.toOrder q hv ≤ i) :
    ∀ j : ι, s.eval (s.skip q hv i) j ≠ 0 → s.toOrder q hv ≤ (j, false) := fun j hj =>
  coeLex_le_iff.mp
    (by
      rw [Stream.coeLex_toOrder]
      refine (hs.spec q hv hi).trans ?_
      simpa using hs.1.index_le_of_mem_support j hj)
#align Stream.is_strict_mono.index_le_of_mem_support Etch.Verification.Stream.IsStrictMono.index_le_of_mem_support

theorem Stream.IsStrictMono.eq_zero_of_lt_index [AddZeroClass α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsStrictMono) {q : s.σ} (hv) {i} (hi : s.toOrder q hv ≤ i) (j : ι) :
    ((j, false) <ₗ s.toOrder q hv) → s.eval (s.skip q hv i) j = 0 := by
  contrapose
  simpa using hs.index_le_of_mem_support hv hi j
#align Stream.is_strict_mono.eq_zero_of_lt_index Etch.Verification.Stream.IsStrictMono.eq_zero_of_lt_index

theorem fst_lt_of_lt_of_lt {α : Type _} [Preorder α] :
    ∀ {x y z : α ×ₗ Bool}, x < y → y < z → x.1 < z.1
  | x, y, ⟨z, false⟩, h₁, h₂ => Prod.Lex.fst_lt_of_lt_of_le (h₁.trans h₂) (by simp)
  | x, ⟨y, true⟩, ⟨z, true⟩, h₁, h₂ =>
    lt_of_le_of_lt (show x.1 ≤ y from Prod.Lex.fst_le_of_le h₁.le) (by simpa using h₂)
  | x, ⟨y, false⟩, ⟨z, true⟩, h₁, h₂ =>
    lt_of_lt_of_le (show x.1 < y from Prod.Lex.fst_lt_of_lt_of_le h₁ (by simp))
      (Prod.Lex.fst_le_of_le h₂.le)
#align fst_lt_of_lt_of_lt Etch.Verification.fst_lt_of_lt_of_lt

theorem Stream.IsStrictMono.eval_skip_eq_zero [AddZeroClass α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsStrictMono) {q : s.σ} (hv : s.valid q) {i : StreamOrder ι} {j : ι}
    (h₁ : (j, false) <ₗ i) (h₂ : i ≤ₗ s.toOrder q hv) : s.eval (s.skip q hv i) j = 0 := by
  rcases eq_or_lt_of_le h₂ with h₂ | h₂
  · refine hs.eq_zero_of_lt_index _ h₂.symm.le _ ?_
    rwa [← h₂]
  · apply hs.1.eq_zero_of_lt_index
    refine lt_of_lt_of_le ?_ (hs.1 _ _ _)
    rw [Stream.index'_val hv, WithTop.coe_lt_coe]
    exact fst_lt_of_lt_of_lt h₁ h₂
#align Stream.is_strict_mono.eval_skip_eq_zero Etch.Verification.Stream.IsStrictMono.eval_skip_eq_zero

theorem Stream.IsStrictMono.eval₀_eq_eval_filter [AddCommMonoid α] {s : Stream ι α} [IsBounded s]
    (hs : s.IsStrictMono) (q : s.σ) (hv : s.valid q) :
    s.eval₀ q hv = (s.eval q).filter fun i => (i, false) <ₗ s.toOrder q hv := by
  rw [s.eval_valid _ hv, Finsupp.filter_add]
  convert (add_zero (M := ι →₀ α) _).symm
  · rw [Finsupp.filter_eq_self_iff]
    intro i hi
    rw [s.eval₀_support' hv hi]
    simp
  · rw [Finsupp.filter_eq_zero_iff]
    intro i hi
    rw [Stream.next_val hv]
    exact hs.eq_zero_of_lt_index hv rfl.le i hi
#align Stream.is_strict_mono.eval₀_eq_eval_filter Etch.Verification.Stream.IsStrictMono.eval₀_eq_eval_filter

end Mono

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
  skip_spec : ∀ q hq i j, (i ≤ₗ (j, false)) → s.eval (s.skip q hq i) j = s.eval q j
#align is_lawful Etch.Verification.IsLawful

/-- A stream is strictly lawful if in addition to being lawful, it is strictly monotonic -/
class IsStrictLawful {ι : Type} {α : Type _} [LinearOrder ι] [AddZeroClass α]
  (s : Stream ι α) extends IsLawful s where
  StrictMono : s.IsStrictMono
#align is_strict_lawful Etch.Verification.IsStrictLawful

variable [AddZeroClass α]

theorem Stream.mono (s : Stream ι α) [IsLawful s] : s.IsMonotonic :=
  ‹IsLawful s›.mono
#align Stream.mono Etch.Verification.Stream.mono

theorem Stream.strictMono (s : Stream ι α) [IsStrictLawful s] : s.IsStrictMono :=
  ‹IsStrictLawful s›.StrictMono
#align Stream.strict_mono Etch.Verification.Stream.strictMono

theorem Stream.skip_spec (s : Stream ι α) [IsLawful s] (q : s.σ) (hq : s.valid q)
    (i : StreamOrder ι) :
    ((s.eval (s.skip q hq i)).filter fun j => i ≤ₗ (j, false)) =
      (s.eval q).filter fun j => i ≤ₗ (j, false) := by
  rw [Finsupp.filter_ext_iff]
  exact IsLawful.skip_spec q hq i
#align Stream.skip_spec Etch.Verification.Stream.skip_spec

theorem Stream.skip_lt_toOrder {s : Stream ι α} [IsLawful s] {q : s.σ} {hq : s.valid q}
    {i : StreamOrder ι} (hi : i < s.toOrder q hq) : s.eval (s.skip q hq i) = s.eval q := by
  ext j
  by_cases H : s.toOrder q hq ≤ (j, true)
  · rw [IsLawful.skip_spec q hq]
    simpa [Prod.Lex.lt_iff'', Prod.Lex.le_iff''] using lt_of_lt_of_le hi H
  have : ↑j < s.index' q := by
    simpa [hq] using fst_lt_of_lt_of_lt (show (j, false) <ₗ (j, true) by simp) (not_le.mp H)
  rw [s.mono.eq_zero_of_lt_index j this,
    s.mono.eq_zero_of_lt_index _ (this.trans_le (s.mono q hq i))]
#align Stream.skip_lt_to_order Etch.Verification.Stream.skip_lt_toOrder

theorem Stream.skip'_spec (s : Stream ι α) [IsLawful s] (q : s.σ) (i : StreamOrder ι) (j : ι)
    (h : i ≤ (j, false)) : s.eval (s.skip' q i) j = s.eval q j := by
  by_cases hq : s.valid q
  · rw [Stream.skip'_val hq, IsLawful.skip_spec _ hq _ _ h]
  rw [Stream.skip'_invalid hq]
#align Stream.skip'_spec Etch.Verification.Stream.skip'_spec

theorem Stream.skip'_lt_toOrder {s : Stream ι α} [IsLawful s] {q : s.σ} {i : StreamOrder ι}
    (hi : coeLex i < s.toOrder' q) : s.eval (s.skip' q i) = s.eval q := by
  by_cases hq : s.valid q; swap; · rw [Stream.skip'_invalid hq]
  rw [← Stream.coeLex_toOrder hq, coeLex_lt_iff] at hi
  rw [Stream.skip'_val hq, Stream.skip_lt_toOrder hi]
#align Stream.skip'_lt_to_order Etch.Verification.Stream.skip'_lt_toOrder

theorem Stream.eval_skip_eq_of_false (s : Stream ι α) [IsLawful s] (q : s.σ) (hq : s.valid q) :
    s.eval (s.skip q hq (s.index q hq, false)) = s.eval q := by
  by_cases hr : s.ready q
  · apply Stream.skip_lt_toOrder
    simp [Stream.toOrder, hr]
  simp [s.eval_valid q hq, Stream.eval₀, hr, Stream.next_val hq, Stream.toOrder]
#align Stream.eval_skip_eq_of_ff Etch.Verification.Stream.eval_skip_eq_of_false

end StreamDefs

section Functor

variable {ι : Type} {α β γ : Type _}

/-- Solve goal by definitional simplification, heq/eq, and `rfl` -/
macro (name := solveRefl) "solve_refl" : tactic =>
  `(tactic| focus
              try dsimp
              try (simp only [heq_iff_eq])
              try intros
              try subst_vars
              try rfl)

@[simps]
def Stream.map (f : α → β) (s : Stream ι α) : Stream ι β :=
  { s with value := fun q hq => f (s.value q hq) }
#align Stream.map Etch.Verification.Stream.map

@[simp]
theorem Stream.map_id (s : Stream ι α) : s.map id = s :=
  by ext <;> solve_refl
#align Stream.map_id Etch.Verification.Stream.map_id

theorem Stream.map_map (g : α → β) (f : β → γ) (s : Stream ι α) : (s.map g).map f = s.map (f ∘ g) :=
  by ext <;> solve_refl
#align Stream.map_map Etch.Verification.Stream.map_map

@[simp]
theorem Stream.toOrder_map (s : Stream ι α) (f : α → β) : (s.map f).toOrder = s.toOrder :=
  rfl
#align Stream.to_order_map Etch.Verification.Stream.toOrder_map

@[simp]
theorem Stream.toOrder'_map (s : Stream ι α) (f : α → β) : (s.map f).toOrder' = s.toOrder' :=
  rfl
#align Stream.to_order'_map Etch.Verification.Stream.toOrder'_map

theorem Stream.map_value' [Zero α] [Zero β] (f : α → β) (hf : f 0 = 0) (s : Stream ι α) (q : s.σ) :
    (s.map f).value' q = f (s.value' q) := by
  unfold Stream.value'
  split_ifs
  · rfl
  · contradiction
  · contradiction
  · rw [hf]
#align Stream.map_value' Etch.Verification.Stream.map_value'

variable [LinearOrder ι]

@[simp]
theorem map_IsBounded_iff (f : α → β) (s : Stream ι α) : IsBounded (s.map f) ↔ IsBounded s := by
  simp only [IsBounded_iff]
  rfl
#align map_is_bounded_iff Etch.Verification.map_IsBounded_iff

end Functor

end Etch.Verification
