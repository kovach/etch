import tactic.linarith
import finsupp_lemmas
import verification.misc

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

open_locale classical
noncomputable theory

universes u

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
structure Stream (ι : Type) (α : Type u) : Type (max 1 u) :=
(σ : Type)
(valid : σ → Prop)
(ready : σ → Prop)
(skip  : Π x, valid x → ι ×ₗ bool → σ)
(index : Π (x : σ), valid x → ι)
(value : Π (x : σ), ready x → α)

@[ext]
lemma Stream.ext {ι α} {s₁ s₂ : Stream ι α} (h₀ : s₁.σ = s₂.σ)
  (h₁ : ∀ x y, x == y → (s₁.valid x ↔ s₂.valid y)) (h₂ : ∀ x y, x == y → (s₁.ready x ↔ s₂.ready y)) (h₃ : ∀ x y H₁ H₂ i, x == y → s₁.skip x H₁ i == s₂.skip y H₂ i)
  (h₄ : ∀ x y H₁ H₂, x == y → s₁.index x H₁ == s₂.index y H₂) (h₅ : ∀ x y H₁ H₂, x == y → s₁.value x H₁ == s₂.value y H₂) :  s₁ = s₂ :=
begin
  cases s₁ with σ₁ v₁ r₁ n₁ i₁ l₁, cases s₂ with σ₂ v₂ r₂ n₂ i₂ l₂, dsimp only at *,
  subst h₀, simp only [heq_iff_eq] at *,
  obtain rfl : v₁ = v₂ := funext (λ x, propext $ h₁ x x rfl), obtain rfl : r₁ = r₂ := funext (λ x, propext $ h₂ x x rfl),
  refine ⟨rfl, rfl, rfl, _, _, _⟩; try { simp only [heq_iff_eq] at * }; ext, { apply h₃ x x _ _ _ rfl; assumption, }, { apply h₄ x x _ _ rfl; assumption, },
  { apply h₅ x x _ _ rfl; assumption, },
end


section stream_defs

/- In this section we give many simple, auxiliary definitions related to streams. 
  Many of these simply give default values to partial functions e.g. `index'` gives the default value `⊤` when
  the stream has terminated (is invalid). -/
variables {ι : Type} {α : Type*}

/-- The current emmited value; if ready, this is `index ↦ value`, otherwise it is 0.
  This is denoted `index(r) ↦ −→ ready(r) · ⟦value(r)⟧` in the paper. -/
def Stream.eval₀ [has_zero α] (s : Stream ι α) (σ₀ : s.σ) (h₁ : s.valid σ₀) : ι →₀ α :=
if h₂ : s.ready σ₀ then finsupp.single (s.index _ h₁) (s.value _ h₂) else 0

/-- Abbreviation for `ι × bool` with the lexicographic ordering (an index with a strictness indicator) -/
@[reducible]
def stream_order (ι : Type) : Type := ι ×ₗ bool

/-- The current `(index, ready)` value of the stream -/
@[simps]
def Stream.to_order (s : Stream ι α) (q : s.σ) (h : s.valid q) : stream_order ι :=
(s.index q h, s.ready q)

/-- The index with a default value of `⊤` if the state `x` is not valid -/
def Stream.index' (s : Stream ι α) (x : s.σ) : with_top ι :=
if h : s.valid x then s.index x h else ⊤ 

/-- The current `(index', ready)` value of the stream -/
def Stream.to_order' (s : Stream ι α) (q : s.σ) : (with_top ι) ×ₗ bool :=
(s.index' q, s.valid q ∧ s.ready q)

/-- The value, with a default value of `0` if the stream is not ready -/
def Stream.value' [has_zero α] (s : Stream ι α) (x : s.σ) : α :=
if h : s.ready x then s.value _ h else 0

/-- The next state, which is defined as the resulting state from skipping past the current index,
  or the same state if the stream has terminated -/
def Stream.next (s : Stream ι α) (q : s.σ) : s.σ :=
if h : s.valid q then s.skip q h (s.to_order q h) else q

/-- Skips to `i` from `q`, or stays at the same state if the stream has terminated -/
def Stream.skip' (s : Stream ι α) (q : s.σ) (i : ι ×ₗ bool) : s.σ :=
if h : s.valid q then s.skip q h i else q

/-- Order injection from `stream_order ι` to `(with_top ι) ×ₗ bool` by coercing the first argument -/
abbreviation coe_lex (x : stream_order ι) : (with_top ι) ×ₗ bool := (↑x.1, x.2)

@[simp] lemma coe_lex_le_iff [preorder ι] {x y : stream_order ι} :
  coe_lex x ≤ coe_lex y ↔ x ≤ y := by simp [prod.lex.le_iff']

@[simp] lemma coe_lex_lt_iff [preorder ι] {x y : stream_order ι} :
  coe_lex x < coe_lex y ↔ x < y := by simp [prod.lex.lt_iff']

lemma coe_lex_injective : function.injective (@coe_lex ι)
| ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by simpa using and.intro

@[simp] lemma coe_lex_inj (x y : stream_order ι) : coe_lex x = coe_lex y ↔ x = y :=
coe_lex_injective.eq_iff

@[simp] lemma Stream.index'_val {s : Stream ι α} {x : s.σ} (h : s.valid x) : s.index' x = s.index x h := dif_pos h

@[simp] lemma Stream.index'_invalid {s : Stream ι α} {x : s.σ} (h : ¬s.valid x) : s.index' x = ⊤ := dif_neg h

@[simp] lemma Stream.value'_val [has_zero α] {s : Stream ι α} {x : s.σ} (h : s.ready x) : s.value' x = s.value x h := dif_pos h

@[simp] lemma Stream.next_val {s : Stream ι α} {x : s.σ} (h : s.valid x) : s.next x = s.skip x h (s.to_order x h) := dif_pos h

@[simp] lemma Stream.next_invalid {s : Stream ι α} {x : s.σ} (h : ¬s.valid x) : s.next x = x := dif_neg h

@[simp] lemma Stream.to_order'_fst (s : Stream ι α) (q : s.σ) :
  (s.to_order' q).1 = s.index' q := rfl

@[simp] lemma Stream.skip'_val {s : Stream ι α} {q : s.σ} (hq : s.valid q) (i : ι ×ₗ bool) :
  s.skip' q i = s.skip q hq i := dif_pos hq

@[simp] lemma Stream.skip'_invalid {s : Stream ι α} {q : s.σ} (hq : ¬s.valid q) (i : ι ×ₗ bool) :
  s.skip' q i = q := dif_neg hq

lemma Stream.to_order'_val {s : Stream ι α} {q : s.σ} (hq : s.valid q) :
  s.to_order' q = (s.index' q, s.ready q) := by simp [Stream.to_order', hq]

@[simp] lemma Stream.coe_lex_to_order {s : Stream ι α} {q : s.σ} (hq : s.valid q) :
  coe_lex (s.to_order q hq) = s.to_order' q := by simp [Stream.to_order'_val, hq]

@[simp] lemma Stream.to_order'_val_snd {s : Stream ι α} {q : s.σ} (hq : s.valid q) :
  (s.to_order' q).2 = s.ready q := by simp only [Stream.to_order'_val hq]

@[simp] lemma Stream.index'_lt_top_iff [preorder ι] {s : Stream ι α} {q : s.σ} :
  s.index' q < ⊤ ↔ s.valid q :=
by { rw [Stream.index'], split_ifs; simpa [with_top.coe_lt_top], }

@[simp] lemma Stream.get_index' [partial_order ι] {s : Stream ι α} {x : s.σ} (h : (s.index' x).is_some) :
  option.get h = s.index x (by simpa using h) :=
by { generalize_proofs hq, simp [hq], }

-- We use this notation so that we can explicitly ask Lean to use lexicographic comparison (rather than pointwise comparison)
localized "notation a ` <ₗ `:50 b := @has_lt.lt (stream_order _) _ a b" in streams
localized "notation a ` ≤ₗ `:50 b := @has_le.le (stream_order _) _ a b" in streams

/-- The stream is bounded if there is a well-founded relation `≺` on states such that
    a) whenever we are asked to skip past an index `i` past the current index (i.e. `i ≥ s.to_order q`),
        we strictly make progress (`s.skip q hq i ≺ q`)
    b) We always either make progress or remain at the same state
  These properties ensure that evaluation terminates. -/
@[mk_iff] class is_bounded {ι : Type} {α : Type*} [linear_order ι] (s : Stream ι α) : Prop :=
(out : ∃ (wf_rel : s.σ → s.σ → Prop), well_founded wf_rel ∧ 
  (∀ (q hq i), (wf_rel (s.skip q hq i) q) ∨ 
    ((i <ₗ s.to_order q hq) ∧ (s.skip q hq i) = q)))

variable [linear_order ι]

/-- Extract the well-founded relation on a bounded stream -/
def Stream.wf_rel (s : Stream ι α) [is_bounded s] : s.σ → s.σ → Prop := ‹is_bounded s›.out.some    
localized "notation a ` ≺ `:50 b := Stream.wf_rel _ a b" in streams
lemma Stream.wf (s : Stream ι α) [is_bounded s] : well_founded s.wf_rel := ‹is_bounded s›.out.some_spec.1
lemma Stream.wf_valid (s : Stream ι α) [is_bounded s] :
  ∀ (q hq i), ((s.skip q hq i) ≺ q) ∨ ((i <ₗ s.to_order q hq) ∧ (s.skip q hq i) = q) := ‹is_bounded s›.out.some_spec.2

lemma wf_valid_iff {s : Stream ι α} (wf_rel : s.σ → s.σ → Prop) (q hq i) : 
  (wf_rel (s.skip q hq i) q) ∨ ((i < s.to_order q hq) ∧ (s.skip q hq i) = q) ↔
  (wf_rel (s.skip' q i) q) ∨ ((coe_lex i < s.to_order' q) ∧ s.skip' q i = q) :=
by simp only [Stream.skip'_val hq, ← Stream.coe_lex_to_order hq, coe_lex_lt_iff]

lemma is_bounded.mk' {s : Stream ι α} (h : ∃ (wf_rel : s.σ → s.σ → Prop), well_founded wf_rel ∧ 
  (∀ (q i), wf_rel (s.skip' q i) q ∨ ((coe_lex i < s.to_order' q) ∧ s.skip' q i = q))) : is_bounded s :=
⟨by { simp only [wf_valid_iff], rcases h with ⟨r, wfr, hr⟩, exact ⟨r, wfr, λ q _ i, hr q i⟩, }⟩

lemma Stream.wf_valid' (s : Stream ι α) [is_bounded s] (q i) :
  ((s.skip' q i) ≺ q) ∨ ((coe_lex i < s.to_order' q) ∧ s.skip' q i = q) :=
if hq : s.valid q then by { rw ← wf_valid_iff, exact s.wf_valid q hq i, }
else by { right, split, { rw prod.lex.lt_iff', left, simpa [hq] using with_top.coe_lt_top _, }, simp [hq], }

lemma Stream.progress (s : Stream ι α) [is_bounded s] {q hq i} (h : s.to_order q hq ≤ i) :
  (s.skip q hq i) ≺ q :=
(s.wf_valid q hq i).resolve_right (λ H, absurd H.1 h.not_lt)

lemma Stream.next_wf (s : Stream ι α) [is_bounded s] (q) (hq : s.valid q) : (s.next q) ≺ q :=
by { rw [Stream.next_val hq], refine s.progress (le_of_eq _), simp [Stream.to_order, hq], }

lemma Stream.no_backward (s : Stream ι α) [is_bounded s] (q hq i) : 
  ((s.skip q hq i) ≺ q) ∨ ((s.skip q hq i) = q) :=
(s.wf_valid q hq i).imp_right and.right

/-- Evaluates `∑_{q →* r} eval₀ r`, which is well-defined for bounded streams. -/
noncomputable def Stream.eval [add_zero_class α] (s : Stream ι α) [is_bounded s] : s.σ → ι →₀ α
| q := 
  if h : s.valid q then
    have s.wf_rel (s.next q) q, from s.next_wf _ h,
    s.eval₀ q h + Stream.eval (s.next q) 
  else 0
  using_well_founded {rel_tac := λ _ _, `[exact ⟨_, s.wf⟩], dec_tac := `[assumption]}

@[simp] lemma Stream.eval_invalid [add_zero_class α] (s : Stream ι α) [is_bounded s] (q : s.σ) (h : ¬s.valid q) :
  s.eval q = 0 :=
by rwa [Stream.eval, dif_neg]

@[simp] lemma Stream.eval_valid [add_zero_class α] (s : Stream ι α) [is_bounded s] (q : s.σ) (h : s.valid q) :
  s.eval q = s.eval₀ q h + s.eval (s.next q) :=
by rw [Stream.eval, dif_pos]

lemma Stream.eval₀_support [has_zero α] (s : Stream ι α) (x : s.σ) (h : s.valid x) :
  (s.eval₀ x h).support ⊆ {s.index x h} :=
by { rw Stream.eval₀, split_ifs, { exact finsupp.support_single_subset, }, simp, }

lemma Stream.eval₀_support' [has_zero α] (s : Stream ι α) {x : s.σ} (h₁ : s.valid x) {i : ι}
  (h₂ : s.eval₀ x h₁ i ≠ 0) : s.to_order x h₁ = (i, tt) :=
begin
  obtain rfl := finset.eq_of_mem_singleton (s.eval₀_support x h₁ (finsupp.mem_support_iff.mpr h₂)),
  rw [Stream.eval₀] at h₂, split_ifs at h₂ with hr,
  { simpa [Stream.to_order, Stream.index'_val h₁], }, { simpa using h₂, }
end

section mono

/-- A stream is monotonic if the index does not decrease after `skip` is called. -/
def Stream.is_monotonic (s : Stream ι α) : Prop :=
∀ q hq i, s.index' q ≤ s.index' (s.skip q hq i)

/-- A stream is strictly monotonic if it is monotonic and strictly advances its
  index when (non-trivially) skipped from a ready state. -/
def Stream.is_strict_mono (s : Stream ι α) : Prop :=
s.is_monotonic ∧ ∀ (q hq i), s.to_order q hq ≤ i → s.ready q → s.index' q ≠ s.index' (s.skip q hq i)

lemma Stream.is_monotonic.skip' {s : Stream ι α} (hs : s.is_monotonic) (q i) :
  s.index' q ≤ s.index' (s.skip' q i) :=
by { by_cases hq : s.valid q, { rw [Stream.skip'_val hq], apply hs, }, rw [Stream.skip'_invalid hq], exact rfl.le, }

lemma Stream.is_monotonic_iff {s : Stream ι α} :
  s.is_monotonic ↔ (∀ q hq i hq', s.index q hq ≤ s.index (s.skip q hq i) hq') :=
begin
  split, { intros h q hq i hq', specialize h q hq i, simp only [Stream.index'_val, hq, hq', with_top.coe_le_coe] at h, exact h, },
  intros h q hq i,
  by_cases hq' : s.valid (s.skip q hq i),
  { simp only [Stream.index'_val, hq, hq', with_top.coe_le_coe], apply h, },
  { rw Stream.index'_invalid hq', exact le_top, },
end

lemma Stream.is_monotonic.index_le_index_next {s : Stream ι α} (h : s.is_monotonic) (q : s.σ) :
  s.index' q ≤ s.index' (s.next q) :=
begin
  by_cases H : s.valid q, swap, { simp [H], },
  simp only [Stream.next, H, dif_pos],
  apply h,
end

lemma Stream.is_monotonic.index_le_of_mem_support [add_zero_class α] {s : Stream ι α} [is_bounded s] (hs : s.is_monotonic) {q : s.σ} :
  ∀ (i : ι), s.eval q i ≠ 0 → s.index' q ≤ i :=
begin
  simp only [← finsupp.mem_support_iff], refine well_founded.induction s.wf q _,
  intros q ih i hi,
  by_cases H : s.valid q, swap, { exfalso, simpa [H] using hi, },
  rw [s.eval_valid _ H] at hi,
  cases finset.mem_union.mp (finsupp.support_add hi) with hi hi,
  { rw finset.mem_singleton.mp (s.eval₀_support _ H hi), exact (le_of_eq (Stream.index'_val _)), },
  exact trans (hs.index_le_index_next q) (ih (s.next q) (s.next_wf _ H) i hi),
end

lemma Stream.is_monotonic.eq_zero_of_lt_index [add_zero_class α] {s : Stream ι α} [is_bounded s] (hs : s.is_monotonic) {q : s.σ} (i : ι) :
  ↑i < s.index' q → s.eval q i = 0 := by { contrapose!, exact hs.index_le_of_mem_support i, }

lemma Stream.is_strict_mono.lt {s : Stream ι α} (hs : s.is_strict_mono) (q hq i) (H : s.to_order q hq ≤ i) (hr : s.ready q) :
  s.index' q < s.index' (s.skip q hq i) := lt_of_le_of_ne (hs.1 _ _ _) (hs.2 _ _ _ H hr)

lemma Stream.is_strict_mono.next_ne {s : Stream ι α} (hs : s.is_strict_mono)
  {q : s.σ} (hq : s.valid q) (hr : s.ready q) : s.index' q ≠ s.index' (s.next q) :=
by { rw [Stream.next_val hq], exact hs.2 q hq _ rfl.le hr, }

lemma Stream.is_strict_mono.spec {s : Stream ι α} (hs : s.is_strict_mono) (q : s.σ) (hv : s.valid q) {i} (hi : s.to_order q hv ≤ i) :
  s.to_order' q ≤ (s.index' (s.skip q hv i), ff) :=
prod.lex.le_iff''.mpr ⟨by simpa using (hs.1 q hv i), by { simp, contrapose, simpa [hv] using hs.2 q hv i hi, }⟩

lemma Stream.is_strict_mono.index_le_of_mem_support [add_zero_class α] {s : Stream ι α} [is_bounded s]
  (hs : s.is_strict_mono) {q : s.σ} (hv) {i} (hi : s.to_order q hv ≤ i) : ∀ (j : ι), s.eval (s.skip q hv i) j ≠ 0 → s.to_order q hv ≤ (j, ff) :=
λ j hj, coe_lex_le_iff.mp (by { rw [Stream.coe_lex_to_order], refine (hs.spec q hv hi).trans _, simpa using hs.1.index_le_of_mem_support j hj, })

lemma Stream.is_strict_mono.eq_zero_of_lt_index [add_zero_class α] {s : Stream ι α} [is_bounded s]
  (hs : s.is_strict_mono) {q : s.σ} (hv) {i} (hi : s.to_order q hv ≤ i) (j : ι) : ((j, ff) <ₗ s.to_order q hv) → s.eval (s.skip q hv i) j = 0 :=
by { contrapose!, exact hs.index_le_of_mem_support hv hi j, }

lemma fst_lt_of_lt_of_lt {α : Type*} [preorder α] :
  ∀ {x y z : α ×ₗ bool}, x < y → y < z → x.1 < z.1
| x y ⟨z, ff⟩ h₁ h₂ := prod.lex.fst_lt_of_lt_of_le (h₁.trans h₂) (by simp)
| x ⟨y, tt⟩ ⟨z, tt⟩ h₁ h₂ := lt_of_le_of_lt (show x.1 ≤ y, from prod.lex.fst_le_of_le h₁.le) (by simpa using h₂)
| x ⟨y, ff⟩ ⟨z, tt⟩ h₁ h₂ := lt_of_lt_of_le (show x.1 < y, from prod.lex.fst_lt_of_lt_of_le h₁ (by simp)) (prod.lex.fst_le_of_le h₂.le)

lemma Stream.is_strict_mono.eval_skip_eq_zero [add_zero_class α] {s : Stream ι α} [is_bounded s] (hs : s.is_strict_mono) {q : s.σ} (hv : s.valid q) {i : stream_order ι} {j : ι}
  (h₁ : (j, ff) <ₗ i) (h₂ : i ≤ₗ s.to_order q hv) :
  s.eval (s.skip q hv i) j = 0 :=
begin
  cases eq_or_lt_of_le h₂ with h₂ h₂,
  { refine hs.eq_zero_of_lt_index _ h₂.symm.le _ _, rwa ← h₂, },
  { apply hs.1.eq_zero_of_lt_index, refine lt_of_lt_of_le _ (hs.1 _ _ _), rw [Stream.index'_val hv, with_top.coe_lt_coe], exact fst_lt_of_lt_of_lt h₁ h₂, }
end

lemma Stream.is_strict_mono.eval₀_eq_eval_filter [add_comm_monoid α] {s : Stream ι α} [is_bounded s] (hs : s.is_strict_mono) (q : s.σ) (hv : s.valid q) :
  s.eval₀ q hv = (s.eval q).filter (λ i, (i, ff) <ₗ s.to_order q hv) :=
begin
  rw [s.eval_valid _ hv, finsupp.filter_add],
  convert (add_zero _).symm,
  { rw [finsupp.filter_eq_self_iff], intros i hi, rw s.eval₀_support' hv hi, simp, },
  { rw [finsupp.filter_eq_zero_iff], intros i hi, rw [Stream.next_val hv], refine hs.eq_zero_of_lt_index hv rfl.le i hi, },
end

end mono

/-- A stream is lawful if it is monotonic and satisfies the following property about `skip`:
    Whenever we ask the stream to skip past `i : stream_order ι`, we do not affect the evaluation
    of the stream at any `j ≥ i`, where `j : ι` is interpreted in `stream_order ι` as `(j, ff)`.
    In other words, when we ask to skip past `i`, we do not skip past any `j ≥ i`.

    This also demonstrates the interpretation of the strictness indicator: when `i = (i, ff)`, `skip q _ i` means
    "skip up to (but not past) any ready states with index `i`" (since `(j, ff) ≥ (i, ff) ↔ j ≥ i`). On the other hand, when `i = (i, tt)`,
    this means "skip up to and including states with index `i`, but not anything strictly past `i`".
 -/
class is_lawful {ι : Type} {α : Type*} [linear_order ι] [add_zero_class α] (s : Stream ι α) extends is_bounded s :=
(mono : s.is_monotonic)
(skip_spec : ∀ q hq i j, (i ≤ₗ (j, ff)) → s.eval (s.skip q hq i) j = s.eval q j)

/-- A stream is strictly lawful if in addition to being lawful, it is strictly monotonic -/
class is_strict_lawful {ι : Type} {α : Type*} [linear_order ι] [add_zero_class α] (s : Stream ι α) extends is_lawful s :=
(strict_mono : s.is_strict_mono)

variables [add_zero_class α]

lemma Stream.mono (s : Stream ι α) [is_lawful s] : s.is_monotonic :=
‹is_lawful s›.mono

lemma Stream.strict_mono (s : Stream ι α) [is_strict_lawful s] : s.is_strict_mono :=
‹is_strict_lawful s›.strict_mono

lemma Stream.skip_spec (s : Stream ι α) [is_lawful s] (q : s.σ) (hq : s.valid q) (i : stream_order ι) : 
  (s.eval (s.skip q hq i)).filter (λ j, i ≤ₗ (j, ff)) = (s.eval q).filter (λ j, i ≤ₗ (j, ff)) :=
by { rw finsupp.filter_ext_iff, exact is_lawful.skip_spec q hq i, }

lemma Stream.skip_lt_to_order {s : Stream ι α} [is_lawful s] {q : s.σ} {hq : s.valid q}
  {i : stream_order ι} (hi : i < s.to_order q hq) :
  s.eval (s.skip q hq i) = s.eval q :=
begin
  ext j,
  by_cases H : s.to_order q hq ≤ (j, tt),
  { rw is_lawful.skip_spec q hq, simpa [prod.lex.lt_iff'', prod.lex.le_iff''] using lt_of_lt_of_le hi H, },
  have : ↑j < s.index' q := by simpa [hq] using fst_lt_of_lt_of_lt (show (j, ff) <ₗ (j, tt), by simp) (not_le.mp H),
  rw [s.mono.eq_zero_of_lt_index j this, s.mono.eq_zero_of_lt_index _ (this.trans_le (s.mono q hq i))],
end

lemma Stream.skip'_spec (s : Stream ι α) [is_lawful s] (q : s.σ) (i : stream_order ι) (j : ι) (h : i ≤ (j, ff)) :
  s.eval (s.skip' q i) j = s.eval q j :=
by { by_cases hq : s.valid q, { rw [Stream.skip'_val hq, is_lawful.skip_spec _ hq _ _ h], }, rw Stream.skip'_invalid hq, }

lemma Stream.skip'_lt_to_order {s : Stream ι α} [is_lawful s] {q : s.σ}
  {i : stream_order ι} (hi : coe_lex i < s.to_order' q) :
  s.eval (s.skip' q i) = s.eval q :=
begin
  by_cases hq : s.valid q, swap, { rw [Stream.skip'_invalid hq], },
  rw [← Stream.coe_lex_to_order hq, coe_lex_lt_iff] at hi,
  rw [Stream.skip'_val hq, Stream.skip_lt_to_order hi],
end

lemma Stream.eval_skip_eq_of_ff (s : Stream ι α) [is_lawful s] (q : s.σ) (hq : s.valid q) :
  s.eval (s.skip q hq (s.index q hq, ff)) = s.eval q :=
begin
  by_cases hr : s.ready q,
  { apply Stream.skip_lt_to_order, simp [Stream.to_order, hr], },
  simp [s.eval_valid q hq, Stream.eval₀, hr, Stream.next_val hq, Stream.to_order],
end

end stream_defs

section functor
variables {ι : Type} {α β γ : Type*}

/-- Solve as many goals as possible by definitional simplification, use heq/eq, and `refl` -/
meta def tactic.interactive.solve_refl : tactic unit :=
let tactics : list (tactic unit) :=
[`[dsimp],
  `[simp only [heq_iff_eq]],
  `[intros],
  `[subst_vars],
  `[refl]] in 
sequence (tactics.map (λ t, tactic.try t)) >> tactic.skip

@[simps] def Stream.map (f : α → β) (s : Stream ι α) : Stream ι β :=
{ s with value := λ q hq, f (s.value q hq) }

@[simp] lemma Stream.map_id (s : Stream ι α) : s.map id = s := by ext; solve_refl

lemma Stream.map_map (g : α → β) (f : β → γ) (s : Stream ι α) :
  (s.map g).map f = s.map (f ∘ g) := by ext; solve_refl 

@[simp] lemma Stream.to_order_map (s : Stream ι α) (f : α → β) :
  (s.map f).to_order = s.to_order := rfl

@[simp] lemma Stream.to_order'_map (s : Stream ι α) (f : α → β) :
  (s.map f).to_order' = s.to_order' := rfl

lemma Stream.map_value' [has_zero α] [has_zero β] (f : α → β) (hf : f 0 = 0) (s : Stream ι α) (q : s.σ) :
  (s.map f).value' q = f (s.value' q) :=
by { simp only [Stream.value'], split_ifs, { refl, }, rw hf, }

variables [linear_order ι]

@[simp] lemma map_is_bounded_iff (f : α → β) (s : Stream ι α) :
  is_bounded (s.map f) ↔ is_bounded s :=
by { simp only [is_bounded_iff], refl, }

end functor
