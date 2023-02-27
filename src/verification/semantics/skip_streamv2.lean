import tactic.linarith
import finsupp_lemmas
import verification.misc

open_locale classical
noncomputable theory

universes u

structure Stream (ι : Type) (α : Type u) : Type (max 1 u) :=
(σ : Type)
(valid : σ → Prop)
(ready : σ → Prop)
(skip  : Π x, valid x → ι → bool → σ)
(index : Π (x : σ), valid x → ι)
(value : Π (x : σ), ready x → α)

@[ext]
lemma Stream.ext {ι α} {s₁ s₂ : Stream ι α} (h₀ : s₁.σ = s₂.σ)
  (h₁ : ∀ x y, x == y → (s₁.valid x ↔ s₂.valid y)) (h₂ : ∀ x y, x == y → (s₁.ready x ↔ s₂.ready y)) (h₃ : ∀ x y H₁ H₂ i b, x == y → s₁.skip x H₁ i b == s₂.skip y H₂ i b)
  (h₄ : ∀ x y H₁ H₂, x == y → s₁.index x H₁ == s₂.index y H₂) (h₅ : ∀ x y H₁ H₂, x == y → s₁.value x H₁ == s₂.value y H₂) :  s₁ = s₂ :=
begin
  cases s₁ with σ₁ v₁ r₁ n₁ i₁ l₁, cases s₂ with σ₂ v₂ r₂ n₂ i₂ l₂, dsimp only at *,
  subst h₀, simp only [heq_iff_eq] at *,
  obtain rfl : v₁ = v₂ := funext (λ x, propext $ h₁ x x rfl), obtain rfl : r₁ = r₂ := funext (λ x, propext $ h₂ x x rfl),
  refine ⟨rfl, rfl, rfl, _, _, _⟩; try { simp only [heq_iff_eq] at * }; ext, { apply h₃ x x _ _ _ _ rfl; assumption, }, { apply h₄ x x _ _ rfl; assumption, },
  { apply h₅ x x _ _ rfl; assumption, },
end


section stream_defs
variables {ι : Type} {α : Type*}

def Stream.eval₀ [has_zero α] (s : Stream ι α) (σ₀ : s.σ) (h₁ : s.valid σ₀) : ι →₀ α :=
if h₂ : s.ready σ₀ then finsupp.single (s.index _ h₁) (s.value _ h₂) else 0

def Stream.next (s : Stream ι α) (q : s.σ) : s.σ :=
if h : s.valid q then s.skip q h (s.index q h) (s.ready q) else q 

@[simp] noncomputable def Stream.evaln [add_zero_class α] (s : Stream ι α) : ℕ → s.σ → (ι →₀ α)
| 0 q := 0
| (n + 1) q := if h₁ : s.valid q then Stream.evaln n (s.next q) + (s.eval₀ _ h₁) else 0 

def Stream.index' (s : Stream ι α) (x : s.σ) : with_top ι :=
if h : s.valid x then s.index x h else ⊤ 

def Stream.value' [has_zero α] (s : Stream ι α) (x : s.σ) : α :=
if h : s.ready x then s.value _ h else 0

@[simp] lemma Stream.index'_val {s : Stream ι α} {x : s.σ} (h : s.valid x) : s.index' x = s.index x h := dif_pos h

@[simp] lemma Stream.index'_invalid {s : Stream ι α} {x : s.σ} (h : ¬s.valid x) : s.index' x = ⊤ := dif_neg h

@[simp] lemma Stream.value'_val [has_zero α] {s : Stream ι α} {x : s.σ} (h : s.ready x) : s.value' x = s.value x h := dif_pos h

@[simp] lemma Stream.next_val {s : Stream ι α} {x : s.σ} (h : s.valid x) : s.next x = s.skip x h (s.index x h) (s.ready x) := dif_pos h

@[simp] lemma Stream.next_invalid {s : Stream ι α} {x : s.σ} (h : ¬s.valid x) : s.next x = x := dif_neg h

-- index ready
@[reducible]
def stream_order (ι : Type) : Type := with_top ι ×ₗ bool

@[simps]
def Stream.to_order (s : Stream ι α) (x : s.σ) : stream_order ι :=
⟨s.index' x, s.ready x⟩

localized "notation a ` <ₗ `:50 b := @has_lt.lt (stream_order _) _ a b" in streams
localized "notation a ` ≤ₗ `:50 b := @has_le.le (stream_order _) _ a b" in streams

structure BoundedStream (ι : Type) (α : Type*) [linear_order ι] extends Stream ι α :=
(wf_rel : σ → σ → Prop)
(wf : well_founded wf_rel)
(wf_valid : ∀ (q hq i b), (wf_rel (skip q hq i b) q) ∨ 
  (((↑i, b) <ₗ Stream.to_order _ q) ∧ (skip q hq i b) = q))

variable [linear_order ι]
localized "notation a ` ≺ `:50 b := BoundedStream.wf_rel _ a b" in streams

lemma BoundedStream.progress (s : BoundedStream ι α) {q hq i b} (h : s.to_order q ≤ (↑i, b) ) :
  (s.skip q hq i b) ≺ q :=
(s.wf_valid q hq i b).resolve_right (λ H, absurd H.1 h.not_lt)

lemma BoundedStream.next_wf (s : BoundedStream ι α) (q) (hq : s.valid q) : (s.next q) ≺ q :=
by { rw [Stream.next_val hq], refine s.progress (le_of_eq _), simp [Stream.to_order, hq], }

lemma BoundedStream.no_backward (s : BoundedStream ι α) (q hq i b) : 
  ((s.skip q hq i b) ≺ q) ∨ ((s.skip q hq i b) = q) :=
(s.wf_valid q hq i b).imp_right and.right

noncomputable def BoundedStream.eval [add_zero_class α] (s : BoundedStream ι α) : s.σ → ι →₀ α
| q := 
  if h : s.valid q then
    have s.wf_rel (s.next q) q, from s.next_wf _ h,
    s.eval₀ q h + BoundedStream.eval (s.next q) 
  else 0
  using_well_founded {rel_tac := λ _ _, `[exact ⟨_, s.wf⟩], dec_tac := `[assumption]}

@[simp] lemma BoundedStream.eval_invalid [add_zero_class α] (s : BoundedStream ι α) (q : s.σ) (h : ¬s.valid q) :
  s.eval q = 0 :=
by rwa [BoundedStream.eval, dif_neg]

@[simp] lemma BoundedStream.eval_valid [add_zero_class α] (s : BoundedStream ι α) (q : s.σ) (h : s.valid q) :
  s.eval q = s.eval₀ q h + s.eval (s.next q) :=
by rw [BoundedStream.eval, dif_pos]

lemma Stream.eval₀_support [has_zero α] (s : Stream ι α) (x : s.σ) (h : s.valid x) :
  (s.eval₀ x h).support ⊆ {s.index x h} :=
by { rw Stream.eval₀, split_ifs, { exact finsupp.support_single_subset, }, simp, }

lemma Stream.eval₀_support' [has_zero α] (s : Stream ι α) {x : s.σ} (h₁ : s.valid x) {i : ι}
  (h₂ : s.eval₀ x h₁ i ≠ 0) : s.to_order x = (i, tt) :=
begin
  obtain rfl := finset.eq_of_mem_singleton (s.eval₀_support x h₁ (finsupp.mem_support_iff.mpr h₂)),
  rw [Stream.eval₀] at h₂, split_ifs at h₂ with hr,
  { simpa [Stream.to_order, Stream.index'_val h₁], }, { simpa using h₂, }
end

def Stream.is_monotonic (s : Stream ι α) : Prop :=
∀ q hq i b, s.index' q ≤ s.index' (s.skip q hq i b)

section mono

lemma Stream.is_monotonic.index_le_index_next {s : Stream ι α} (h : s.is_monotonic) (q : s.σ) :
  s.index' q ≤ s.index' (s.next q) :=
begin
  by_cases H : s.valid q, swap, { simp [H], },
  convert h _ H (s.index q H) (s.ready q),
  simp [H],
end

lemma Stream.is_monotonic.index_le_of_mem_support [add_zero_class α] {s : BoundedStream ι α} (hs : s.is_monotonic) {q : s.σ} :
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

lemma Stream.is_monotonic.eq_zero_of_lt_index [add_zero_class α] {s : BoundedStream ι α} (hs : s.is_monotonic) {q : s.σ} (i : ι) :
  ↑i < s.index' q → s.eval q i = 0 := by { contrapose!, exact hs.index_le_of_mem_support i, }


def Stream.is_strict_mono (s : Stream ι α) : Prop :=
s.is_monotonic ∧ ∀ (q hq i b), s.to_order q ≤ (↑i, b) → s.ready q → s.index' q ≠ s.index' (s.skip q hq i b)

lemma Stream.is_strict_mono.lt {s : Stream ι α} (hs : s.is_strict_mono) (q hq i b) (H : s.to_order q ≤ (↑i, b)) (hr : s.ready q) :
  s.index' q < s.index' (s.skip q hq i b) := lt_of_le_of_ne (hs.1 _ _ _ _) (hs.2 _ _ _ _ H hr)

lemma Stream.is_strict_mono.next_ne {s : Stream ι α} (hs : s.is_strict_mono)
  {q : s.σ} (hq : s.valid q) (hr : s.ready q) : s.index' q ≠ s.index' (s.next q) :=
by { rw [Stream.next_val hq], refine hs.2 q hq _ _ (le_of_eq _) hr, rw [← Stream.index'_val hq], refl, }

lemma Stream.is_strict_mono.spec {s : Stream ι α} (hs : s.is_strict_mono) (q : s.σ) (hv : s.valid q) {i b} (hi : s.to_order q ≤ (↑i, b)) :
  s.to_order q ≤ (s.index' (s.skip q hv i b), ff) :=
prod.lex.le_iff''.mpr ⟨by { dsimp, exact (hs.1 q hv i b), }, by { dsimp, contrapose, simpa using hs.2 q hv i b hi, }⟩

lemma Stream.is_strict_mono.index_le_of_mem_support [add_zero_class α] {s : BoundedStream ι α}
  (hs : s.is_strict_mono) {q : s.σ} (hv) {i b} (hi : s.to_order q ≤ (↑i, b)) : ∀ (j : ι), s.eval (s.skip q hv i b) j ≠ 0 → s.to_order q ≤ (↑j, ff) :=
λ j hj, (hs.spec q hv hi).trans $ by simpa using hs.1.index_le_of_mem_support j hj

lemma Stream.is_strict_mono.eq_zero_of_lt_index [add_zero_class α] {s : BoundedStream ι α}
  (hs : s.is_strict_mono) {q : s.σ} (hv) {i b} (hi : s.to_order q ≤ (↑i, b)) (j : ι) : ((↑j, ff) <ₗ s.to_order q) → s.eval (s.skip q hv i b) j = 0 :=
by { contrapose!, exact hs.index_le_of_mem_support hv hi j, }

lemma Stream.is_strict_mono.eval₀_eq_eval_filter [add_comm_monoid α] {s : BoundedStream ι α} (hs : s.is_strict_mono) (q : s.σ) (hv : s.valid q) :
  s.eval₀ q hv = (s.eval q).filter (λ i, (↑i, ff) <ₗ s.to_order q) :=
begin
  rw [s.eval_valid _ hv, finsupp.filter_add],
  convert (add_zero _).symm,
  { rw [finsupp.filter_eq_self_iff], intros i hi, rw s.eval₀_support' hv hi, simp, },
  { rw [finsupp.filter_eq_zero_iff], intros i hi, rw [Stream.next_val hv], refine hs.eq_zero_of_lt_index hv (le_of_eq _) i hi, rw [← Stream.index'_val hv], refl, },
end

-- lemma Stream.is_strict_mono.eval_next_eq_eval_filter [add_comm_monoid α] {s : BoundedStream ι α} (hs : s.is_strict_mono) (q : s.σ) :
--   s.eval (s.next q) = (s.eval q).filter (λ i, s.to_order q ≤ (↑i, ff)) :=
-- begin
--   by_cases hv : s.valid q, swap, { simp [hv, finsupp.filter_zero], },
--   rw [s.eval_valid _ hv, finsupp.filter_add],
--   convert (zero_add _).symm,
--   { rw [finsupp.filter_eq_zero_iff], intros i hi, contrapose! hi, rw s.eval₀_support' hv hi, simp, },
--   { rw [finsupp.filter_eq_self_iff], intros i hi, exact hs.index_le_of_mem_support i hi, },
-- end

end mono

structure LawfulStream (ι : Type) (α : Type*) [linear_order ι] [add_zero_class α] extends BoundedStream ι α :=
(mono : to_Stream.is_monotonic)
(skip_spec : ∀ q hq i b j, ((↑i, b) ≤ₗ ((↑j : with_top ι), ff)) → to_BoundedStream.eval (skip q hq i b) j = to_BoundedStream.eval q j)

structure StrictLawfulStream (ι : Type) (α : Type*) [linear_order ι] [add_zero_class α] extends LawfulStream ι α :=
(strict_mono : to_Stream.is_strict_mono)

variables [add_zero_class α]

lemma LawfulStream.skip_spec' (s : LawfulStream ι α) (q : s.σ) (hq : s.valid q) (i : ι) (b : bool) : 
  (s.eval (s.skip q hq i b)).filter (λ j, (↑i, b) ≤ₗ ((↑j : with_top ι), ff)) = (s.eval q).filter (λ j, (↑i, b) ≤ₗ ((↑j : with_top ι), ff)) :=
by { rw finsupp.filter_ext_iff, exact s.skip_spec q hq i b, }
/-
(a * b).eval = (a * b).eval₀ + (a * b).next.eval
             = (a.eval₀ * b.eval₀ or 0) + (a.skip (i, b) * b.skip (i, b)).eval
             = a.eval₀ * b.eval₀ + (a.skip (i, b)).eval * (b.skip (i, b)).eval

(ia, ir) ≤ (a.next.index, ff)
(a.eval₀ * b.eval₀) = a.eval|_{(j, ff) < (ia, ir)} * b.eval|{(j, ff) < (ib, ir)}
(a * b).eval₀ = (a.eval * b.eval)∣_{(i, ff) < to_order}

(a * b).skip (i, b)

a.eval * b.eval = (a.eval * b.eval)|_{(j, ff) < to_order} + (a.eval * b.eval)|_{to_order ≤ (j, ff)}
                = (a * b).eval₀ + (a.eval * b.eval)|_{to_order ≤ (j, ff)}
(a.eval * b.eval)|_{(i, b) ≤ (j, ff)} 
  = a.eval|_{(i, b) ≤ (j, ff)} * b.eval|_{to_order ≤ (i, ff)}
  = (a.eval (skip (i, b)))|_{(i, b) ≤ (j, ff)} * (b.eval.skip (i, b))|_{(i, b) ≤ (j, ff)}
  = (a.eval (skip ..) * b.eval (skip ..))|_{(i, b) ≤ (j, ff)}
  = (a.eval (next ) * (b.eval (next)))

(a + b).eval = (a + b).eval₀ + (a + b).next.eval
             = a.eval₀|_{(j, ff) < (i, b)} + b.eval₀|_{(j, ff) < (i, b)}
                + (a.skip (i, b)).eval + (b.skip (i, b)).eval


-/
end stream_defs

