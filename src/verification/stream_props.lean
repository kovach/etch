import verification.misc
import verification.stream


open_locale classical
noncomputable theory

variables {σ σ₁ σ₂ ι α β : Type} [linear_order ι]

-- index ready
@[reducible]
def stream_order (ι : Type) : Type := with_top ι ×ₗ bool

@[simps]
def Stream.to_order (s : Stream σ ι α) (x : σ) : stream_order ι :=
⟨s.index' x, s.ready x⟩

lemma valid_of_le_valid {s₁ : Stream σ₁ ι α} {s₂ : Stream σ₂ ι β} {x : σ₁} {y : σ₂}
  (h : s₁.to_order x ≤ s₂.to_order y) (h' : s₂.valid y) : s₁.valid x :=
by { simp [Stream.to_order, h'] at h, rw ← Stream.index'_lt_top_iff, refine lt_of_le_of_lt (prod.lex.fst_le_of_le h) _, simpa, }

lemma valid_of_le_or {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} {x : σ₁} {y : σ₂}
  (h : a.valid x ∨ b.valid y) (h' : a.to_order x ≤ b.to_order y) : a.valid x :=
(or_iff_left_of_imp (valid_of_le_valid h')).mp h

def Stream.monotonic (q : Stream σ ι α) : Prop :=
∀ ⦃r⦄ (h : q.valid r), q.index' r ≤ q.index' (q.next r h)

def Stream.reduced (q : Stream σ ι α) : Prop :=
∀ ⦃r⦄ (h : q.valid r) (h' : q.ready r), q.index' r ≠ q.index' (q.next r h)

class Stream.simple (q : Stream σ ι α) : Prop :=
(monotonic : q.monotonic)
(reduced : q.reduced)

lemma Stream.is_monotonic (q : Stream σ ι α) [q.simple] : Stream.monotonic q :=
‹q.simple›.monotonic

lemma Stream.is_reduced (q : Stream σ ι α) [q.simple] : Stream.reduced q :=
‹q.simple›.reduced

lemma Stream.monotonic.index_le_support [add_zero_class α] {q : Stream σ ι α} (hq : q.monotonic) {x : σ} {n : ℕ} :
  ∀ i ∈ (q.eval_steps n x).support, q.index' x ≤ ↑i :=
begin
  induction n with n ih generalizing x,
  { simp, },
  simp only [Stream.eval_steps, ne.def],
  split_ifs, swap, { simp, },
  intros i H,
  rcases (finset.mem_union.mp (finsupp.support_add H)) with H'|H',
  { exact trans (hq _) (ih _ H'), },
  rw finset.mem_singleton.mp (q.eval₀_support _ h H'),
  exact (le_of_eq (Stream.index'_val _)),
end

lemma Stream.index_lt_next [add_zero_class α] (q : Stream σ ι α) [q.simple] {x : σ}
  (hv : q.valid x) (hr : q.ready x) : q.index' x < q.index' (q.next _ hv) :=
by { rw lt_iff_le_and_ne, exact ⟨q.is_monotonic hv, q.is_reduced hv hr⟩, }

lemma Stream.index_lt_support [add_zero_class α] (q : Stream σ ι α) [q.simple] {x : σ} {n : ℕ}
  (hv : q.valid x) (hr : q.ready x) :
  ∀ i ∈ (q.eval_steps n (q.next x hv)).support, q.index' x < ↑i :=
λ i H, lt_of_lt_of_le (q.index_lt_next hv hr) (q.is_monotonic.index_le_support i H)
