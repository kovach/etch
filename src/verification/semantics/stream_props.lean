import verification.misc
import verification.semantics.stream


open_locale classical
noncomputable theory

variables {ι : Type} {α β : Type*} [linear_order ι]

-- index ready
@[reducible]
def stream_order (ι : Type) : Type := with_top ι ×ₗ bool

@[simps]
def Stream.to_order (s : Stream ι α) (x : s.σ) : stream_order ι :=
⟨s.index' x, s.ready x⟩

@[simp] lemma Stream.bimap_to_order (s : Stream ι α) (g : α → β) :
  (g <$₂> s).to_order = s.to_order := rfl

lemma valid_of_le_valid {s₁ : Stream ι α} {s₂ : Stream ι β} {x : s₁.σ} {y : s₂.σ}
  (h : s₁.to_order x ≤ s₂.to_order y) (h' : s₂.valid y) : s₁.valid x :=
by { simp [Stream.to_order, h'] at h, rw ← Stream.index'_lt_top_iff, refine lt_of_le_of_lt (prod.lex.fst_le_of_le h) _, simpa, }

lemma valid_of_le_or {a : Stream ι α} {b : Stream ι α} {x : a.σ} {y : b.σ}
  (h : a.valid x ∨ b.valid y) (h' : a.to_order x ≤ b.to_order y) : a.valid x :=
(or_iff_left_of_imp (valid_of_le_valid h')).mp h

def Stream.monotonic (q : Stream ι α) : Prop :=
∀ ⦃r⦄ (h : q.valid r), q.index' r ≤ q.index' (q.next r h)

def Stream.reduced (q : Stream ι α) : Prop :=
∀ ⦃r⦄ (h : q.valid r) (h' : q.ready r), q.index' r ≠ q.index' (q.next r h)

structure Stream.simple (q : Stream ι α) : Prop :=
(monotonic : q.monotonic)
(reduced : q.reduced)

lemma Stream.monotonic.le_index_iterate {s : Stream ι α} (hs : s.monotonic) (q : s.σ) (n : ℕ) :
  s.index' q ≤ s.index' (s.next'^[n] q) :=
begin
  induction n with n ih generalizing q, { simp, },
  by_cases h : s.valid q, swap,
  { simp [Stream.next'_val_invalid' h], },
  refine (hs h).trans _,
  simpa [Stream.next'_val h] using ih _,
end

lemma Stream.monotonic.index_le_support [add_zero_class α] {q : Stream ι α} (hq : q.monotonic) {x : q.σ} {n : ℕ} :
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

lemma Stream.simple.index_lt_next {q : Stream ι α} (hq : q.simple) {x : q.σ}
  (hv : q.valid x) (hr : q.ready x) : q.index' x < q.index' (q.next _ hv) :=
by { rw lt_iff_le_and_ne, exact ⟨hq.monotonic hv, hq.reduced hv hr⟩, }

lemma Stream.simple.index_lt_support [add_zero_class α] {q : Stream ι α} (hq : q.simple) {x : q.σ} {n : ℕ}
  (hv : q.valid x) (hr : q.ready x) :
  ∀ i ∈ (q.eval_steps n (q.next x hv)).support, q.index' x < ↑i :=
λ i H, lt_of_lt_of_le (hq.index_lt_next hv hr) (hq.monotonic.index_le_support i H)

structure SimpleStream (ι : Type) (α : Type*) [linear_order ι] extends StreamExec ι α :=
(simple : stream.simple)

instance (ι : Type) (α : Type*) [linear_order ι] : has_coe
  (SimpleStream ι α) (StreamExec ι α) := ⟨SimpleStream.to_StreamExec⟩

def SimpleStream.contract {ι α} [linear_order ι] (s : SimpleStream ι α) :
  StreamExec unit α := contract_stream (s : StreamExec ι α)

lemma SimpleStream.monotonic (s : SimpleStream ι α) : s.stream.monotonic :=
s.simple.monotonic

lemma SimpleStream.reduced (s : SimpleStream ι α) : s.stream.reduced :=
s.simple.reduced
