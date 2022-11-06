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
∀ {r} (h : q.valid r), q.index' r ≤ q.index' (q.next r h)

def Stream.reduced (q : Stream σ ι α) : Prop :=
∀ {r} (h : q.valid r) (h' : q.ready r), q.index' r ≠ q.index' (q.next r h)


