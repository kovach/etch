import verification.misc
import verification.stream


open_locale classical
noncomputable theory

variables {σ σ₁ σ₂ ι α β : Type} [linear_order ι]

def Stream.index' (s : Stream σ ι α) (x : σ) : with_top ι :=
if h : s.valid x then s.index x h else ⊤ 

@[simp] lemma Stream.index'_lt_top_iff {s : Stream σ ι α} {x : σ} :
  s.index' x < ⊤ ↔ s.valid x :=
by { rw Stream.index', split_ifs; simp [h], exact with_top.coe_lt_top _, }

-- valid index ready
@[reducible]
def stream_order (ι : Type) : Type := bool ×ₗ with_top ι ×ₗ bool

def Stream.to_order (s : Stream σ ι α) (x : σ) : stream_order ι :=
⟨¬s.valid x, s.index' x, s.ready x⟩

lemma valid_of_le_valid {s₁ : Stream σ₁ ι α} {s₂ : Stream σ₂ ι β} {x : σ₁} {y : σ₂}
  (h : s₁.to_order x ≤ s₂.to_order y) (h' : s₂.valid y) : s₁.valid x :=
by { simp [Stream.to_order, h'] at h, simpa using prod.lex.fst_le_of_le h, }

lemma valid_of_le_or {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} {x : σ₁} {y : σ₂}
  (h : a.valid x ∨ b.valid y) (h' : a.to_order x ≤ b.to_order y) : a.valid x :=
(or_iff_left_of_imp (valid_of_le_valid h')).mp h

def Stream.monotonic (q : Stream σ ι α) : Prop :=
∀ {r} (h : q.valid r), (q.to_order r) ≤ (q.to_order (q.next r h))

def Stream.reduced (q : Stream σ ι α) : Prop :=
∀ {s t} (hs : q.valid s) (ht : q.valid t), q.ready s → q.ready t → q.index s hs = q.index t ht → s = t



