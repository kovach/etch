import tactic.linarith
import finsupp_lemmas

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
  (h₄ : ∀ x y H₁ H₂, x == y → s₁.index x H₁ == s₂.index y H₂) (h₅ : ∀ x y H₁ H₂, x == y → s₁.value x H₁ == s₂.value y H₂) :
  s₁ = s₂ :=
begin
  cases s₁ with σ₁ v₁ r₁ n₁ i₁ l₁, cases s₂ with σ₂ v₂ r₂ n₂ i₂ l₂, dsimp only at *,
  subst h₀, simp only [heq_iff_eq] at *,
  obtain rfl : v₁ = v₂ := funext (λ x, propext $ h₁ x x rfl), obtain rfl : r₁ = r₂ := funext (λ x, propext $ h₂ x x rfl),
  refine ⟨rfl, rfl, rfl, _, _, _⟩; simp only [heq_iff_eq] at *; ext, { apply h₃ x x _ _ _ _ rfl; assumption, }, { apply h₄ x x _ _ rfl; assumption, },
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

def Stream.wf (s : Stream ι α) : Prop :=
∃ (r : s.σ → s.σ → Prop), well_founded r ∧ ∀ q, s.valid q → r (s.next q) q

def Stream.rel (s : Stream ι α) : s.σ → s.σ → Prop := 
if wf : s.wf then wf.some else λ _ _, false

notation a ` ≺ `:50 b := Stream.rel _ a b 

lemma false.well_founded {α : Type*} : well_founded (λ (_ : α) (_ : α), false) :=
well_founded.intro $ λ x, acc.intro _ (λ y, false.elim)

lemma Stream.rel_wf (s : Stream ι α) : well_founded s.rel  := 
by { rw [Stream.rel], by_cases wf : s.wf, { simpa [wf] using wf.some_spec.1, }, simpa [wf] using false.well_founded, }

lemma Stream.wf.rel_next {s : Stream ι α} (wf : s.wf) (q : s.σ) (h : s.valid q) : (s.next q) ≺ q :=
by { rw [Stream.rel, dif_pos wf], exact wf.some_spec.2 q h, }

noncomputable def Stream.eval [add_zero_class α] (s : Stream ι α) (wf : s.wf) : s.σ → ι →₀ α
| q := 
  if h : s.valid q then 
    have (s.next q) ≺ q, from wf.rel_next q h,
    Stream.eval (s.next q) + s.eval₀ q h 
  else 0
  using_well_founded {rel_tac := λ _ _, `[exact ⟨_, s.rel_wf⟩], dec_tac := `[assumption]}

@[simp] lemma Stream.eval_invalid [add_zero_class α] (s : Stream ι α) (wf : s.wf) (q : s.σ) (h : ¬s.valid q) :
  s.eval wf q = 0 :=
by rwa [Stream.eval, dif_neg]

@[simp] lemma Stream.eval_valid [add_zero_class α] (s : Stream ι α) (wf : s.wf) (q : s.σ) (h : s.valid q) :
  s.eval wf q = s.eval wf (s.next q) + s.eval₀ q h :=
by rw [Stream.eval, dif_pos]

-- index ready
@[reducible]
def stream_order (ι : Type) : Type := with_top ι ×ₗ bool

@[simps]
def Stream.to_order (s : Stream ι α) (x : s.σ) : stream_order ι :=
⟨s.index' x, s.ready x⟩

structure LawfulStream [linear_order ι] [add_comm_monoid α] extends Stream ι α := 
(wf : Stream.wf to_Stream)
(skip_wf : ∀ q hq i b, ((↑i, b) : stream_order ι) ≤ Stream.to_order _ q → (skip q hq i b) ≺ q)
(skip_spec : ∀ q hq i b j, ((↑i, b) : stream_order ι) ≤ (↑j, ff) → Stream.eval _ wf (skip q hq i b) j = Stream.eval _ wf q j)
(mono : ∀ (q : σ), Stream.to_order _ q ≤ Stream.to_order _ (Stream.next _ q))

def Stream.strict_mono (s : Stream ι α) : Prop :=
∀ ⦃r⦄ (h : s.valid r) (h' : s.ready r), s.index' r ≠ s.index' (s.next r)

/-
(a * b).eval = (a * b).eval₀ + (a * b).next.eval
             = (a.eval₀ * b.eval₀ or 0) + (a.skip (i, b) * b.skip (i, b)).eval
             = a.eval₀ * b.eval₀ + (a.skip (i, b)).eval * (b.skip (i, b)).eval

(a * b).eval₀ = (a.eval * b.eval)∣_{(i, ff) < to_order}

(a * b).skip (i, b)


-/
end stream_defs

