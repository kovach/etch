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
(wf : σ → σ → Prop)


@[ext]
lemma Stream.ext {ι α} {s₁ s₂ : Stream ι α} (h₀ : s₁.σ = s₂.σ)
  (h₁ : ∀ x y, x == y → (s₁.valid x ↔ s₂.valid y)) (h₂ : ∀ x y, x == y → (s₁.ready x ↔ s₂.ready y)) (h₃ : ∀ x y H₁ H₂ i b, x == y → s₁.skip x H₁ i b == s₂.skip y H₂ i b)
  (h₄ : ∀ x y H₁ H₂, x == y → s₁.index x H₁ == s₂.index y H₂) (h₅ : ∀ x y H₁ H₂, x == y → s₁.value x H₁ == s₂.value y H₂) 
  (h₆ : ∀ x₁ y₁ x₂ y₂, x₁ == y₁ → x₂ == y₂ → (s₁.wf x₁ x₂ ↔ s₂.wf y₁ y₂)) :
  s₁ = s₂ :=
begin
  cases s₁ with σ₁ v₁ r₁ n₁ i₁ l₁, cases s₂ with σ₂ v₂ r₂ n₂ i₂ l₂, dsimp only at *,
  subst h₀, simp only [heq_iff_eq] at *,
  obtain rfl : v₁ = v₂ := funext (λ x, propext $ h₁ x x rfl), obtain rfl : r₁ = r₂ := funext (λ x, propext $ h₂ x x rfl),
  refine ⟨rfl, rfl, rfl, _, _, _, _⟩; try { simp only [heq_iff_eq] at * }; ext, { apply h₃ x x _ _ _ _ rfl; assumption, }, { apply h₄ x x _ _ rfl; assumption, },
  { apply h₅ x x _ _ rfl; assumption, }, { apply h₆; refl, },
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

local notation a ` ≺ `:50 b := Stream.wf _ a b 

def Stream.valid_wf (s : Stream ι α) : Prop :=
well_founded s.wf ∧ ∀ q, s.valid q → (s.next q) ≺ q 

noncomputable def Stream.eval [add_zero_class α] (s : Stream ι α) (wf : s.valid_wf) : s.σ → ι →₀ α
| q := 
  if h : s.valid q then
    have s.next q ≺ q, from wf.2 _ h,
    s.eval₀ q h + Stream.eval (s.next q) 
  else 0
  using_well_founded {rel_tac := λ _ _, `[exact ⟨_, wf.1⟩], dec_tac := `[assumption]}

lemma Stream.eval_invalid [add_zero_class α] (s : Stream ι α) (wf : s.valid_wf) (q : s.σ) (h : ¬s.valid q) :
  s.eval wf q = 0 :=
by rwa [Stream.eval, dif_neg]

lemma Stream.eval_valid [add_zero_class α] (s : Stream ι α) (wf : s.valid_wf) (q : s.σ) (h : s.valid q) :
  s.eval wf q = s.eval₀ q h + s.eval wf (s.next q) :=
by rw [Stream.eval, dif_pos]

lemma Stream.eval₀_support [has_zero α] (s : Stream ι α) (x : s.σ) (h : s.valid x) :
  (s.eval₀ x h).support ⊆ {s.index x h} :=
by { rw Stream.eval₀, split_ifs, { exact finsupp.support_single_subset, }, simp, }

-- index ready
@[reducible]
def stream_order (ι : Type) : Type := with_top ι ×ₗ bool

@[simps]
def Stream.to_order (s : Stream ι α) (x : s.σ) : stream_order ι :=
⟨s.index' x, s.ready x⟩

def Stream.skip_valid_wf [has_le ι] (s : Stream ι α) : Prop :=
well_founded s.wf ∧ ∀ ⦃q hq i b⦄, ((↑i, b) : stream_order ι) ≤ s.to_order q → (s.skip q hq i b) ≺ q

def Stream.skip_valid_wf.to_valid_wf [preorder ι] {s : Stream ι α} (h : s.skip_valid_wf) :
  s.valid_wf :=
⟨h.1, λ q hq, by { rw [Stream.next_val hq], refine h.2 (le_of_eq _), simp [Stream.to_order, hq], }⟩ 

structure LawfulStream (ι : Type) (α : Type*) [linear_order ι] [add_comm_monoid α] extends Stream ι α := 
(skip_wf : Stream.skip_valid_wf to_Stream)
(skip_spec : ∀ q hq i b j, ((↑i, b) : stream_order ι) ≤ (↑j, ff) → Stream.eval _ skip_wf.to_valid_wf (skip q hq i b) j = Stream.eval _ skip_wf.to_valid_wf q j)
(mono : ∀ (q : σ) hq i b, Stream.to_order _ q ≤ Stream.to_order _ (skip q hq i b))

-- def Stream.strict_mono (s : Stream ι α) : Prop :=
-- ∀ ⦃r⦄, s.valid r → s.ready r → s.index' r ≠ s.index' (s.next r)

structure StrictLawfulStream (ι : Type) (α : Type*) [linear_order ι] [add_comm_monoid α] extends LawfulStream ι α :=
(strict_mono : ∀ ⦃r⦄, valid r → ready r → Stream.index' _ r ≠ Stream.index' _ (Stream.next _ r))

variables [linear_order ι] [add_comm_monoid α]

def LawfulStream.eval (s : LawfulStream ι α) : s.σ → ι →₀ α := Stream.eval _ s.skip_wf.to_valid_wf  

@[simp] lemma LawfulStream.eval_invalid (s : LawfulStream ι α) (q : s.σ) (h : ¬s.valid q) :
  s.eval q = 0 := Stream.eval_invalid _ _ q h

@[simp] lemma LawfulStream.eval_valid (s : LawfulStream ι α) (q : s.σ) (h : s.valid q) :
  s.eval q = s.eval₀ q h + s.eval (s.next q) := Stream.eval_valid _ _ q h

lemma LawfulStream.rel_next (s : LawfulStream ι α) (q : s.σ) (h : s.valid q) : (s.next q) ≺ q :=
s.skip_wf.to_valid_wf.2 q h

lemma LawfulStream.next_mono (s : LawfulStream ι α) (q : s.σ) :
  s.index' q ≤ s.index' (s.next q) :=
begin
  by_cases H : s.valid q, swap, { simp [H], },
  convert prod.lex.fst_le_of_le (s.mono _ H (s.index q H) (s.ready q)),
  simp [H],
end

lemma LawfulStream.index_le_of_mem_support {s : LawfulStream ι α} {q : s.σ } :
  ∀ (i : ι), i ∈ (s.eval q).support → s.index' q ≤ i :=
begin
  refine well_founded.induction s.skip_wf.1 q _,
  intros q ih i hi,
  by_cases H : s.valid q, swap, { exfalso, simpa [H] using hi, },
  rw [s.eval_valid _ H] at hi,
  cases finset.mem_union.mp (finsupp.support_add hi) with hi hi,
  { rw finset.mem_singleton.mp (s.eval₀_support _ H hi), exact (le_of_eq (Stream.index'_val _)), },
  exact trans (s.next_mono q) (ih (s.next q) (s.rel_next _ H) i hi),
end



/-
(a * b).eval = (a * b).eval₀ + (a * b).next.eval
             = (a.eval₀ * b.eval₀ or 0) + (a.skip (i, b) * b.skip (i, b)).eval
             = a.eval₀ * b.eval₀ + (a.skip (i, b)).eval * (b.skip (i, b)).eval

(a * b).eval₀ = (a.eval * b.eval)∣_{(i, ff) < to_order}

(a * b).skip (i, b)


-/
end stream_defs

