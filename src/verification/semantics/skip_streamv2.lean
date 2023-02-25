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

structure BoundedStream (ι : Type) (α : Type*) extends Stream ι α :=
(wf_rel : σ → σ → Prop)
(wf : well_founded wf_rel)
-- TODO: should this just be replaced by the stronger "wf_skip_valid"?
(wf_valid : ∀ q, valid q → wf_rel (Stream.next _ q) q)

noncomputable def BoundedStream.eval [add_zero_class α] (s : BoundedStream ι α) : s.σ → ι →₀ α
| q := 
  if h : s.valid q then
    have s.wf_rel (s.next q) q, from s.wf_valid _ h,
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

-- index ready
@[reducible]
def stream_order (ι : Type) : Type := with_top ι ×ₗ bool

@[simps]
def Stream.to_order (s : Stream ι α) (x : s.σ) : stream_order ι :=
⟨s.index' x, s.ready x⟩

variable [linear_order ι]

local notation a ` <ₗ `:50 b := @has_lt.lt (stream_order _) _ a b
local notation a ` ≤ₗ `:50 b := @has_le.le (stream_order _) _ a b

section

def Stream.skip_valid_wf (s : Stream ι α) (rel : s.σ → s.σ → Prop) : Prop :=
∀ (q hq i b), (rel (s.skip q hq i b) q) ∨ 
  (((↑i, b) <ₗ s.to_order q) ∧ (s.skip q hq i b) = q)

variables {s : Stream ι α} {rel : s.σ → s.σ → Prop}
local notation a ` ≺ `:50 b := rel a b

lemma Stream.skip_valid_wf.progress (h : s.skip_valid_wf rel) :
  ∀ ⦃q hq i b⦄, s.to_order q ≤ (↑i, b) → (s.skip q hq i b) ≺ q :=
begin
  intros q hq i b,
  cases h q hq i b with H H,
  { intro, assumption, }, { intro not_H, cases H.1.not_le not_H, },
end

lemma Stream.skip_valid_wf.to_valid_wf (h : s.skip_valid_wf rel) 
  (q : s.σ) (hq : s.valid q) : (s.next q) ≺ q :=
by { rw [Stream.next_val hq], refine h.progress (le_of_eq _), simp [Stream.to_order, hq], }

lemma Stream.skip_valid_wf.no_backward (h : s.skip_valid_wf rel) (q hq i b) : 
  ((s.skip q hq i b) ≺ q) ∨ ((s.skip q hq i b) = q) :=
(h q hq i b).imp_right and.right

end

def Stream.is_monotonic (s : Stream ι α) : Prop :=
∀ q hq i b, s.to_order q ≤ s.to_order (s.skip q hq i b)

section mono

lemma Stream.is_monotonic.index_le_index_next {s : Stream ι α} (h : s.is_monotonic) (q : s.σ) :
  s.index' q ≤ s.index' (s.next q) :=
begin
  by_cases H : s.valid q, swap, { simp [H], },
  convert prod.lex.fst_le_of_le (h _ H (s.index q H) (s.ready q)),
  simp [H],
end

lemma Stream.is_monotonic.index_le_of_mem_support [add_zero_class α] {s : BoundedStream ι α} (hs : s.is_monotonic) {q : s.σ } :
  ∀ (i : ι), i ∈ (s.eval q).support → s.index' q ≤ i :=
begin
  refine well_founded.induction s.wf q _,
  intros q ih i hi,
  by_cases H : s.valid q, swap, { exfalso, simpa [H] using hi, },
  rw [s.eval_valid _ H] at hi,
  cases finset.mem_union.mp (finsupp.support_add hi) with hi hi,
  { rw finset.mem_singleton.mp (s.eval₀_support _ H hi), exact (le_of_eq (Stream.index'_val _)), },
  exact trans (hs.index_le_index_next q) (ih (s.next q) (s.wf_valid _ H) i hi),
end

end mono

def Stream.is_strict_mono (s : Stream ι α) : Prop :=
∀ ⦃q⦄, s.valid q → s.ready q → s.index' q ≠ s.index' (s.next q) 

structure LawfulStream (ι : Type) (α : Type*) [linear_order ι] [add_comm_monoid α] extends BoundedStream ι α :=
(wf_valid' : to_Stream.skip_valid_wf wf_rel)
(mono : to_Stream.is_monotonic)
(skip_spec : ∀ q hq i b j, ((↑i, b) ≤ₗ ((↑j : with_top ι), ff)) → to_BoundedStream.eval (skip q hq i b) j = to_BoundedStream.eval q j)

structure StrictLawfulStream (ι : Type) (α : Type*) [linear_order ι] [add_comm_monoid α] extends LawfulStream ι α :=
(strict_mono : to_Stream.is_strict_mono)

/-
(a * b).eval = (a * b).eval₀ + (a * b).next.eval
             = (a.eval₀ * b.eval₀ or 0) + (a.skip (i, b) * b.skip (i, b)).eval
             = a.eval₀ * b.eval₀ + (a.skip (i, b)).eval * (b.skip (i, b)).eval

(a * b).eval₀ = (a.eval * b.eval)∣_{(i, ff) < to_order}

(a * b).skip (i, b)

a.eval * b.eval = (a.eval * b.eval)|_{(j, ff) < to_order} + (a.eval * b.eval)|_{to_order ≤ (j, ff)}
                = (a * b).eval₀ + (a.eval * b.eval)|_{to_order ≤ (j, ff)}
(a.eval * b.eval)|_{(i, b) ≤ (j, ff)} 
  = a.eval|_{(i, b) ≤ (j, ff)} * b.eval|_{to_order ≤ (i, ff)}
  = (a.eval (skip (i, b)))|_{(i, b) ≤ (j, ff)} * (b.eval.skip (i, b))|_{(i, b) ≤ (j, ff)}
  = (a.eval (skip ..) * b.eval (skip ..))|_{(i, b) ≤ (j, ff)}

(a + b).eval = (a + b).eval₀ + (a + b).next.eval
             = a.eval₀|_{(j, ff) < (i, b)} + b.eval₀|_{(j, ff) < (i, b)}
                + (a.skip (i, b)).eval + (b.skip (i, b)).eval


-/
end stream_defs

