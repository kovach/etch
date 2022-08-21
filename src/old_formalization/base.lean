import algebra
import algebra.group
import algebra.group.defs
import logic.relation
import order.lexicographic
import declare

instance fin.has_top (k : ℕ) : has_top (fin k.succ) := ⟨k⟩
-- todo instance i2 : linear_order unit := sorry
-- instance i2 (k : ℕ) : linear_order (fin k) := infer_instance
-- instance i3 {α β: Type*} [linear_order α] [linear_order β] : linear_order (lex α β) := infer_instance

universes u v
variables (α β : Type*)

def emit_type (I V : Type*) := option (I × option V)

structure iter (σ I V : Type*) :=
  (δ : function.End σ)
  (emit : σ → emit_type I V)

def_declare one := "variables {σ I V : Type} [linear_order I] (a : iter σ I V)"
def_declare two := "variables {σ₁ σ₂ I I₁ I₂ V V₁ V₂ V₃ : Type} [linear_order I] [linear_order I₁] [linear_order I₂] (a : iter σ₁ I V₁) (b : iter σ₂ I V₂)"
def_declare add := "variables (add : V₁ → V₂ → V₃) [has_zero V₁] [has_zero V₂] [has_zero V₃]"
def_declare mul := "variables (mul : V₁ → V₂ → V₃)"

namespace iter

section params_unary
variables {σ I V : Type} (a : iter σ I V) (s t : σ)

def ι : with_top I := match a.emit s with | none := none | some (i, _) := some i end
def ν :   option V := match a.emit s with | none := none | some (_, v) := v end
--def ν :   option V := option.bind (a.emit s) prod.snd

section semantics
variables [add_monoid V] [decidable_eq I]

def elementary (i : I) (v : V) := λ j, if i = j then v else 0

@[simp] def semantics₁ (s : σ) : I → V :=
  match a.emit s with
  | none := 0
  | some (i, none) := 0
  | some (i, some v) := elementary i v
  end

@[simp] def semantics : σ → ℕ → I → V
| _ 0 := 0
| s (n+1) := a.semantics₁ s + semantics (a.δ s) n

--notation `⟦` a, s `⟧` := a.semantics s
notation `⟦` a, s, j `⟧` := a.semantics s j
--example (j : ℕ) : ∀ i:I, ⟦a, s, j⟧ i = ⟦a, s⟧ j i := λ _, rfl

end semantics

variables [linear_order I]

def reachable := relation.refl_trans_gen (λ s t, t = a.δ s)

namespace transition -- can't use reachable??
open relation.refl_trans_gen
theorem trans {x y z : σ} : reachable a x y → reachable a y z → reachable a x z := trans
def step {x : σ} : reachable a x (a.δ x) := single rfl
end transition

theorem none_top {α : Type*} [linear_order α] : ∀ {i : with_top α}, ⊤ ≤ i → i = none | _ h := le_antisymm le_top h

def step       (s : σ) (i:ℕ) := a.δ^i • s
def monotonic          := ∀ (s t : σ), a.reachable s t → a.ι s ≤ a.ι t
def terminal   (s : σ) := a.ι s = ⊤
def finite     (s : σ) := ∃ (t : σ), reachable a s t ∧ terminal a t
def productive (s : σ) := ν a s ≠ none
def reduced    (s : σ) := ∀ (t t' : σ), a.reachable s t → a.reachable s t' →
  productive a t → productive a t' → ι a t = ι a t' → t = t'

def future (s : σ) : set σ := { t | reachable a s t ∧ ¬ terminal a t}
@[simp] def terminal_by (s : σ) (i : ℕ) := a.terminal (a.step s i)

instance [decidable_eq I] : decidable (terminal a s) := if h : ι a s = none then is_true h else is_false h

lemma some_not_terminal {a : iter σ I V} {s} {i : I} : a.ι s = some i → ¬ a.terminal s :=
λ h1 h2, false.rec _ (option.some_ne_none i (h1 ▸ h2))

open relation.refl_trans_gen
def path_of_index {a : iter σ I V} : ∀ (i:ℕ), a.reachable s (a.step s i)
| 0 := refl
| (n+1) := tail (path_of_index n) rfl

lemma le_of_index_lt {a : iter σ I V} (i j : ℕ) : a.monotonic → i ≤ j → a.ι ((a.δ^i)•s) ≤ a.ι ((a.δ^j) • s) := begin
  intros mono lt, apply mono, induction lt, exact refl, exact tail ‹_› rfl,
end
lemma index_lt_of_ge {a : iter σ I V} (i j : ℕ) : a.monotonic → a.ι ((a.δ^i)•s) < a.ι ((a.δ^j)•s) → i < j := λ mono, begin
have h := mt (le_of_index_lt s j i mono),
simpa using h,
end

@[simp] lemma step_zero : a.step s 0 = s := rfl
@[simp] lemma step_succ (s : σ) (i : ℕ) : a.step s i.succ = a.step (a.δ s) i :=
begin
change a.δ ^ (i+1) • s = a.δ ^ i • a.δ^1 • s,
rw [pow_add, mul_smul],
end

lemma not_terminal_succ {a : iter σ I V} {i : ℕ} {s} : ¬ a.terminal s → a.terminal_by s i → ∃ i':ℕ, i = i'.succ := begin
intros hnt ht, induction i with i hi,
exact false.rec _ (hnt ht),
exact ⟨i, rfl⟩,
end

lemma index_of_path {a : iter σ I V} {s t} : a.reachable s t → ∃ (i: ℕ), t = a.step s i := begin
  intros p, induction p, refine ⟨0 , _⟩, refl,
  case tail : s1 s2 path st h {
    cases h with i hh, refine ⟨i+1, _⟩,
    simp only [step] at *,
    rw [add_comm, pow_add, mul_smul, ← hh], exact st,
  }
end

section lemmas

lemma ι_top_emit_none {a : iter σ I V} {s} : a.ι s = ⊤ ↔ a.emit s = none := begin
split; intro h1,
{ cases h : a.emit s, exact rfl,
  cases val,
  simp only [ι, h] at h1,
  exfalso, apply option.some_ne_none _ h1 },
{ simp only [ι, h1], refl },
end

@[simp]
theorem terminal_succ_terminal {a : iter σ I V} (m : a.monotonic) (h : a.terminal t) : a.terminal (a.δ t) :=
begin
simp only [terminal] at *, apply none_top, rw ←h, exact m _ _ (transition.step _)
end

@[simp]
theorem emit_none_of_terminal {a : iter σ I V} {t} : a.terminal t → a.emit t = none := begin
intro h, simp only [terminal] at h, exact ι_top_emit_none.1 h,
end

end lemmas
end params_unary
end iter

structure stream (σ I V : Type*) :=
  (q : σ)
  (iter : iter σ I V)

namespace stream
variables {σ I V : Type} (s : stream σ I V)

@[simp] def ι := s.iter.ι s.q
@[simp] def ν := s.iter.ν s.q

@[simp] def δ (s : stream σ I V) : stream σ I V :=
{ q := s.iter.δ s.q .. s}

@[simp] def emit : emit_type I V := s.iter.emit s.q

variables [decidable_eq I]

@[simp] def semantics₁ [add_monoid V] (s : stream σ I V) : I → V
:= s.iter.semantics₁ s.q
-- simp?
@[simp] def semantics [add_monoid V] (s : stream σ I V) : ℕ → I → V
:= s.iter.semantics s.q
notation `⟦` s, i `⟧` := s.semantics i

variables [linear_order I]

@[simp] def terminal_by (i : ℕ) := s.iter.terminal_by s.q i

@[simp] def monotonic := s.iter.monotonic

end stream
