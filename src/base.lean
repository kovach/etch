-- main definition: iter
import algebra
import algebra.group
import algebra.group.defs
import tactic
import logic.relation

universes u v
variables (α β : Type*)

-- todo, already exists as function.End.smul_def
instance comp_monoid (ν : Type*) : monoid (ν → ν) :=
{ mul := λ a b, a ∘ b , mul_assoc := λ a b c, rfl
, one := λ a, a , one_mul := λ a, rfl , mul_one := λ a, rfl }

instance endo_action : mul_action (α → α) α :=
{ smul := λ f a, f a
, one_smul := λ a, begin unfold has_one.one mul_one_class.one monoid.one, end
, mul_smul := λ f g x , begin unfold has_mul.mul mul_one_class.mul monoid.mul function.comp, end }

-- not used
instance fish_monoid (m : _) (ν : Type) [monad m] [is_lawful_monad m] : monoid (ν → m ν) :=
{ mul := λ a b, (a >=> b)
, mul_assoc := λ a b c, begin unfold has_mul.mul, rw fish_assoc, end --needed for rev version?
, one := pure
, one_mul := fish_pipe
, mul_one := fish_pure
}

def emit_type (I V : Type) := option (I × option V)
structure iter (σ I V : Type) [linear_order I] :=
  (δ : σ → σ)
  (emit : σ → emit_type I V)

namespace iter

section params_unary
variables {σ I V : Type} [linear_order I]
(a : iter σ I V)
variables (s t : σ)

def ι : with_top I := match a.emit s with | none := none | some (i, _) := some i end
def ν :   option V := match a.emit s with | none := none | some (_, v) := v end

-- @[reducible, inline]
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
def strict             := ∀ (s t : σ), productive a s → productive a t → ι a s = ι a t → s = t

def future (s : σ) : set σ := { t | reachable a s t ∧ ¬ terminal a t}
@[simp] def terminal_by (s : σ) (i : ℕ) := a.terminal (a.step s i)
def minimal_terminal (s : σ) (i : ℕ) := a.terminal (a.step s i) ∧ ∀ j, a.terminal (a.step s j) → i ≤ j

instance [decidable_eq I] : decidable (terminal a s) := if h : ι a s = none then is_true h else is_false h

lemma some_not_terminal {a : iter σ I V} {s} {i : I} : a.ι s = some i → ¬ a.terminal s :=
λ h1 h2, false.rec _ (option.some_ne_none i (h1 ▸ h2))

def nat_iter : iter ℕ ℕ ℕ :=
{ δ := λ n, n+1
, emit := λ n, some (n, some n)
}

def iota (k : ℕ): iter (fin k.succ) (fin k) (fin k) :=
{ δ := λ n, if h : n.val < k then ⟨n.val+1,  nat.succ_lt_succ h⟩ else n
, emit := λ n, if h : n.val < k then some (⟨n.val, h⟩, some ⟨n.val, h⟩) else none
}

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
@[simp] lemma step_succ (s : σ) (i : ℕ) : a.step (a.δ s) i = a.step s i.succ :=
begin
change a.δ ^ i • a.δ^1 • s = a.δ ^ i.succ • s,
rw [← mul_smul, ← pow_add],
end

lemma minimal_terminal_unique {i i'} : a.minimal_terminal s i → a.minimal_terminal s i' → i = i' :=
begin rintros ⟨t1, h1⟩ ⟨t2, h2⟩, exact le_antisymm (h1 _ t2) (h2 _ t1), end

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

section semantics
variable [add_comm_monoid V]

def elementary (i : I) (v : V) := λ j, if i = j then v else 0
@[simp]
def semantics₁ (s : σ) : I → V :=
  match a.emit s with
  | none := 0
  | some (i, none) := 0
  | some (i, some v) := elementary i v
  end

@[simp]
def semantics' : σ → ℕ → I → V
| _ 0 := 0
| s (n+1) := a.semantics₁ s + semantics' (a.δ s) n
notation `⟦` a, s `⟧` := a.semantics' s

-- e.g.
#reduce (⟦iter.iota 4, 0⟧ 5) 2
#reduce (⟦iter.nat_iter, 0⟧ 20) 12
end semantics

lemma ι_top_emit_none {a : iter σ I V} {s} : a.ι s = ⊤ ↔ a.emit s = none := begin
split,
{
  cases h : a.emit s, exact λ _, rfl,
  intro h1,
  cases val,
  simp only [ι, h] at h1,
  exfalso, apply option.some_ne_none _ h1,
},
{
    intro h1,
    simp only [ι, h1], refl,
},
end

@[simp]
theorem terminal_succ_terminal {a : iter σ I V} (m : a.monotonic) (h : a.terminal t) : a.terminal (a.δ t) := begin
simp only [terminal] at *, apply none_top, rw ←h, apply m, exact transition.step _, end

@[simp]
theorem emit_none_of_terminal {a : iter σ I V} {t} : a.terminal t → a.emit t = none := begin
intro h, simp only [terminal] at h, exact ι_top_emit_none.1 h,
end

end params_unary

section params_binary
variables {σ₁ σ₂ I V : Type} [linear_order I] [decidable_eq σ₁] [decidable_eq σ₂]
[add_comm_monoid V]
(a : iter σ₁ I V) (b : iter σ₂ I V)
(s₁ : σ₁) (s₂ : σ₂)

def merge_indexed_values : I×(option V) → I×(option V) → I×(option V) | (i₁, v₁) (_, v₂) :=
    (i₁, option.lift_or_get (λ v₁ v₂, (v₁ + v₂)) v₁ v₂)
def add_emit : σ₁ × σ₂ → emit_type I V | ⟨s, t⟩ :=
    if a.ι s < b.ι t then a.emit s else if a.ι s > b.ι t then b.emit t
    else option.lift_or_get merge_indexed_values (a.emit s) (b.emit t)

def add_iter (a : iter σ₁ I V) (b : iter σ₂ I V) : iter (σ₁×σ₂) I V :=
{ δ := λ ⟨s,t⟩, if a.ι s < b.ι t then (a.δ s,t) else if a.ι s > b.ι t then (s, b.δ t) else (a.δ s, b.δ t)
, emit := add_emit a b,
}
infix `+'`:50 := add_iter

lemma add_iter_terminal {a : iter σ₁ I V} {b : iter σ₂ I V} {s₁ s₂} : a.terminal s₁ → b.terminal s₂ → (a+' b).terminal (s₁, s₂) := λ h1 h2,
begin
unfold terminal at *,
simp only [ι, add_iter, add_emit, h1, h2],
simp only [ι_top_emit_none.1 h1, ι_top_emit_none.1 h2],
split_ifs, repeat {refl},
end

end params_binary

end iter
