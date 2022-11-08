import data.finsupp.basic
import finsupp_lemmas
import algebra.big_operators.fin
import data.nat.succ_pred
import tactic.linarith

open_locale classical
noncomputable theory

universes u

structure Stream (ι : Type) (α : Type u) : Type (max 1 u) :=
(σ : Type)
(valid : σ → Prop)
(ready : σ → Prop)
(next  : Π (x : σ), valid x → σ)
(index : Π (x : σ), valid x → ι)
(value : Π (x : σ), ready x → α)

@[ext]
lemma Stream.ext {ι α} {s₁ s₂ : Stream ι α} (h₀ : s₁.σ = s₂.σ)
  (h₁ : ∀ x y, x == y → (s₁.valid x ↔ s₂.valid y)) (h₂ : ∀ x y, x == y → (s₁.ready x ↔ s₂.ready y)) (h₃ : ∀ x y H₁ H₂, x == y → s₁.next x H₁ == s₂.next y H₂)
  (h₄ : ∀ x y H₁ H₂, x == y → s₁.index x H₁ == s₂.index y H₂) (h₅ : ∀ x y H₁ H₂, x == y → s₁.value x H₁ == s₂.value y H₂) :
  s₁ = s₂ :=
begin
  cases s₁ with σ₁ v₁ r₁ n₁ i₁ l₁, cases s₂ with σ₂ v₂ r₂ n₂ i₂ l₂, dsimp only at *,
  subst h₀, simp only [heq_iff_eq] at *,
  obtain rfl : v₁ = v₂ := funext (λ x, propext $ h₁ x x rfl), obtain rfl : r₁ = r₂ := funext (λ x, propext $ h₂ x x rfl),
  refine ⟨rfl, rfl, rfl, _, _, _⟩; simp only [heq_iff_eq] at *; ext, { apply h₃ x x _ _ rfl; assumption, }, { apply h₄ x x _ _ rfl; assumption, },
  { apply h₅ x x _ _ rfl; assumption, },
end

section stream_defs
variables {ι : Type} {α : Type*}

def Stream.eval₀ [has_zero α] (s : Stream ι α) (σ₀ : s.σ) (h₁ : s.valid σ₀) : ι →₀ α :=
if h₂ : s.ready σ₀ then finsupp.single (s.index _ h₁) (s.value _ h₂) else 0

@[simp]
noncomputable def Stream.eval_steps [add_zero_class α] (s : Stream ι α) :
  ℕ → s.σ → ι →₀ α
| 0 _ := 0
| (n + 1) σ₀ := if h₁ : s.valid σ₀ then (Stream.eval_steps n (s.next σ₀ h₁)) + (s.eval₀ _ h₁) else 0

lemma Stream.eval_invalid [add_zero_class α] {s : Stream ι α} {σ₀ : s.σ} (h : ¬s.valid σ₀) (n : ℕ) :
  s.eval_steps n σ₀ = 0 :=
by cases n; simp [h]

inductive Stream.bound_valid : ℕ → ∀ (s : Stream ι α), s.σ → Prop
| start (n : ℕ) {s : Stream ι α} {σ₀ : s.σ} : ¬s.valid σ₀ → Stream.bound_valid n s σ₀
| step {n : ℕ} {s : Stream ι α} {σ₀ : s.σ} : ∀ (h : s.valid σ₀), Stream.bound_valid n s (s.next σ₀ h) → Stream.bound_valid (n + 1) s σ₀

end stream_defs

@[ext]
structure StreamExec (ι : Type) (α : Type u) :=
(stream : Stream ι α)
(state : stream.σ)
(bound : ℕ)
(bound_valid : stream.bound_valid bound state)

structure status (σ ι α : Type*) :=
(next  : σ)
(index : ι)
(value : α)
(ready : bool)
(valid : bool)
(state : σ)

universes v w
variables {ι ι' ι'' : Type} {α : Type u} {β : Type v} {γ : Type w}

/-- Solve as many goals as possible by definitional simplification, use heq/eq, and `refl` -/
meta def tactic.interactive.solve_refl : tactic unit :=
let tactics : list (tactic unit) :=
[`[dsimp],
  `[simp only [heq_iff_eq]],
  `[intros],
  `[subst_vars],
  `[refl]] in 
sequence (tactics.map (λ t, tactic.try t)) >> tactic.skip

@[simps]
def Stream.bimap (s : Stream ι α) (f : ι → ι') (g : α → β) : Stream ι' β :=
{ s with value := λ x hx, g (s.value x hx), index := λ x hx, f (s.index x hx) }

@[simp] lemma Stream.id_bimap (s : Stream ι α) : s.bimap id id = s :=
by ext; solve_refl

@[simp] lemma Stream.bimap_bimap (s : Stream ι α)
  (f : ι → ι') (f' : ι' → ι'') (g : α → β) (h : β → γ) :
  (s.bimap f g).bimap f' h = s.bimap (f' ∘ f) (h ∘ g) :=
by ext; solve_refl

notation f ` <$₁> `:1 s := s.bimap f id
notation g ` <$₂> `:1 s := s.bimap id g

@[reducible, inline]
def StreamExec.valid (s : StreamExec ι α) : Prop := s.stream.valid s.state

@[reducible, inline]
def StreamExec.ready (s : StreamExec ι α) : Prop := s.stream.ready s.state

open Stream.bound_valid (start step)

@[simp] lemma Stream.bound_valid_zero {s : Stream ι α} {σ₀ : s.σ} :
  s.bound_valid 0 σ₀ ↔ ¬s.valid σ₀ :=
⟨λ h, by { cases h, assumption, }, λ h, start _ h⟩

lemma Stream.bound_valid.mono {s : Stream ι α} {σ₀ : s.σ} {n m : ℕ} (h : s.bound_valid n σ₀) (n_le : n ≤ m) :
  s.bound_valid m σ₀ :=
begin
  induction h with _ _ _ _ _ _ _ hv _ ih generalizing m,
  { apply Stream.bound_valid.start, assumption, },
  cases m, { cases nat.not_succ_le_zero _ n_le, },
  exact Stream.bound_valid.step hv (ih (nat.le_of_succ_le_succ n_le)),
end

lemma Stream.eval_ge_bound [add_zero_class α] {s : Stream ι α} {σ₀ : s.σ} {n b : ℕ} (hb : s.bound_valid b σ₀) (hn : b ≤ n) :
  s.eval_steps n σ₀ = s.eval_steps b σ₀ :=
begin
  induction hb with _ _ _ _ n' σ₀' s' hv _ ih generalizing n,
  { simp [Stream.eval_invalid, *], },
  cases n, { cases nat.not_succ_le_zero _ hn, },
  simp [hv, ih (nat.le_of_succ_le_succ hn)],
end

lemma Stream.eval_min_bound [add_zero_class α] {s : Stream ι α} {σ₀ : s.σ} {n b : ℕ} (hb : s.bound_valid b σ₀) :
  s.eval_steps (min b n) σ₀ = s.eval_steps n σ₀ :=
by { rw min_def, split_ifs, { rw Stream.eval_ge_bound hb h, }, refl, }

lemma Stream.valid.bound_pos {s : Stream ι α} {σ₀ : s.σ} (h : s.valid σ₀) :
  ¬s.bound_valid 0 σ₀ := by simpa

lemma Stream.eval₀_support [has_zero α] (s : Stream ι α) (x : s.σ) (h : s.valid x) :
  (s.eval₀ x h).support ⊆ {s.index x h} :=
by { rw Stream.eval₀, split_ifs, { exact finsupp.support_single_subset, }, simp, }

@[simp] lemma Stream.bound_valid_succ {s : Stream ι α} {n : ℕ} {σ₀ : s.σ} :
  s.bound_valid (n + 1) σ₀ ↔ (∀ (h : s.valid σ₀), s.bound_valid n (s.next σ₀ h)) :=
⟨λ h, by { cases h, { intro, contradiction, }, intro, assumption, }, λ h, if H : s.valid σ₀ then step H (h H) else start _ H⟩

def StreamExec.eval [add_zero_class α] (s : StreamExec ι α) : ι →₀ α :=
s.stream.eval_steps s.bound s.state

section defs

@[simp] lemma imap_eval₀_spec [add_comm_monoid α] (f : ι → ι') (s : Stream ι α) (σ₀ : s.σ) (h : s.valid σ₀) :
  (f <$₁> s).eval₀ _ h = (s.eval₀ _ h).map_domain f :=
by { simp only [Stream.eval₀], split_ifs; simp, }

@[simp] lemma imap_eval_steps_spec [add_comm_monoid α] (f : ι → ι') (s : Stream ι α) (σ₀ : s.σ) (n : ℕ) :
  (f <$₁> s).eval_steps n σ₀ = (s.eval_steps n σ₀).map_domain f :=
begin
  induction n with n ih generalizing s σ₀; simp,
  split_ifs; simp [ih, finsupp.map_domain_add], refl,
end

@[simp] lemma bimap_bound_valid_iff (f : ι → ι') (g : α → β) (s : Stream ι α) (n : ℕ) (x : s.σ) :
  (s.bimap f g).bound_valid n x ↔ s.bound_valid n x :=
by { induction n with n ih generalizing x; simp [*]; refl, }

@[simps]
def StreamExec.bimap (s : StreamExec ι α) (f : ι → ι') (g : α → β) : StreamExec ι' β :=
{ s with stream := s.stream.bimap f g, bound_valid := by simpa using s.bound_valid }

@[simp] lemma StreamExec.id_bimap (s : StreamExec ι α) : s.bimap id id = s :=
by ext; solve_refl

@[simp] lemma StreamExec.bimap_bimap (s : StreamExec ι α)
  (f : ι → ι') (f' : ι' → ι'') (g : α → β) (h : β → γ) :
  (s.bimap f g).bimap f' h = s.bimap (f' ∘ f) (h ∘ g) :=
by ext; solve_refl

@[simp] lemma imap_stream (s : StreamExec ι α) (f : ι → ι') :
  (f <$₁> s).stream = (f <$₁> s.stream) := rfl

@[simp] lemma imap_stream_eval [add_zero_class α] (s : StreamExec ι α) (f : ι → ι') (n : ℕ) :
  (f <$₁> s).stream.eval_steps n s.state = (f <$₁> s.stream).eval_steps n s.state := rfl

@[simp] lemma StreamExec.bifunctor_bimap_valid (s : StreamExec ι α) (f : ι → ι') (g : α → β) :
  (s.bimap f g).valid ↔ s.valid := iff.rfl

@[simp] lemma StreamExec.bifunctor_bimap_ready (s : StreamExec ι α) (f : ι → ι') (g : α → β) :
  (s.bimap f g).ready ↔ s.ready := iff.rfl


def contract_stream (s : StreamExec ι α) : StreamExec unit α :=
(λ _, ()) <$₁> s

@[simp] lemma contract_stream_spec [add_comm_monoid α] (s : StreamExec ι α) :
  (contract_stream s).eval = finsupp.single () (finsupp.sum_range s.eval) :=
by { ext, simp [finsupp.sum_range, contract_stream, StreamExec.eval], }


def Stream.index' (s : Stream ι α) (x : s.σ) : with_top ι :=
if h : s.valid x then s.index x h else ⊤ 

def Stream.value' [has_zero α] (s : Stream ι α) (x : s.σ) : α :=
if h : s.ready x then s.value _ h else 0

def Stream.next' (s : Stream ι α) (x : s.σ) : s.σ :=
if h : s.valid x then s.next x h else x

@[simp] lemma Stream.index'_lt_top_iff [preorder ι] {s : Stream ι α} {x : s.σ} :
  s.index' x < ⊤ ↔ s.valid x :=
by { rw Stream.index', split_ifs; simp [h], exact with_top.coe_lt_top _, }

lemma Stream.eval₀_eq_single [has_zero α] (s : Stream ι α) (x : s.σ) (h : s.valid x) :
  s.eval₀ x h = finsupp.single (s.index _ h) (s.value' x) :=
by { rw [Stream.eval₀, Stream.value'], split_ifs with hr; simp, }

lemma Stream.index'_val {s : Stream ι α} {x : s.σ} (h : s.valid x) : s.index' x = s.index x h := dif_pos h

lemma Stream.index'_invalid {s : Stream ι α} {x : s.σ} (h : ¬s.valid x) : s.index' x = ⊤ := dif_neg h

lemma Stream.value'_val [has_zero α] {s : Stream ι α} {x : s.σ} (h : s.ready x) : s.value' x = s.value x h := dif_pos h

lemma Stream.next'_val {s : Stream ι α} {x : s.σ} (hx) : s.next' x = s.next x hx := dif_pos hx

lemma Stream.next'_val_invalid {s : Stream ι α} {x : s.σ} (hx : ¬s.valid x) : s.next' x = x := dif_neg hx

lemma Stream.next'_val_invalid' {s : Stream ι α} {x : s.σ} (hx : ¬s.valid x) (n : ℕ) :
  s.next'^[n] x = x := function.iterate_fixed (Stream.next'_val_invalid hx) n

lemma bound_valid_iff_next'_iterate {s : Stream ι α} {x : s.σ} {n : ℕ} :
  s.bound_valid n x ↔ ¬s.valid (s.next'^[n] x) :=
by { induction n with n ih generalizing x, { simp, }, by_cases H : s.valid x; simp [ih, H, Stream.next'_val, Stream.next'_val_invalid, Stream.next'_val_invalid'], }

lemma Stream.next'_ge_bound {s : Stream ι α} {σ₀ : s.σ} {n b : ℕ} (hb : s.bound_valid b σ₀) (hn : b ≤ n) :
  (s.next'^[n] σ₀) = (s.next'^[b] σ₀) :=
begin
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le hn,
  rw add_comm b k,
  rw bound_valid_iff_next'_iterate at hb,
  simp [function.iterate_add_apply, Stream.next'_val_invalid' hb],
end

lemma Stream.next'_min_bound {s : Stream ι α} {σ₀ : s.σ} {n b : ℕ} (hb : s.bound_valid b σ₀) :
  (s.next'^[min b n] σ₀) = (s.next'^[n] σ₀) :=
by { rw min_def, split_ifs, { rw Stream.next'_ge_bound hb h, }, refl, }

lemma Stream.bimap_value' [has_zero α] [has_zero β] (s : Stream ι α) (f : ι → ι') (g : α → β) (hg : g 0 = 0) :
  (s.bimap f g).value' = g ∘ s.value' :=
by { ext x, simp [Stream.value', apply_dite g, hg], refl, }

lemma Stream.bimap_value'_apply [has_zero α] [has_zero β] (s : Stream ι α) (f : ι → ι') (g : α → β) (hg : g 0 = 0) (x) :
  (s.bimap f g).value' x = g (s.value' x) :=
by rwa Stream.bimap_value'

end defs

open_locale big_operators

lemma Stream.spec_of_iterate [add_comm_monoid α] (s : Stream ι α)
  (B : ℕ) (σ₀ : s.σ) (h : ∀ i < B, s.valid (s.next'^[i] σ₀)) :
  s.eval_steps B σ₀ = ∑ i : fin B, finsupp.single (s.index (s.next'^[i] σ₀) (h i i.prop)) (s.value' (s.next'^[i] σ₀)) :=
begin
  induction B with B ih generalizing σ₀,
  { simp, },
  have hv : s.valid σ₀, { exact h 0 (nat.zero_lt_succ _), },
  specialize ih (s.next _ hv) (λ i hi, by simpa [Stream.next'_val hv] using h (i + 1) (nat.succ_lt_succ hi)),
  simp [hv, fin.sum_univ_succ, ih, Stream.eval₀_eq_single _ _ hv, Stream.next'_val hv],
  rw add_comm,
end

namespace primitives

@[simps]
def externSparseVec_stream {len : ℕ} (inds : vector ι len) (vals : vector α len) :
  Stream ι α :=
{ σ := ℕ,
  valid := λ i, i < len,
  ready := λ i, i < len,
  next := λ i hi, i + 1,
  index := λ i hi, inds.nth ⟨i, hi⟩,
  value := λ i hi, vals.nth ⟨i, hi⟩ }

@[simp] lemma externSparseVec_stream_value' [has_zero α] {len : ℕ} (inds : vector ι len) (vals : vector α len) (i : fin len) :
  (externSparseVec_stream inds vals).value' (i : ℕ) = vals.nth i := 
by { rw Stream.value'_val, swap, { exact i.prop, }, simp, }

@[simp] lemma externSparseVec_next'_iterate {len : ℕ} (inds : vector ι len) (vals : vector α len) (i : ℕ) :
  ((externSparseVec_stream inds vals).next'^[i] 0 : ℕ) = min len i :=
begin
  induction i with i ih, { simp [externSparseVec_stream], },
  rw [function.iterate_succ_apply', ih],
  simp [Stream.next', min_def, nat.succ_eq_add_one], clear ih,
  split_ifs; linarith,
end

@[simps]
def externSparseVec {len : ℕ} (inds : vector ι len) (vals : vector α len) :
  StreamExec ι α :=
{ stream := externSparseVec_stream inds vals,
  state := (0 : ℕ),
  bound := len,
  bound_valid := by simp [bound_valid_iff_next'_iterate] }

@[simp] lemma externSparseVec.spec [add_comm_monoid α] {len : ℕ} (inds : vector ι len) (vals : vector α len) :
  (externSparseVec inds vals).eval = ∑ i : fin len, finsupp.single (inds.nth i) (vals.nth i) :=
begin
  rw [StreamExec.eval, Stream.spec_of_iterate], swap, { dsimp, simp, },
  dsimp, apply fintype.sum_congr,
  intro i,
  congr; { simp [min_eq_right i.prop.le], },
end

def range (n : ℕ) : Stream ℕ ℕ :=
{ σ := ℕ,
  next  := λ k _, k+1,
  index := λ k _, k,
  value := λ k _, k,
  ready := λ _, true,
  valid := λ k, k < n, }

end primitives
