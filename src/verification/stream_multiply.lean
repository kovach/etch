import tactic
import data.finsupp.basic
import control.bifunctor
import verification.vars
import verification.verify

open_locale classical
noncomputable theory

variables {σ α ι γ β ρ : Type}
variables (R : Type) [add_zero_class R] [has_one R] [has_mul R]

noncomputable instance finsupp.has_mul [mul_zero_class α] : has_mul (ι →₀ α) :=
⟨λ a b, finsupp.zip_with (*) (zero_mul _) a b⟩

lemma finsupp.mul_apply [mul_zero_class α] (g₁ g₂ : ι →₀ α) (a : ι) : (g₁ * g₂) a = g₁ a * g₂ a := rfl

-- #check pi.distrib -- todo, tactic like this?
noncomputable instance finsupp.non_unital_semiring [non_unital_semiring α] : non_unital_semiring (ι →₀ α) :=
{
  zero := 0,
  add_assoc := λ a b c, fun_like.ext _ _ (by simp [finsupp.add_apply, add_assoc]),
  zero_add  := λ a,     fun_like.ext _ _ (by simp [finsupp.add_apply]),
  add_zero  := λ a,     fun_like.ext _ _ (by simp [finsupp.add_apply]),
  add_comm  := λ a b,   fun_like.ext _ _ (by simp [finsupp.add_apply, add_comm] ),
  zero_mul  := λ a,     fun_like.ext _ _ (by simp [finsupp.mul_apply]),
  mul_zero  := λ a,     fun_like.ext _ _ (by simp [finsupp.mul_apply]),

  left_distrib  := λ a b c, by simp [fun_like.ext_iff, finsupp.mul_apply, finsupp.add_apply, left_distrib],
  right_distrib := λ a b c, by simp [fun_like.ext_iff, finsupp.mul_apply, finsupp.add_apply, right_distrib],

  mul_assoc     := λ a b c, by simp [fun_like.ext_iff, finsupp.mul_apply, mul_assoc],

  ..finsupp.has_mul, ..finsupp.has_add, } .

variables
[linear_order ι]
[non_unital_semiring γ]

structure partial_status (σ ι α : Type) :=
(index : with_top ι)
(value : option α)
(ready : bool)
(valid : bool)
(state : σ)

@[reducible, inline]
def StreamState.valid (s : StreamState σ ι α) : Prop := s.stream.valid s.state
@[reducible, inline]
def StreamState.ready (s : StreamState σ ι α) : Prop := s.stream.ready s.state

def StreamState.now' (s : StreamState σ ι ρ) : partial_status σ ι ρ :=
{ index := if h : s.stream.valid s.state then s.stream.index s.state h else ⊤,
  value := if h : s.stream.ready s.state then s.stream.value s.state h else none,
  ready := s.stream.ready s.state,
  valid := s.stream.valid s.state,
  state := s.state }

@[simp]
def StreamExec.now' (s : StreamExec σ ι ρ) : partial_status σ ι ρ :=
s.to_StreamState.now'

open Types

open Stream StreamExec

@[reducible] def stream_order_tuple (ι : Type) : Type := bool ×ₗ with_top ι ×ₗ bool
example : linear_order (stream_order_tuple ι) := infer_instance

def StreamState.to_order_tuple {α} (a : StreamState σ ι α) : stream_order_tuple ι :=
(¬ a.now'.valid, a.now'.index, a.now'.ready)
--let a := p.1, s := p.2 in (¬ a.valid s, if h : a.valid s then a.index s h else ⊤, a.ready s)
def StreamExec.to_order_tuple {α} (a : StreamExec σ ι α) : bool ×ₗ with_top ι ×ₗ bool :=
a.to_StreamState.to_order_tuple .

variables {σ₁ σ₂ : Type}

def StreamState.lag {σ₁ σ₂ ι α β} [linear_order ι] : StreamState σ₁ ι α → StreamState σ₂ ι β → Prop := λ a b, a.to_order_tuple ≤ b.to_order_tuple
def StreamState.lag_lt {α β} : StreamState σ₁ ι α → StreamState σ₂ ι β → Prop := λ a b, a.to_order_tuple < b.to_order_tuple
def StreamExec.lag  {α β} : StreamExec σ₁ ι α → StreamExec σ₂ ι β → Prop := λ a b, a.to_order_tuple ≤ b.to_order_tuple
def StreamExec.lag_lt  {α β} : StreamExec σ₁ ι α → StreamExec σ₂ ι β → Prop := λ a b, a.to_order_tuple < b.to_order_tuple
local infix `⊑`:50    := StreamExec.lag
local infix `⊏`:50    := StreamExec.lag_lt

instance (σ ι α : Type) : has_coe (StreamExec σ ι α) (StreamState σ ι α) := ⟨StreamExec.to_StreamState⟩

--instance StreamState.preorder : preorder (StreamState σ ι α) := preorder.lift to_order_tuple
--instance StreamExec.preorder : preorder (StreamExec σ ι α) := preorder.lift StreamExec.to_order_tuple

lemma StreamExec.le_total {α β : Type} (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι β) : a.lag b ∨ b.lag a := le_total a.to_order_tuple b.to_order_tuple

def Stream.monotonic (q : Stream σ ι α) : Prop :=
∀ {r} (h : q.valid r), StreamState.lag ⟨q, r⟩ ⟨q, q.next r h⟩

def Stream.reduced (q : Stream σ ι α) : Prop :=
∀ {s t} (hs : q.valid s) (ht : q.valid t), q.ready s → q.ready t → q.index s hs = q.index t ht → s = t

variables {σ ι α}

variables
(s : StreamExec σ ι γ)
(a : StreamExec σ₁ ι α)
(b : StreamExec σ₂ ι α)
(s₁ : σ₁) (s₂ : σ₂)
[has_mul α]

-- no assumptions on value type
variables (q : StreamExec σ ι ρ)

@[simp] lemma StreamExec.bound_valid_zero' {s : StreamExec σ ι α} :
  s.bound = 0 → (s.bound_valid ↔ ¬s.valid) := λ bz,
⟨λ h, by { simpa [StreamExec.bound_valid, bz] using h }, λ h, StreamExec.bound_valid_aux.invalid _ h⟩

structure Stream.mul.ready (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) (s : σ₁ × σ₂) : Prop :=
(valid : a.valid s.1 ∧ b.valid s.2)
(ready : a.ready s.1 ∧ b.ready s.2)
(index : a.index s.1 valid.1 = b.index s.2 valid.2)

@[simps]
def Stream.mul {σ₁ σ₂} (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) : Stream (σ₁ × σ₂) ι α :=
{ valid := λ p, a.valid p.1 ∧ b.valid p.2,
  ready := λ p, Stream.mul.ready a b p,
  next  := λ p hv, if StreamState.lag ⟨a, p.1⟩ ⟨b, p.2⟩ then (a.next p.1 hv.1, p.2) else (p.1, b.next p.2 hv.2),
  index := λ p hv, max (a.index p.1 hv.1) (b.index p.2 hv.2),
  value := λ p hr, a.value p.1 hr.ready.1 * b.value p.2 hr.ready.2 }

@[simps]
def StreamExec.mul {σ₁ σ₂} (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) : StreamExec (σ₁ × σ₂) ι α :=
{ stream := a.stream.mul b.stream,
  state := (a.state, b.state),
  bound := a.bound + b.bound }

infix ` ⋆ `:71 := StreamExec.mul

open StreamExec

@[simp] lemma mul.valid (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) : (a ⋆ b).valid ↔ a.valid ∧ b.valid := iff.rfl.

lemma mul.invalid (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) :
¬ a.valid ∨ ¬ b.valid → ¬ (a.mul b).valid := λ d,
begin
  cases d;
  simp [d],
end

lemma invalid_eval_zero : ¬ s.valid → s.eval = 0 :=
begin
  intros,
  simp only [eval, eval_steps],
  cases s.bound; simp only [eval_steps],
  split_ifs,
  refl,
end

def Stream.reduced' (q : Stream σ ι α) : Prop :=
∀ {s t} (hs : q.valid s) (ht : q.valid t), q.ready s → q.ready t → q.index s hs = q.index t ht → s = t

class Stream.is_simple (q : Stream σ ι α) : Prop :=
(monotonic : ∀ {r} (h : q.valid r), StreamState.lag ⟨q, r⟩ ⟨q, q.next r h⟩)
(reduced : ∀ {s t} (hs : q.valid s) (ht : q.valid t), q.ready s → q.ready t → q.index s hs = q.index t ht → s = t)

#check @Stream.is_simple.monotonic
--class StreamExec.is_simple (q : StreamExec σ ι α) : Prop := (is_simple : q.stream.is_simple)
@[simp] def StreamExec.is_simple (q : StreamExec σ ι α) : Prop := q.stream.is_simple

@[simps]
def StreamExec.succ : StreamExec σ ι ρ :=
{ stream := q.stream,
  state := if h : q.valid then q.stream.next q.state h else q.state,
  bound := q.bound.pred }

@[simp] def StreamExec.succ.stream : q.succ.stream = q.stream := rfl

open StreamExec

@[simp] lemma delta_stream_eq (h : a.valid) : (a.δ h).stream = a.stream := rfl
@[simp] lemma succ_stream_eq : a.succ.stream = a.stream := rfl
@[simp] lemma succ_bound : a.succ.bound = a.bound.pred := rfl

@[simp] lemma delta_succ (h : q.valid) : q.δ h = q.succ :=
begin
  simp only [succ],
  split_ifs,
  refl,
end

variables {a b}
lemma invalid_succ_invalid : ¬ a.valid → ¬ a.succ.valid :=
λ h v, begin simp only [succ] at v, split_ifs at v, exact h v end

lemma succ_bound_valid : a.bound_valid → a.succ.bound_valid :=
begin
  simp [bound_valid],
  intro h,
  induction h with _ _ _ a b c d e,
  { solve_by_elim [StreamExec.bound_valid_aux.invalid, invalid_succ_invalid] },
  { simpa using d }
end

lemma lag.lt_iff_le_not_le : a ⊏ b ↔ (a ⊑ b ∧ ¬ b ⊑ a) := begin
split,
intro h,
split,
{ exact le_of_lt h },
{ simpa [StreamExec.lag, StreamExec.lag_lt, le_of_lt] using h },
{ simp [StreamExec.lag, StreamExec.lag_lt, le_of_lt] },
end

@[simp] lemma le_succ_left (v : (a ⋆ b).valid) : a.bound_valid → b.bound_valid → a ⊑ b → (a ⋆ b).succ = a.succ ⋆ b :=
begin
  intros ha _ le,
  simp at v,
  have : a.valid := v.1,
  have : a.bound ≠ 0,
  { intro,
    simpa [bound_valid, *] using ha },
  obtain ⟨_, _⟩ := nat.exists_eq_succ_of_ne_zero this,

  simp [StreamExec.succ],
  split_ifs,
  simp [nat.succ_add, nat.pred, (⋆), *],
end
@[simp] lemma lt_succ_right (v : (a ⋆ b).valid) : a.bound_valid → b.bound_valid → b ⊏ a → (a ⋆ b).succ = a ⋆ b.succ :=
begin
  intros _ hb lt,
  simp at v,
  have : b.valid := v.2,
  have : ¬ a ⊑ b, { simp only [lag.lt_iff_le_not_le] at lt, simp [lt], },
  have : b.bound ≠ 0,
  { intro, simpa [bound_valid, *] using hb },
    obtain ⟨_, _⟩ := nat.exists_eq_succ_of_ne_zero this,

  simp [StreamExec.succ],
  split_ifs,
  simp [nat.add_succ, nat.pred, (⋆), *],
end

variables (a b)

lemma mul.bound_valid
(a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) :
a.bound_valid → b.bound_valid → (a.mul b).bound_valid :=
begin
  intros h1 h2,
  generalize ha : a.bound = n₁,
  generalize hb : b.bound = n₂,
  induction n₁ with _ _ c d e f g h generalizing a n₂ b;
  induction n₂ with _ _ k l m n o p generalizing b,
  { apply bound_valid_aux.invalid, simp [*] at * },
  { apply bound_valid_aux.invalid, simp [*] at * },
  { apply bound_valid_aux.invalid, simp [*] at * },
  {
    cases em a.valid; cases em b.valid,
    { simp only [StreamExec.mul_bound, bound_valid, *],
      have : (a ⋆ b).valid, { simp, split; assumption },
      apply bound_valid_aux.next_bound_valid this,
      simp only [delta_succ],
      cases em (a ⊑ b) with ale nale,
      { rw le_succ_left,
        change bound_valid_aux (n₁_n.succ + n₂_n) (a.succ ⋆ b),
        rw [nat.succ_add],
        have ha' : a.succ.bound = n₁_n, { simp [succ, *] },
        rw [← ha', ← nat.add_succ, ← hb],
        change (a.succ ⋆ b).bound_valid,
        have := succ_bound_valid h1,
        apply n₁_ih,
        all_goals { assumption },
      },

      cases le_total a b with le le, {contradiction},
      { have : b ⊏ a,
        { rw lag.lt_iff_le_not_le,
          simp [*] },
        simp only [lt_succ_right, *],
        have hb' : b.succ.bound = n₂_n, { simp [succ, *] },
        rw [← hb', ← ha],
        change (a ⋆ b.succ).bound_valid,
        apply n₂_ih,
        { exact succ_bound_valid h2 },
        { assumption }
      },
    },
    { apply bound_valid_aux.invalid, simp [*] },
    { apply bound_valid_aux.invalid, simp [*] },
    { apply bound_valid_aux.invalid, simp [*] } }
end

instance hmul.is_simple
(a : Stream σ₁ ι α) (b : Stream σ₂ ι α)
(ha : a.is_simple) (hb : b.is_simple) : (a.mul b).is_simple :=
{ monotonic := sorry,
  reduced :=
  begin
    intros s t hs ht ready_s ready_t eq,
    cases ready_s,
    cases ready_t,

    simp only [(*), Stream.mul] at hs ht,
    simp [(*), Stream.mul, *, max_idem.idempotent] at eq,

    ext,
    { apply @Stream.is_simple.reduced _ _ _ _ _ a; simp [*] },
    { apply @Stream.is_simple.reduced _ _ _ _ _ b; simp [*] },
  end
}

variables
[non_unital_semiring α]
(a_simple : a.is_simple)
(b_simple : b.is_simple)

def StreamExec.eval₀' [has_zero α] (s : StreamExec σ ι α) : ι →₀ α :=
if h : s.valid ∧ s.ready then finsupp.single (s.now h.1 h.2).index (s.now h.1 h.2).value else 0

noncomputable def StreamExec.eval_steps' [add_zero_class α] :
  ℕ → (StreamExec σ ι α) → ι →₀ α
| 0 s := 0
| (n + 1) s := (StreamExec.eval_steps' n (s.succ)) + (s.eval₀')

@[simp]
def StreamExec.eval' [add_zero_class α] (s : StreamExec σ ι α) : ι →₀ α :=
s.eval_steps' s.bound

open StreamExec

@[simp] lemma invalid_eval₀_zero : ¬ a.valid → a.eval₀' = 0 := begin simp [eval₀'], rintro _ ⟨_, _⟩, contradiction end

@[simp] lemma invalid_zero {n} : ¬ a.valid → a.eval_steps' n = 0 := begin
  intros h,
  induction n generalizing a,
  { simp [eval_steps'] },
  { have : ¬ a.succ.valid := invalid_succ_invalid h, simp [eval_steps', *] },
end

@[simp] lemma invalid_mul_zero_l {n} : ¬ a.valid → (a ⋆ b).eval_steps' n = 0 :=
begin
  intros h,
  have : ¬ (a ⋆ b).valid, { simp [h] },
  induction n generalizing a,
  { simp [eval_steps'] },
  { have : ¬ (a ⋆ b).succ.valid := invalid_succ_invalid this, simp [eval_steps', *] },
end
@[simp] lemma invalid_mul_zero_r {n} : ¬ b.valid → (a ⋆ b).eval_steps' n = 0 :=
begin
  intros h,
  have : ¬ (a ⋆ b).valid, { simp [h] },
  induction n generalizing a,
  { simp [eval_steps'] },
  { have : ¬ (a ⋆ b).succ.valid := invalid_succ_invalid this, simp [eval_steps', *] },
end
@[simp] lemma invalid_eval₀_zero_l : ¬ a.valid → (a ⋆ b).eval₀' = 0 :=
begin
  intros h,
  have : ¬ (a ⋆ b).valid, { simp [h] },
  simp [eval₀'],
  rintros ⟨_, _⟩,
  contradiction,
end
@[simp] lemma invalid_eval₀_zero_r : ¬ b.valid → (a ⋆ b).eval₀' = 0 :=
begin
  intros h,
  have : ¬ (a ⋆ b).valid, { simp [h] },
  simp [eval₀'],
  rintros ⟨_, _⟩,
  contradiction,
end

@[simp] lemma reduced_mul_eval_l (ha : a.is_simple) (hb : b.is_simple) :
a ⊑ b → (a ⋆ b).eval₀'  = a.eval₀' * b.eval' :=
begin
  intros le,
  sorry,
end

@[simp] lemma reduced_mul_eval_r : b ⊑ a → (a ⋆ b).eval₀' = a.eval' * b.eval₀' := sorry
@[simp] lemma eval_steps_zero' : eval_steps' 0 a = 0 := rfl

@[simp] lemma not_bool_eq : ∀ {a b : bool}, !a = !b ↔ a = b := by { intros, cases a; cases b; dec_trivial }

@[simp] lemma StreamState.order_eq_iff (a : StreamState σ₁ ι α) (b : StreamState σ₁ ι β) :
a.to_order_tuple = b.to_order_tuple ↔
a.valid = b.valid ∧ a.now'.index = b.now'.index ∧ a.ready = b.ready :=
by { simp [StreamState.to_order_tuple, StreamState.now'], }

-- @[simp] lemma StreamExec.order_eq_iff_(a : StreamExec σ₁ ι α) (b : StreamExec σ₁ ι β) :
-- a.to_StreamState.to_order_tuple = b.to_StreamState.to_order_tuple ↔
-- a.valid = b.valid ∧ a.now'.index = b.now'.index ∧ a.ready = b.ready :=
-- by { simp [StreamState.to_order_tuple] }

#check StreamState.ext
@[simp] lemma StreamState.simp_ext : ({stream := a.to_StreamState.stream, state := a.to_StreamState.state} : StreamState σ₁ ι α) = a.to_StreamState := StreamState.ext _ a.to_StreamState rfl rfl

variable
(ss : StreamState σ ι ρ)

lemma succ_state_not_eq (h : a.valid) (bv : a.bound_valid) : a.state ≠ a.succ.state :=
begin
  simp [bound_valid] at bv,
  induction bv,
  { contradiction },
  { intro eq,
    set eq := eq.symm,
    simp at eq,
    simp [eq h] at bv_ih,
    apply bv_ih,
    simp [succ],
    split_ifs,
    simpa [StreamExec.valid, h, eq] using bv_h }
end

@[simp] theorem with_top_inj {a b : ι} : (↑ a : with_top ι) = ↑ b ↔ a = b :=
by { simp [← with_top.some_eq_coe, option.some_inj] }

lemma reduced_ready_progress (h : a.valid) (bv : a.bound_valid) : a.stream.is_simple → a.ready → a ⊏ a.succ :=
begin
  intros as ar,
  cases as with mono red,
  have := mono h,
  simp [StreamState.lag, le_iff_eq_or_lt] at this,
  cases this,
  { obtain ⟨eqv, eqi, eqr⟩ := this,
    suffices : a.state = a.succ.state,
    { have := succ_state_not_eq a h bv, contradiction },
    { have : a.stream.valid (a.to_StreamState.stream.next a.to_StreamState.state h),
      { apply eqv.mp, assumption },
      simp [succ], split_ifs,

      apply red h this,
      { assumption, },
      { apply eqr.mp, assumption },
      { simp [StreamExec.valid] at h,
        simp [StreamState.now'] at eqi,
        simp [StreamState.valid] at eqv,

        split_ifs at eqi,
        simpa using eqi } } },
  { simp [StreamExec.to_order_tuple, StreamExec.lag_lt, succ, *] },
end

theorem mul_spec : a.bound_valid → b.bound_valid → a.is_simple → b.is_simple → (a ⋆ b).eval' = a.eval' * b.eval' :=
begin
  intros abv bbv _ _,
  simp,
  generalize hba : a.bound = ba,
  generalize hbb : b.bound = bb,

  induction ba generalizing a bb b;
  induction bb generalizing b, simp [StreamExec.eval_steps'],

  { have : ¬ a.valid, { simpa [hba] using abv }, simp [*] },
  { have : ¬ b.valid, { simpa [hbb] using bbv }, simp [*] },

  cases em a.valid; cases em b.valid,

  { have hav : (a ⋆ b).valid := ⟨h, h_1⟩,
    cases em (a ⊑ b) with ale nale,
    {
      simp only [nat.succ_add, le_succ_left, eval_steps', *],
      rw ba_ih,
      { simp [*, eval_steps', right_distrib, left_distrib], abel, },
      { exact succ_bound_valid abv },
      { assumption },
      { simpa },
      { assumption },
      { simp [*] },
      { simp [*] },
    },
    cases le_total a b with le le, {contradiction},
    {
      have : b ⊏ a,
      { rw lag.lt_iff_le_not_le,
        simp [*] },

      simp only [nat.add_succ, lt_succ_right, eval_steps', *],
      rw bb_ih,
      { simp [*, eval_steps', right_distrib, left_distrib], },
      { exact succ_bound_valid bbv },
      { simpa [*] },
      { simp [succ, *] },
    }
  },

  { have : ¬ (a ⋆ b).valid, {simp [*]}, simp [*] },
  { have : ¬ (a ⋆ b).valid, {simp [*]}, simp [*] },
  { have : ¬ (a ⋆ b).valid, {simp [*]}, simp [*] },

end
