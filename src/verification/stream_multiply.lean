import tactic
import data.finsupp.basic
import control.bifunctor
import verification.vars
import verification.verify
import verification.misc

open_locale classical
noncomputable theory

variables {σ α ι β ρ : Type}
variables (R : Type) [add_zero_class R] [has_one R] [has_mul R]

variables
[linear_order ι]

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
a.to_StreamState.to_order_tuple

variables {σ₁ σ₂ : Type}

def StreamState.lag {σ₁ σ₂ ι α β} [linear_order ι] : StreamState σ₁ ι α → StreamState σ₂ ι β → Prop := λ a b, a.to_order_tuple ≤ b.to_order_tuple
def StreamState.lag_lt {α β} : StreamState σ₁ ι α → StreamState σ₂ ι β → Prop := λ a b, a.to_order_tuple < b.to_order_tuple
def StreamExec.lag  {α β} : StreamExec σ₁ ι α → StreamExec σ₂ ι β → Prop := λ a b, a.to_order_tuple ≤ b.to_order_tuple
def StreamExec.lag_lt  {α β} : StreamExec σ₁ ι α → StreamExec σ₂ ι β → Prop := λ a b, a.to_order_tuple < b.to_order_tuple

instance (σ ι α : Type) : has_coe (StreamExec σ ι α) (StreamState σ ι α) := ⟨StreamExec.to_StreamState⟩

instance StreamState.preorder : preorder (StreamState σ ι α) := preorder.lift StreamState.to_order_tuple
instance StreamExec.preorder : preorder (StreamExec σ ι α) := preorder.lift StreamExec.to_order_tuple

local infix `⊑`:50    := StreamExec.lag
local infix `⊏`:50    := StreamExec.lag_lt
local infix `⊑ₛ`:50   := StreamState.lag
local infix `⊏ₛ`:50   := StreamState.lag_lt

lemma StreamExec.le_total {α β : Type} (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι β) : a.lag b ∨ b.lag a := le_total a.to_order_tuple b.to_order_tuple

def Stream.monotonic (q : Stream σ ι α) : Prop :=
∀ {r} (h : q.valid r), StreamState.lag ⟨q, r⟩ ⟨q, q.next r h⟩

def Stream.reduced (q : Stream σ ι α) : Prop :=
∀ {s t} (hs : q.valid s) (ht : q.valid t), q.ready s → q.ready t → q.index s hs = q.index t ht → s = t

variables {σ ι α}

variables
(s : StreamExec σ ι α)
(a : StreamExec σ₁ ι α)
(b : StreamExec σ₂ ι α)
(s₁ : σ₁) (s₂ : σ₂)
[non_unital_semiring α]

-- no assumptions on value type
variables (q : StreamExec σ ι ρ)

@[simp] lemma StreamExec.bound_valid_zero' {s : StreamExec σ ι α} :
  s.bound = 0 → (s.bound_valid ↔ ¬s.valid) := λ bz,
by simp [StreamExec.bound_valid, bz]

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

@[simp] lemma StreamExec.mul.valid (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) : (a ⋆ b).valid ↔ a.valid ∧ b.valid := iff.rfl.

lemma Stream.mul.valid.comm (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) (s₁ s₂) :
  (a.mul b).valid (s₁, s₂) ↔ (b.mul a).valid (s₂, s₁) := by simp [and.comm].

lemma StreamExec.mul.valid.comm (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) :
  (a ⋆ b).valid ↔ (b ⋆ a).valid := Stream.mul.valid.comm _ _ _ _.

lemma Stream.mul.ready.comm (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) (s₁ s₂) :
  Stream.mul.ready a b (s₁, s₂) ↔ Stream.mul.ready b a (s₂, s₁) := begin

  split; intro h; split;
  { simpa [and.comm] using h.ready <|>
    simpa [and.comm] using h.valid <|>
    simp [h.index] }
end

lemma StreamExec.mul.ready.comm (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) :
  (a ⋆ b).ready ↔ (b ⋆ a).ready := Stream.mul.ready.comm _ _ _ _.

lemma Stream.mul.index.comm (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) (s₁ s₂)
  (h : (a.mul b).valid (s₁, s₂)) (h' : (b.mul a).valid (s₂, s₁)) :
  (a.mul b).index (s₁, s₂) h = (b.mul a).index (s₂, s₁) h' :=
  by simpa [Stream.mul] using max_comm _ _.

lemma StreamState.mul.now'.index.comm {a : Stream σ₁ ι α} {b : Stream σ₂ ι α} :
  (StreamState.mk (a.mul b) (s₁, s₂)).now'.index =
  (StreamState.mk (b.mul a) (s₂, s₁)).now'.index := begin

  simp only [StreamState.now'],
  split_ifs,
  { simp [max_comm] },
  { simp at h h_1, exact absurd h.1 (h_1 h.2) },
  { simp at h h_1, exact absurd h_1.1 (h h_1.2) },
  { refl }
end

lemma mul.to_order_tuple.comm (a : Stream σ₁ ι α) (b : Stream σ₂ ι α) (s₁ : σ₁) (s₂ : σ₂) :
  { StreamState . stream := a.mul b, state := (s₁, s₂) }.to_order_tuple =
  { StreamState . stream := b.mul a, state := (s₂, s₁) }.to_order_tuple := begin

  simp only [StreamState.to_order_tuple, prod.mk.inj_iff],
  split,
  { simp_rw [StreamState.now', Stream.mul.valid.comm] },
  split,
  { exact StreamState.mul.now'.index.comm _ _ },
  { simp_rw [StreamState.now', Stream.mul_ready, Stream.mul.ready.comm] }
end

lemma mul.invalid (a : StreamExec σ₁ ι α) (b : StreamExec σ₂ ι α) :
¬ a.valid ∨ ¬ b.valid → ¬ (a.mul b).valid := λ d,
begin
  cases d;
  simp [d],
end

def Stream.reduced' (q : Stream σ ι α) : Prop :=
∀ {s t} (hs : q.valid s) (ht : q.valid t), q.ready s → q.ready t → q.index s hs = q.index t ht → s = t

class Stream.is_simple (q : Stream σ ι ρ) : Prop :=
(monotonic : ∀ {r} (h : q.valid r), StreamState.lag ⟨q, r⟩ ⟨q, q.next r h⟩)
(reduced : ∀ {s t} (hs : q.valid s) (ht : q.valid t), q.ready s → q.ready t → q.index s hs = q.index t ht → s = t)

@[simp] def StreamExec.is_simple : Prop := q.stream.is_simple

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

@[simp] lemma invalid_succ_eq : ¬ a.valid → a.succ.valid = ff :=
λ h, begin simp [succ], split_ifs, simp [StreamExec.valid], simpa using h end

lemma succ_bound_valid' {s : Stream σ ι α} {σ₀ : σ} {n : ℕ} (h : s.bound_valid n σ₀)
  (hv : s.valid σ₀) : s.bound_valid (n - 1) (s.next σ₀ hv) :=
by { induction h, { trivial, }, assumption, }

lemma succ_bound_valid (h : a.bound_valid) : a.succ.bound_valid :=
begin
  simp [StreamExec.bound_valid] at *,
  split_ifs with H,
  { exact succ_bound_valid' h H, },
  { exact Stream.bound_valid.start _ H, },
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
    simpa [StreamExec.bound_valid, *] using ha },
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
  { intro, simpa [StreamExec.bound_valid, *] using hb },
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
  { apply bound_valid.start, simp [StreamExec.bound_valid, *] at * },
  { apply bound_valid.start, simp [StreamExec.bound_valid, *] at * },
  { apply bound_valid.start, simp [StreamExec.bound_valid, *] at * },
  {
    cases em a.valid; cases em b.valid,
    { simp only [StreamExec.mul_bound, StreamExec.bound_valid, *],
      have : (a ⋆ b).valid, { simp, split; assumption },
      apply bound_valid.step this,
      simp only [delta_succ],
      cases em (a ⊑ b) with ale nale,
      { rw le_succ_left,
        change bound_valid (n₁_n.succ + n₂_n) (a.succ ⋆ b),
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
    { apply bound_valid.start, simp [StreamExec.valid, *] at * },
    { apply bound_valid.start, simp [StreamExec.valid, *] at * },
    { apply bound_valid.start, simp [StreamExec.valid, *] at * } }
end

lemma prod_le_iff {α₁ β₁} [has_lt α₁] [has_le β₁] (a b : α₁ ×ₗ β₁) :
  a ≤ b ↔
    a.1 < b.1 ∨
    a.1 = b.1 ∧ a.2 ≤ b.2 := prod.lex_def _ _

lemma bool_not_iff (a b : bool) : !a = !b ↔ a = b :=
  by cases a; cases b; simp

lemma mul.mono.a_lags_b {a : Stream σ₁ ι α} {b : Stream σ₂ ι α}
  [ha : a.is_simple] [hb : b.is_simple]
  {r} (h : (a.mul b).valid r) :
  (StreamState.mk a r.1) ⊑ₛ (StreamState.mk b r.2) →
  (StreamState.mk (a.mul b) r) ⊑ₛ (StreamState.mk (a.mul b) (a.next r.1 h.1, r.2)) := begin

  intro a_lags,
  cases h with ha_valid hb_valid,
  let r' := (a.next r.fst _, r.snd),
  have a_mono := is_simple.monotonic ha_valid,
  simp only [StreamState.lag, StreamState.to_order_tuple, StreamState.now', bool_not_iff] at ⊢ a_mono a_lags,

  rw prod_le_iff at a_lags,
  cases a_lags with ab_valid_lt a_lags,
  { -- a is valid but b is invalid (impossible case)
    revert ab_valid_lt,
    simp only [bool.lt_iff, bool.of_to_bool_iff, to_bool_iff, and_imp],
    intros _ hb_invalid, from absurd hb_valid hb_invalid
  },

  rw prod_le_iff at a_mono,
  cases a_mono with valid_lt hh,
  { -- a went from valid to invalid
    left, simpa only [hb_valid, Stream.mul_valid, and_true] using valid_lt
  },

  cases hh with valid_eq hh,
  replace valid_eq : a.valid r.fst ↔ a.valid (a.next r.fst ha_valid) :=
    by simpa only [bool_not_iff, bool.of_to_bool_iff, bool.to_bool_not, bool.to_bool_eq] using valid_eq,

  have ha_valid' : a.valid (a.next r.fst _) := valid_eq.mp ha_valid,

  rw prod_le_iff at |- hh,
  right, rw prod_le_iff,

  split,
  { -- Since a's validity did not change,
    -- (a.mul b)'s validity must not change either.
    simp only [bool.of_to_bool_iff, bool.to_bool_eq, not_iff_not],

    change (a.mul b).valid r ↔ (a.mul b).valid r',
      simp only [Stream.mul_valid],
      split; rw and_imp; intros _ h; split; assumption'
  },

  cases hh with idx_lt hh,
  { -- a's index increased
    rw prod_le_iff at a_lags,
    split_ifs at ⊢ idx_lt,
    { -- a and b remain valid.
      rw with_top.coe_eq_coe at ⊢,
      rw with_top.coe_lt_coe at ⊢ idx_lt,
      cases em (b.index r.snd _ < a.index (a.next r.fst _) _) with idx'_gt idx'_le,
      { -- a's new index > b's
        left,
        show (a.mul b).index r _ < (a.mul b).index r' _,
          simp only [Stream.mul_index, with_top.coe_lt_coe, max_lt_iff],
          split; apply lt_max_iff.mpr; left; assumption
      },
      { -- a's new index ≤ b's
        right,
        simp only [not_lt] at idx'_le,
        simp only [bool.le_iff_imp, bool.of_to_bool_iff],
        split,

        show (a.mul b).index r _ = (a.mul b).index r' _,
          simp only [Stream.mul_index, with_top.coe_eq_coe],
          rw max_eq_right idx'_le,
          rw max_eq_right (has_le.le.trans (le_of_lt idx_lt) idx'_le),

        show (a.mul b).ready r → (a.mul b).ready r',
          suffices : ¬(a.mul b).ready r,
            intro h, from absurd h this,
          simp only [Stream.mul_ready],
          have : a.index r.fst _ < b.index r.snd _ :=
            has_lt.lt.trans_le idx_lt idx'_le,
          intro h, from absurd h.index (ne_of_lt this),
      }
    },

    -- Various impossible cases (either a or b is invalid).
    all_goals {
      { simp only [Stream.mul_index, Stream.mul_valid, not_and] at h_1,
        from absurd hb_valid (h_1 ha_valid') }
      <|>
      { simp only [Stream.mul_index, Stream.mul_valid, not_and] at h,
        from absurd hb_valid (h ha_valid) }
      <|>
      contradiction
    }
  },

  right,
  cases hh with idx_eq ready_le,
  { -- a became ready or stayed the same
    simp only [bool_not_iff, bool.le_iff_imp, bool.of_to_bool_iff] at ⊢ idx_eq ready_le,
    split_ifs at ⊢ idx_eq ready_le,
    { -- a and b remain valid
      rw with_top.coe_eq_coe at ⊢ idx_eq,
      split,
      show (a.mul b).index r _ = (a.mul b).index r' _,
        simp only [Stream.mul_index, idx_eq],

      show (a.mul b).ready r → (a.mul b).ready r',
        simp only [Stream.mul_ready],
        intro prev_mul_ready,
        cases prev_mul_ready.ready with ha_ready hb_ready,

        have ha_ready' : a.ready (a.next r.fst _) := ready_le ha_ready,
        exact {
          valid := ⟨ha_valid', hb_valid⟩,
          ready := ⟨ha_ready', hb_ready⟩,
          index := begin
            have := prev_mul_ready.index,
            transitivity; { symmetry, assumption } <|> assumption
          end,
        }
    },

    -- Various impossible cases (either a or b is invalid).
    all_goals {
      { simp only [Stream.mul_index, Stream.mul_valid, not_and] at h_1,
        from absurd hb_valid (h_1 ha_valid') }
      <|>
      { simp only [Stream.mul_index, Stream.mul_valid, not_and] at h,
        from absurd hb_valid (h ha_valid) }
      <|>
      contradiction
    }
  }
end

instance hmul.is_simple
(a : Stream σ₁ ι α) (b : Stream σ₂ ι α)
[ha : a.is_simple] [hb : b.is_simple] : (a.mul b).is_simple :=
{ monotonic := begin
    intros r h,
    obtain ⟨s₁, s₂⟩ := r,
    obtain ⟨ha_valid, hb_valid⟩ := h,
    rw Stream.mul_next,

    split_ifs with lags,
    { -- a lags b
      apply mul.mono.a_lags_b, refine ⟨ha_valid, hb_valid⟩, assumption },

    { -- b (strictly) lags a; weaken the hypothesis first to reuse mul.mono.a_lags_b
      have := le_of_lt (not_le.mp lags),
      simp_rw [StreamState.lag, mul.to_order_tuple.comm a b],
      apply mul.mono.a_lags_b,
      { exact ⟨hb_valid, ha_valid⟩ },
      { assumption }
    }
  end,

  reduced :=
  begin
    intros s t hs ht ready_s ready_t eq,
    cases ready_s,
    cases ready_t,

    simp only [(*), Stream.mul] at hs ht,
    simp [Stream.mul, *, max_idem.idempotent] at eq,

    ext,
    { apply @is_simple.reduced _ _ _ _ _ ha; simp [*] },
    { apply @is_simple.reduced _ _ _ _ _ hb; simp [*] },
  end
}

#check primitives.range 2

instance primitives.range.is_simple (n : ℕ) : (primitives.range n).is_simple := {
  monotonic := begin
    intros ctr h_valid,
    simp only [StreamState.lag, StreamState.to_order_tuple, StreamState.now', prod_le_iff],
    cases em (n ≤ ctr + 1),
    { left,
      simp only [primitives.range] at ⊢ h_valid,
      simp only [bool.lt_iff],
      split; simpa },
    { right, split,
      { simp only [primitives.range] at ⊢ h_valid,
        simp [h_valid, lt_of_not_le h] },
      { left, split_ifs,
        { simp [with_top.coe_lt_coe, primitives.range] },
        { apply with_top.coe_lt_top },
        { contradiction },
        { apply with_top.coe_lt_top } } }
  end,

  reduced := begin
    intros s t hs ht ready_s ready_t eq,
    cases ready_s,
    cases ready_t,

    simp only [primitives.range] at eq,
    assumption
  end,
}

example : (primitives.range 2).is_simple := infer_instance
example : ((primitives.range 2).mul (primitives.range 3)).is_simple := by apply_instance
example : (((primitives.range 2).mul (primitives.range 3)).mul (primitives.range 4)).is_simple := by apply_instance

variables
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

@[simp] lemma not_ready_eval₀_zero : ¬ s.ready → s.eval₀' = 0 :=
begin
  intro n,
  simp [eval₀', n],
end

@[simp] lemma not_ready_mul_eval₀_zero_l : ¬ a.ready → (a ⋆ b).eval₀' = 0 :=
begin
  intro n,
  simp [eval₀'],
  rintro ⟨_, ⟨_, ⟨_,_⟩, _⟩⟩, contradiction,
end

@[simp] lemma not_ready_mul_eval₀_zero_r : ¬ b.ready → (a ⋆ b).eval₀' = 0 :=
begin
  intro n,
  simp [eval₀'],
  rintro ⟨_, ⟨_, ⟨_,_⟩, _⟩⟩, contradiction,
end

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

@[simp] lemma eval_steps_zero' : eval_steps' 0 a = 0 := rfl

@[simp] lemma not_bool_eq : ∀ {a b : bool}, !a = !b ↔ a = b := by { intros, cases a; cases b; dec_trivial }

@[simp] lemma StreamState.order_eq_iff (a : StreamState σ₁ ι α) (b : StreamState σ₁ ι β) :
a.to_order_tuple = b.to_order_tuple ↔
a.valid = b.valid ∧ a.now'.index = b.now'.index ∧ a.ready = b.ready :=
by { simp [StreamState.to_order_tuple, StreamState.now'], }

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

@[simp] lemma is_simple_succ_is_simple : q.succ.is_simple ↔ q.is_simple := iff.rfl

section algebra
open StreamState

@[simp] lemma lt_mul_eval₀ : a ⊏ b → a.eval₀' * b.eval₀' = 0 :=
begin
intro lt,
simp [eval₀'],
split_ifs with ha hb,
{ suffices : a.to_StreamState.stream.index a.to_StreamState.state ha.1 ≠ b.to_StreamState.stream.index b.to_StreamState.state hb.1,
  { ext,
    rw finsupp.mul_apply,
    simp [finsupp.single],
    intros e1 e2, simp [e1, e2] at this,
    contradiction },
  {
    intro eq,
    have := ha.1,
    have := ha.2,
    have := hb.1,
    have := hb.2,
    simp [StreamExec.valid, StreamExec.ready] at *,
    simp [StreamExec.lag_lt, StreamExec.to_order_tuple, StreamState.to_order_tuple, StreamState.now'] at lt,
    simp [to_bool_tt, *] at lt,
    exact lt
  }
},
{ simp },
{ simp },
{ simp },
end

@[simp] lemma lt_mul_eval₀_r : b ⊏ a → a.eval₀' * b.eval₀' = 0 :=
begin
intro lt,
simp [eval₀'],
split_ifs with ha hb,
{ suffices : a.to_StreamState.stream.index a.to_StreamState.state ha.1 ≠ b.to_StreamState.stream.index b.to_StreamState.state hb.1,
  { ext,
    rw finsupp.mul_apply,
    simp [finsupp.single],
    intros e1 e2, simp [e1, e2] at this,
    contradiction },
  {
    intro eq,
    have := ha.1,
    have := ha.2,
    have := hb.1,
    have := hb.2,
    simp [StreamExec.valid, StreamExec.ready] at *,
    simp [StreamExec.lag_lt, StreamExec.to_order_tuple, StreamState.to_order_tuple, StreamState.now'] at lt,
    simp [to_bool_tt, *] at lt,
    exact lt
  }
},
{ simp },
{ simp },
{ simp },
end

variables {a}
lemma succ_squb : a.is_simple → a ⊑ a.succ := begin
intro h,
cases h with mono _,
cases em a.valid with h h,
{ simp only [*, succ],
  exact mono h },
{ simp only [*, succ],
  change a≤a,
  refl }
end
variables (a)

@[simp] lemma lt_mul_eval {n} (hb : b.is_simple) :
a ⊏ b → a.eval₀' * b.eval_steps' n = 0 :=
begin
  intro lt,
  unfreezingI { induction n generalizing b },
  { simp [*] },
  simp [eval_steps', left_distrib, *],
  apply n_ih,
  { simpa [*] },
  { exact lt_of_lt_of_le lt (succ_squb hb) }
end

@[simp] lemma lt_mul_eval_r {n} (ha : a.is_simple) :
b ⊏ a → a.eval_steps' n * b.eval₀' = 0 :=
begin
  intro lt,
  unfreezingI { induction n generalizing a },
  { simp [*] },
  simp [eval_steps', right_distrib, *],
  apply n_ih,
  { simpa [*] },
  { exact lt_of_lt_of_le lt (succ_squb ha) }
end

@[simp] lemma order_eq_ready_iff (h : a.to_order_tuple = b.to_order_tuple) : (a.ready ↔ b.ready) :=
by simp [StreamExec.to_order_tuple, StreamState.to_order_tuple, StreamExec.ready, StreamState.now', *] at *

@[simp] lemma order_eq_valid_iff (h : a.to_order_tuple = b.to_order_tuple) : (a.valid ↔ b.valid) :=
by simp [StreamExec.to_order_tuple, StreamState.to_order_tuple, StreamExec.valid, StreamState.now', *] at *

-- @[simp] lemma reduced_mul_succ' {n} (ha : a.is_simple) (hb : b.is_simple) (bv : b.bound_valid) :
-- a ⊑ b → a.eval₀' * b.succ.eval_steps' n = 0 := sorry

@[simp] lemma reduced_mul_succ2 {n} (hb : b.is_simple) (bv : b.bound_valid) :
a ⊑ b → a.eval₀' * b.succ.eval_steps' n = 0 :=
begin
  intro le,
  cases em a.valid with ha ha; cases em a.ready,
  {
    { suffices : a ⊏ b.succ,
      { rw [lt_mul_eval _ _ _ this],
        { simpa [succ] } },
      { cases em (a.to_order_tuple = b.to_order_tuple) with eq eq,
        {
          apply lt_of_le_of_lt le (reduced_ready_progress _ _ bv hb _),
          { rw [← order_eq_valid_iff a _ eq], assumption },
          { rw [← order_eq_ready_iff a _ eq], assumption },
        },
        {
          simp only [StreamExec.lag] at le,
          simp [le_iff_eq_or_lt] at le,
          cases le, contradiction,
          simp only [StreamExec.lag_lt] at |-,
          apply lt_of_lt_of_le le,
          apply succ_squb, assumption,
        },
      }
  } },
  { simp [*] },
  { simp [*] },
  { simp [*] },

end.

lemma mul_eval₀ :
(a ⋆ b).eval₀'  = a.eval₀' * b.eval₀' :=
begin
cases em a.valid with ha; cases em b.valid with hb; cases em a.ready; cases em b.ready,
{ cases em (a.stream.index a.state ha = b.stream.index b.state hb),
  { have : (a ⋆ b).ready := ⟨⟨ha, hb⟩, ⟨h, h_1⟩, h_2⟩,
    simp [*, eval₀'],
    { ext,
      simp [finsupp.mul_apply, finsupp.single],
      split_ifs,
      refl,
      refl,
    },
  },
  { suffices : ¬ (a ⋆ b).ready,
    { have : (a ⋆ b).valid := ⟨ha, hb⟩,
      simp only [*, eval₀'],
      ext,
      rw finsupp.mul_apply,
      simp [finsupp.single],
      split_ifs with h_3 h_4,
      rw h_3 at h_2, rw h_4 at h_2, contradiction,
      refl, refl },
    rintro ⟨_, _, h⟩, simp [(⋆)] at h, rw h at h_2, contradiction,
} },

all_goals { simp [*] },
end

end algebra

-- @[simp] lemma reduced_mul_eval_l (ha : a.is_simple) (hb : b.is_simple) (vb : b.bound_valid) :
-- a ⊑ b → (a ⋆ b).eval₀'  = a.eval₀' * b.eval' :=
-- begin
--   intros le,
--   simp,
--   generalize h : b.bound = n,
--   unfreezingI { induction n generalizing b },
--   { simp at h, suffices : ¬ b.valid,
--     { simp [this] },
--     { simpa [bound_valid, h] using vb } },
--   { simp [eval_steps', left_distrib], suffices : a ⊑ b.succ, simp [*],
--     have := succ_squb hb,
--     simp [StreamExec.lag, StreamExec.lag_lt] at le this |-,
--     exact le_trans le this }
-- end

@[simp] lemma reduced_mul_eval_r (ha : a.is_simple) (hb : b.is_simple) (va : a.bound_valid) :
b ⊏ a → (a ⋆ b).eval₀' = a.eval' * b.eval₀' :=
begin
  intros le,
  simp,
  generalize h : a.bound = n,
  unfreezingI { induction n generalizing a },
  { simp at h, suffices : ¬ a.valid,
    { simp [this] },
    { simpa [bound_valid, h] using va } },
  { simp [eval_steps', right_distrib], suffices : b ⊏ a.succ, simp [*],
    have := succ_squb ha,
    simp [StreamExec.lag, StreamExec.lag_lt] at le this |-,
    exact lt_of_lt_of_le le this }
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
      { simp [*, eval_steps', right_distrib, left_distrib, mul_eval₀], abel, },
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
