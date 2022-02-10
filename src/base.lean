-- main definition: iter
import algebra
import algebra.group
import algebra.group.defs
import logic.relation
import order.lexicographic

instance i1 (k : ℕ) : has_top (fin k.succ) := ⟨k⟩
-- instance i2 (k : ℕ) : linear_order (fin k) := infer_instance
-- instance i3 {α β: Type*} [linear_order α] [linear_order β] : linear_order (lex α β) := infer_instance

universes u v
variables (α β : Type*)

def emit_type (I V : Type) := option (I × option V)

structure iter (σ I V : Type) :=
  (δ : function.End σ)
  (emit : σ → emit_type I V)

namespace iter

section params_unary
variables {σ I V : Type} [linear_order I] (a : iter σ I V) (s t : σ)

def ι : with_top I := match a.emit s with | none := none | some (i, _) := some i end
def ν :   option V := match a.emit s with | none := none | some (_, v) := v end

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

section semantics
variables [add_monoid V]

def elementary (i : I) (v : V) := λ j, if i = j then v else 0

@[simp] def semantics₁ (s : σ) : I → V :=
  match a.emit s with
  | none := 0
  | some (i, none) := 0
  | some (i, some v) := elementary i v
  end

@[simp] def semantics' : σ → ℕ → I → V
| _ 0 := 0
| s (n+1) := a.semantics₁ s + semantics' (a.δ s) n

notation `⟦` a, s `⟧` := a.semantics' s
notation `⟦` a, s, j `⟧` := a.semantics' s j

example (j : ℕ) : ∀ i:I, ⟦a, s, j⟧ i = ⟦a, s⟧ j i := λ _, rfl

end semantics

lemma ι_top_emit_none {a : iter σ I V} {s} : a.ι s = ⊤ ↔ a.emit s = none := begin
split; intro h1,
{ cases h : a.emit s, exact rfl,
  cases val,
  simp only [ι, h] at h1,
  exfalso, apply option.some_ne_none _ h1 },
{ simp only [ι, h1], refl },
end

@[simp]
theorem terminal_succ_terminal {a : iter σ I V} (m : a.monotonic) (h : a.terminal t) : a.terminal (a.δ t) := begin
simp only [terminal] at *, apply none_top, rw ←h, exact m _ _ (transition.step _) end

@[simp]
theorem emit_none_of_terminal {a : iter σ I V} {t} : a.terminal t → a.emit t = none := begin
intro h, simp only [terminal] at h, exact ι_top_emit_none.1 h,
end

end params_unary

section params_binary
variables {σ₁ σ₂ I V : Type}
[linear_order I]
[add_monoid V]
(a : iter σ₁ I V) (b : iter σ₂ I V)
(s₁ : σ₁) (s₂ : σ₂)

def merge_indexed_values : I×(option V) → I×(option V) → I×(option V)
| (i₁, v₁) (_, v₂) := (i₁, option.lift_or_get (λ v₁ v₂, (v₁ + v₂)) v₁ v₂)
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

section params_binary
variables {V₁ V₂ V₃ : Type} (mul : V₁ → V₂ → V₃)
variables {σ σ₁ σ₂ I I₁ I₂ V : Type}
[linear_order I]
[linear_order I₁]
[linear_order I₂]
(a : iter σ₁ I V₁) (b : iter σ₂ I V₂)
(s₁ : σ₁) (s₂ : σ₂)

def mul_emit : σ₁ × σ₂ → emit_type I V₃ | ⟨s, t⟩ :=
  match (a.emit s), (b.emit t) with
  | some (i₁, some v₁), some (i₂, some v₂) := if i₁ = i₂ then some (i₁, mul v₁ v₂) else none
  | _, _ := none
  end

def mul_iter (a : iter σ₁ I V₁) (b : iter σ₂ I V₂) : iter (σ₁×σ₂) I V₃ :=
{ δ := λ ⟨s,t⟩, if a.ι s < b.ι t then (a.δ s,t) else if a.ι s > b.ι t then (s, b.δ t) else (a.δ s, b.δ t)
, emit := mul_emit mul a b,
}

structure stream (σ I V : Type) :=
  (q : σ)
  (iter : iter σ I V)

def mk_mul (a : stream σ₁ I V₁) (b : stream σ₂ I V₂) : stream (σ₁×σ₂) I V₃ :=
⟨ (a.q, b.q), mul_iter mul a.iter b.iter ⟩

def iota (k : ℕ): iter (fin k.succ) (fin k) ℕ :=
{ δ := λ n, if h : n.val < k then ⟨n.val.succ,  nat.succ_lt_succ h⟩ else n
, emit := λ n, if h : n.val < k then some (⟨n.val, h⟩, n.val) else none
}

def iota' {k : ℕ} : iter (fin k.succ) (fin k) (fin k) :=
{ δ := λ n, if h : n.val < k then ⟨n.val.succ,  nat.succ_lt_succ h⟩ else n
, emit := λ n, if h : n.val < k then some (⟨n.val, h⟩, some ⟨n.val, h⟩) else none
}

def mk_iota {k : ℕ} : stream (fin k.succ) (fin k) (fin k) := ⟨ 0, iota' ⟩

def stream.imap {α β} (f : α → β) : stream σ₁ α V → stream σ₁ β V := λ s,
let i := s.iter in {
  q := s.q,
  iter :=
    { δ := i.δ
    , emit := λ s, match i.emit s with | none := none | some (i, v) := some (f i, v) end
    }
}

def stream.vmap {α β} (f : α → β) : stream σ₁ I α → stream σ₁ I β := λ s,
let i := s.iter in {
  q := s.q,
  iter :=
    { δ := i.δ
    , emit := λ s, match i.emit s with | none := none | some (i, v) := some (i, v.map f) end
    }
}

def dense {k : ℕ} : iter (fin k.succ × (fin k → V)) (fin k) V :=
{ δ := λ s, (iota'.δ s.1, s.2)
, emit := λ s, (iota'.emit s.1).map (λ iv, (iv.1, iv.2.map s.2))
}
#check @dense

def mk_dense {k : ℕ} (f : fin k → V) : stream (fin k.succ × (fin k → V)) (fin k) V :=
  ⟨ (0, f), dense ⟩

def sparse {k : ℕ} : iter (fin k.succ × (fin k → I) × (fin k → V)) I V :=
{ δ := λ s, (iota'.δ s.1, s.2)
, emit := λ s, let (state, ifn, vfn) := s in
  (iota'.emit s.1).map (λ iv, (ifn iv.1, iv.2.map vfn))
}

def mk_sparse {k : ℕ} (ifn : fin k → I) (vfn : fin k → V) : stream (fin k.succ × (fin k → I) × (fin k → V)) I V := ⟨ (0, ifn, vfn), sparse ⟩

#check has_mul
class hmul (α β : Type) (γ : out_param Type) := (mul : α → β → γ)
instance hmul_iter {α β γ σ₁ σ₂ : Type} [h : hmul α β γ] : hmul (iter σ₁ I α) (iter σ₂ I β) (iter (σ₁×σ₂) I γ) :=
  ⟨λ i1 i2, mul_iter h.mul i1 i2⟩
instance hmul_stream {α β γ σ₁ σ₂ : Type} [h : hmul α β γ] : hmul (stream σ₁ I α) (stream σ₂ I β) (stream (σ₁×σ₂) I γ) :=
  ⟨λ i1 i2, mk_mul h.mul i1 i2⟩
instance hmul_of_has_mul {α} [has_mul α] : hmul α α α := ⟨has_mul.mul⟩

class it (σ t1 t2 : Type) := (iter : iter σ t1 t2)

instance iota_it   {k : ℕ} : it (fin k.succ) (fin k) (fin k) := ⟨ iota' ⟩
instance dense_it  {k : ℕ} : it (fin k.succ × (fin k → V)) (fin k) V := ⟨dense⟩
instance sparse_it {k : ℕ} : it (fin k.succ × (fin k → I) × (fin k → V)) I V := ⟨sparse⟩

def stream.δ {σ I V} (s : stream σ I V) : stream σ I V :=
{iter := s.iter, q := s.iter.δ s.q}

def flatten' [has_top I₂] : iter σ₁ I₁ (stream σ₂ I₂ V) →
iter (σ₁ × option (stream σ₂ I₂ V)) (lex I₁ I₂) V := λ i,
{ δ := λ s, let (s₁,s₂) := s in
  match s₂ with
  | none := (i.δ s₁, i.ν (i.δ s₁))
  | some s₂ := if s₂.iter.ι s₂.q = ⊤ then (i.δ s₁, i.ν (i.δ s₁)) else (s₁, s₂.δ)
  end
, emit := λ s, let (s₁,s₂) := s in
  match i.emit s₁ with
  | none := none
  | some (i₁, _) :=
    match s₂ with
    | none := some ((i₁, ⊤), none)
    | some s₂ := match s₂.iter.emit s₂.q with
      | none := some ((i₁, ⊤), none)
      | some (i₂, v) := some ((i₁, i₂), v)
    end
    end
  end
}

def mk_flatten [has_top I₂] : stream σ₁ I₁ (stream σ₂ I₂ V) →
stream (σ₁ × option (stream σ₂ I₂ V)) (lex I₁ I₂) V := λ s,
  { q    := (s.q, s.iter.ν s.q)
  , iter := flatten' s.iter
  }


#check mk_flatten $ mk_dense (λ (i : fin 22), mk_dense (id : fin 4 → fin 4))

def contraction_non_mono [has_top I₂] : stream σ₁ I₁ (stream σ₂ I₂ V) → stream _ I₂ V :=
  stream.imap prod.snd ∘ mk_flatten
#check @contraction_non_mono

def mk_broad (k : ℕ) {α : Type} : α → stream (fin k.succ) (fin k) α :=
λ v, mk_iota.vmap (λ _, v)

infixl ` ** `:70  := hmul.mul
prefix ` ↓ `:60 := mk_flatten

/- ========= Examples ========= -/

def mat (i j : ℕ) (V : Type) := fin i → fin j → V
def const3 (v : V) : mat 3 3 V := λ _ _, v
variables {i j k : ℕ}
(A : mat i j V)
(B : mat j k V)

def C : mat 3 4 ℕ := λ _ _, 2
def D : mat 4 5 ℕ := λ _ _, 3

def m2 (A : fin i → fin j → V) := (mk_dense A).vmap mk_dense

def C' := stream.vmap (stream.vmap $ mk_broad 5) $ m2 C
def D' := mk_broad 3 $ m2 D
def v7 := mk_dense (λ (i : fin 7), 0)
#check mk_mul (*) v7 v7
#check v7 ** v7
#check C'
#check C' ** D'
#check ↓↓ C' ** D'
def CD : stream _ _ _ := mk_flatten $ mk_flatten $ C' ** D'
def CD_mul : stream _ (lex (fin 3) (fin 5)) _ :=
↓ stream.vmap contraction_non_mono (C' ** D')
#check CD
#check CD_mul
#check ↓ contraction_non_mono (C' ** D')
#check ↓ stream.vmap contraction_non_mono (C' ** D')

def stream.semantics [add_monoid V] : stream σ I V → ℕ → I → V
| _ 0 := 0
| s (n+1) := s.iter.semantics₁ s.q + (s.δ).semantics n

#eval (mk_flatten $ mk_flatten $ C').semantics 30 ((1,0),0)

#eval CD.semantics 33 ((0,0),0)

#eval CD_mul.semantics 33 (0,0)

end params_binary

end iter
