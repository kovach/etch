import base

open iter

section params_binary
variables {σ₁ σ₂ I V : Type}
[linear_order I]
[has_add V]
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

def mk_add (a : stream σ₁ I V) (b : stream σ₂ I V) : stream (σ₁×σ₂) I V :=
⟨ (a.q, b.q), add_iter a.iter b.iter ⟩

infix `+'`:50 := add_iter

section lemmas

lemma add_iter_terminal {a : iter σ₁ I V} {b : iter σ₂ I V} {s₁ s₂} : a.terminal s₁ → b.terminal s₂ → (a+' b).terminal (s₁, s₂) := λ h1 h2,
begin
unfold terminal at *,
simp only [ι, add_iter, add_emit, h1, h2],
simp only [ι_top_emit_none.1 h1, ι_top_emit_none.1 h2],
split_ifs, repeat {refl},
end

end lemmas

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

-- fin 1 instead of unit because linear_order is defined
def mk_single (v : V) : stream bool (fin 1) V :=
  { q := false
  , iter :=
    { δ := λ s, match s with | ff := true | tt := true end
    , emit := λ s, match s with | ff := some (0, some v) | tt := none end
    }
  }

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

def map {α β} (f : α → β) : stream σ₁ I α → stream σ₁ I β := stream.vmap f

def dense {k : ℕ} : iter (fin k.succ × (fin k → V)) (fin k) V :=
{ δ := λ s, (iota'.δ s.1, s.2)
, emit := λ s, (iota'.emit s.1).map (λ iv, (iv.1, iv.2.map s.2))
}

def mk_dense {k : ℕ} (f : fin k → V) : stream (fin k.succ × (fin k → V)) (fin k) V :=
  ⟨ (0, f), dense ⟩

def sparse {k : ℕ} : iter (fin k.succ × (fin k → I) × (fin k → V)) I V :=
{ δ := λ s, (iota'.δ s.1, s.2)
, emit := λ s, let (state, ifn, vfn) := s in
  (iota'.emit s.1).map (λ iv, (ifn iv.1, iv.2.map vfn))
}

def mk_sparse {k : ℕ} (ifn : fin k → I) (vfn : fin k → V) : stream (fin k.succ × (fin k → I) × (fin k → V)) I V := ⟨ (0, ifn, vfn), sparse ⟩

class hmul (α β : Type) (γ : out_param Type) := (mul : α → β → γ)
-- instance hmul_iter {α β γ σ₁ σ₂ : Type} [h : hmul α β γ] : hmul (iter σ₁ I α) (iter σ₂ I β) (iter (σ₁×σ₂) I γ) :=
--   ⟨λ i1 i2, mul_iter h.mul i1 i2⟩
instance hmul_stream {α β γ σ₁ σ₂ I : Type} [linear_order I] [h : hmul α β γ] : hmul (stream σ₁ I α) (stream σ₂ I β) (stream (σ₁×σ₂) I γ) :=
  ⟨mk_mul h.mul⟩
instance hmul_of_has_mul {α} [has_mul α] : hmul α α α := ⟨has_mul.mul⟩

class it (σ t1 t2 : Type) := (iter : iter σ t1 t2)

instance iota_it   {k : ℕ} : it (fin k.succ) (fin k) (fin k) := ⟨ iota' ⟩
instance dense_it  {k : ℕ} : it (fin k.succ × (fin k → V)) (fin k) V := ⟨dense⟩
instance sparse_it {k : ℕ} : it (fin k.succ × (fin k → I) × (fin k → V)) I V := ⟨sparse⟩

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


def contraction_non_mono [has_top I₂] : stream σ₁ I₁ (stream σ₂ I₂ V) → stream _ I₂ V :=
  stream.imap prod.snd ∘ mk_flatten

def mk_broad (k : ℕ) {α : Type} : α → stream (fin k.succ) (fin k) α :=
λ v, mk_iota.vmap (λ _, v)

infixl ` ** `:70  := hmul.mul
prefix ` ↓ `:60 := mk_flatten
notation ` Σ ` := contraction_non_mono

/- ========= Examples ========= -/


-- labeled (ordered) indices?

end params_binary
