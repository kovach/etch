import base

open iter

instance : linear_order unit := linear_order.lift (λ _, 0) (by dec_trivial)

def mk_single {V} (v : V) : stream bool unit V :=
  { q := false
  , iter :=
    { δ    := λ s, match s with | ff := tt | tt := tt end
    , emit := λ s, match s with | ff := some (⟨⟩, some v) | tt := none end
    }
  }

section params_unary
declare one

def iota (k : ℕ): iter (fin k.succ) (fin k) ℕ :=
{ δ := λ n, if h : n.val < k then ⟨n.val.succ,  nat.succ_lt_succ h⟩ else n
, emit := λ n, if h : n.val < k then some (⟨n.val, h⟩, n.val) else none
}

def iota' {k : ℕ} : iter (fin k.succ) (fin k) (fin k) :=
{ δ := λ n, if h : n.val < k then ⟨n.val.succ,  nat.succ_lt_succ h⟩ else n
, emit := λ n, if h : n.val < k then some (⟨n.val, h⟩, some ⟨n.val, h⟩) else none
}

def mk_iota {k : ℕ} : stream (fin k.succ) (fin k) (fin k) := ⟨ 0, iota' ⟩

def stream.imap {α β} (f : α → β) : stream σ α V → stream σ β V := λ s,
let i := s.iter in {
  q := s.q,
  iter :=
    { δ := i.δ
    , emit := λ s, match i.emit s with | none := none | some (i, v) := some (f i, v) end
    }
}

def stream.vmap {α β} (f : α → β) : stream σ I α → stream σ I β := λ s,
let i := s.iter in {
  q := s.q,
  iter :=
    { δ := i.δ
    , emit := λ s, match i.emit s with | none := none | some (i, v) := some (i, v.map f) end
    }
}

def map {α β} (f : α → β) : stream σ I α → stream σ I β := stream.vmap f

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

--class it (σ t1 t2 : Type) := (iter : iter σ t1 t2)
--instance iota_it   {k : ℕ} : it (fin k.succ) (fin k) (fin k) := ⟨ iota' ⟩
--instance dense_it  {k : ℕ} : it (fin k.succ × (fin k → V)) (fin k) V := ⟨dense⟩
--instance sparse_it {k : ℕ} : it (fin k.succ × (fin k → I) × (fin k → V)) I V := ⟨sparse⟩

def mk_broad (k : ℕ) {α : Type} : α → stream (fin k.succ) (fin k) α :=
λ v, mk_iota.vmap (λ _, v)

end params_unary
section params_binary
declare two
declare add

def add_option : option V₁ → option V₂ → option V₃
| (none) (none) := none
| (none) (some v₂) := some $ add 0 v₂
| (some v₁) (none) := some $ add v₁ 0
| (some v₁) (some v₂) := some $ add v₁ v₂

def add_emit : σ₁ × σ₂ → emit_type I V₃ | ⟨s, t⟩ :=
  match (a.emit s), (b.emit t) with
  | some (i₁, v₁), some (i₂, v₂) :=
    if i₁ = i₂ then some (i₁, add_option add v₁ v₂) else
    if i₁ < i₂ then some (i₁, add_option add v₁ none) else
                    some (i₂, add_option add none v₂)
  | none, some (i₂, v₂) := some (i₂, add_option add none v₂)
  | some (i₁, v₁), none := some (i₁, add_option add v₁ none)
  | _, _ := none
  end

-- todo
def lags (a : iter σ₁ I V₁) (b : iter σ₂ I V₂) : σ₁ × σ₂ → bool | ⟨s, t⟩ :=
  if a.ι s < b.ι t then true else if a.ι s > b.ι t then false else option.is_none $ a.ν s

#check @add_emit
def add_iter (a : iter σ₁ I V₁) (b : iter σ₂ I V₂) : iter (σ₁×σ₂) I V₃ :=
{ δ := λ ⟨s,t⟩, if a.ι s < b.ι t then (a.δ s,t) else if a.ι s > b.ι t then (s, b.δ t) else (a.δ s, b.δ t)
, emit := add_emit a b add,
}

def mk_add (a : stream σ₁ I V₁) (b : stream σ₂ I V₂) : stream (σ₁×σ₂) I V₃ :=
⟨ (a.q, b.q), add_iter add a.iter b.iter ⟩

local infix `+'`:50 := add_iter add

section lemmas

def add_iter_terminal {a : iter σ₁ I V₁} {b : iter σ₂ I V₂} {s₁ s₂} : a.terminal s₁ → b.terminal s₂ → (a+' b).terminal (s₁, s₂) := λ h1 h2,
begin
unfold terminal at *,
simp only [ι, add_iter, add_emit, h1, h2],
simp only [ι_top_emit_none.1 h1, ι_top_emit_none.1 h2],
refl,
--split_ifs, repeat {refl},
end

end lemmas

end params_binary
section params_binary
declare two
declare mul

def mul_emit : σ₁ × σ₂ → emit_type I V₃ | ⟨s, t⟩ :=
  match (a.emit s), (b.emit t) with
  | some (i₁, some v₁), some (i₂, some v₂) := if i₁ = i₂ then some (i₁, mul v₁ v₂) else some (max i₁ i₂, none)
  | some (i₁, _), some (i₂, _) := some (max i₁ i₂, none)
  | _, _ := none
  end

def mul_iter (a : iter σ₁ I V₁) (b : iter σ₂ I V₂) : iter (σ₁×σ₂) I V₃ :=
{ δ := λ ⟨s,t⟩, if a.ι s < b.ι t then (a.δ s,t) else if a.ι s > b.ι t then (s, b.δ t) else (a.δ s, b.δ t)
, emit := mul_emit a b mul,
}

def mk_mul (a : stream σ₁ I V₁) (b : stream σ₂ I V₂) : stream (σ₁×σ₂) I V₃ :=
⟨ (a.q, b.q), mul_iter mul a.iter b.iter ⟩

def flatten' [has_top I₂] : iter σ₁ I₁ (stream σ₂ I₂ V) →
iter (σ₁ × option (stream σ₂ I₂ V)) (I₁ ×ₗ I₂) V := λ i,
{ δ := λ s,
  let (s₁,s₂) := s in
  let outer := (i.δ s₁, i.ν (i.δ s₁)) in
  match s₂ with
  | none := outer
  | some s₂ := if s₂.ι = ⊤ then outer else (s₁, s₂.δ)
  end
, emit := λ s, let (s₁,s₂) := s in
  match i.emit s₁ with
  | none := none
  | some (i₁, _) :=
    match s₂ with
    | none := some ((i₁, ⊤), none)
    | some s₂ := match s₂.emit with
      | none := some ((i₁, ⊤), none)
      | some (i₂, v) := some ((i₁, i₂), v)
    end
    end
  end
}

def flatten'' [has_top I₂] : iter σ₁ I₁ σ₂ →
iter (σ₁ × option σ₂ × (iter σ₂ I₂ V)) (I₁ ×ₗ I₂) V := λ outer,
{ δ := λ s,
  let (s₁,s₂,inner) := s in
  let outer := (outer.δ s₁, outer.ν (outer.δ s₁), inner) in
  match s₂ with
  | none := outer
  | some s₂ := if inner.ι s₂ = ⊤ then outer else (s₁, inner.δ s₂, inner)
  end
, emit := λ s, let (s₁,s₂,inner) := s in
  match outer.emit s₁ with
  | none := none
  | some (i₁, _) :=
    match s₂ with
    | none := some ((i₁, ⊤), none)
    | some s₂ := match inner.emit s₂ with
      | none := some ((i₁, ⊤), none)
      | some (i₂, v) := some ((i₁, i₂), v)
    end
    end
  end
}

def mk_flatten [has_top I₂] : stream σ₁ I₁ (stream σ₂ I₂ V) →
stream (σ₁ × option (stream σ₂ I₂ V)) (I₁ ×ₗ I₂) V :=
λ s,
  { q    := (s.q, s.iter.ν s.q)
  , iter := flatten' s.iter
  }

def contraction_non_mono [has_top I₂] : stream σ₁ I₁ (stream σ₂ I₂ V) → stream _ I₂ V :=
  stream.imap prod.snd ∘ mk_flatten

end params_binary

/- Notation -/

class hmul (α β : Type) (γ : out_param Type) := (mul : α → β → γ)
instance hmul_of_has_mul {α} [has_mul α] : hmul α α α := ⟨has_mul.mul⟩
instance hmul_stream {α β γ σ₁ σ₂ I : Type} [linear_order I] [h : hmul α β γ]
: hmul (stream σ₁ I α) (stream σ₂ I β) (stream (σ₁×σ₂) I γ) :=
  ⟨mk_mul h.mul⟩

class hadd (α β : Type) (γ : out_param Type) := (add : α → β → γ)
instance hadd_of_has_add {α} [has_add α] : hmul α α α := ⟨has_add.add⟩
instance hadd_stream {α β γ σ₁ σ₂ I : Type} [linear_order I] [has_zero α] [has_zero β] [has_zero γ] [h : hadd α β γ]
: hadd (stream σ₁ I α) (stream σ₂ I β) (stream (σ₁×σ₂) I γ) :=
  ⟨mk_add h.add⟩

infixl ` ** `:70  := hmul.mul
infixl ` * `:70  := hmul.mul
prefix ` ↓ `:60 := mk_flatten
notation ` Σ ` := contraction_non_mono

-- labeled (ordered) indices?
