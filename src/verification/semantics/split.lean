import verification.semantics.stream_props

variables {α ι₁ ι₂ : Type}

section streams

@[simps]
def substream (s : Stream (ι₁ × ι₂) α) (i₁ : ι₁) : Stream ι₂ α :=
{ σ := s.σ,
  valid := λ p, ∃ (h : s.valid p), (s.index p h).1 = i₁,
  ready := λ p, s.ready p,
  next := λ p h, s.next p h.fst,
  index := λ p h, (s.index p h.fst).2,
  value := λ p h, s.value p h,
}

variables {s : Stream (ι₁ × ι₂) α} {i₁ : ι₁}

@[simp] lemma substream.next'_eq {x : s.σ} :
(substream s i₁).valid x → (substream s i₁).next' x = s.next' x :=
λ h, by rw [Stream.next'_val h, substream_next, Stream.next'_val]

lemma substream.valid_subsumes {n : ℕ} {x : s.σ} :
(substream s i₁).valid ((substream s i₁).next'^[n] x) → s.valid (s.next'^[n] x) :=
begin
  induction n with n ih generalizing x,
  { simp only [function.iterate_zero, substream_valid],
    exact Exists.fst },
  { intro h,
    have hxv := Stream.next'_valid' _ h,
    rw [function.iterate_succ_apply] at h,
    simpa [hxv] using ih h }
end

lemma substream.bound_valid {B : ℕ} {x : s.σ} :
s.bound_valid B x → ∀ i₁, (substream s i₁).bound_valid B x :=
begin
  simp_rw bound_valid_iff_next'_iterate,
  induction B with n ih generalizing x,
  { simp_rw [function.iterate_zero_apply, substream_valid, not_exists],
    intros; contradiction },
  { intros hnv _,
    exact mt substream.valid_subsumes hnv }
end

end streams

section stream_exec

structure split_state (s : StreamExec (ι₁ × ι₂) α) :=
(state : s.stream.σ)
(last : option ι₁)
(remaining : ℕ)
(bound_valid : s.stream.bound_valid remaining state)

@[simps]
def Stream.split (s : StreamExec (ι₁ × ι₂) α) : Stream ι₁ (StreamExec ι₂ α) :=
{ σ := split_state s,
  valid := λ p, s.stream.valid p.1,
  ready := λ p, s.stream.ready p.1 ∧
                ∃ hv, p.last ≠ (s.stream.index p.1 hv).1,
  next := λ p h, ⟨s.stream.next p.1 h,
                  (s.stream.index p.1 h).1,
                  p.remaining.pred,
                  show s.stream.bound_valid p.remaining.pred _, by {
                    apply Stream.bound_valid_succ.1,
                    cases hp : p.remaining,
                    { have := p.bound_valid, rw hp at this,
                      cases this, contradiction, },
                    { simpa [hp] using p.bound_valid }
                  }⟩,
  index := λ p h, (s.stream.index p.1 h).1,
  value := λ p h, {
    stream := substream s.stream (s.stream.index p.1 h.2.fst).1,
    state := p.1,
    bound := p.remaining,
    bound_valid := substream.bound_valid p.bound_valid _,
  },
}

variables {s : StreamExec (ι₁ × ι₂) α}

@[simp] lemma Stream.split_next'_state (p : split_state s) :
((Stream.split s).next' p).state = s.stream.next' p.state :=
by { by_cases H : s.stream.valid p.state, { simpa [H] }, { simp [H] } }

@[simp] lemma Stream.split_next'_state' (x : split_state s) (n) :
((Stream.split s).next'^[n] x).state = (s.stream.next'^[n] x.state) :=
begin
  induction n with _ ih generalizing x,
  { simp },
  { simp_rw [function.iterate_succ_apply, ← Stream.split_next'_state],
    exact ih _ }
end

def StreamExec.split (s : StreamExec (ι₁ × ι₂) α) : StreamExec ι₁ (StreamExec ι₂ α) :=
{ stream := Stream.split s,
  state := ⟨s.state, none, s.bound, s.bound_valid⟩,
  bound := s.bound,
  bound_valid := begin
    have bv := s.bound_valid,
    rw bound_valid_iff_next'_iterate at ⊢ bv,
    induction eq : s.bound; simpa [eq] using bv,
  end,
}

variables [add_comm_monoid α]

/-
TODOs:
- do we need a no-lookback hypothesis for `i₁`?
 -/

theorem StreamExec.split.spec (i₁ i₂) :
(StreamExec.eval <$₂> StreamExec.split s).eval i₁ i₂ = s.eval (i₁, i₂) :=
sorry

end stream_exec
