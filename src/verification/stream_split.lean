import verification.stream_props

section
variables {α ι ι₁ ι₂ : Type}
{n : ℕ} {v : α}

open_locale classical

-- valid as long as the current index is in w
@[simps]
def substream (s : Stream ι α) (w : set ι) : Stream ι α :=
{ σ := s.σ,
  valid := λ p, ∃ h, s.index p h ∈ w,
  ready := λ p, s.ready p,
  next := λ p h, s.next p h.fst,
  index := λ p h, s.index p h.fst,
  value := λ p h, s.value p h,
}

-- lemma substream.state_eq (s : Stream ι α) (w : set ι) :
-- ∀ n x, s.next'^[n] = (substream s w).next'^[n]

lemma substream.bound_valid (s : Stream ι α) (B x) :
s.bound_valid B x → ∀ w, (substream s w).bound_valid B x :=
begin
  simp_rw bound_valid_iff_next'_iterate,
  induction B generalizing x,
  { simp_rw [function.iterate_zero_apply, substream_valid, not_exists],
    intros,
    contradiction },
  { by_cases s.valid (s.next'^[B_n] x); intros hnv w,
    { simp_rw [function.iterate_succ_apply'], sorry },
    { sorry } }
end

@[simps]
def Stream.split (r : ι → ι → Prop) (s : StreamExec ι α) : Stream (quot r) (StreamExec ι α) :=
{ σ := s.stream.σ × option (quot r), -- keep track of the last element seen
  valid := λ p, s.stream.valid p.1,
  ready := λ p, s.stream.ready p.1 ∧
                s.stream.bound_valid s.bound p.1 ∧ -- this is weird
                ∃ hv, p.2 ≠ quot.mk r (s.stream.index p.1 hv),
  next := λ p h, (s.stream.next p.1 h, quot.mk r (s.stream.index p.1 h)),
  index := λ p h, quot.mk r (s.stream.index p.1 h),
  value := λ p h, {
    stream := substream s.stream (r (s.stream.index p.1 h.2.2.fst)),
    state := p.1,
    bound := s.bound,
    bound_valid := begin
      have := h.2.1,
      sorry
    end,
  },
}

lemma Stream.split_state {r} {s : StreamExec ι α} {prev} :
∀ (x: s.stream.σ) n,
((Stream.split r s).next'^[n] (x, prev)).1 = (s.stream.next'^[n] x) :=
begin
  intros,
  induction n with _ ih generalizing x prev,
  { simp },
  { simp_rw function.iterate_succ_apply,
    rw ← ih (s.stream.next' x),
    suffices : (s.stream.next' x, _) = (Stream.split r s).next' (x, prev), by rw this,
    suffices : s.stream.next' x = ((Stream.split r s).next' (x, prev)).1, by ext; simp [this],
    unfold Stream.next',
    split_ifs,
    { dunfold Stream.split, simp },
    { simp } }
end

def StreamExec.split (r : ι → ι → Prop) (s : StreamExec ι α) : StreamExec (quot r) (StreamExec ι α) :=
{ stream := Stream.split r s,
  state := (s.state, none),
  bound := s.bound,
  bound_valid := begin
    have bv := s.bound_valid,
    rw bound_valid_iff_next'_iterate at ⊢ bv,
    induction eq : s.bound,
    { simpa [eq] using bv },
    { simp_rw [Stream.split_valid, Stream.split_state],
      simpa [eq] using bv }
  end,
}

end
