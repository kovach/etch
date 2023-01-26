import verification.stream_props

variables {α ι : Type}

section streams

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

variables {s : Stream ι α} {w : set ι}

@[simp]
private lemma substream.next'_eq {x : s.σ} :
(substream s w).valid x → (substream s w).next' x = s.next' x :=
λ h, by rw [Stream.next'_val h, substream_next, Stream.next'_val]

private lemma substream.valid_subsumes {n : ℕ} {x : s.σ} :
(substream s w).valid ((substream s w).next'^[n] x) → s.valid (s.next'^[n] x) :=
begin
  induction n with n ih generalizing x,
  { simp only [function.iterate_zero, substream_valid],
    exact Exists.fst },
  { intro h,
    have hxv := Stream.next'_valid' _ h,
    rw [function.iterate_succ_apply] at h,
    simpa [hxv] using ih h }
end

private lemma substream.bound_valid {B : ℕ} {x : s.σ} :
s.bound_valid B x → ∀ w, (substream s w).bound_valid B x :=
begin
  simp_rw bound_valid_iff_next'_iterate,
  induction B with n ih generalizing x,
  { simp_rw [function.iterate_zero_apply, substream_valid, not_exists],
    intros; contradiction },
  { intros hnv w,
    exact mt substream.valid_subsumes hnv }
end

end streams

section stream_exec

@[simps]
def Stream.split (r : ι → ι → Prop) (s : StreamExec ι α) : Stream (quot r) (StreamExec ι α) :=
{ σ := s.stream.σ × option (quot r), -- keep track of the last element seen
  valid := λ p, s.stream.valid p.1,
  -- TODO: instead of making the stream merely non-ready while skipping,
  -- we should change next to recurse until it reaches the next window.
  -- Will need to prove well-foundedness using bound_valid.
  ready := λ p, s.stream.ready p.1 ∧
                s.stream.bound_valid s.bound p.1 ∧ -- this is weird
                ∃ hv, p.2 ≠ quot.mk r (s.stream.index p.1 hv),
  next := λ p h, (s.stream.next p.1 h, quot.mk r (s.stream.index p.1 h)),
  index := λ p h, quot.mk r (s.stream.index p.1 h),
  value := λ p h, {
    stream := substream s.stream (r (s.stream.index p.1 h.2.2.fst)),
    state := p.1,
    bound := s.bound,
    bound_valid := substream.bound_valid h.2.1 _,
  },
}

variables {r : ι → ι → Prop} {s : StreamExec ι α}

lemma Stream.split_state {prev : option (quot r)} :
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

variables [add_comm_monoid α]

/-
TODOs:
- do we need `r` to be an equivalence relation?
- do we need a no-lookback hypothesis for `s` and `r`?
 -/

theorem StreamExec.split.spec :
finsupp.sum_range (StreamExec.eval <$₂> StreamExec.split r s).eval = s.eval :=
sorry

end stream_exec
