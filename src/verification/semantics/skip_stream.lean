import verification.semantics.stream_props

noncomputable theory
open_locale classical

-- skip s i : if current index < i, must advance; may advance to first ready index ≥ i.
-- succ s i : if current index ≤ i, must advance; may advance to first ready index > i.

/-
if current index < (i, b), must advance; may advance up to first ready index ≥ (i, b) 
-/

/-- Returns the set of `q` that `s` could skip to if the current state is `x` 
  and it is supposed to skip past `(i, b)` -/
def skip_set {ι α : Type*} [linear_order ι] (s : Stream ι α) (x : s.σ) (i : ι) (b : bool) : set s.σ :=
{q | ∃ (n : ℕ), q = (s.next'^[n] x) ∧ (0 < n ↔ s.to_order x ≤ (i, b)) ∧
      ∀ m, 0 < m → m < n → s.valid (s.next'^[m] x) → s.ready (s.next'^[m] x) → s.index' (s.next'^[m] x) < i}

structure SkipStream (ι α : Type*) [linear_order ι] extends Stream ι α :=
(skip : Π x, valid x → ι → bool → σ)
(hskip : ∀ x hx i b, skip x hx i b ∈ skip_set _ x i b)

variables {ι : Type} {α : Type*} [linear_order ι]

@[simp] noncomputable def SkipStream.eval_skip [add_zero_class α] (s : SkipStream ι α) : ℕ → s.σ → (ι →₀ α)
| 0 q := 0
| (n + 1) q := if h₁ : s.valid q then (SkipStream.eval_skip n (s.skip q h₁ (s.index q h₁) (s.ready q))) + (s.eval₀ _ h₁) else 0 

/-- The number of steps a stream would skip at index `(i, b)` -/
noncomputable def SkipStream.nskip (s : SkipStream ι α) (q : s.σ) (h : s.valid q) (i : ι) (b : bool) : ℕ :=
  (s.hskip q h i b).some

lemma SkipStream.skip_eq (s : SkipStream ι α) (q : s.σ) (h : s.valid q) (i : ι) (b : bool) :
  s.skip q h i b = (s.next'^[s.nskip q h i b] q) := (s.hskip q h i b).some_spec.1

lemma SkipStream.advance_iff (s : SkipStream ι α) (q : s.σ) (h : s.valid q) (i : ι) (b : bool) :
  0 < s.nskip q h i b ↔ s.to_order q ≤ (i, b) := (s.hskip q h i b).some_spec.2.1

/-- All skipped values are less than `i` -/
lemma SkipStream.lt_of_skipped (s : SkipStream ι α) (q : s.σ) (h : s.valid q) (i : ι) (b : bool)
  (m : ℕ) (h₁m : 0 < m) (h₂m : m < s.nskip q h i b) (h₃ : s.valid (s.next'^[m] q)) (h₄ : s.ready (s.next'^[m] q)) :
  s.index' (s.next'^[m] q) < i := (s.hskip q h i b).some_spec.2.2 m h₁m h₂m h₃ h₄

lemma SkipStream.not_ready_of_skipped_of_monotonic (s : SkipStream ι α) (hs : s.monotonic) (q : s.σ) (h : s.valid q) (b : bool)
  (m : ℕ) (h₁m : 0 < m) (h₂m : m < s.nskip q h (s.index q h) b) (h₃ : s.valid (s.next'^[m] q)) :
  ¬s.ready (s.next'^[m] q) := λ h₄,
begin
  refine (s.lt_of_skipped q h _ b m h₁m h₂m h₃ h₄).not_le _,
  simpa [Stream.index'_val h] using hs.le_index_iterate q m,
end

/-- If all skipped states are non-ready, then the eval's are equal -/
theorem Stream.eval₀_skip_eq [add_comm_monoid α] (s : Stream ι α) (q : s.σ)
  (n : ℕ) (hn : ∀ m < n, s.valid (s.next'^[m] q) → ¬s.ready (s.next'^[m] q)) :
  s.eval_steps n q = 0 :=
begin
  induction n with n ih generalizing q, { simp, },
  simp only [Stream.eval_steps, dite_eq_right_iff, forall_true_left],
  intro h,
  simp only [Stream.eval₀, (show ¬s.ready q, from hn 0 (nat.zero_lt_succ _) h), dif_neg, not_false_iff, add_zero],
  apply ih,
  intros m hm, specialize hn (m + 1) (nat.succ_lt_succ hm),
  simpa [Stream.next'_val h] using hn,
end

theorem Stream.eval₀_skip_eq' [add_comm_monoid α] (s : Stream ι α) (q : s.σ) (h : s.valid q)
  (n : ℕ) (hn : n ≠ 0) (hn : ∀ m, 0 < m → m < n → s.valid (s.next'^[m] q) → ¬s.ready (s.next'^[m] q)) :
  s.eval_steps n q = s.eval₀ q h :=
begin
  cases n, {  contradiction, },
  have := s.eval₀_skip_eq (s.next q h) n _,
  { simp [Stream.eval_steps, h, this], },
  intros m hm,
  simpa [Stream.next'_val h] using hn (m + 1) m.zero_lt_succ (nat.succ_lt_succ hm),
end

theorem SkipStream.eval_skip_eq [add_comm_monoid α] (s : SkipStream ι α) (hs : s.monotonic) (q : s.σ) (n : ℕ) :
  ∃ (m : ℕ), n ≤ m ∧ s.eval_skip n q = s.eval_steps m q :=
begin
  induction n with n ih generalizing q, { refine ⟨0, rfl.le, _⟩, simp, },
  by_cases h : s.valid q, swap,
  { refine ⟨n + 1, rfl.le, _⟩, simp [h], },
  rcases ih (s.skip q h (s.index q h) (s.ready q)) with ⟨m, hm₁, hm₂⟩,
  have : 0 < s.nskip q h (s.index q h) (s.ready q),
  { rw SkipStream.advance_iff, refine le_of_eq _, ext : 1; simp [Stream.index'_val h], },
  refine ⟨s.nskip q h (s.index q h) (s.ready q) + m, _, _⟩,
  { rw nat.succ_le_iff, refine lt_of_le_of_lt hm₁ _, simpa, },
  rw [s.eval_steps_add, s.eval₀_skip_eq' q h, ← SkipStream.skip_eq],
  { simp [h, add_comm, hm₂], }, { rwa ← zero_lt_iff, },
  exact s.not_ready_of_skipped_of_monotonic hs q h _,
end

