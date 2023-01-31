import data.finsupp.basic
import data.fintype.basic
import logic.equiv.fintype
import logic.function.iterate
import tactic.basic
import verification.stream_props
import verification.finsuppeval

/- ### Definitions -/

variables {α : Type}
{n : ℕ} {v : α}

section

variable [add_zero_class α]

@[simps]
def Stream.replicate (n : ℕ) (v : α) : Stream (fin n) α :=
{ σ := fin n.succ,
  valid := λ i, i.val < n,
  ready := λ _, true,
  next := λ i h, ⟨i.val+1, nat.succ_lt_succ h⟩,
  index := λ i h, ⟨i.val, h⟩,
  value := λ _ _, v,
}

instance Stream.replicate.σ.has_zero : has_zero (Stream.replicate n v).σ :=
⟨⟨0, nat.zero_lt_succ _⟩⟩

/- ### StreamExec -/

lemma Stream.replicate.valid_monotonic {B : ℕ} {r : fin n.succ} :
  (Stream.replicate n v).valid ((Stream.replicate n v).next'^[B.succ] r) →
  (Stream.replicate n v).valid ((Stream.replicate n v).next'^[B] r) :=
begin
  contrapose, intro h,
  rw [function.iterate_succ_apply', Stream.next'],
  split_ifs, assumption,
end

lemma Stream.replicate.next_state {B : ℕ} {r : fin n.succ}
  (hv : (Stream.replicate n v).valid ((Stream.replicate n v).next'^[B] r)) :
  ∃h, ((Stream.replicate n v).next'^[B] r = ⟨r.val + B, h⟩) :=
begin
  induction B,
  { existsi r.property, simp },
  { cases r with r r_prop,
    replace B_ih := B_ih (Stream.replicate.valid_monotonic hv),
    cases B_ih with h B_ih,
    have : ((Stream.replicate n v).next'^[B_n.succ] ⟨r, r_prop⟩) = ((Stream.replicate n v).next' ⟨r + B_n, h⟩),
    { rw [function.iterate_succ_apply', B_ih] },
    rw this at ⊢ hv,
    simp only [Stream.replicate_valid, Stream.next', h] at hv,
    split_ifs at hv,
    { split,
      { simp_rw [Stream.next', Stream.replicate_valid],
        split_ifs, apply fin.eq_of_veq, simp, refl },
      { exact nat.succ_lt_succ h_1 } },
    { contradiction } }
end

def StreamExec.replicate (n : ℕ) (v : α) : StreamExec (fin n) α :=
{ stream := Stream.replicate n v,
  state := 0,
  bound := n.succ,
  bound_valid := begin
    rw [bound_valid_iff_next'_iterate],
    intro h,
    cases Stream.replicate.next_state h with h',
    simpa using h',
  end,
}

/- ### SimpleStream -/

lemma Stream.replicate.reduced : (Stream.replicate n v).reduced :=
begin
  intros r hv hr,
  rw [Stream.index'_val hv, Stream.index'],
  split_ifs,
  { dunfold Stream.replicate, simp },
  { simp }
end

lemma Stream.replicate.monotonic : (Stream.replicate n v).monotonic :=
begin
  intros r hv,
  rw [Stream.index'_val hv, Stream.index'],
  split_ifs,
  { simpa using nat.le_succ r.val },
  { simp }
end

def Stream.replicate.simple : (Stream.replicate n v).simple :=
{ reduced := Stream.replicate.reduced,
  monotonic := Stream.replicate.monotonic,
}

def SimpleStream.replicate (n : ℕ) (v : α) : SimpleStream (fin n) α :=
{ StreamExec.replicate n v with simple := Stream.replicate.simple }

/- ### Correctness -/

namespace finsupp

noncomputable def const {ι : Type} [fintype ι] (v : α) : ι →₀ α :=
equiv_fun_on_finite.inv_fun $ λ _, v

end finsupp

noncomputable def replicate_aux (n : ℕ) (v : α) (r : fin n.succ) : fin n →₀ α :=
finsupp.equiv_fun_on_finite.inv_fun $ λ i, if i.val ≥ r.val then v else 0

lemma replicate_aux.const : replicate_aux n v 0 = finsupp.const v :=
begin
  ext i, cases i with i i_prop,
  simp [replicate_aux, finsupp.const]
end

lemma replicate_aux.zero : replicate_aux n v ⟨n, nat.lt_succ_self n⟩ = 0 :=
begin
  ext i, cases i with i i_prop,
  simp [replicate_aux, not_le.mpr i_prop],
end

lemma replicate_aux.step {r : fin n.succ} (h : r.val < n) :
  replicate_aux n v ⟨r.val+1, nat.succ_lt_succ h⟩ + finsupp.single ⟨r.val, h⟩ v =
  replicate_aux n v r :=
begin
  ext i,
  cases i with i i_prop,
  cases r with r r_prop, change r < n at h,
  simp [replicate_aux, finsupp.single, pi.single_apply], -- TODO: don't simp mid-proof
  split_ifs,
  { exfalso, revert h_1, simp [h_2] },
  { have : r ≤ i := le_of_eq h_2.symm,      contradiction },
  { exact add_zero _ },
  { have : r ≤ i := nat.le_of_succ_le h_1,  contradiction },
  { exact zero_add _ },
  { have : r ≤ i := le_of_eq h_2.symm,      contradiction },
  { have : r < i := lt_of_le_of_ne h_3 (ne.symm h_2), contradiction },
  { exact add_zero _ }
end

lemma Stream.replicate.spec' {B : ℕ} {r : fin n.succ} :
  B + r.val ≥ n →
  (Stream.replicate n v).eval_steps B r = replicate_aux n v r :=
begin
  intro h,
  induction B generalizing r; rw [Stream.eval_steps],
  { ext i, cases i with i i_prop,
    have : ¬↑r ≤ i := begin
      rw not_le, apply lt_of_lt_of_le i_prop, simpa using h,
    end,
    simp [replicate_aux, this] },

  { simp_rw [Stream.replicate_valid, Stream.eval₀],
    split_ifs with hv hr,
    { rw [← replicate_aux.step hv],
      let r' : fin n.succ := ⟨r.val + 1, nat.succ_lt_succ hv⟩,
      change (Stream.replicate n v).eval_steps B_n r' + finsupp.single ⟨r.val, hv⟩ v =
          replicate_aux n v r' + finsupp.single ⟨r.val, hv⟩ v,
      congr,
      apply B_ih,
      change B_n + 1 + r.val ≥ n at h,
      rw [add_assoc, add_comm 1 r.val] at h,
      exact h },
    { have : (Stream.replicate n v).ready r := by simp,
      contradiction },
    { ext i, cases i with i i_prop,
      have : ¬↑r ≤ i := begin
        rw not_le, apply lt_of_lt_of_le i_prop, simpa using hv
      end,
      simp [replicate_aux, this] } }
end

theorem Stream.replicate.spec : (Stream.replicate n v).eval_steps n.succ 0 = finsupp.const v :=
begin
  rw ← replicate_aux.const,
  apply Stream.replicate.spec',
  simpa using le_of_lt (nat.lt_succ_self n)
end

theorem Stream.replicate.spec_apply (i : fin n) : (Stream.replicate n v).eval_steps n.succ 0 i = v :=
by rw Stream.replicate.spec; simp [finsupp.const]

theorem StreamExec.replicate.spec : (StreamExec.replicate n v).eval = finsupp.const v :=
Stream.replicate.spec

end

/- ### replicate': replicate for any type -/

section

variables {ι : Type} [add_comm_monoid α]

section replicate'

variables {m : fin n ↪ ι}

def Stream.replicate' (m : fin n ↪ ι) (v : α) : Stream ι α :=
m <$₁> Stream.replicate n v

instance Stream.replicate'.σ.has_zero : has_zero (Stream.replicate' m v).σ :=
⟨⟨0, nat.zero_lt_succ _⟩⟩

def StreamExec.replicate' (m : fin n ↪ ι) (v : α) : StreamExec ι α :=
m <$₁> StreamExec.replicate n v

def SimpleStream.replicate' [linear_order ι] (m : fin n ↪o ι) (v : α) : SimpleStream ι α :=
m <§₁> SimpleStream.replicate n v

end replicate'

/- ### Specs -/

section spec

section
variables {m : fin n ↪ ι}

open_locale classical

theorem Stream.replicate'.spec (i : ι) :
(Stream.replicate' m v).eval_steps n.succ 0 i = if i ∈ set.range m then v else 0 :=
begin
  dunfold Stream.replicate',
  rw imap_eval_steps_spec _ _ _ _,

  split_ifs with h_range h_range,
  { cases set.mem_range.mp h_range with x hx,
    have : (Stream.replicate n v).eval_steps n.succ 0 x = v,
    { rw Stream.replicate.spec, simp [finsupp.const] },
    conv { congr, { rw ← hx }, { rw ← this } },
    exact finsupp.map_domain_apply m.inj' _ _ },
  { exact finsupp.map_domain_notin_range _ _ h_range }
end

theorem StreamExec.replicate'.spec (i : ι) :
(StreamExec.replicate' m v).eval i = if i ∈ set.range m then v else 0 :=
begin
  unfold StreamExec.eval,
  erw imap_stream_eval,
  exact Stream.replicate'.spec i,
end

theorem SimpleStream.replicate'.spec [linear_order ι] {m : fin n ↪o ι} (i : ι) :
(SimpleStream.replicate' m v : StreamExec ι α).eval i = if i ∈ set.range m then v else 0 :=
StreamExec.replicate'.spec i

end

/- #### Convenience specs for `fin n ≃ ι` -/

section

variable {m : fin n ≃ ι}

instance ι.fintype : fintype ι := fintype.of_equiv _ m

@[reducible, simp]
noncomputable def const' (m : fin n ≃ ι) : α → ι →₀ α :=
@finsupp.const α _ ι (fintype.of_equiv _ m)

theorem Stream.replicate'.spec_equiv :
(Stream.replicate' (m : fin n ↪ ι) v).eval_steps n.succ 0 = const' m v :=
begin
  ext i, rw Stream.replicate'.spec i,
  have : i ∈ set.range m, from set.mem_range.mpr ⟨m.inv_fun i, by simp⟩,
  simp [this, finsupp.const]
end

theorem StreamExec.replicate'.spec_equiv :
(StreamExec.replicate' (m : fin n ↪ ι) v).eval = const' m v :=
begin
  ext i, rw StreamExec.replicate'.spec i,
  have : i ∈ set.range m, from set.mem_range.mpr ⟨m.inv_fun i, by simp⟩,
  simp [this, finsupp.const]
end

theorem SimpleStream.replicate'.spec_equiv [linear_order ι] {m : fin n ≃o ι} :
(SimpleStream.replicate' (m : fin n ↪o ι) v : StreamExec ι α).eval = const' m.to_equiv v :=
StreamExec.replicate'.spec_equiv

end

end spec

end
