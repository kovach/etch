import data.finsupp.basic
import data.fintype.basic
import logic.function.iterate
import tactic.basic
import verification.stream_props

/- ### Definitions -/

variables {α : Type}
[add_zero_class α]
{n : ℕ} {v : α}

@[simps]
def Stream.replicate (n : ℕ) (v : α) : Stream (fin n) α :=
{ σ := fin n.succ,
  valid := λ i, i.val < n,
  ready := λ _, true,
  next := λ i h, ⟨i.val+1, nat.succ_lt_succ h⟩,
  index := λ i h, ⟨i.val, h⟩,
  value := λ _ _, v,
}

instance : has_zero (Stream.replicate n v).σ := ⟨⟨0, nat.zero_lt_succ _⟩⟩

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
  rw Stream.reduced,
  intros r hv hr,
  rw [Stream.index'_val hv, Stream.index'],
  split_ifs,
  { dunfold Stream.replicate, simp },
  { simp }
end

lemma Stream.replicate.monotonic : (Stream.replicate n v).monotonic :=
begin
  rw Stream.monotonic,
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
{ simple := Stream.replicate.simple,
  ..(StreamExec.replicate n v) }

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
  { have : r ≤ i := le_of_eq (eq.symm h_2), contradiction },
  { exact add_zero _ },
  { have : r ≤ i := nat.le_of_succ_le h_1,  contradiction },
  { exact zero_add _ },
  { have : r ≤ i := le_of_eq (eq.symm h_2), contradiction },
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

theorem StreamExec.replicate.spec : (StreamExec.replicate n v).eval = finsupp.const v :=
Stream.replicate.spec
