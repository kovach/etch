import algebra
import algebra.group
import algebra.group.defs
import tactic
import logic.relation
import base
import data.stream.basic

namespace iter

universes u v
variables {α β : Type*}

section params_unary
variables {σ I V : Type} [linear_order I]
[decidable_eq σ]
(a : iter σ I V)
variables (s t : σ)

section semantics
variable [add_comm_monoid V]

def semantics' : σ → ℕ → I → V
| _ 0 := 0
| s (n+1) := a.semantics₁ s + semantics' (a.δ s) n
notation `⟦` a, s `⟧` := a.semantics' s

#reduce ⟦iter.iota 4, 0⟧ 5 2
#reduce ⟦iter.nat_iter, 0⟧ 20 12

def semantics_stream (s : σ) : stream (I → V) := λ n, a.semantics₁ (a.δ^n • s)

theorem stream_head : (a.semantics_stream s).head = a.semantics₁ s := rfl
theorem stream_tail : (a.semantics_stream s).tail = a.semantics_stream (a.δ s) := begin
rw [stream.tail],
funext, simp only [semantics_stream, stream.tail], rw [pow_add], refl,
end
theorem sem_approx_sum (s : σ) (j:ℕ)  : a.semantics' s j = ((a.semantics_stream s).approx j).sum := begin
induction j generalizing s, case zero {refl},
case succ : _ h {
    simp only [semantics', stream.approx],
    rw [stream_head, stream_tail],
    rw [list.sum_cons],
    rw [← h],
} end


example {k n : ℕ} (h : n < k) : (list.range k).nth_le n ((list.length_range k).symm ▸ h) = n := sorry

theorem approx_range_map (j : ℕ) (s : stream α) : s.approx j = (list.range j).map s := begin
--stream.approx j.succ s = stream.approx j s ++  [s j] := begin
induction j with _ h generalizing s, case zero { refl }, -- simp only [stream.approx, stream.head], rw list.nil_append, },
--#check list.range_succ
case succ {
    rw list.range_succ,
    rw list.map_append,
    rw ←h,
    rw stream.approx_succ,
    rw h,

    rw ← h,
    rw stream.tail,
    sorry,
    -- rw list.map_append,
    -- rw ← h, rw list.map_singleton,

},
end
theorem semantics_ind_last (s : σ) (j:ℕ)  : a.semantics' s j.succ = a.semantics' s j + a.semantics₁ (a.δ^j • s) := begin
 rw [sem_approx_sum, approx_range_map],
 rw [list.range_succ], rw list.map_append,
 rw list.map_singleton, rw list.sum_append, rw list.sum_singleton,
 rw [← approx_range_map, ← sem_approx_sum],
 refl,
end
end semantics

section finiteness

lemma index_of_path {a : iter σ I V} {s t} : a.reachable s t → ∃ (i: ℕ), t = (a.δ^i) • s := begin
  intros p, induction p, refine ⟨0 , _⟩, refl,
  case tail : s1 s2 path step h {
    cases h with i hh, refine ⟨i+1, _⟩,
    rw [add_comm, pow_add, mul_smul, ← hh], exact step,
  }
end

noncomputable def index_of_path_sigma {s t} (r : a.reachable s t) : Σ' (i : ℕ), t = a.δ^i•s :=
    ⟨(index_of_path r).some, (index_of_path r).some_spec⟩

lemma finite1 {a : iter σ I V} {s T : σ} : a.monotonic → a.reachable s T → terminal a T → ∃ (j : ℕ),
                            ∀ (t':σ), a.reachable s t' → not (terminal a t') →  ∃ (i : ℕ),
                            t' = (a.δ^i) s ∧ T = (a.δ^j) s ∧ i < j := begin
  intros mono pathT Tterm, refine ⟨(index_of_path pathT).some, _⟩,
  intros t path neq,
  refine ⟨(index_of_path path).some, _⟩,
  split, exact (index_of_path path).some_spec,
  split, exact (index_of_path pathT).some_spec,
  apply index_lt_of_ge s _ _ mono,
  rw ← (index_of_path path).some_spec,
  rw ← (index_of_path pathT).some_spec,
  cases h2 : (ι a t : with_top I), exfalso, exact neq h2,
  cases h3 : (ι a T : with_top I), dec_trivial, exfalso, simp only [terminal] at *,
  exact option.some_ne_none _ (h3.symm.trans Tterm),
end

def nth_path (n : ℕ) : finset σ := (fintype.elems (fin n)).image (λ i, ((a.δ^i.val) s))
--def semantics [add_comm_monoid V] (j:ℕ) : I → V := finset.sum (a.nth_path s j) a.semantics₁

-- instance i1 : decidable_pred terminal := λ s, if h : terminal s then is_true h else is_false h

#check @finset.set_of_mem
theorem finite₂ {a : iter σ I V} (mono : a.monotonic) (hfinite : a.finite s) : ∃ (j:ℕ), a.future s ⊆ a.nth_path s j :=
begin
  cases finite1 mono hfinite.some_spec.1 hfinite.some_spec.2 with bound h1,
  refine ⟨bound, _⟩,
  simp only [iter.nth_path],
  rintros t ⟨path, nterm⟩,
  simp only [finset.mem_coe],
  rw finset.mem_image,
  cases h1 t path nterm with i h2,
  have h3 : i < bound := h2.2.2,
  refine ⟨⟨i,h3⟩,_⟩,
  rw ← h2.1,
  refine ⟨finset.mem_fin_range _, rfl⟩,
end

theorem finite_of_sub_finset (p : set α) (s : finset α) : p⊆s → p.finite := s.finite_to_set.subset

noncomputable def fintype_of_sub_finset (p : set α) (s : finset α) (h : ∀ x, x∈p → x∈s) : fintype p :=
@set.fintype_subset _ _ _ (fintype.of_finset s (λ _, iff.rfl)) (classical.dec_pred p) h

def finite₃ {a : iter σ I V} (mono : a.monotonic) (hfinite : a.finite s) : (a.future s).finite :=
    let ⟨j, h⟩ := finite₂ s mono hfinite in finite_of_sub_finset _ (a.nth_path s j) h

noncomputable def finite₄ {a : iter σ I V} (mono : a.monotonic) (hfinite : a.finite s) : fintype (a.future s) := (finite₃ s mono hfinite).fintype

noncomputable def fin_future (m : a.monotonic) (hfin : a.finite s) : finset {x // a.future s x} :=
@finset.univ (a.future s) (finite₃ s m hfin).fintype

end finiteness

-- todo
#check stream.approx_succ
#check finset.range
#check list.range_succ
#check list.sum_cons
#check list.range_succ

variable [add_comm_monoid V]
theorem semantics_ind  (j:ℕ) : a.semantics' s j.succ = a.semantics₁ s + a.semantics'  (a.δ s) j  := rfl
theorem emit_none_of_terminal {a : iter σ I V} : a.terminal t → a.emit t = none := begin
intro h, simp only [terminal] at h, cases h2 : a.emit t, {refl},
exfalso,
cases val, simp only [ι,h2] at h,
apply option.some_ne_none _ h,
end
theorem terminal_zero {a : iter σ I V} (h : a.terminal t) : a.semantics₁ t = 0 := begin
simp only [semantics₁], rw [emit_none_of_terminal _ h], refl, end
theorem terminal_succ_terminal {a : iter σ I V} (m : a.monotonic) (h : a.terminal t) : a.terminal (a.δ t) := begin
simp only [terminal] at *, apply none_top, rw ←h, apply m, exact transition.step _, end
theorem semantics_zero {a : iter σ I V} (m : a.monotonic) (h : a.terminal t) (j:ℕ) : a.semantics' t j = 0 := begin
induction j with _ jh generalizing t, {refl},
rw [semantics_ind, terminal_zero _ h, zero_add],
exact jh _ (terminal_succ_terminal _ m h)
end

end params_unary

section params_binary

variables {σ₁ σ₂ I V : Type} [linear_order I] [decidable_eq σ₁] [decidable_eq σ₂] [add_comm_monoid V]
(a : iter σ₁ I V) (b : iter σ₂ I V)

theorem terminal_1_delta_2 (s₁:σ₁)(s₂:σ₂) : a.terminal s₁ → ((a +'b).δ (s₁,s₂)).2 = b.δ s₂ := λ t, begin
simp only [add_iter, iter.terminal, iter.δ] at *, rw t,
simp only [not_top_lt], split_ifs, repeat {refl}, {exact false.rec _ h},
end
theorem terminal_2_delta_1 (s₁:σ₁)(s₂:σ₂) : b.terminal s₂ → ((a +'b).δ (s₁,s₂)).1 = a.δ s₁ := λ t, begin
simp only [add_iter, iter.terminal, iter.δ] at *, rw t,
simp only [gt_iff_lt, not_top_lt], split_ifs with _ h, repeat {refl}, {exact false.rec _ h},
end

theorem add_iter_finite    (s₁:σ₁) (s₂:σ₂) : a.finite s₁ → b.finite s₂ → (a +' b).finite (s₁,s₂) := begin
rintros ⟨sa, ⟨patha, terma⟩⟩ ⟨sb, ⟨pathb, termb⟩⟩,
have h1 := index_of_path patha,
have h2 := index_of_path pathb,
sorry,
end

end params_binary

end iter
