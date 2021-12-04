-- coe_fun? iter -> δ or emit
-- library_search
import algebra
import algebra.group
import algebra.group.defs
import tactic
import logic.relation
import base
import data.stream.basic
import combinatorics.simple_graph.subgraph
set_option pp.proofs true
-- set_option pp.notation false

#check stream
#check simple_graph
#check finset.range

universes u v
variables {α β : Type*}

structure iter (σ I V : Type) [linear_order I] :=
  (δ : σ → σ)
  (emit : σ → option (I × option V))

section params
-- we fix one iterator, and its associated types, for the section. the states s and t vary
open iter
-- parameters {σ : Type} [decidable_eq σ] [iter σ] [linear_order (I σ)]
parameters {σ I V : Type} [linear_order I]
[decidable_eq σ]
(a : iter σ I V)
variables (s t : σ)

def ι : with_top I := match a.emit s with | none := none | some (i, _) := some i end
def ν :   option V := match a.emit s with | none := none | some (_, v) := v end
def δ := a.δ

open relation
open relation.refl_trans_gen

-- inductive reach (x : σ) : σ → Type
-- | refl : reach x
-- | tail {b c} : reach b → (δ b = c) → reach c

-- @[reducible, inline]
def reachable := relation.refl_trans_gen (λ a b, b = δ a)
namespace transition -- can't use reachable??
theorem trans {x y z : σ} : reachable x y → reachable y z → reachable x z := trans
theorem refl {x : σ} : reachable x x := refl
def step {x : σ} : reachable x (δ x) := single rfl
end transition

theorem none_top {α : Type*} [linear_order α] : ∀ {i : with_top α}, ⊤ ≤ i → i = none := λ _ big, le_antisymm le_top big

def monotonic          := ∀ (s t : σ), reachable s t → ι s ≤ ι t
#print monotonic
def terminal   (s : σ) := ι s = ⊤
def finite     (s : σ) := ∃ (t : σ), reachable s t ∧ terminal t
def productive (s : σ) := ν s ≠ none
def strict             := ∀ (s t : σ), productive s → productive t → ι s = ι t → s = t
instance [decidable_eq I] : decidable (terminal s) := if h : ι s = none then is_true h else is_false h
-- instance [decidable_eq I] : decidable (terminal s) := if h : a.emit s = none then is_true h else is_false h
#check classical.dec_eq

lemma index_of_path {s t} : reachable s t → ∃ (i: ℕ), t = (δ^i) • s := begin
  intros p, induction p, refine ⟨0 , _⟩, refl,
  case tail : s1 s2 path step h {
    cases h with i hh, refine ⟨i+1, _⟩,
    rw [add_comm, pow_add, mul_smul, ← hh], exact step,
  }
end
#check Exists.some
noncomputable def index_of_path' {s t} (r : reachable s t) : Σ' (i : ℕ), t = δ^i•s :=
    ⟨(index_of_path r).some, (index_of_path r).some_spec⟩

def path_of_index : ∀ (i:ℕ), reachable s ((δ^i)•s)
| 0 := refl
| (n+1) := tail (path_of_index n) rfl

lemma le_of_index_lt (i j : ℕ) : monotonic → i ≤ j → ι ((δ^i)•s) ≤ ι ((δ^j)•s) := begin
  intros mono lt, apply mono, induction lt, exact refl, exact tail ‹_› rfl,
end
lemma index_lt_of_ge (i j : ℕ) : monotonic → ι ((δ^i)•s) < ι ((δ^j)•s) → i < j := λ mono, begin
have h := mt (le_of_index_lt s j i mono),
simpa only [not_le,h] using h,
end #print index_lt_of_ge

#check pow_add
@[simp] lemma mono_iff_delta_mono : monotonic ↔ ∀ t, ι t ≤ ι (δ t) := begin
split, intros m t,
exact m _ _ (transition.step a),
intro h, intros w x path, obtain ⟨len, h⟩ : _ := index_of_path path,
rw h,
induction len with pl h1 generalizing x w,
simp only [pow_zero, one_smul, le_refl],
exact calc
  ι w ≤ ι (δ ^ pl • w)      : by {exact h1 _ w (path_of_index _ _) rfl}
  ... ≤ ι (δ • δ ^ pl • w)  : by {change ι (δ ^ pl • w) ≤ ι (δ (δ ^ pl • w)), apply h, }
  ... ≤ ι (δ ^ pl.succ • w) : by {simp only [← mul_smul], simp,
                                  change ι ((δ^1 * δ ^ pl) w) ≤ ι ((δ ^ pl.succ) w),
                                  simp only [← pow_add, add_comm, le_refl]},
end

lemma finite1 {s T : σ} : monotonic → reachable s T → terminal T → ∃ (j : ℕ),
                            ∀ (t':σ), reachable s t' → not (terminal t') →  ∃ (i : ℕ),
                            t' = (δ^i) s ∧ T = (δ^j) s ∧ i < j := begin
  intros mono pathT Tterm, refine ⟨(index_of_path pathT).some, _⟩,
  intros t path neq,
  refine ⟨(index_of_path path).some, _⟩,
  split, exact (index_of_path path).some_spec,
  split, exact (index_of_path pathT).some_spec,
  apply index_lt_of_ge s _ _ mono,
  rw ← (index_of_path path).some_spec,
  rw ← (index_of_path pathT).some_spec,
  cases h2 : (ι t : with_top I), exfalso, exact neq h2,
  cases h3 : (ι T : with_top I), dec_trivial, exfalso, simp only [terminal] at *,
  exact option.some_ne_none _ (h3.symm.trans Tterm),
end
#check finite1

def nth_path (n : ℕ) : finset σ := (fintype.elems (fin n)).image (λ i, ((δ^i.val) s))

def future (s : σ) : set σ := { t | reachable s t ∧ ¬ terminal t}
-- instance i1 : decidable_pred terminal := λ s, if h : terminal s then is_true h else is_false h

-- theorem finite₂ (mono : monotonic) (hfinite : finite s) : ∃ (j:ℕ), ∀ (t':σ), t' ∈ future s → t' ∈ nth_path s j :=
#check finset.set_of_mem
theorem finite₂ (mono : monotonic) (hfinite : finite s) : ∃ (j:ℕ), future s ⊆ nth_path s j :=
begin
  cases finite1 mono hfinite.some_spec.1 hfinite.some_spec.2 with bound h1,
  refine ⟨bound, _⟩,
  simp only [nth_path],
  rintros t ⟨path, nterm⟩,
  simp only [finset.mem_coe],
  rw finset.mem_image,
  cases h1 t path nterm with i h2,
  have h3 : i < bound := h2.2.2,
  refine ⟨⟨i,h3⟩,_⟩,
  rw ← h2.1,
  refine ⟨finset.mem_fin_range _, rfl⟩,
end
#check finite₂

theorem finite_of_sub_finset (p : set α) (s : finset α) : p⊆s → p.finite := s.finite_to_set.subset

noncomputable def fintype_of_sub_finset (p : set α) (s : finset α) (h : ∀ x, x∈p → x∈s) : fintype p :=
@set.fintype_subset _ _ _ (fintype.of_finset s (λ _, iff.rfl)) (classical.dec_pred p) h

def finite₃ (mono : monotonic) (hfinite : finite s) : (future s).finite :=
    let ⟨j, h⟩ := finite₂ s mono hfinite in finite_of_sub_finset _ (nth_path s j) h

noncomputable def finite₄ (mono : monotonic) (hfinite : finite s) : fintype (future s) := (finite₃ s mono hfinite).fintype

def elementary [decidable_eq I] [add_monoid V] (i : I) (v : V) := λ j, if i = j then v else 0
def semantics₁ [decidable_eq I] [add_monoid V] (s : σ) : I → V :=
  match a.emit s with
  | none := 0
  | some (i, none) := 0
  | some (i, some v) := elementary i v
  end

parameters [add_comm_monoid V]

noncomputable def fin_future (m : monotonic) (hfin : finite s) : finset {x // future s x} :=
@finset.univ (future s) (finite₃ s m hfin).fintype

def res_fun {γ : Type*} {p : set α} (f : α → γ) (x : {y // p y}) : γ := f ↑x

def semantics (j:ℕ) : I → V := finset.sum (nth_path s j) semantics₁
def semantics' : σ → ℕ → I → V
| _ 0 := 0
| s (n+1) := semantics₁ s + semantics' (δ s) n
def semantics_stream (s : σ) : stream (I → V) := λ n, semantics₁ (δ^n • s)
theorem stream_head : (semantics_stream s).head = semantics₁ s := rfl
theorem stream_tail : (semantics_stream s).tail = semantics_stream (δ s) := begin
rw [stream.tail],
funext, simp only [semantics_stream, stream.tail], rw [pow_add], refl,
end
theorem sem_approx_sum (s : σ) (j:ℕ)  : semantics' s j = ((semantics_stream s).approx j).sum := begin
induction j generalizing s, case zero {refl},
case succ : _ h {
    simp only [semantics', stream.approx],
    rw [stream_head, stream_tail],
    rw [list.sum_cons],
    rw [← h],
} end

lemma mwe1 {k n : ℕ} (h : n < k) : (list.range k).nth_le n ((list.length_range k).symm ▸ h) = n := sorry
--lemma mwe1 {k n : ℕ} (h : n < k) : (list.range k).nth_le n (by simpa only [list.length_range] using h) = n := sorry
#print mwe1

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
theorem semantics_ind_last (s : σ) (j:ℕ)  : semantics' s j.succ = semantics' s j + semantics₁ (δ^j • s) := begin
 rw [sem_approx_sum, approx_range_map],
 rw [list.range_succ], rw list.map_append,
 rw list.map_singleton, rw list.sum_append, rw list.sum_singleton,
 rw [← approx_range_map, ← sem_approx_sum],
 refl,
end

#check stream.approx_succ
#check finset.range
#check list.range_succ
#check list.sum_cons
#check list.range_succ
theorem semantics_ind  (j:ℕ) : semantics' s j.succ = semantics₁ s + semantics'  (δ s) j  := rfl
theorem emit_none_of_terminal : terminal t → a.emit t = none := begin
intro h, simp only [terminal] at h, cases h2 : a.emit t, {refl},
exfalso,
cases val, simp only [ι,h2] at h,
apply option.some_ne_none _ h,
end
theorem terminal_zero (h : terminal t) : semantics₁ t = 0 := begin
simp only [semantics₁], rw [emit_none_of_terminal _ h], refl, end
theorem terminal_succ_terminal (m : monotonic) (h : terminal t) : terminal (δ t) := begin
simp only [terminal] at *, apply none_top, rw ←h, apply m, exact transition.step _, end
theorem semantics_zero (m : monotonic) (h : terminal t) (j:ℕ) : semantics' t j = 0 := begin
induction j with _ jh generalizing t, {refl},
rw [semantics_ind, terminal_zero _ h, zero_add],
exact jh _ (terminal_succ_terminal _ m h)
end

theorem progress (s t : σ) :  terminal t → true := sorry

end params

local notation `⟦` a, s `⟧` := semantics' a s

def nat_iter : iter ℕ ℕ ℕ :=
{ δ := λ n, n+1
, emit := λ n, some (n, some n)
-- , wf := λ _ h, begin exfalso, exact nat.succ_ne_self _ h, end
}
def steps := 10
#reduce ⟦nat_iter, 0 ⟧ steps 5

def iota (k : ℕ): iter (fin k.succ) (fin k) (fin k) :=
{ δ := λ n, if h : n.val < k then ⟨n.val+1,  nat.succ_lt_succ h⟩ else n
, emit := λ n, if h : n.val < k then some (⟨n.val, h⟩, some ⟨n.val, h⟩) else none
}
-- #reduce (semantics (iota 4) 1 5 3)
#reduce ⟦iota 4, 0⟧ 5 2

section params_binary
parameters {σ₁ σ₂ I V : Type} [linear_order I] [decidable_eq σ₁] [decidable_eq σ₂] [add_comm_monoid V]
(a : iter σ₁ I V) (b : iter σ₂ I V)

instance [linear_order I][add_comm_monoid V] : add_comm_monoid (option (I × option V)) := begin
fsplit, exact λ a b,
match a, b with
| none, none := none
| none,some v := some v | some v, none := some v
| some (i₁, v₁), some (i₂, v₂) := if i₁ < i₂ then some (i₁, v₁) else if i₁ > i₂ then some (i₂, v₂) else
  some (i₁, match v₁, v₂ with
  | none, none := none
  | some v, none := some v
  | none, some v := some v
  | some v₁, some v₂ := some (v₁ + v₂)
  end)
end,
sorry -- todo, replace emit with semantics₁?
end
example (f : α → α) (sz : α → ℕ) (dec : ∀ x, sz (f x) < sz x) (x : α) : ∃ (i:ℕ), sz (f^i • x) = 0 := begin

end

def add_iter (a : iter σ₁ I V) (b : iter σ₂ I V) : iter (σ₁×σ₂) I V :=
{ δ := λ ⟨s,t⟩, if ι a s < ι b t then (δ a s,t) else if ι a s > ι b t then (s, δ b t) else (δ a s, δ b t)
, emit := λ ⟨s,t⟩, if ι a s < ι b t then a.emit s else if ι a s > ι b t then b.emit t else a.emit s + b.emit t
}
local infix `+'`:50 := add_iter
#check min
lemma add_ι_min {s} : ι (a+'b) s = min (ι a s.1) (ι b s.2) := begin
cases s, simp [add_iter, ι, iter.emit],
end

#check tactic.simp_config_ext
theorem terminal_1_delta_2 (s₁:σ₁)(s₂:σ₂) : terminal a s₁ → (δ (a +'b) (s₁,s₂)).2 = δ b s₂ := λ t, begin
simp only [add_iter, terminal, δ] at *, rw t,
simp only [not_top_lt], split_ifs, {exact false.rec _ h}, repeat {refl},
end
theorem terminal_2_delta_1 (s₁:σ₁)(s₂:σ₂) : terminal b s₂ → (δ (a +'b) (s₁,s₂)).1 = δ a s₁ := λ t, begin
simp only [add_iter, terminal, δ] at *, rw t,
simp only [gt_iff_lt, not_top_lt], split_ifs with _ h, refl, {exact false.rec _ h}, {refl},
end
example (s₁:σ₁)(s₂:σ₂) {t} (sz : ℕ) (h : δ (a+'b)^sz • (s₁,s₂) = t) : true := begin

end
theorem add_iter_finite    (s₁:σ₁) (s₂:σ₂) : finite a s₁ → finite b s₂ → finite (a +' b) (s₁,s₂) := begin
rintros ⟨sa, ⟨patha, terma⟩⟩ ⟨sb, ⟨pathb, termb⟩⟩,
have h1 := index_of_path a patha,
have h2 := index_of_path b pathb,

end
#check index_of_path
theorem add_iter_monotonic (s₁:σ₁) (s₂:σ₂) : monotonic a → monotonic b → monotonic (a +' b) := begin
intros m1 m2,
simp only [mono_iff_delta_mono],

rintro ⟨t₁, t₂⟩, simp only [ι], cases ι a t₁ < ι b t₂,
end
theorem add_iter_strict    (s₁:σ₁) (s₂:σ₂) : strict a    → strict b    → strict (a +' b) := sorry
theorem add_iter_sound     (s₁:σ₁) (s₂:σ₂) : ∃ j, ⟦a +' b, (s₁,s₂)⟧ j = ⟦a, s₁⟧ j + ⟦b, s₂⟧ j := sorry

end params_binary
