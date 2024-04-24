import Etch.StreamFusion.Proofs.StreamProof
import Etch.StreamFusion.Multiply

namespace Etch.Verification.Stream

open Streams

universe u v
variable {ι : Type} [LinearOrder ι] {α : Type u} {β : Type v}

section Defs

@[macro_inline, simps (config := { simpRhs := true })]
def zip (a : Stream ι α) (b : Stream ι β) : Stream ι (α × β) where
  σ         := a.σ × b.σ
  valid q   := let (qa, qb) := q; a.valid qa && b.valid qb
  index q   := let (qa, qb) := mul.valid.cases q; max (a.index qa) (b.index qb)
  seek  q i := let (qa, qb) := mul.valid.cases q; ⟨a.seek qa i, b.seek qb i⟩
  ready q   := let (qa, qb) := mul.valid.cases q; a.ready qa && b.ready qb && (a.index qa = b.index qb)
  value q   := let (qa, qb) := mul.ready.cases q; ((a.value qa), (b.value qb))

end Defs

section IndexLemmas

theorem mul.ready.order_eq {a : Stream ι α} {b : Stream ι β} {q}
    (h : mul.ready a b q) : a.toOrder (mul.valid.fst q) = b.toOrder (mul.valid.snd q) := by
  dsimp only [Stream.toOrder]
  aesop

theorem order_eq_of_zip_ready {a : Stream ι α} {b : Stream ι β} {q}
    (h : mul.ready a b q) : a.toOrder (mul.valid.fst q) = (a.zip b).toOrder q ∧
      b.toOrder (mul.valid.snd q) = (a.zip b).toOrder q := by
  dsimp only [Stream.toOrder]
  aesop

theorem zip_index' (a : Stream ι α) (b : Stream ι β) (q) :
    (a.zip b).index' q = max (a.index' q.1) (b.index' q.2) := by
  rw [Stream.index']
  split_ifs with h
  · simp at h; simp [index'_val' _ h.1, index'_val' _ h.2]; rfl
  · simp [-not_and, not_and_or] at h
    rcases h with h | h
    <;> simp [index'_invalid h]

theorem min_toOrder_le (a : Stream ι α) (b : Stream ι β) (q) :
    min (a.toOrder (mul.valid.fst q)) (b.toOrder (mul.valid.snd q)) ≤ (a.zip b).toOrder q := by
  rw [Prod.Lex.le_iff'']
  simp only [Monotone.map_min (@Prod.Lex.fst_mono ι Bool _ _)]
  constructor
  · exact min_le_max
  · simp only [toOrder]
    aesop

theorem toOrder_le_max (a : Stream ι α) (b : Stream ι β) (q) :
    (a.zip b).toOrder q ≤ max (a.toOrder <| mul.valid.fst q) (b.toOrder <| mul.valid.snd q) := by
  rw [Prod.Lex.le_iff']; right; constructor
  · simp [Monotone.map_max (@Prod.Lex.fst_mono ι Bool _ _)]
  · simp only [Bool.le_iff_imp, toOrder]
    aesop

instance zip.isBounded (a : Stream ι α) (b : Stream ι β) [IsBounded a] [IsBounded b] :
    IsBounded (a.zip b) :=
  ⟨⟨Prod.rprodEq a.wfRel b.wfRel,
    fun q i => by
      rcases a.wf_valid (mul.valid.fst q) i with (h | ⟨ha₁, ha₂⟩)
      · left; left; exact ⟨h, b.no_backward ..⟩
      · rcases b.wf_valid (mul.valid.snd q) i with (h | ⟨hb₁, hb₂⟩)
        · left; right; exact ⟨h, a.no_backward ..⟩
        · right; constructor; swap
          · simp [ha₂, hb₂]
          · exact lt_of_lt_of_le (lt_min ha₁ hb₁) (min_toOrder_le ..)⟩⟩


theorem zip_mono {a : Stream ι α} {b : Stream ι β} (ha : a.IsMonotonic) (hb : b.IsMonotonic) :
    (a.zip b).IsMonotonic := by
  intro q i
  simp only [zip_index']
  exact max_le_max (ha _ _) (hb _ _)

theorem zip_strict_mono {a : Stream ι α} {b : Stream ι β} (ha : a.IsStrictMono) (hb : b.IsStrictMono) :
    (a.zip b).IsStrictMono where
  left := zip_mono ha.1 hb.1
  right q i H hr :=
    ne_of_lt (by
      simp only [zip_index']
      have := order_eq_of_zip_ready hr
      simp at hr
      apply max_lt_max (ha.lt (hr := hr.1.1) ..) (hb.lt (hr := hr.1.2) ..) <;>
        simpa [this])

end IndexLemmas

section ValueLemmas
/-
if (i, true) < (a.zip b).toOrder q:
  (a.zip b).eval q i = 0
  a.eval q i = 0 or b.eval q i = 0

if (i, true) = (a.zip b).toOrder q:
  (a.zip b).eval q i =
    some (a.value q, b.value q) =
    (a.eval q i, b.value q i)

if (i, true) > (a.zip b).toOrder q:
  (a.zip b).eval q i =
    (a.zip b).eval (advance q) i =
    (a.eval (advance q) i) <(*,*)> (b.eval (advance q) i) =
    -- for this, need (a.zip b).toOrder q ≤ (i, false)
    (a.eval q i) <(*,*)> (b.eval q i)

-/
variable {a : Stream ι α} {b : Stream ι β} [IsStrictLawful a] [IsStrictLawful b]

lemma zip_eq_zero_of_lt_toOrder {i : ι} {q} (hi : i < (a.zip b).index q) :
    (a.zip b).evalOption q i = none := by
  have := (zip_strict_mono a.strictMono b.strictMono).1.eq_empty_of_lt_index (q := q) i (by rwa [index'_val, WithTop.coe_lt_coe])
  rw [Stream.evalOption, this, Multiset.get_zero]

lemma zip_left_or_right_eq_zero_of_lt_toOrder {i : ι} {q} (hi : i < (a.zip b).index q) :
    a.evalOption (mul.valid.fst q) i = none ∨ b.evalOption (mul.valid.snd q) i = none := by
  simp only [zip_index, lt_max_iff] at hi
  refine hi.imp ?_ ?_ <;> intro hi
  · have := a.mono.eq_empty_of_lt_index (q := mul.valid.fst q) i (by rwa [index'_val, WithTop.coe_lt_coe])
    rw [Stream.evalOption, this, Multiset.get_zero]
  · have := b.mono.eq_empty_of_lt_index (q := mul.valid.snd q) i (by rwa [index'_val, WithTop.coe_lt_coe])
    rw [Stream.evalOption, this, Multiset.get_zero]

lemma zip_ready_eq {q} (h : (a.zip b).ready q) :
    (a.zip b).evalOption q ((a.zip b).index q) = some ((a.value <| mul.ready.fst ⟨q, h⟩), (b.value <| mul.ready.snd ⟨q, h⟩)) := by
  rw [(zip_strict_mono a.strictMono b.strictMono).evalOption_ready h]
  rfl

lemma zip_ready_eq' {q} (h : (a.zip b).ready q) :
    a.evalOption (mul.valid.fst q) ((a.zip b).index q) = some (a.value <| mul.ready.fst ⟨q, h⟩) ∧
    b.evalOption (mul.valid.snd q) ((a.zip b).index q) = some (b.value <| mul.ready.snd ⟨q, h⟩) := by
  have Ha : (a.zip b).index q = (a.index <| mul.valid.fst q) := by aesop
  have Hb : (a.zip b).index q = (b.index <| mul.valid.snd q) := by aesop
  constructor
  · rw [Ha, a.strictMono.evalOption_ready]; rfl
  · rw [Hb, b.strictMono.evalOption_ready]; rfl

lemma zip_ready_eq'' {q} (h : (a.zip b).ready q) :
    a.evalOption q.1.1 ((a.zip b).index q) = some (a.value <| mul.ready.fst ⟨q, h⟩) ∧
    b.evalOption q.1.2 ((a.zip b).index q) = some (b.value <| mul.ready.snd ⟨q, h⟩) :=
  zip_ready_eq' h

lemma left_right_eval_eq_of_toOrder_le {i : ι} {q} (hi : (a.zip b).toOrder q ≤ (i, false)) :
    a.evalOption ((a.zip b).advance q).1 i = a.evalOption (mul.valid.fst q) i ∧
      b.evalOption ((a.zip b).advance q).2 i = b.evalOption (mul.valid.snd q) i := by
  constructor <;>
  · simp only [zip_σ, zip_valid, advance_val, zip_seek, evalOption, coe_mul_valid_fst, coe_mul_valid_snd, mul.valid]
    rw [IsLawful.seek_spec _ _ _ hi]
    rfl

theorem zip_spec (q : (a.zip b).σ) (i : ι) :
    (a.zip b).evalOption q i = (Option.map₂ Prod.mk (a.evalOption q.1 i) (b.evalOption q.2 i)) := by
  apply (a.zip b).wf.induction q; clear q
  intro q ih
  by_cases hv : (a.zip b).valid q; swap
  · have := hv
    simp only [zip_valid, Bool.and_eq_true, not_and_or, Bool.not_eq_true] at hv
    rcases hv with hv' | hv' <;> simp [this, hv']
  · rcases lt_trichotomy (α := StreamOrder ι) (i, true) ((a.zip b).toOrder ⟨q, hv⟩) with h|h|h
    · -- i < toOrder
      rw [Prod.Lex.mk_true_lt_iff_lt, toOrder_fst] at h
      rw [zip_eq_zero_of_lt_toOrder h]
      rcases zip_left_or_right_eq_zero_of_lt_toOrder h with h₂|h₂ <;>
      · simp only [zip_σ, zip_valid, coe_mul_valid_fst, coe_mul_valid_snd] at h₂
        simp [h₂]
    · -- i = toOrder
      rw [toOrder, Eq.comm, Prod.ext_iff] at h
      simp only [zip_σ, zip_valid, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨rfl, hr⟩
      rw [zip_ready_eq hr, (zip_ready_eq'' hr).1, (zip_ready_eq'' hr).2]
      rfl
    · -- i > toOrder
      have not_ready := not_ready_of_toOrder_lt h
      rw [Prod.Lex.lt_mk_true_iff] at h
      have := left_right_eval_eq_of_toOrder_le h
      rw [(a.zip b).evalOption_not_ready ⟨q, hv⟩ _ not_ready, ih _ ((a.zip b).next_wf ⟨q, hv⟩), this.1, this.2]
      rfl


theorem zip_spec' (q : (a.zip b).σ) (i : ι) :
    (a.zip b).evalMultiset q i = ((Option.map₂ Prod.mk (a.evalOption q.1 i) (b.evalOption q.2 i)).map (fun x => {x})).getD 0 := by
  rw [(zip_strict_mono a.strictMono b.strictMono ).evalMultiset_eq_evalOption, zip_spec]

theorem zip_seek_spec (q : {q // (a.zip b).valid q}) (i : StreamOrder ι) (j : ι) (h : i ≤ (j, false)) :
    (a.zip b).evalMultiset ((a.zip b).seek q i) j = (a.zip b).evalMultiset q j := by
  simp only [zip_spec', evalOption, zip_seek]
  congr 4 <;>
    apply IsLawful.seek_spec _ _ _ h

instance (a : Stream ι α) (b : Stream ι β) [IsStrictLawful a] [IsStrictLawful b] :
    IsStrictLawful (a.zip b) where
  seek_spec := zip_seek_spec
  strictMono := zip_strict_mono a.strictMono b.strictMono

end ValueLemmas

end Etch.Verification.Stream
