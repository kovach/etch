import Etch.StreamFusion.Proofs.StreamProof

namespace Etch.Verification.Stream
open Streams

variable {ι ι' : Type} [LinearOrder ι] [LinearOrder ι']

theorem lt_iff_of_eq_compare {a b : ι} {c d : ι'} (h : compareOfLessAndEq a b = compareOfLessAndEq c d) :
    a < b ↔ c < d := by
  simp only [compareOfLessAndEq] at h
  split_ifs at h <;> simp [*]

theorem eq_iff_of_eq_compare {a b : ι} {c d : ι'} (h : compareOfLessAndEq a b = compareOfLessAndEq c d) :
    a = b ↔ c = d := by
  simp only [compareOfLessAndEq] at h
  split_ifs at h with h₁ h₂ <;> aesop

theorem le_iff_of_eq_compare {a b : ι} {c d : ι'} (h : compareOfLessAndEq a b = compareOfLessAndEq c d) :
    a ≤ b ↔ c ≤ d := by
  simp [le_iff_lt_or_eq, lt_iff_of_eq_compare h, eq_iff_of_eq_compare h]

theorem gt_iff_of_eq_compare {a b : ι} {c d : ι'} (h : compareOfLessAndEq a b = compareOfLessAndEq c d) :
    b < a ↔ d < c := by
  simpa using (le_iff_of_eq_compare h).not

-- theorem attach_lex_of_eq_compare [LinearOrder γ] (a b : ι) (c : ι')

theorem IsBounded.imap (s : Stream ι α) [IsBounded s]
    (f : ι → ι') (g : ι → ι' → ι)
    (hfg : ∀ (i : ι) (j : ι'), compareOfLessAndEq j (f i) = compareOfLessAndEq (g i j) i) :
    IsBounded (s.imap_general f g) := by
  refine ⟨s.wfRel, ?_⟩
  rintro q ⟨j, b⟩
  refine (s.wf_valid q (g (s.index q) j, b)).imp_right (And.imp_left ?_)
  dsimp [toOrder]
  convert id
  simp only [Prod.Lex.lt_iff', ← lt_iff_of_eq_compare (hfg (s.index q) j),
    eq_iff_of_eq_compare (hfg (s.index q) j)]

theorem IsMonotonic.imap {s : Stream ι α} (hs : s.IsMonotonic) {f : ι → ι'} (g : ι → ι' → ι) (hf : Monotone f) :
    IsMonotonic (s.imap_general f g) := by
  rw [Stream.isMonotonic_iff]
  rintro q ⟨i, b⟩ hq
  dsimp at q hq ⊢
  apply hf
  apply Stream.isMonotonic_iff.mp hs q

theorem IsLawful.imap {s : Stream ι α} [AddZeroClass α] [IsLawful s] {f : ι → ι'} {g : ι → ι' → ι}
      (hf : Monotone f) (hg : ∀ j, Monotone (g · j))
      (hfg : ∀ (i : ι) (j : ι'), compareOfLessAndEq j (f i) = compareOfLessAndEq (g i j) i) :
    IsLawful (s.imap_general f g) := by
  haveI : IsBounded (s.imap_general f g) := IsBounded.imap s f g hfg
  refine ⟨s.mono.imap g hf, ?_⟩
  rintro q ⟨j₁, b⟩ j₂ hj
  dsimp only [imap_general_seek, imap_general_σ, imap_general_valid]
  dsimp at q
  suffices ∀ i, f i = j₂ → s.eval (s.seek q (g (s.index q) j₁, b)) i = s.eval q i by sorry
  rintro i rfl
  by_cases le : s.index q ≤ i
  · apply ‹IsLawful s›.seek_spec
    have : (g i j₁, b) ≤ₗ (i, false) := sorry
    refine le_trans ?_ this
    simp only [Prod.Lex.mk_snd_mono_le_iff]
    exact hg _ le
  · rw [s.mono.eq_zero_of_lt_index, s.mono.eq_zero_of_lt_index]
    · simpa using le
    · refine lt_of_lt_of_le ?_ (s.mono q _)
      simpa using le

end Etch.Verification.Stream
