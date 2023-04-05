import verification.semantics.skip_stream

noncomputable theory
open_locale streams
variables {ι : Type} [linear_order ι] {α : Type*}

@[simps] def Stream.add [has_zero α] [has_add α] (a b : Stream ι α) : Stream ι α :=
{ σ := a.σ × b.σ,
  valid := λ s, a.valid s.1 ∨ b.valid s.2,
  ready := λ s, (a.to_order' s.1 ≤ b.to_order' s.2 ∧ a.ready s.1) ∨ (b.to_order' s.2 ≤ a.to_order' s.1 ∧ b.ready s.2),
  skip := λ p hp i, (a.skip' p.1 i, b.skip' p.2 i),
  index := λ s h, option.get (show (min (a.index' s.1) (b.index' s.2)).is_some, by simpa),
  value := λ s h, (if a.to_order' s.1 ≤ b.to_order' s.2 then a.value' s.1 else 0) +
                  (if b.to_order' s.2 ≤ a.to_order' s.1 then b.value' s.2 else 0) } 

section index_lemmas
variables [has_zero α] [has_add α]

@[simp] lemma add_index_eq_min {a b : Stream ι α} (q : (a.add b).σ) :
  (a.add b).index' q = min (a.index' q.1) (b.index' q.2) :=
by { by_cases H : (a.add b).valid q, { simp [H], }, { simp [H, not_or_distrib.mp H], } }

lemma valid_of_to_order_lt {a b : Stream ι α} {qa : a.σ} {qb : b.σ} (h : a.to_order' qa < b.to_order' qb) :
  a.valid qa :=
by { contrapose! h, by_cases hb : b.valid qb, { rw prod.lex.le_iff', left, simpa [h], }, { simp [Stream.to_order', h, hb], } }

@[simp] lemma add_skip_fst {a b : Stream ι α} (q i) : ((a.add b).skip' q i).fst = a.skip' q.1 i :=
by { simp only [Stream.skip'], split_ifs with h₁ h₂ h₂, { simp [h₂], }, { simp [h₂], }, { cases h₁ (or.inl h₂), }, { refl, }, }

@[simp] lemma add_skip_snd {a b : Stream ι α} (q i) : ((a.add b).skip' q i).snd = b.skip' q.2 i :=
by { simp only [Stream.skip'], split_ifs with h₁ h₂ h₂, { simp [h₂], }, { simp [h₂], }, { cases h₁ (or.inr h₂), }, { refl, }, }

lemma of_to_order_eq {a b : Stream ι α} (q : (a.add b).σ) (h : a.to_order' q.1 = b.to_order' q.2) :
  (¬((a.add b).valid q) ∧ ¬(a.valid q.1) ∧ ¬(b.valid q.2)) ∨
  ((a.add b).valid q ∧ a.valid q.1 ∧ b.valid q.2 ∧ (a.ready q.1 ↔ b.ready q.2) ∧ a.index' q.1 = b.index' q.2) :=
begin
  have : a.index' q.1 = b.index' q.2 := by simpa using congr_arg prod.fst h,
  by_cases H : (a.add b).valid q,
  { right, 
    obtain ⟨hv₁, hv₂⟩ : a.valid q.1 ∧ b.valid q.2, { simp only [← Stream.index'_lt_top_iff] at H ⊢, simpa [this, -Stream.index'_lt_top_iff] using H, },
    refine ⟨H, hv₁, hv₂, _, this⟩,
    simpa [hv₁, hv₂] using congr_arg prod.snd h, },
  { left, refine ⟨H, not_or_distrib.mp H⟩, },
end

lemma add_to_order_eq_min {a b : Stream ι α} (q : (a.add b).σ) :
  (a.add b).to_order' q = min (a.to_order' q.1) (b.to_order' q.2) :=
begin
  rcases lt_trichotomy (a.to_order' q.1) (b.to_order' q.2) with (h|h|h),
  { rw min_eq_left h.le, ext : 1,
    { simpa using prod.lex.fst_le_of_le h.le, },
    { simp [valid_of_to_order_lt h, h.le, h.not_le], }, },
  { rcases of_to_order_eq _ h with (⟨H, hv₁, hv₂⟩|⟨H, hv₁, hv₂, hr, hi⟩),
    { simp [Stream.to_order', H, hv₁, hv₂], },
    ext : 1, { simp [h, hi], }, simp [Stream.to_order'_val_snd H, h, Stream.to_order'_val_snd hv₂, hr], },
  { rw min_eq_right h.le, ext : 1,
    { simpa using prod.lex.fst_le_of_le h.le, },
    { simp [valid_of_to_order_lt h, h.le, h.not_le], }, },
end

lemma add_to_order_left {a b : Stream ι α} {q : (a.add b).σ} (hq hq') (ha : a.to_order' q.1 ≤ b.to_order' q.2) :
  (a.add b).to_order q hq = a.to_order q.1 hq' :=
coe_lex_injective (by simpa [add_to_order_eq_min])

lemma add_to_order_right {a b : Stream ι α} {q : (a.add b).σ} (hq hq') (ha : b.to_order' q.2 ≤ a.to_order' q.1) :
  (a.add b).to_order q hq = b.to_order q.2 hq' :=
coe_lex_injective (by simpa [add_to_order_eq_min])

instance Stream.add.is_bounded (a b : Stream ι α) [is_bounded a] [is_bounded b] : is_bounded (a.add b) :=
is_bounded.mk' ⟨prod.rprod_eq a.wf_rel b.wf_rel, prod.rprod_eq_wf a.wf b.wf, λ q i, begin
  rcases a.wf_valid' q.1 i with (h|⟨ha₁, ha₂⟩),
  { left, left, simp only [add_skip_fst, add_skip_snd], exact ⟨h, (b.wf_valid' q.2 i).imp_right and.right⟩, },
  rcases b.wf_valid' q.2 i with (h|⟨hb₁, hb₂⟩),
  { left, right, simp only [add_skip_fst, add_skip_snd], exact ⟨h, (a.wf_valid' q.1 i).imp_right and.right⟩, },
  right, split,
  { rw [add_to_order_eq_min, lt_min_iff], split; assumption, }, { ext; simpa, }
end⟩

lemma add_mono {a b : Stream ι α}  (ha : a.is_monotonic) (hb : b.is_monotonic) : (a.add b).is_monotonic :=
by { intros q hv i, simp only [add_index_eq_min], exact min_le_min (ha.skip' _ _) (hb.skip' _ _), }

lemma add_strict_mono {a b : Stream ι α} (ha : a.is_strict_mono) (hb : b.is_strict_mono) : (a.add b).is_strict_mono :=
⟨add_mono ha.1 hb.1, λ q hq i hi hr, ne_of_lt begin
  replace hi : min (a.to_order' q.1) (b.to_order' q.2) ≤ coe_lex i, { rwa [← add_to_order_eq_min, ← Stream.coe_lex_to_order hq, coe_lex_le_iff], },
  rcases (lt_trichotomy (a.to_order' q.1) (b.to_order' q.2)) with (h|h|h),
  { replace hr : a.ready q.1 := by simpa [h.le, h.not_le] using hr,
    have hqa : a.valid q.1 := valid_of_to_order_lt h,
    replace hi : a.to_order q.1 hqa ≤ i, { rw [min_eq_left h.le] at hi, rwa [← coe_lex_le_iff, Stream.coe_lex_to_order], }, 
    have : a.index' q.1 < b.index' q.2, { refine prod.lex.fst_lt_of_lt_of_le h _, simp [hqa, hr], },
    simp only [add_index_eq_min, min_eq_left this.le, Stream.add_skip, add_index_eq_min, lt_min_iff, Stream.skip'_val hqa],
    split, { exact ha.lt _ _ _ hi hr, }, { refine this.trans_le _, apply hb.1.skip', }, },
  { obtain ⟨hv₀, hv₁, hv₂, hr_iff, hind⟩ := (of_to_order_eq _ h).resolve_left (λ h', h'.1 hq),
    simp only [add_index_eq_min, hind, min_self, Stream.add_skip, lt_min_iff],
    obtain ⟨hr₁, hr₂⟩ : a.ready q.1 ∧ b.ready q.2, { split; simpa [h, hr_iff] using hr, }, 
    split,
    { rw [← hind, Stream.skip'_val hv₁], rw [← h, min_self, ← Stream.coe_lex_to_order hv₁, coe_lex_le_iff] at hi, exact ha.lt _ _ _ hi hr₁, },
    { rw [Stream.skip'_val hv₂], rw [h, min_self, ← Stream.coe_lex_to_order hv₂, coe_lex_le_iff] at hi, exact hb.lt _ _ _ hi hr₂, }, },
  { replace hr : b.ready q.2 := by simpa [h.le, h.not_le] using hr,
    have hqb : b.valid q.2 := valid_of_to_order_lt h,
    replace hi : b.to_order q.2 hqb ≤ i, { rw [min_eq_right h.le] at hi, rwa [← coe_lex_le_iff, Stream.coe_lex_to_order], }, 
    have : b.index' q.2 < a.index' q.1, { refine prod.lex.fst_lt_of_lt_of_le h _, simp [hqb, hr], },
    simp only [add_index_eq_min, min_eq_right this.le, Stream.add_skip, add_index_eq_min, lt_min_iff, Stream.skip'_val hqb],
    split, swap, { exact hb.lt _ _ _ hi hr, }, { refine this.trans_le _, apply ha.1.skip', }, },
end⟩

end index_lemmas

section value_lemmas
variables [add_comm_monoid α]

lemma Stream.add.eval₀_eq_left {a b : Stream ι α} {q : (a.add b).σ} (hq : (a.add b).valid q) (H : a.to_order' q.1 < b.to_order' q.2) :
  (a.add b).eval₀ q hq = a.eval₀ q.1 (valid_of_to_order_lt H) :=
begin
  have := add_to_order_left hq (valid_of_to_order_lt H) H.le,
  have hr : (a.add b).ready q ↔ a.ready q.1, { simpa using congr_arg prod.snd this, },
  simp only [Stream.eval₀, ← Stream.value'_val, dite_eq_ite], rw [hr],
  split_ifs with hr', swap, { refl, },
  congr' 1, { simpa using congr_arg prod.fst this, },
  simp [@Stream.value'_val _ _ _ (a.add b) _ (or.inl ⟨H.le, hr'⟩), H.le, H.not_le],
end

lemma Stream.add.eval₀_eq_right {a b : Stream ι α} {q : (a.add b).σ} (hq : (a.add b).valid q) (H : b.to_order' q.2 < a.to_order' q.1) :
  (a.add b).eval₀ q hq = b.eval₀ q.2 (valid_of_to_order_lt H) :=
begin
  have := add_to_order_right hq (valid_of_to_order_lt H) H.le,
  have hr : (a.add b).ready q ↔ b.ready q.2, { simpa using congr_arg prod.snd this, },
  simp only [Stream.eval₀, ← Stream.value'_val, dite_eq_ite], rw [hr],
  split_ifs with hr', swap, { refl, },
  congr' 1, { simpa using congr_arg prod.fst this, },
  simp [@Stream.value'_val _ _ _ (a.add b) _ (or.inr ⟨H.le, hr'⟩), H.le, H.not_le],
end

lemma Stream.add.eval₀_eq_both {a b : Stream ι α} {q : (a.add b).σ} (hq : (a.add b).valid q) (H : a.to_order' q.1 = b.to_order' q.2) (hv₁ hv₂) (hr : a.ready q.1 ↔ b.ready q.2) 
  (hi : a.index q.1 hv₁ = b.index q.2 hv₂) : (a.add b).eval₀ q hq = a.eval₀ q.1 hv₁ + b.eval₀ q.2 hv₂ :=
begin
  have : (a.add b).ready q ↔ b.ready q.2, { simp [H, hr], },
  simp only [Stream.eval₀, ← Stream.value'_val, dite_eq_ite], rw [this, hr],
  split_ifs with hr', swap, { simp, },
  rw [hi, ← finsupp.single_add, Stream.add_index, @Stream.value'_val _ _ _ (a.add b)],
  { simp [Stream.index'_val hv₁, Stream.index'_val hv₂, hi, -finsupp.single_add, H], },
  right, refine ⟨_, hr'⟩, rw [H],
end

lemma Stream.add_spec (a b : Stream ι α) [is_lawful a] [is_lawful b] (q : (a.add b).σ) :
  (a.add b).eval q = (a.eval q.1) + (b.eval q.2) :=
begin
  refine @well_founded.induction _ (a.add b).wf_rel (a.add b).wf _ q _,
  clear q, intros q ih,
  rcases lt_trichotomy (a.to_order' q.1) (b.to_order' q.2) with (h|h|h),
  { have hv : a.valid q.1 := valid_of_to_order_lt h,
    have hq : (a.add b).valid q := or.inl hv,
    rw [(a.add b).eval_valid q hq, ih _ ((a.add b).next_wf _ hq), Stream.next_val hq, Stream.add_skip, @Stream.skip'_lt_to_order _ _ _ _ b,
      add_to_order_left hq hv h.le, Stream.skip'_val hv, a.eval_valid _ hv, add_assoc, Stream.add.eval₀_eq_left hq h, Stream.next_val hv],
    simpa [add_to_order_eq_min], },
  { rcases of_to_order_eq _ h with (⟨H, hv₁, hv₂⟩|⟨hq, hv₁, hv₂, hr, hi⟩),
    { simp [H, hv₁, hv₂], },
    obtain ⟨t₀, t₁⟩ : (a.add b).to_order q hq = a.to_order q.1 hv₁ ∧ (a.add b).to_order q hq = b.to_order q.2 hv₂,
    { split; apply_fun coe_lex using coe_lex_injective; simp [add_to_order_eq_min, h], },
    simp only [Stream.index'_val, hv₁, hv₂, with_top.coe_eq_coe] at hi,
    rw [(a.add b).eval_valid q hq, ih _ ((a.add b).next_wf _ hq), Stream.next_val hq, Stream.add_skip, Stream.add.eval₀_eq_both hq h hv₁ hv₂ hr hi,
      (show ∀ (w x y z : ι →₀ α), (w + x) + (y + z) = (w + y) + (x + z), by intros; abel)], dsimp only,
    congr' 1,
    { rw [a.eval_valid _ hv₁, Stream.next_val hv₁, t₀, Stream.skip'_val hv₁], },
    { rw [b.eval_valid _ hv₂, Stream.next_val hv₂, t₁, Stream.skip'_val hv₂], }, },
  { have hv : b.valid q.2 := valid_of_to_order_lt h,
    have hq : (a.add b).valid q := or.inr hv,
    rw [(a.add b).eval_valid q hq, ih _ ((a.add b).next_wf _ hq), Stream.next_val hq, Stream.add_skip, @Stream.skip'_lt_to_order _ _ _ _ a,
      add_to_order_right hq hv h.le, Stream.skip'_val hv, b.eval_valid _ hv, add_left_comm, Stream.add.eval₀_eq_right hq h, Stream.next_val hv],
    simpa [add_to_order_eq_min], },
end

instance (a b : Stream ι α) [is_lawful a] [is_lawful b] : is_lawful (a.add b) :=
⟨add_mono a.mono b.mono, λ q hq i j hj, begin
  simp only [Stream.add_spec], dsimp,
  congr' 1; rwa Stream.skip'_spec,
end⟩

instance (a b : Stream ι α) [is_strict_lawful a] [is_strict_lawful b] : is_strict_lawful (a.add b) :=
{ strict_mono := add_strict_mono a.strict_mono b.strict_mono }

end value_lemmas




