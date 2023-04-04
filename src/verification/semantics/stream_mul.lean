import verification.semantics.skip_stream

lemma mul_eq_zero_of {α : Type*} [mul_zero_class α] {x y : α} : x = 0 ∨ y = 0 → x * y = 0
| (or.inl h) := by { rw h, exact zero_mul y, }
| (or.inr h) := by { rw h, exact mul_zero x, }

open_locale streams
variables {ι : Type} [linear_order ι] {α : Type*}

@[mk_iff]
structure Stream.mul.ready {ι : Type} (a : Stream ι α) (b : Stream ι α) (s : a.σ × b.σ) : Prop :=
(v₁ : a.valid s.1)
(v₂ : b.valid s.2)
(r₁ : a.ready s.1)
(r₂ : b.ready s.2)
(index : a.index s.1 v₁ = b.index s.2 v₂)

@[simps]
def Stream.mul [has_mul α] (a b : Stream ι α) : Stream ι α :=
{ σ := a.σ × b.σ,
  valid := λ p, a.valid p.1 ∧ b.valid p.2,
  ready := λ p, Stream.mul.ready a b p,
  skip := λ p hp i, (a.skip p.1 hp.1 i, b.skip p.2 hp.2 i),
  index := λ p hv, max (a.index p.1 hv.1) (b.index p.2 hv.2),
  value := λ p hr, a.value p.1 hr.r₁ * b.value p.2 hr.r₂ }

section index_lemmas
variables [has_mul α]

lemma Stream.mul.ready.index' {a : Stream ι α} {b : Stream ι α} {x y} (h : (a.mul b).ready (x, y)) :
  a.index' x = b.index' y :=
by simp [Stream.index'_val h.v₁, Stream.index'_val h.v₂, h.index]

lemma Stream.mul.ready.order_eq {a : Stream ι α} {b : Stream ι α} {x y} (h : (a.mul b).ready (x, y)) :
  a.to_order x h.v₁ = b.to_order y h.v₂ :=
by { dsimp only [Stream.to_order], simp [h.r₁, h.r₂, h.index], }

lemma Stream.mul_index' (a b : Stream ι α) (xy : a.σ × b.σ) :
  (a.mul b).index' xy = max (a.index' xy.1) (b.index' xy.2) :=
begin
  cases xy with x y,
  rw [Stream.index'],
  simp only [Stream.mul_index, with_top.coe_max],
  split_ifs with h,
  { simp [Stream.index'_val h.1, Stream.index'_val h.2], },
  erw not_and_distrib at h, cases h; simp [h],
end

lemma order_eq_of_mul_ready {a b : Stream ι α} {x y} (h : (a.mul b).ready (x, y)) :
  a.to_order x h.v₁ = (a.mul b).to_order (x, y) ⟨h.v₁, h.v₂⟩ ∧ b.to_order y h.v₂ = (a.mul b).to_order (x, y) ⟨h.v₁, h.v₂⟩ :=
by { split; simp only [Stream.to_order, h, h.r₁, h.r₂]; simp [h.index], } 

/-- This lemma takes a surprising amount of effort to prove -/
lemma min_to_order_le (a b : Stream ι α) (q : a.σ × b.σ) (hv : (a.mul b).valid q) :
  min (a.to_order q.1 hv.1) (b.to_order q.2 hv.2) ≤ (a.mul b).to_order q hv :=
begin
  rw prod.lex.le_iff'', 
  simp only [monotone.map_min (@prod.lex.fst_mono ι bool _ _)],
  split, { exact min_le_max, },
  intro h,
  simp only [Stream.to_order_fst, Stream.mul_index, max_eq_min_iff] at h,
  suffices : a.ready q.1 → b.ready q.2 → (a.mul b).ready q,
  { simpa [Stream.to_order, h, prod.lex.mk_min, bool.min_eq_and, bool.le_iff_imp], },
  intros hr₁ hr₂,
  refine ⟨hv.1, hv.2, hr₁, hr₂, _⟩,
  simpa [hv.1, hv.2] using h,
end

lemma to_order_le_max (a b : Stream ι α) (q : a.σ × b.σ) (hv : (a.mul b).valid q) :
  (a.mul b).to_order q hv ≤ max (a.to_order q.1 hv.1) (b.to_order q.2 hv.2) :=
begin
  rw prod.lex.le_iff', right, split,
  { simp [monotone.map_max (@prod.lex.fst_mono ι bool _ _), Stream.mul_index'], },
  simp only [bool.le_iff_imp, Stream.to_order_snd, bool.of_to_bool_iff],
  intro hr, cases q with qa qb,
  simpa [order_eq_of_mul_ready hr],
end

instance Stream.mul.is_bounded (a b : Stream ι α) [is_bounded a] [is_bounded b] : is_bounded (a.mul b) :=
⟨⟨prod.rprod_eq a.wf_rel b.wf_rel, prod.rprod_eq_wf a.wf b.wf,
λ q hq i, begin
  rcases a.wf_valid q.1 hq.1 i with (h|⟨ha₁, ha₂⟩),
  { exact or.inl (or.inl ⟨h, b.no_backward _ _ _⟩), },
  rcases b.wf_valid q.2 hq.2 i with (h|⟨hb₁, hb₂⟩),
  { exact or.inl (or.inr ⟨h, a.no_backward _ _ _⟩), },
  right, split, swap,
  { dsimp, simp [ha₂, hb₂], },
  exact lt_of_lt_of_le (lt_min ha₁ hb₁) (min_to_order_le _ _ _ hq),
end⟩⟩

end index_lemmas

section value_lemmas
variables [non_unital_non_assoc_semiring α]

lemma mul_eval₀_of_neq {a : Stream ι α} {b : Stream ι α} {x y} (H : (a.mul b).valid (x, y)) (h : a.to_order x H.1 ≠ b.to_order y H.2) :
  (a.mul b).eval₀ (x, y) H = 0 :=
by { contrapose! h, apply Stream.mul.ready.order_eq, simp [Stream.eval₀] at h, exact h.fst, }

lemma mul_eval₀ (a b : Stream ι α) (x : a.σ) (y : b.σ) (H) :
  (a.mul b).eval₀ (x, y) H = (a.eval₀ x H.1) * (b.eval₀ y H.2) :=
begin
  rw [Stream.eval₀], split_ifs with hr,
  { simp [Stream.eval₀, hr.r₁, hr.r₂, hr.index], },
  simp [Stream.mul.ready_iff, H.1, H.2] at hr,
  simp [Stream.eval₀], split_ifs with h₁ h₂; try { simp },
  rw finsupp.mul_single_eq_zero _ _ (hr h₁ h₂),
end

lemma mul_eval₀_spec (a b : Stream ι α) [is_bounded a] [is_bounded b]
  (ha : a.is_strict_mono) (hb : b.is_strict_mono) (q : (a.mul b).σ) (hv : (a.mul b).valid q) :
  (a.mul b).eval₀ q hv = ((a.eval q.1) * (b.eval q.2)).filter (λ i, (i, ff) <ₗ (a.mul b).to_order q hv) :=
begin
  classical,
  by_cases H : (a.mul b).ready q,
  { cases q with qa qb,
    calc (a.mul b).eval₀ (qa, qb) hv 
        = (a.eval₀ qa hv.1) * (b.eval₀ qb hv.2) : by { dsimp, rw [mul_eval₀], }
    ... = (a.eval qa).filter (λ i, (i, ff) <ₗ a.to_order qa hv.1) *
            (b.eval qb).filter (λ i, (i, ff) <ₗ b.to_order qb hv.2) : by rw [ha.eval₀_eq_eval_filter, hb.eval₀_eq_eval_filter]
    ... = ((a.eval qa) * (b.eval qb)).filter (λ i, (i, ff) <ₗ min (a.to_order qa hv.1) (b.to_order qb hv.2)) : by simp only [finsupp.mul_filter, lt_min_iff]
    ... = ((a.eval qa) * (b.eval qb)).filter (λ i, (i, ff) <ₗ (a.mul b).to_order (qa, qb) hv) : 
            by { congr, ext i, simp [(order_eq_of_mul_ready H).1, (order_eq_of_mul_ready H).2], refl, } },
  { symmetry,
    simp only [Stream.eval₀, H, dif_neg, not_false_iff, finsupp.filter_eq_zero_iff, Stream.to_order,
      to_bool_false_eq_ff, prod.lex.mk_snd_mono_lt_iff, finsupp.mul_apply, Stream.mul_index, lt_max_iff],
    intros i hi, 
    refine mul_eq_zero_of (hi.imp (λ h, ha.1.eq_zero_of_lt_index i _) (λ h, hb.1.eq_zero_of_lt_index i _));
    simpa [hv.1, hv.2] using h, }
end

lemma mul_mono {a b : Stream ι α} (ha : a.is_monotonic) (hb : b.is_monotonic) :
  (a.mul b).is_monotonic :=
by { intros q hv i, simp only [Stream.mul_index'], exact max_le_max (ha _ _ _) (hb _ _ _), }

lemma mul_strict_mono {a b : Stream ι α} (ha : a.is_strict_mono) (hb : b.is_strict_mono) :
  (a.mul b).is_strict_mono :=
⟨mul_mono ha.1 hb.1, λ q hv i H hr, ne_of_lt begin
  simp only [Stream.mul_index'],
  cases q with qa qb,
  refine max_lt_max (ha.lt _ _ _ _ hr.r₁) (hb.lt _ _ _ _ hr.r₂);
  simpa [order_eq_of_mul_ready hr],
end⟩

lemma next_eval_mul_eq (a b : Stream ι α) [is_strict_lawful a] [is_strict_lawful b] (q : (a.mul b).σ) (hv : (a.mul b).valid q) :
  (a.eval ((a.mul b).next q).1) * (b.eval ((a.mul b).next q).2) =
    ((a.eval q.1) * (b.eval q.2)).filter (λ i, (a.mul b).to_order q hv ≤ (i, ff)) :=
begin
  ext j,
  simp only [finsupp.mul_apply, finsupp.filter_apply, Stream.next_val hv],
  split_ifs with hj,
  { simp only [Stream.to_order, Stream.index'_val hv, Stream.mul_skip] at hj ⊢,
    rw [is_lawful.skip_spec q.1 hv.1 _ _ hj, is_lawful.skip_spec q.2 hv.2 _ _ hj], },
  change (a.eval (a.skip _ _ _) j) * (b.eval (b.skip _ _ _) j) = 0,
  rw not_le at hj,
  cases (le_max_iff.mp $ to_order_le_max _ _ _ hv) with hj' hj',
  { rw [a.strict_mono.eval_skip_eq_zero, zero_mul]; assumption, },
  { rw [b.strict_mono.eval_skip_eq_zero, mul_zero]; assumption, },
end

lemma mul_spec (a b : Stream ι α) [is_strict_lawful a] [is_strict_lawful b] (q : (a.mul b).σ) :
  ((a.mul b).eval q) = (a.eval q.1) * (b.eval q.2) :=
begin
  refine @well_founded.induction _ (a.mul b).wf_rel (a.mul b).wf _ q _,
  clear q, intros q ih,
  by_cases hv : (a.mul b).valid q, swap,
  { cases not_and_distrib.mp hv with hv' hv'; simp [hv, hv'], },
  rw [Stream.eval_valid _ _ hv, ih _ ((a.mul b).next_wf q hv),
    next_eval_mul_eq _ _ _ hv, mul_eval₀_spec _ _ a.strict_mono b.strict_mono _ hv],
  convert finsupp.filter_pos_add_filter_neg _ _,
  simp,
end

lemma mul_skip_spec (a b : Stream ι α) [is_strict_lawful a] [is_strict_lawful b] (q : (a.mul b).σ) (hq : (a.mul b).valid q)
  (i : ι ×ₗ bool) (j : ι) (h : i ≤ₗ (j, ff)) :
  (a.mul b).eval ((a.mul b).skip q hq i) j = (a.mul b).eval q j :=
begin
  simp only [finsupp.mul_apply, mul_spec], congr' 1;
  { dsimp, rwa is_lawful.skip_spec, }
end

instance Stream.mul.is_strict_lawful (a b : Stream ι α) [is_strict_lawful a] [is_strict_lawful b] : is_strict_lawful (a.mul b) :=
{ skip_spec := mul_skip_spec a b,
  mono := (mul_strict_mono a.strict_mono b.strict_mono).1,
  strict_mono := mul_strict_mono a.strict_mono b.strict_mono, }

instance : has_mul (Stream ι α) := ⟨Stream.mul⟩

@[simp] lemma StrictLawfulStream.mul_spec (a b : Stream ι α) [is_strict_lawful a] [is_strict_lawful b] (q : (a * b).σ) :
  (a * b).eval q = (a.eval q.1) * (b.eval q.2) :=
by { change (a.mul b).eval q = _, rw mul_spec, }

end value_lemmas
