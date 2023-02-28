import verification.semantics.skip_streamv2

namespace prod
variables {α β : Type*} (r₁ : α → α → Prop) (r₂ : β → β → Prop)

def rprod_eq (s₁ s₂ : α × β) : Prop :=
(r₁ s₁.1 s₂.1 ∧ (r₂ s₁.2 s₂.2 ∨ s₁.2 = s₂.2)) ∨
  (r₂ s₁.2 s₂.2 ∧ (r₁ s₁.1 s₂.1 ∨ s₁.1 = s₂.1))

variables {r₁ r₂}

theorem rprod_eq_sub_lex (s₁ s₂ : α × β) (h : rprod_eq r₁ r₂ s₁ s₂) :
  prod.lex r₁ r₂ s₁ s₂ :=
begin
  cases s₁ with a b, cases s₂ with c d,
  rcases h with (⟨h₁, _⟩|⟨h₁, (h₂|h₂)⟩),
  { exact prod.lex.left _ _ h₁, },
  { exact prod.lex.left _ _ h₂, },
  { dsimp only at h₁ h₂, rw h₂, exact prod.lex.right _ h₁, }
end

theorem rprod_eq_wf (h₁ : well_founded r₁) (h₂ : well_founded r₂) :
  well_founded (rprod_eq r₁ r₂) :=
subrelation.wf rprod_eq_sub_lex (lex_wf h₁ h₂)

end prod

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
  skip := λ p hp i r, (a.skip p.1 hp.1 i r, b.skip p.2 hp.2 i r),
  index := λ p hv, max (a.index p.1 hv.1) (b.index p.2 hv.2),
  value := λ p hr, a.value p.1 hr.r₁ * b.value p.2 hr.r₂ }

section index_lemmas
variables [has_mul α]

lemma Stream.mul.ready.index' {a : Stream ι α} {b : Stream ι α} {x y} (h : (a.mul b).ready (x, y)) :
  a.index' x = b.index' y :=
by simp [Stream.index'_val h.v₁, Stream.index'_val h.v₂, h.index]

lemma Stream.mul.ready.order_eq {a : Stream ι α} {b : Stream ι α} {x y} (h : (a.mul b).ready (x, y)) :
  a.to_order x = b.to_order y :=
by ext : 1; simp [h.r₁, h.r₂, h.index']

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
  a.to_order x = (a.mul b).to_order (x, y) ∧ b.to_order y = (a.mul b).to_order (x, y) :=
by { split; simp only [Stream.to_order, h, h.r₁, h.r₂]; simp [Stream.mul_index', Stream.mul.ready.index' h], } 

/-- This lemma takes a surprising amount of effort to prove -/
lemma min_to_order_le (a b : Stream ι α) (q : a.σ × b.σ) (hv : (a.mul b).valid q) :
  min (a.to_order q.1) (b.to_order q.2) ≤ (a.mul b).to_order q :=
begin
  rw prod.lex.le_iff'', 
  simp only [monotone.map_min (@prod.lex.fst_mono (with_top ι) bool _ _)],
  split, { convert min_le_max, simp [Stream.mul_index'], },
  intro h,
  replace h : a.index' q.1 = b.index' q.2 := by simpa [Stream.mul_index'] using h,
  suffices : a.ready q.1 → b.ready q.2 → (a.mul b).ready q,
  { simpa [Stream.to_order, h, prod.lex.mk_min, bool.min_eq_and, bool.le_iff_imp], },
  intros hr₁ hr₂,
  refine ⟨hv.1, hv.2, hr₁, hr₂, _⟩,
  simpa [hv.1, hv.2] using h,
end

lemma to_order_le_max (a b : Stream ι α) (q : a.σ × b.σ) (hv : (a.mul b).valid q) :
  (a.mul b).to_order q ≤ max (a.to_order q.1) (b.to_order q.2) :=
begin
  rw prod.lex.le_iff', right, split,
  { simp [monotone.map_max (@prod.lex.fst_mono (with_top ι) bool _ _), Stream.mul_index'], },
  simp only [bool.le_iff_imp, Stream.to_order_snd, bool.of_to_bool_iff],
  intro hr, cases q with qa qb,
  simpa [order_eq_of_mul_ready hr],
end

def BoundedStream.mul (a b : BoundedStream ι α) : BoundedStream ι α :=
{ wf_rel := prod.rprod_eq a.wf_rel b.wf_rel,
  wf := prod.rprod_eq_wf a.wf b.wf,
  wf_valid := λ q hq i r, begin
    rcases a.wf_valid q.1 hq.1 i r with (h|⟨ha₁, ha₂⟩),
    { exact or.inl (or.inl ⟨h, b.no_backward _ _ _ _⟩), },
    rcases b.wf_valid q.2 hq.2 i r with (h|⟨hb₁, hb₂⟩),
    { exact or.inl (or.inr ⟨h, a.no_backward _ _ _ _⟩), },
    right, split, swap,
    { dsimp, simp [ha₂, hb₂], },
    exact lt_of_lt_of_le (lt_min ha₁ hb₁) (min_to_order_le _ _ _ hq),
  end ,
  ..(a.mul b.to_Stream) }

@[simp] lemma BoundedStream.mul_to_Stream (a b : BoundedStream ι α) :
  (a.mul b).to_Stream = a.to_Stream.mul b.to_Stream := rfl

end index_lemmas

section value_lemmas
variables [non_unital_non_assoc_semiring α]

lemma mul_eval₀_of_neq {a : Stream ι α} {b : Stream ι α} {x y} (h : a.to_order x ≠ b.to_order y) (H) :
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

lemma mul_eval₀_spec (a b : BoundedStream ι α)
  (ha : a.is_strict_mono) (hb : b.is_strict_mono) (q : (a.mul b).σ) (hv : Stream.valid _ q) :
  (a.mul b).eval₀ q hv = ((a.eval q.1) * (b.eval q.2)).filter (λ i, (↑i, ff) <ₗ (a.mul b).to_order q) :=
begin
  classical,
  by_cases H : (a.mul b).ready q,
  { cases q with qa qb,
    calc (a.mul b).eval₀ (qa, qb) hv 
        = (a.eval₀ qa hv.1) * (b.eval₀ qb hv.2) : by { dsimp, rw [mul_eval₀], }
    ... = (a.eval qa).filter (λ i, (↑i, ff) <ₗ a.to_order qa) *
            (b.eval qb).filter (λ i, (↑i, ff) <ₗ b.to_order qb) : by rw [ha.eval₀_eq_eval_filter, hb.eval₀_eq_eval_filter]
    ... = ((a.eval qa) * (b.eval qb)).filter (λ i, (↑i, ff) <ₗ min (a.to_order qa) (b.to_order qb)) : by simp only [finsupp.mul_filter, lt_min_iff]
    ... = ((a.eval qa) * (b.eval qb)).filter (λ i, (↑i, ff) <ₗ (a.mul b).to_order (qa, qb)) : 
            by { congr, ext i, simp [(order_eq_of_mul_ready H).1, (order_eq_of_mul_ready H).2], refl, } },
  { symmetry,
    simp only [Stream.eval₀, H, dif_neg, not_false_iff, finsupp.filter_eq_zero_iff, Stream.to_order], dsimp only [BoundedStream.mul_to_Stream],
    simp only [to_bool_false_eq_ff, prod.lex.mk_snd_mono_lt_iff, finsupp.mul_apply, Stream.mul_index', lt_max_iff],
    intros i hi, cases hi.imp (ha.1.eq_zero_of_lt_index i) (hb.1.eq_zero_of_lt_index i) with h h; simp [h], }
end

lemma mul_mono {a b : Stream ι α} (ha : a.is_monotonic) (hb : b.is_monotonic) :
  (a.mul b).is_monotonic :=
by { intros q hv i r, simp only [Stream.mul_index'], exact max_le_max (ha _ _ _ _) (hb _ _ _ _), }

lemma mul_strict_mono {a b : Stream ι α} (ha : a.is_strict_mono) (hb : b.is_strict_mono) :
  (a.mul b).is_strict_mono :=
⟨mul_mono ha.1 hb.1, λ q hv i r H hr, ne_of_lt begin
  simp only [Stream.mul_index'],
  cases q with qa qb,
  refine max_lt_max (ha.lt _ _ _ _ _ hr.r₁) (hb.lt _ _ _ _ _ hr.r₂);
  simpa [order_eq_of_mul_ready hr],
end⟩

local notation ` ↑ₛ `:1000 a := a.to_BoundedStream

lemma next_eval_mul_eq (a b : StrictLawfulStream ι α) (q : ((↑ₛa).mul (↑ₛb)).σ) (hv : Stream.valid _ q) :
  (a.eval $ (((↑ₛa).mul (↑ₛb)).next q).1) * (b.eval $ (((↑ₛa).mul (↑ₛb)).next q).2) =
    ((a.eval q.1) * (b.eval q.2)).filter (λ i, ((↑ₛa).mul (↑ₛb)).to_order q ≤ (↑i, ff)) :=
begin
  ext j,
  simp only [finsupp.mul_apply, finsupp.filter_apply, Stream.next_val hv],
  split_ifs with hj,
  { simp only [Stream.to_order, Stream.index'_val hv] at hj,
    dsimp only [BoundedStream.mul_to_Stream, Stream.mul_skip] at hj ⊢,
    rw [a.skip_spec q.1 hv.1 _ _ _ hj, b.skip_spec q.2 hv.2 _ _ _ hj], },
  change (a.eval (a.skip _ _ _ _) j) * (b.eval (b.skip _ _ _ _) j) = 0,
  rw not_le at hj,
  cases (le_max_iff.mp $ to_order_le_max _ _ _ hv) with hj' hj',
  { rw [a.strict_mono.eval_skip_eq_zero, zero_mul],
    { convert hj, rw [Stream.index'_val hv], }, { convert hj', rw ← Stream.index'_val, refl, }, },
  { rw [b.strict_mono.eval_skip_eq_zero, mul_zero],
    { convert hj, rw [Stream.index'_val hv], }, { convert hj', rw ← Stream.index'_val, refl, }, },
  
end

lemma mul_spec (a b : StrictLawfulStream ι α) (q : ((↑ₛa).mul (↑ₛb)).σ) :
  (BoundedStream.eval _ q) = (a.eval q.1) * (b.eval q.2) :=
begin
  refine @well_founded.induction _ (a.to_BoundedStream.mul b.to_BoundedStream).wf_rel (a.to_BoundedStream.mul b.to_BoundedStream).wf _ q _,
  clear q, intros q ih,
  by_cases hv : ((↑ₛa).mul (↑ₛb)).valid q, swap,
  { cases not_and_distrib.mp hv with hv' hv'; simp [hv, hv'], },
  rw [BoundedStream.eval_valid _ _ hv, ih _ (((↑ₛa).mul (↑ₛb)).next_wf q hv),
    next_eval_mul_eq _ _ _ hv, mul_eval₀_spec _ _ a.strict_mono b.strict_mono _ hv],
  convert finsupp.filter_pos_add_filter_neg _ _,
  simp,
end

lemma mul_skip_spec (a b : StrictLawfulStream ι α) (q : ((↑ₛa).mul (↑ₛb)).σ) (hq : Stream.valid _ q)
  (i : ι) (r : bool) (j : ι) (h : ((↑i : with_top ι), r) ≤ₗ (↑j, ff)) :
  ((↑ₛa).mul (↑ₛb)).eval (((↑ₛa).mul (↑ₛb)).skip q hq i r) j = ((↑ₛa).mul (↑ₛb)).eval q j :=
begin
  simp only [finsupp.mul_apply, mul_spec], congr' 1;
  { dsimp, rw LawfulStream.skip_spec, assumption, }
end

def StrictLawfulStream.mul (a b : StrictLawfulStream ι α) : StrictLawfulStream ι α :=
{ skip_spec := mul_skip_spec a b,
  mono := (mul_strict_mono a.strict_mono b.strict_mono).1,
  strict_mono := mul_strict_mono a.strict_mono b.strict_mono,
  ..(a.to_BoundedStream.mul b.to_BoundedStream) }

instance : has_mul (StrictLawfulStream ι α) := ⟨StrictLawfulStream.mul⟩

@[simp] lemma StrictLawfulStream.mul_spec (a b : StrictLawfulStream ι α) (q : (a * b).σ) :
  (a * b).eval q = (a.eval q.1) * (b.eval q.2) :=
by { change (a.to_BoundedStream.mul b.to_BoundedStream).eval q = _, rw mul_spec, }

end value_lemmas
