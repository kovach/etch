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

variables {ι : Type} [linear_order ι] {α : Type*}

@[mk_iff]
structure Stream.mul.ready {ι : Type} (a : Stream ι α) (b : Stream ι α) (s : a.σ × b.σ) : Prop :=
(v₁ : a.valid s.1)
(v₂ : b.valid s.2)
(r₁ : a.ready s.1)
(r₂ : b.ready s.2)
(index : a.index s.1 v₁ = b.index s.2 v₂)

local notation a ` ≺ `:50 b := Stream.wf_rel _ a b 

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

/-- This lemma takes a surprising amount of effort to prove -/
lemma Stream.min_to_order_le (a b : Stream ι α) (q : a.σ × b.σ) (hv : (a.mul b).valid q) :
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

lemma mul_rel_wf (a b : BoundedStream ι α) : well_founded (prod.rprod_eq a.wf_rel b.wf_rel) :=
prod.rprod_eq_wf a.wf b.wf

lemma mul_is_skip_valid {a b : BoundedStream ι α} (ha : a.skip_valid_wf a.wf_rel) (hb : b.skip_valid_wf b.wf_rel) :
  (a.mul b.to_Stream).skip_valid_wf (prod.rprod_eq a.wf_rel b.wf_rel) :=
begin
  intros q hq i r,
  rcases ha q.1 hq.1 i r with (h|⟨ha₁, ha₂⟩),
  { exact or.inl (or.inl ⟨h, hb.no_backward _ _ _ _⟩), },
  rcases hb q.2 hq.2 i r with (h|⟨hb₁, hb₂⟩),
  { exact or.inl (or.inr ⟨h, ha.no_backward _ _ _ _⟩), },
  right, split, swap,
  { dsimp, simp [ha₂, hb₂], },
  exact lt_of_lt_of_le (lt_min ha₁ hb₁) (Stream.min_to_order_le _ _ _ hq),
end

end index_lemmas
