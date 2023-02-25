import verification.semantics.skip_streamv2

lemma prod.rprod_iff {α β : Type*} {r₁ : α → α → Prop} {r₂ : β → β → Prop} {s₁ s₂ : α × β} :
  (prod.rprod r₁ r₂ s₁ s₂) ↔ r₁ s₁.1 s₂.1 ∧ r₂ s₁.2 s₂.2 :=
⟨by { rintro ⟨h⟩, split; assumption, }, by { rintro ⟨h₁, h₂⟩, cases s₁, cases s₂, exact prod.rprod.intro h₁ h₂, }⟩  

variables {ι : Type} [linear_order ι] {α : Type*}

@[mk_iff]
structure Stream.mul.ready {ι : Type} (a : Stream ι α) (b : Stream ι α) (s : a.σ × b.σ) : Prop :=
(v₁ : a.valid s.1)
(v₂ : b.valid s.2)
(r₁ : a.ready s.1)
(r₂ : b.ready s.2)
(index : a.index s.1 v₁ = b.index s.2 v₂)

@[simps]
instance [has_mul α] : has_mul (Stream ι α) := ⟨λ (a b : Stream ι α),
{ σ := a.σ × b.σ,
  valid := λ p, a.valid p.1 ∧ b.valid p.2,
  ready := λ p, Stream.mul.ready a b p,
  skip := λ p hp i r, (a.skip p.1 hp.1 i r, b.skip p.2 hp.2 i r),
  index := λ p hv, max (a.index p.1 hv.1) (b.index p.2 hv.2),
  value := λ p hr, a.value p.1 hr.r₁ * b.value p.2 hr.r₂ }⟩

variables [non_unital_non_assoc_semiring α]

@[simp]
def LawfulStream.mul (a b : LawfulStream ι α) : Stream ι α := a.to_Stream * b.to_Stream

namespace LawfulStream.mul


local notation a ` ≺ `:50 b := Stream.rel _ a b 

variables {a b : LawfulStream ι α}

def rel {a b : LawfulStream ι α} : (a.σ × b.σ) → (a.σ × b.σ) → Prop :=
prod.rprod a.rel b.rel

local notation a ` ≺ₘ `:50 b := rel a b 

lemma rel_iff  (q₁ q₂ : a.σ × b.σ) :
  (q₁ ≺ₘ q₂) ↔ (q₁.1 ≺ q₂.1) ∧ (q₁.2 ≺ q₂.2) := by rw [rel, prod.rprod_iff]

lemma rel_wf : well_founded (@rel _ _ _ _ a b) := prod.rprod_wf a.rel_wf b.rel_wf



end LawfulStream.mul

-- theorem LawfulStream.mul_spec (s₁ s₂ : LawfulStream ι α) (q₁ : s₁.σ) (q₂ : s₂.σ) :
--   (s₁.mul s₂).eval 
