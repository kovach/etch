import logic.function.basic
import data.finset.basic

namespace function
variables {α β γ δ : Type*} (f : (α → β) → γ)

def has_frame (S : finset α) : Prop :=
∃ (g : (S → β) → γ), f = g ∘ (set.restrict S)

variables {f} {S : finset α}

theorem has_frame_iff [nonempty β] : has_frame f S ↔ ∀ ⦃c₁ c₂ : α → β⦄, (∀ x ∈ S, c₁ x = c₂ x) → f c₁ = f c₂ :=
begin
  split,
  { rintro ⟨g, rfl⟩, intros c₁ c₂ h, dsimp only [function.comp_app],
    congr' 1, ext, simp only [set.restrict_apply], apply h, exact finset.coe_mem x, },
  classical,
  intro h,
  use (λ c : S → β, f (λ v, if h : v ∈ S then c ⟨v, h⟩ else nonempty.some infer_instance)),
  ext c, simp only [function.comp_app], apply h, intros x hx, simp [hx],
end

theorem has_frame.mono {S'} (h : has_frame f S) (hS' : S ⊆ S') : has_frame f S' :=
by { rcases h with ⟨g, rfl⟩, use (λ c : S' → β, g (λ v, c ⟨v.1, hS' v.2⟩)), ext x, simp, congr, }

theorem has_frame.const (α β : Type*) (C : γ) : has_frame (const (α → β) C) ∅ :=
⟨λ _, C, by { ext, simp, skip, }⟩ 

theorem has_frame.postcomp (h : has_frame f S) (g : γ → δ) :
  has_frame (g ∘ f) S :=
by { rcases h with ⟨g', rfl⟩, use (g ∘ g'), }

end function