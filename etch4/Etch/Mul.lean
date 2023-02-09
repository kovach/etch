import Etch.Stream

variable {ι : Type} [Tagged ι] [DecidableEq ι] [Max ι]

def S.mul [HMul α β γ] (a : S ι α) (b : S ι β) : (S ι γ) where
  σ := a.σ × b.σ
  value p := a.value p.1 * b.value p.2
  skip  p := λ i => a.skip p.1 i;; b.skip p.2 i
  succ  p i := a.succ p.1 i;; b.succ p.2 i
  ready p := a.ready p.1 * b.ready p.2 * (a.index p.1 == b.index p.2)
  index p := .call .max ![a.index p.1, b.index p.2]
  valid p := a.valid p.1 * b.valid p.2
  init    := seqInit a b

--class Telescope (α β : Type _) where
--  map (f : α → β) : F ι α → F ι β
--class Zip (α β : Type _) (γ : outParam Type _) where

class NatLT (m n : ℕ) where proof : m < n
instance NatLT.zero (n : ℕ) : NatLT 0 n.succ := ⟨Nat.succ_pos _⟩
instance NatLT.succ (m n : ℕ) [h : NatLT m n] : NatLT (m+1) (n+1) :=
⟨Nat.succ_lt_succ h.proof⟩

class Rank (α : Type _) (n : ℕ)

class TypeLT (α β : Type)
instance [Rank α m] [Rank β n] [NatLT m n] : TypeLT α β := ⟨⟩

class Prism (F : Type → Type _ → Type _) where
  map {ι} (f : α → β) : F ι α → F ι β

section Prism

variable
(f₁ f₂ : Type → Type _ → Type _)
[Prism f₁] [Prism f₂]

instance [TypeLT ι₁ ι₂] [HMul α₁ (f₂ ι₂ α₂) γ] : HMul (f₁ ι₁ α₁) (f₂ ι₂ α₂) (f₁ ι₁ γ)
  where hMul a b := Prism.map (. * b) a
instance [TypeLT ι₂ ι₁] [HMul (f₁ ι₁ α₁) α₂ γ] : HMul (f₁ ι₁ α₁) (f₂ ι₂ α₂) (f₂ ι₂ γ)
  where hMul a b := Prism.map (a * .) b

instance [HMul β (E α) γ] : HMul (f₁ ι₁ β) (E α) (f₁ ι₁ γ)
  where hMul a b := Prism.map (. * b) a
instance [HMul (E α) β γ] : HMul (E α) (f₁ ι₁ β) (f₁ ι₁ γ)
  where hMul a b := Prism.map (a * .) b

end Prism

instance [HMul α β γ] : HMul (ι →ₛ α) (ι →ₛ β) (ι →ₛ γ) := ⟨S.mul⟩
instance [HMul α β γ] : HMul (ι →ₐ α) (ι →ₐ β) (ι →ₐ γ) := ⟨fun a b v ↦ a v * b v⟩
instance [HMul α β γ] : HMul (ι →ₛ α) (ι →ₐ β) (ι →ₛ γ) := ⟨fun a b ↦ {a with value := λ s => a.value s * b (a.index s)}⟩
instance [HMul β α γ] : HMul (ι →ₐ β) (ι →ₛ α) (ι →ₛ γ) := ⟨fun a b ↦ {b with value := λ s => a (b.index s) * b.value s}⟩

--instance [HMul α β γ] : HMul (ι →ₛ. α) (ι →ₛ. β) (ι →ₛ. γ) := ⟨fun a b ↦ { a.toS * b.toS with state := (a.state, b.state)}⟩

/-instance [Prism f₁] [HMul α₁ α₂ γ]
  HMul (f₁ ι₁ α₁) (f₁ ι₁ α₁) (f₁ ι₁ γ)
  where hMul a b := Prism.map (a * .) b
  -/

def i := ℕ deriving Tagged, Max, DecidableEq
local instance : Rank i 0 := ⟨⟩
def j := ℕ deriving Tagged, Max, DecidableEq
local instance : Rank j 1 := ⟨⟩
def k := ℕ deriving Tagged, Max, DecidableEq
local instance : Rank k 2 := ⟨⟩

variable
(n : ℕ)
(α β γ : Type)
[HMul α β γ]
[Mul α]
[Mul (E α)]
(v : E α)
(a : i →ₛ E α) (f : i →ₐ E α) (b : j →ₛ E α)
(a' : ℕ →ₛ ℕ →ₛ E α)
(m₁ : i →ₛ j →ₛ E α)
(m₂ : j →ₛ k →ₛ E α)
(m₃ : k →ₛ j →ₛ E α)

#check a * a
instance [∀ ι, Functor (F ι)] : Prism F where
  map f a := @Functor.map (F _) _ _ _ f a

#synth Prism S
#synth Prism Fun

--local instance : TypeLT i j := ⟨⟩
--local instance : TypeLT i k := ⟨⟩
--local instance : TypeLT k j := ⟨⟩
#check a' * a'
#check v * v
#check v * f
#check f * f
#check f * b
#check v * a
#check a * b
#check a * f
--set_option trace.Meta.synthInstance.instances true
#check m₁ * m₂
#check m₁ * m₃


#exit


