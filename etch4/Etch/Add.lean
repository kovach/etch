import Etch.Stream

variable {ι : Type} {α : Type _} [Tagged ι] [DecidableEq ι]
  [LT ι] [LE ι] [DecidableRel (LT.lt : ι → ι → Prop)]
  [DecidableRel (LE.le : ι → ι → _)]

class Guard (α : Type _) where
  guard : E Bool → α → α

instance [Tagged α] [OfNat α (nat_lit 0)] : Guard (E α) where
  guard := λ b v => .call O.ternary ![b, v, (0 : E α)]

instance : Guard (S ι α) where guard := λ b s => {s with valid := λ l => b * s.valid l}

/-- Returns an expression which evaluates to `true` iff `a.index' ≤ b.index'` -/
def S_le (a : S ι α) (b : S ι β) (l : a.σ × b.σ) : E Bool :=
  (.call O.neg ![b.valid l.2]) + (a.valid l.1 * (a.index l.1 <= b.index l.2))

infixr:40 "≤ₛ" => S_le

def Prod.symm (f : α × β) := (f.2, f.1)

def S.add [HAdd α β γ] [Guard α] [Guard β] (a : S ι α) (b : S ι β) : S ι γ where
  σ := (a.σ × b.σ) × Var Bool
  value := λ (p, _) => (Guard.guard ((S_le a b p) * a.ready p.1) $ a.value p.1) +
             (Guard.guard ((S_le b a p.symm) * b.ready p.2) $ b.value p.2)
  skip  := λ (p, _) i => a.skip p.1 i ;; b.skip p.2 i -- TODO: is skip allowed if `a` is invalid, or do we need to guard
                                        -- that `a` is valid?
                                        -- Also, I am assuming you cannot skip backwards (i.e. it becomes a no-op
                                        -- if `i < .index`). Otherwise, each skip should be guarded by `≤ₛ` as well
  succ  := λ (p, t)  => .store_var t (S_le b a p.symm);; P.if1 ((S_le a b p) * a.ready p.1) (a.succ p.1) ;; P.if1 (t * b.ready p.2) (b.succ p.2)
  ready := λ (p, _) => (S_le a b p) * a.ready p.1 + (S_le b a p.symm) * b.ready p.2
  index := λ (p, _) => .call O.ternary ![S_le a b p, a.index p.1, b.index p.2]
  valid := λ (p, _) => a.valid p.1 + b.valid p.2
  init  := λ n => let (i, s) := seqInit a b n; (i, (s, (Var.mk "temp").fresh n))

instance [Add α] [Guard α] : Add (ι →ₛ α) := ⟨S.add⟩
instance [HAdd α β γ] [Guard α] [Guard β] : HAdd (S ι α) (S ι β) (S ι γ) := ⟨S.add⟩
instance [HAdd α β γ] : HAdd (ι →ₐ α) (ι →ₐ β) (ι →ₐ γ) where hAdd a b := λ v => a v + b v
