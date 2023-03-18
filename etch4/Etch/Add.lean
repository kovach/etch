import Etch.Stream

variable {ι : Type} {α : Type _} [Tagged ι] [TaggedC ι] [DecidableEq ι]
  [LT ι] [LE ι] [DecidableRel (LT.lt : ι → ι → Prop)]
  [DecidableRel (LE.le : ι → ι → _)]

-- `guard b s` returns a stream which returns `0` (empty stream) if `b` is false
--  and acts identically to `s` if `b` is true.
class Guard (α : Type _) where
  guard : E Bool → α → α

instance [Tagged α] [OfNat α (nat_lit 0)] : Guard (E α) where
  guard b v := .call Op.ternary ![b, v, (0 : E α)]

instance : Guard (S ι α) where
  guard b s := {s with valid := λ l => b * s.valid l}

instance [Tagged α] [OfNat α (nat_lit 0)] : Guard (ι →ₐ E α) where
  guard b s := Guard.guard b ∘ s

-- Returns an expression which evaluates to `true` iff `a.index' ≤ b.index'`
def S_le (a : S ι α) (b : S ι β) (l : a.σ × b.σ) : E Bool :=
  (.call Op.neg ![b.valid l.2]) + (a.valid l.1 * (a.index l.1 <= b.index l.2))

infixr:40 "≤ₛ" => S_le

def Prod.symm (f : α × β) := (f.2, f.1)

-- Local temporary variables for `add`
structure AddTmp (ι : Type) [TaggedC ι] where
(ci : Var ι)

def AddTmp.ofName (n : Name) : AddTmp ι :=
⟨(Var.mk "ci").fresh n⟩

def S.add [HAdd α β γ] [Guard α] [Guard β] (a : S ι α) (b : S ι β) : S ι γ where
  σ := (a.σ × b.σ) × AddTmp ι
  value := λ (p, _) =>
             (Guard.guard ((S_le a b p) * a.ready p.1) $ a.value p.1) +
             (Guard.guard ((S_le b a p.symm) * b.ready p.2) $ b.value p.2)
  skip  := λ (p, _) i => a.skip p.1 i ;; b.skip p.2 i
  succ  := λ (p, t) i =>
    t.ci.decl i;;
    a.succ p.1 t.ci;; b.succ p.2 t.ci
  ready := λ (p, _) => (S_le a b p) * a.ready p.1 + (S_le b a p.symm) * b.ready p.2
  index := λ (p, _) => .call Op.ternary ![S_le a b p, a.index p.1, b.index p.2]
  valid := λ (p, _) => a.valid p.1 + b.valid p.2
  init  := λ n => let (i, s) := seqInit a b n; (i, (s, .ofName n))

instance [Add α] [Guard α] : Add (ι →ₛ α) := ⟨S.add⟩
instance [HAdd α β γ] [Guard α] [Guard β] : HAdd (S ι α) (S ι β) (S ι γ) := ⟨S.add⟩
instance [HAdd α β γ] : HAdd (ι →ₐ α) (ι →ₐ β) (ι →ₐ γ) where hAdd a b := λ v => a v + b v
instance [HAdd α β γ] : HAdd (ι →ₛ α) (ι →ₐ β) (ι →ₛ γ) where hAdd a b := {a with value := λ s => a.value s + b (a.index s)}
instance [HAdd β α γ] : HAdd (ι →ₐ β) (ι →ₛ α) (ι →ₛ γ) where hAdd b a := {a with value := λ s => b (a.index s) + a.value s}
