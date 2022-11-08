import Etch.ExtStream

variable {ι : Type} {α : Type _} [Tagged ι] [DecidableEq ι]
  [LT ι] [LE ι] [DecidableRel (LT.lt : ι → ι → Prop)]
  [DecidableRel (LE.le : ι → ι → _)]

class Guard (α : Type _) where
  guard : E 𝟚 → α → α

instance [Tagged α] [OfNat α (nat_lit 0)] : Guard (E α) where
  guard := λ b v =>
  let zero : E α := E.call O.zero (λ i => nomatch i)
  .call O.ternary ![b, v, zero]

instance : Guard (S ι α) where
  guard := λ b s => {s with valid := b * s.valid}

/-- Returns an expression which evaluates to `true` iff `a.index' ≤ b.index'` -/
def S_le (a b : S ι α) : E 𝟚 :=
  (.call O.neg ![b.valid]) + (a.valid * (a.bound <= b.bound))

infixr:40 "≤ₛ" => S_le

def S.add [Add α] [Guard α] (a b : S ι α) : S ι α where
  value := (Guard.guard ((a ≤ₛ b) * a.ready) a.value) +
           (Guard.guard ((b ≤ₛ a) * b.ready) b.value)
  skip := λ i => a.skip i ;; b.skip i -- TODO: is skip allowed if `a` is invalid, or do we need to guard
                                      -- that `a` is valid?
                                      -- Also, I am assuming you cannot skip backwards (i.e. it becomes a no-op
                                      -- if `i < .bound`). Otherwise, each skip should be guarded by `≤ₛ` as well
  succ := .store_var "temp" (b ≤ₛ a);; P.if1 ((a ≤ₛ b) * a.ready) a.succ ;; P.if1 ("temp" * b.ready) b.succ
  ready := (a ≤ₛ b) * a.ready + (b ≤ₛ a) * b.ready
  bound := .call O.ternary ![a ≤ₛ b, a.bound, b.bound]
  valid := a.valid + b.valid
  init := a.init ;; b.init

instance [Add α] [Guard α] : Add (ι →ₛ α) := ⟨S.add⟩
example : HAdd (ℕ →ₛ ℕ →ₛ E R) (ℕ →ₛ ℕ →ₛ E R) (ℕ →ₛ ℕ →ₛ E R):= inferInstance
