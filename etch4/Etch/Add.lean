import Etch.ExtStream
-- structure S (ι : Type _) (α : Type _) where
--   value : α
--   skip  : E ι → P
--   succ  : P
--   ready : E Bool
--   bound : E ι
--   valid : E Bool
--   init  : P


-- def S.mul [Mul α]  (a b : S ι α) : S ι α where
--   value := a.value * b.value
--   skip  := λ i => a.skip i;; b.skip i
--   succ  := a.succ;; b.succ
--   ready := a.ready * b.ready * (a.bound == b.bound)
--   bound := .call .max ![a.bound, b.bound]
--   valid := a.valid * b.valid
--   init := a.init ;; b.init

variable {ι : Type} {α : Type _} [Tagged ι] [DecidableEq ι]
  [LT ι] [LE ι] [DecidableRel (LT.lt : ι → ι → Prop)]
  [DecidableRel (LE.le : ι → ι → _)]

class Guard (α : Type _) where
  guard : E 𝟚 → α → α


instance [Tagged α] [OfNat α 0] : Guard (E α) where
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
  skip := λ i => a.skip i ;; b.skip i
  succ := P.if1 ((a ≤ₛ b) * a.ready) a.succ ;; P.if1 ((b ≤ₛ a) * b.ready) b.succ
  ready := (a ≤ₛ b) * a.ready + (b ≤ₛ a) * b.ready
  bound := .call O.ternary ![a ≤ₛ b, a.bound, b.bound]
  valid := a.valid + b.valid
  init := a.init ;; b.init
