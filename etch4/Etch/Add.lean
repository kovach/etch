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

variable {ι α : Type} [Tagged ι] [DecidableEq ι]
  [LT ι] [LE ι] [DecidableRel (LT.lt : ι → ι → Prop)]
  [DecidableRel (LE.le : ι → ι → _)]

def S_le (a b : S ι α) : E 𝟚 

def S.add [Add α] (a b : S ι α) : S ι α where
  value := _
  skip := _
  succ := _
  ready := _
  bound := .call .max ![a.bound, b.bound]
  valid := a.valid + b.valid
  init := a.init ;; b.init
