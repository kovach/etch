import Etch.Benchmark.Basic
import Etch.Benchmark.SQL
import Etch.LVal
import Etch.Mul
import Etch.ShapeInference
import Etch.Stream

namespace Etch.Benchmark.TPCHq18

-- Helpers

/-- Make sure one index is only emitted once. TODO -/
-- def S.regularize (a : ι →ₛ α) : ι →ₛ α where
--   σ        := a.σ × Var Bool × Var ι
--   skip p i := .skip -- TODO
--   succ p i := a.succ p.1 i

def S.singleton (i : E ι) (v : E α) : ι →ₛ E α where
  σ        := Var Bool
  skip _ _ := .skip
  succ p _ := p.store_var 1
  value _  := v
  ready _  := 1
  index _  := i
  valid p  := -p
  init  n  := let v := Var.fresh "visited" n; ⟨v.decl 0, v⟩

def S.reflect [Tagged α] [Zero α] [DecidableEq α] (a : ι →ₛ E α) : ι →ₛ α →ₛ E α :=
{ a with
  value := fun p => S.singleton (a.value p) (a.value p) }

def StrS.reflect [Tagged α] [Zero α] [DecidableEq α] {m} : (n × ι ⟶ₛ E α) → (n × ι ⟶ₛ m × α ⟶ₛ E α)
| .str s => .str (.str <$> S.reflect s)

-- Schema

abbrev orderkey    := (0, ℕ)
abbrev orderkey'   := (1, ℕ)
abbrev linenumber  := (2, ℕ)
abbrev linenumber' := (3, ℕ)
abbrev quantity    := (4, ℕ)
abbrev quantity'   := (5, ℕ)
abbrev sumquantity := (6, ℕ)

def lineitem : orderkey ↠ₛ linenumber ↠ₛ quantity ↠ₛ E ℕ :=
  (SQL.sss "tpch_lineitem" : ℕ →ₛ ℕ →ₛ ℕ →ₛ E ℕ)
def lineitem' : orderkey ↠ₛ linenumber ↠ₛ quantity' ↠ₛ E ℕ :=
  (SQL.sss "tpch_lineitem" : ℕ →ₛ ℕ →ₛ ℕ →ₛ E ℕ)

-- Query

def quantity_id : quantity ↠ₐ E ℕ := f
  where f : ℕ →ₐ E ℕ := id
def lineitem_with_sumquantity : orderkey ↠ₛ linenumber ↠ₛ quantity ↠ₛ sumquantity ↠ₛ E ℕ :=
  (StrS.reflect <$> ·) <$> (lineitem * quantity_id)

def filter : sumquantity ↠ₐ E Bool := f
  where f : ℕ →ₐ E Bool := fun q => q >ᵣ (300 : E ℕ)

def test2 := ∑ linenumber, quantity : lineitem_with_sumquantity * filter

def funcs : List (String × String) := [
  let fn := "test2"; (fn, compileFunMap2 ℕ ℕ ℕ fn test2)
  -- let fn := "q18"; (fn, compileFunMap String R fn q18)
]

end Etch.Benchmark.TPCHq18

