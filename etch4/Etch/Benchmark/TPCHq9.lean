import Etch.Benchmark.Basic
import Etch.Benchmark.SQL
import Etch.Op
import Etch.Mul
import Etch.ShapeInference
import Etch.Stream

-- simple O(mn) algorithm
partial def String.findStr? (s f : String) : Option String.Pos :=
  loop 0
where
  loop (off : String.Pos) :=
    if s.substrEq off f 0 f.length then
      some off
    else if off + f.endPos < s.endPos then
      loop (s.next off)
    else
      none

-- `![a, b]` means find `b` within `a`
-- if found, ≥0 is byte index; if not found, -1
private def Op.findStr : Op Int where
  argTypes := ![String, String]
  spec := fun x => match (x 0).findStr? (x 1) with
                   | some off => off.byteIdx
                   | none     => -1
  opName := "str_find"
  -- We will implement this using C's strstr(), which is not exactly
  -- the same thing since it's not UTF-8 aware, but close enough.

private def E.findStr (s f : E String) : E Int := E.call Op.findStr ![s, f]
private def E.hasSubstr (s f : E String) : E Bool := s.findStr f >= (0 : E ℤ)

private def Op.dateToYear : Op ℤ where
  argTypes := ![ℤ]
  spec := fun a => 1970 + (a 0) / (365 * 24 * 60 * 60) -- not exactly
  opName := "date_to_year"

-- compute ι₂ from ι₁
def S.deriveIdx {ι₁} [Tagged ι₁] [TaggedC ι₁] [Zero ι₁]
                {ι₂} [Tagged ι₂] [LT ι₂] [@DecidableRel ι₂ LT.lt]
                (α) [Tagged α] [One α] (f : E ι₁ → E ι₂) : ι₁ →ₛ ι₂ →ₛ E α where
  σ := Var ι₁
  skip  pos := pos.store_var
  succ  _ _ := .skip
  ready _   := 1
  valid _   := 1
  index pos := pos.expr
  -- value pos := S.predRangeIncl (f pos.expr) (f pos.expr) -- equiv but slower
  value pos := {
    σ     := Var Bool
    skip  := fun v i => .if1 (f pos.expr << i) (v.store_var 1)
    succ  := fun v _ => v.store_var 1
    ready := fun v => E.call Op.neg ![v.expr]
    valid := fun v => E.call Op.neg ![v.expr]
    index := fun _ => f pos.expr
    value := fun _ => 1
    init  := fun n => let v := Var.fresh "visited" n; ⟨v.decl 0, v⟩
  }
  init n := let v := Var.fresh "pos" n; ⟨v.decl 0, v⟩

namespace Etch.Benchmark.TPCHq9

-- Schema

abbrev partkey       := (0, ℕ)
abbrev partname      := (1, String)
abbrev suppkey       := (2, ℕ)
abbrev orderkey      := (3, ℕ)
abbrev nationkey     := (4, ℕ)
abbrev orderdate     := (5, ℤ)
abbrev orderyear     := (6, ℤ)
abbrev nationname    := (7, String)
abbrev supplycost    := (8, R)
abbrev extendedprice := (9, R)
abbrev discount      := (10, R)
abbrev quantity      := (11, R)

def lineitem : partkey ↠ₛ suppkey ↠ₛ orderkey ↠ₛ extendedprice ↠ₛ discount ↠ₛ quantity ↠ₛ E R :=
  (SQL.sss___ "tpch9_lineitem" : ℕ →ₛ ℕ →ₛ ℕ →ₛ R →ₛ R →ₛ R →ₛ E R)

def part     : partkey   ↠ₐ partname  ↠ₛ E R := (SQL.d_ "tpch9_part" : ℕ →ₐ String →ₛ E R)
def orders   : orderkey  ↠ₐ orderdate ↠ₛ E R := (SQL.d_ "tpch9_orders" : ℕ →ₐ ℤ →ₛ E R)
def supplier : suppkey   ↠ₐ nationkey ↠ₛ E R := (SQL.d_ "tpch9_supplier" : ℕ →ₐ ℕ →ₛ E R)
def partsupp : partkey   ↠ₐ suppkey ↠ₛ supplycost ↠ₛ E R := (SQL.ds_ "tpch9_partsupp" .binarySearch : ℕ →ₐ ℕ →ₛ R →ₛ E R)
def nation   : nationkey ↠ₐ nationname ↠ₛ E R := (SQL.d_ "tpch9_nation" : ℕ →ₐ String →ₛ E R)

-- Query

def orderyearCalc : orderdate ↠ₛ orderyear ↠ₛ E R :=
  S.deriveIdx R (fun (d : E ℤ) => E.call Op.dateToYear ![d])
def partGreen : partname ↠ₐ E Bool := hasGreen
  where hasGreen : String →ₐ E Bool := fun v => v.hasSubstr "green"
def profitCalc : supplycost ↠ₐ extendedprice ↠ₐ discount ↠ₐ quantity ↠ₐ E R := profitCalc'
  where profitCalc' : R →ₐ R →ₐ R →ₐ R →ₐ E R := fun c p d q => p * (1 - d) - c * q

def q9 := ∑ partkey, partname, suppkey: ∑ orderkey, nationkey, orderdate: ∑ supplycost, extendedprice, discount, quantity:
          lineitem * part * partGreen * partsupp * supplier * nation * profitCalc * (orders * orderyearCalc)

def funcs : List (String × String) := [
  let fn := "q9"; (fn, compileFunMap2 ℤ String R fn q9)
]

end Etch.Benchmark.TPCHq9
