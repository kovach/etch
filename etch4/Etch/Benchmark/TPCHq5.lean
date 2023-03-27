import Etch.Benchmark.Basic
import Etch.Benchmark.SQL
import Etch.LVal
import Etch.Mul
import Etch.ShapeInference
import Etch.Stream

namespace Etch.Benchmark.TPCHq5

-- Schema

abbrev orderkey   := (0, ℕ)
abbrev orderdate  := (1, ℕ)
abbrev custkey    := (2, ℕ)
abbrev suppkey    := (3, ℕ)
abbrev nationkey  := (4, ℕ)
abbrev regionkey  := (5, ℕ)
abbrev nationname := (6, String)
abbrev regionname := (7, String)
abbrev extendedprice := (8, R)
abbrev discount   := (9, R)

def lineitem : orderkey ↠ₛ suppkey ↠ₛ extendedprice ↠ₛ discount ↠ₛ E R :=
  (SQL.ss__ "tpch_lineitem" : ℕ →ₛ ℕ →ₛ R →ₛ R →ₛ E R)

def revenue_calc' : R →ₐ R →ₐ E R := fun p d => p * (1 - d)
def revenue_calc : extendedprice ↠ₐ discount ↠ₐ E R := revenue_calc'
def lineitem_revenue : orderkey ↠ₛ suppkey ↠ₛ extendedprice ↠ₛ discount ↠ₛ E R := lineitem * revenue_calc

def orders   : orderkey  ↠ₐ orderdate ↠ₛ custkey ↠ₛ E R := (SQL.dss "tpch_orders" .binarySearch : ℕ →ₐ ℕ →ₛ ℕ →ₛ E R)
def customer : custkey   ↠ₐ nationkey ↠ₛ E R := (SQL.ds "tpch_customer" : ℕ →ₐ ℕ →ₛ E R)
def supplier : suppkey   ↠ₐ nationkey ↠ₛ E R := (SQL.ds "tpch_supplier" : ℕ →ₐ ℕ →ₛ E R)
def nation   : nationkey ↠ₐ regionkey ↠ₛ nationname ↠ₛ E R := (SQL.ds_ "tpch_nation" : ℕ →ₐ ℕ →ₛ String →ₛ E R)
def region   : regionkey ↠ₐ regionname ↠ₛ E R := (SQL.ds "tpch_region" : ℕ →ₐ String →ₛ E R)

-- Query

def asia : regionname ↠ₛ E R := (S.predRangeIncl "ASIA" "ASIA" : String →ₛ E R)

def year1994unix := 757411200
def year1995unix := 788947200
def orders1994 : orderdate ↠ₛ E R := (S.predRange year1994unix year1995unix : ℕ →ₛ E R)

def q5 := ∑ orderkey, orderdate, custkey: ∑ suppkey, nationkey, regionkey: ∑ regionname, extendedprice, discount:
          lineitem_revenue * orders * orders1994 * customer * supplier * (nation * region * asia)

def funcs : List (String × String) := [
  let fn := "q5"; (fn, compileFunMap String R fn q5)
]

end Etch.Benchmark.TPCHq5
