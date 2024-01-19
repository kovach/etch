import Etch.Benchmark.Basic
import Etch.Benchmark.SQL
import Etch.ShapeInference
import Etch.Stream

namespace Etch.Benchmark.OldSQL

def FSQLCallback : (E ℕ × E ℕ × E R) :=
(.call Op.atoi ![.access "argv" 0],
 .call Op.atoi ![.access "argv" 1],
 1)

def l_ssF : lvl ℕ (lvl ℕ (MemLoc R)) := dcsr "ssF"

abbrev cause := (0, ℕ)
abbrev year  := (1, ℕ)
abbrev objid := (2, ℕ)

def fires : year ↠ₛ objid ↠ₛ E R := (SQL.ss "ssF" : ℕ →ₛ ℕ →ₛ E R)
def range_06_08 : year ↠ₛ E R := (S.predRange 2006 2008 : ℕ →ₛ E R)
def countRange := ∑ year, objid: range_06_08 * fires

def funcs : List (String × String) := [
  ("gen_query_fires.c", go l_ssF FSQLCallback),
  ("count_range", compileFun R "count_range" countRange) ]

end Etch.Benchmark.OldSQL