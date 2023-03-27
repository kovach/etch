import Etch.Benchmark.Basic
import Etch.Benchmark.SQL
import Etch.LVal
import Etch.Mul
import Etch.ShapeInference
import Etch.Stream

namespace Etch.Benchmark.WCOJ

-- For data loading

def SQLCallback : (E ℕ × E ℕ × E ℕ) :=
(.call Op.atoi ![.access "argv" 0],
 .call Op.atoi ![.access "argv" 1],
 1)

def load_ss (l : String) : lvl ℕ (lvl ℕ (Dump ℕ)) :=
  (interval_vl $ l ++ "1_pos").value 0 |>
  (with_values (sparse_il (l ++ "1_crd" : ArrayVar ℕ)) (interval_vl $ l ++ "2_pos")) ⊚
  (without_values (sparse_il (l ++ "2_crd" : ArrayVar ℕ)))
def l_dsR : lvl ℕ (lvl ℕ (Dump ℕ)) := load_ss "dsR"
def l_dsS : lvl ℕ (lvl ℕ (Dump ℕ)) := load_ss "dsS"
def l_dsT : lvl ℕ (lvl ℕ (Dump ℕ)) := load_ss "dsT"

abbrev a := (0, ℕ)
abbrev b := (1, ℕ)
abbrev c := (2, ℕ)

def r : a ↠ₛ b ↠ₛ E ℕ := (SQL.ss "dsR" : ℕ →ₛ ℕ →ₛ E ℕ)
def s : b ↠ₛ c ↠ₛ E ℕ := (SQL.ss "dsS" : ℕ →ₛ ℕ →ₛ E ℕ)
def t : a ↠ₛ c ↠ₛ E ℕ := (SQL.ss "dsT" : ℕ →ₛ ℕ →ₛ E ℕ)
def out := ∑ a, b, c: r * s * t

def funcs : List (String × String) := [
  let fn := "gen_callback_wcoj_R"; (fn, compileSqliteCb fn [go l_dsR SQLCallback]),
  let fn := "gen_callback_wcoj_S"; (fn, compileSqliteCb fn [go l_dsS SQLCallback]),
  let fn := "gen_callback_wcoj_T"; (fn, compileSqliteCb fn [go l_dsT SQLCallback]),
  let fn := "wcoj";                (fn, compileFun ℕ fn out)
]

end Etch.Benchmark.WCOJ
