import Etch.Basic
import Etch.Stream
import Etch.LVal
import Etch.Add
import Etch.Mul
import Etch.Compile
import Etch.ShapeInference
import Etch.Benchmark.OldSQL
import Etch.Benchmark.TACO
import Etch.Benchmark.TPCHq5
import Etch.Benchmark.TPCHq9
import Etch.Benchmark.WCOJ

open Etch.Benchmark

private def files : List (String × List (String × String)) := [
  ("old_sql", OldSQL.funcs),
  ("taco",    TACO.funcs),
  ("matmul",  TACO.funcsMatmul),
  ("filtered_spmv",  TACO.funcsFilterSpMV),
  ("tpch_q5", TPCHq5.funcs),
  ("tpch_q9", TPCHq9.funcs),
  ("wcoj",    WCOJ.funcs) ]

def main : IO Unit := do
  for (f, ops) in files do
    let mut file := ""
    for x in ops do
      file := file.append (x.2 ++ "\n")
    IO.FS.writeFile s!"gen_{f}.c" file

#eval main
