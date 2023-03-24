import numpy as np
import sqlite3
import sys
from pathlib import Path


def makeA(p=0.1, nonzeros=400000):
    # 2000 × 2000 × 0.1 = 400000

    n = int(np.round(np.sqrt(nonzeros / p)))
    matrix_size = n * n
    m = np.random.rand(nonzeros)
    m *= (matrix_size - nonzeros) / np.sum(m)
    m += 1

    # Extra correction
    # print(np.sum(np.round(m)))
    m /= np.sum(np.round(m)) / matrix_size
    # print(np.sum(np.round(m)))
    m /= np.sum(np.round(m)) / matrix_size
    # print(np.sum(np.round(m)))

    result = set()
    last = 0
    for r in m:
        if last >= matrix_size:
            break
        i, j = last // n, last % n
        result.add((i, j, float(r)))
        last += int(np.round(r))
    print(
        f"expected={nonzeros} actual={len(result)} expect_sparsity={p} actual_sparsity={len(result) / matrix_size}"
    )
    return result


def main(db: Path = Path("data/pldi.db"), p: float = 0.0002, nonzeros: int = 20000):
    c = sqlite3.connect(str(db))
    c.execute("DROP TABLE IF EXISTS A")
    c.execute("DROP TABLE IF EXISTS B")
    c.execute("CREATE TABLE A(i INTEGER NOT NULL, j INTEGER NOT NULL, v REAL NOT NULL)")
    c.execute("CREATE TABLE B(i INTEGER NOT NULL, j INTEGER NOT NULL, v REAL NOT NULL)")
    print("A")
    c.executemany(f"INSERT INTO A VALUES(?,?,?)", makeA(p, nonzeros))
    print("B")
    c.executemany(f"INSERT INTO B VALUES(?,?,?)", makeA(p, nonzeros))
    c.commit()


main(Path(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]))
