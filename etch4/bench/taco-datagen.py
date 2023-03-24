import numpy as np
import sqlite3
import sys
from pathlib import Path


def makeV(p=0.1, nonzeros=200):
    # 2000 × 0.1 = 200

    n = int(np.round(nonzeros / p))
    matrix_size = n
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
        result.add((last, float(r)))
        last += int(np.round(r))
    print(f"expected={nonzeros} actual={len(result)}")
    return result


def makeA(p=0.1, nonzeros = 400000):
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
    print(f"expected={nonzeros} actual={len(result)}")
    return result


def makeC(p=0.1, nonzeros=800000):
    # 200 × 200 × 200 * 0.1 = 800000

    n = int(np.round(np.cbrt(nonzeros / p)))
    matrix_size = n * n * n
    m = np.random.rand(nonzeros)
    m *= (matrix_size - nonzeros) / np.sum(m)
    m += 1

    # Rounding correction
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
        i, j, k = last // (n * n), (last // n) % n, last % n
        result.add((i, j, k, float(r)))
        last += int(np.round(r))
    print(f"expected={nonzeros} actual={len(result)}")
    return result


def main(db: Path = Path("data/pldi.db"), sparsity: float = 0.1):
    c = sqlite3.connect(str(db))
    c.execute("DROP TABLE IF EXISTS A")
    c.execute("DROP TABLE IF EXISTS B")
    c.execute("DROP TABLE IF EXISTS C")
    c.execute("DROP TABLE IF EXISTS V")
    c.execute("CREATE TABLE A(i INTEGER NOT NULL, j INTEGER NOT NULL, v REAL NOT NULL)")
    c.execute("CREATE TABLE B(i INTEGER NOT NULL, j INTEGER NOT NULL, v REAL NOT NULL)")
    c.execute(
        "CREATE TABLE C(i INTEGER NOT NULL, j INTEGER NOT NULL, k INTEGER NOT NULL, v REAL NOT NULL)"
    )
    c.execute("CREATE TABLE V(i INTEGER NOT NULL, v REAL NOT NULL)")
    print("A")
    # reference factor = 20
    c.executemany(f"INSERT INTO A VALUES(?,?,?)", makeA(sparsity))
    print("B")
    c.executemany(f"INSERT INTO B VALUES(?,?,?)", makeA(sparsity))
    print("C")
    c.executemany(f"INSERT INTO C VALUES(?,?,?,?)", makeC(sparsity))
    print("V")
    c.executemany(f"INSERT INTO V VALUES(?,?)", makeV(sparsity))
    c.commit()


main(Path(sys.argv[1]), float(sys.argv[2]))
