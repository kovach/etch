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

    R = np.random.rand(nonzeros)

    result = set()
    last = 0
    for idx, r in enumerate(m):
        if last >= matrix_size:
            break
        i, j = last // n, last % n
        result.add((i, j, float(R[idx])))
        last += int(np.round(r))
    print(
        f"expected={nonzeros} actual={len(result)} expect_sparsity={p} actual_sparsity={len(result) / matrix_size}"
    )
    return result


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

    R = np.random.rand(nonzeros)

    result = set()
    last = 0
    for i, r in enumerate(m):
        if last >= matrix_size:
            break
        result.add((last, float(R[i])))
        last += int(np.round(r))
    print(
        f"expected={nonzeros} actual={len(result)} expect_sparsity={p} actual_sparsity={len(result) / matrix_size}"
    )
    return result


def main(
    db: Path = Path("data/pldi.db"),
    pA: float = 0.0002,
    pV: float = 0.1,
    nonzeros: int = 20000,
):
    c = sqlite3.connect(str(db))
    c.execute("DROP TABLE IF EXISTS A")
    c.execute("DROP TABLE IF EXISTS V")
    c.execute("CREATE TABLE A(i INTEGER NOT NULL, j INTEGER NOT NULL, v REAL NOT NULL)")
    c.execute("CREATE TABLE V(i INTEGER NOT NULL, v REAL NOT NULL)")
    print("A")
    c.executemany(f"INSERT INTO A VALUES(?,?,?)", makeA(pA, nonzeros))
    print("V")
    v_nonzeros = int(np.sqrt(nonzeros / pA) * pV)
    c.executemany(f"INSERT INTO V VALUES(?,?)", makeV(pV, v_nonzeros))
    c.commit()


main(Path(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]))
