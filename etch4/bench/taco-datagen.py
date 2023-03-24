import numpy as np
import sqlite3
import sys
from pathlib import Path


def makeV(n=100, p=0.1):
    result = set()
    m = np.random.rand(n)
    it = np.nditer(m, flags=["multi_index"])
    for i in it:
        if i < p:
            result.add((int(it.multi_index[0]), float(i)))
    return result


def makeA(n=100, p=0.1):
    result = set()
    m = np.random.rand(n, n)
    it = np.nditer(m, flags=["multi_index"])
    for i in it:
        if i < p:
            result.add((int(it.multi_index[0]), int(it.multi_index[1]), float(i)))
    return result


def makeC(n=100, p=0.1):
    result = set()
    m = np.random.rand(n, n, n)
    it = np.nditer(m, flags=["multi_index"])
    for i in it:
        if i < p:
            result.add(
                (
                    int(it.multi_index[0]),
                    int(it.multi_index[1]),
                    int(it.multi_index[2]),
                    float(i),
                )
            )
    return result


def main(db: Path = Path("data/pldi.db"), factor: float = 1, sparsity: float = 0.1):
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
    c.executemany(f"INSERT INTO A VALUES(?,?,?)", makeA(int(factor * 100), sparsity))
    print("B")
    c.executemany(f"INSERT INTO B VALUES(?,?,?)", makeA(int(factor * 100), sparsity))
    print("C")
    c.executemany(f"INSERT INTO C VALUES(?,?,?,?)", makeC(int(factor * 10), sparsity))
    print("V")
    c.executemany(f"INSERT INTO V VALUES(?,?)", makeV(int(factor * 100), sparsity))
    c.commit()


main(Path(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]))
