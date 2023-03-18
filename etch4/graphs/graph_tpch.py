import re
import numpy as np
from matplotlib import pyplot as plt
from matplotlib.ticker import ScalarFormatter


def graph_q5():
    SIZES = ["x0.01", "x0.025", "x0.05", "x0.1", "x0.25", "x0.5", "x1", "x2", "x4"]
    SIZES_NUM = [0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2, 4]
    DBS = ["duckdb", "duckdbforeign", "etch", "sqlite"]

    nums = {}
    for db in DBS:
        nums[db] = []
        for sz in SIZES:
            tmp = []
            with open(f"bench-output/run-tpch-{sz}-q5-{db}.txt") as f:
                if db.startswith("duckdb"):
                    r = re.compile(r"q2 took \(s\): real ([^ ]*)s.*")
                elif db.startswith("sqlite"):
                    r = re.compile(r"Run Time: real ([^ ]*) .*")
                elif db.startswith("etch"):
                    r = re.compile(r"q5 took \(s\): real ([^ ]*)s.*")

                for l in f:
                    res = r.match(l)
                    if not res:
                        continue
                    tmp.append(float(res[1]))
            nums[db].append(np.average(tmp))

    print(nums)

    fig, ax = plt.subplots()
    for db in DBS:
        ax.plot(SIZES_NUM, nums[db], label=db, marker="o")
    ax.set_title("TPC-H Query 5")
    ax.set_xscale("log", base=10)
    ax.set_yscale("log", base=10)
    for axis in (ax.xaxis,):
        axis.set_major_formatter(ScalarFormatter())
    ax.set_xlabel("TPC-H Scaling Factor")
    ax.set_ylabel("Time (s)")
    ax.legend()
    plt.savefig("tpch_q5_scaling.pdf")


graph_q5()
