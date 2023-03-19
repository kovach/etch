import re
import numpy as np
from matplotlib import pyplot as plt
from matplotlib.ticker import ScalarFormatter
from cycler import cycler
from numpy.polynomial import polynomial as P


def graph_q5():
    SFS = ["x0.01", "x0.025", "x0.05", "x0.1", "x0.25", "x0.5", "x1", "x2", "x4"]
    SF_NUMS = [0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2, 4]
    # ❯ for size in x0.01 x0.025 x0.05 x0.1 x0.25 x0.5 x1 x2 x4; do echo $size `wc -c tpch-csv-$size-q5/*.csv | grep total`; done
    BYTES = [
        1780915,
        4648233,
        9487650,
        19271743,
        50144641,
        102488785,
        207793787,
        427239748,
        876270111,
    ]
    sf_to_byte = np.poly1d(np.polyfit(SF_NUMS, BYTES, 1))
    byte_to_sf = np.poly1d(np.polyfit(BYTES, SF_NUMS, 1))

    print(sf_to_byte)

    DBS = ["duckdb", "duckdbforeign", "etch", "sqlite"]

    nums = {}
    for db in DBS:
        nums[db] = []
        for sz in SFS:
            tmp = []
            with open(f"bench-output/run-tpch-{sz}-q5-{db}.txt") as f:
                if db.startswith("duckdb") or db.startswith("sqlite"):
                    r = re.compile(r"q2 took \(s\): real ([^ ]*)s.*")
                elif db.startswith("etch"):
                    r = re.compile(r"q5 took \(s\): real ([^ ]*)s.*")

                for l in f:
                    res = r.match(l)
                    if not res:
                        continue
                    tmp.append(float(res[1]))
            nums[db].append(np.average(tmp))

    print(nums)

    monochrome = cycler("color", ["k"]) * (
        cycler("marker", [".", "v", "s", "*"])
        + cycler("linestyle", ["-", "--", ":", "-."])
    )
    plt.rc("axes", prop_cycle=monochrome)

    fig, ax = plt.subplots()
    for db in DBS:
        ax.plot(SF_NUMS, nums[db], label=db)
    ax.set_title("TPC-H Query 5")
    ax.set_xscale("log", base=10)
    ax.set_yscale("log", base=10)
    for axis in (ax.xaxis,):
        axis.set_major_formatter(ScalarFormatter())
    ax.set_xlabel("TPC-H Scaling Factor")
    ax.set_ylabel("Time (s)")
    ax.legend()
    plt.savefig("tpch_q5_scaling.pdf")


def graph_q9():
    SFS = ["x0.01", "x0.025", "x0.05", "x0.1", "x0.25", "x0.5", "x1", "x2", "x4"]
    SF_NUMS = [0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2, 4]
    # ❯ for size in x0.01 x0.025 x0.05 x0.1 x0.25 x0.5 x1 x2 x4; do echo $size `wc -c tpch-csv-$size-q9/*.csv | grep total`; done
    BYTES = [
        2453811,
        6383292,
        12983685,
        26604032,
        68989290,
        140539517,
        287217107,
        589590576,
        1204531842,
    ]
    sf_to_byte = np.poly1d(np.polyfit(SF_NUMS, BYTES, 1))
    byte_to_sf = np.poly1d(np.polyfit(BYTES, SF_NUMS, 1))

    print(sf_to_byte)

    DBS = ["duckdb", "duckdbforeign", "etch", "sqlite"]

    nums = {}
    for db in DBS:
        nums[db] = []
        for sz in SFS:
            tmp = []
            with open(f"bench-output/run-tpch-{sz}-q9-{db}.txt") as f:
                if db.startswith("duckdb") or db.startswith("sqlite"):
                    r = re.compile(r"q2 took \(s\): real ([^ ]*)s.*")
                elif db.startswith("etch"):
                    r = re.compile(r"q9 took \(s\): real ([^ ]*)s.*")

                for l in f:
                    res = r.match(l)
                    if not res:
                        continue
                    tmp.append(float(res[1]))
            nums[db].append(np.average(tmp))

    print(nums)

    monochrome = cycler("color", ["k"]) * (
        cycler("marker", [".", "v", "s", "*"])
        + cycler("linestyle", ["-", "--", ":", "-."])
    )
    plt.rc("axes", prop_cycle=monochrome)

    fig, ax = plt.subplots()
    for db in DBS:
        ax.plot(SF_NUMS, nums[db], label=db)
    ax.set_title("TPC-H Query 9")
    ax.set_xscale("log", base=10)
    ax.set_yscale("log", base=10)
    for axis in (ax.xaxis,):
        axis.set_major_formatter(ScalarFormatter())
    ax.set_xlabel("TPC-H Scaling Factor")
    ax.set_ylabel("Time (s)")
    ax.legend()
    plt.savefig("tpch_q9_scaling.pdf")


graph_q5()
graph_q9()
