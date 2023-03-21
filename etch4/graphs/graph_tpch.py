from collections import defaultdict
import re
import numpy as np
from matplotlib import pyplot as plt
import matplotlib.ticker as ticker
from matplotlib.legend_handler import HandlerTuple
from numpy.polynomial import polynomial as P


styles = {
    "duckdb": {"color": "C0", "marker": "v", "linestyle": "--"},
    "etch": {"color": "k", "marker": "s", "linestyle": "-"},
    "sqlite": {"color": "C1", "marker": "o", "linestyle": "-."},
}
tpch_styles = {
    "duckdb": {"color": "C0", "marker": "*", "linestyle": ":"},
    "duckdbforeign": {"color": "C0", "marker": "v", "linestyle": "--"},
    "etch": {"color": "k", "marker": "s", "linestyle": "-"},
    "sqlite": {"color": "C1", "marker": "o", "linestyle": "-."},
}
tpch_labels = {
    "duckdb": "duckdb w/o foreign key",
    "duckdbforeign": "duckdb",
}


def graph_q5(ax):
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
            nums[db].append(1000 * np.average(tmp))  # s → ms

    print("q5")
    print(nums)

    for db in DBS:
        ax.plot(SF_NUMS, nums[db], label=tpch_labels.get(db, db), **tpch_styles[db])
    ax.set_title("TPC-H Query 5")


def graph_q5_standalone():
    fig, ax = plt.subplots()
    fig.set_size_inches((4, 3))
    graph_q5(ax)
    ax.set_xscale("log", base=10)
    ax.set_yscale("log", base=10)
    for axis in (ax.xaxis,):
        axis.set_major_formatter(ticker.ScalarFormatter())
    ax.set_xlabel("scaling factor (SF)")
    fig.supylabel("milliseconds")
    ax.legend()
    plt.tight_layout()
    plt.savefig("tpch_q5_scaling.pdf")


def graph_q9(ax):
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

    DBS = ["duckdbforeign", "duckdb", "etch", "sqlite"]

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
            nums[db].append(1000 * np.average(tmp))  # s → ms

    print("q9")
    print(nums)

    for db in DBS:
        ax.plot(SF_NUMS, nums[db], label=tpch_labels.get(db, db), **tpch_styles[db])
    ax.set_title("TPC-H Query 9")


def graph_q9_standalone():
    fig, ax = plt.subplots()
    fig.set_size_inches((4, 3))
    graph_q9(ax)
    ax.set_xscale("log", base=10)
    ax.set_yscale("log", base=10)
    for axis in (ax.xaxis,):
        axis.set_major_formatter(ticker.ScalarFormatter())
    ax.set_xlabel("scaling factor (SF)")
    fig.supylabel("milliseconds")
    ax.legend()
    plt.tight_layout()
    plt.savefig("tpch_q9_scaling.pdf")


def graph_tpch():
    fig, axes = plt.subplots(nrows=1, ncols=2, sharex=True, sharey=True, figsize=(8, 3))

    # these apply to all axes
    axes[0].set_xscale("log", base=10)
    axes[0].set_yscale("log", base=10)
    for axis in (axes[0].xaxis,):
        axis.set_major_formatter(ticker.ScalarFormatter())

    graph_q5(axes[0])
    graph_q9(axes[1])
    fig.supxlabel("scaling factor (SF)", y=0.08)
    fig.supylabel("milliseconds")

    plt.tight_layout()

    # dedupe legends
    handles, labels = plt.gca().get_legend_handles_labels()
    newLabels, newHandles = [], []
    for handle, label in zip(handles, labels):
        if label not in newLabels:
            newLabels.append(label)
            newHandles.append(handle)
    plt.figlegend(newHandles, newLabels, bbox_to_anchor=(0.85, 0.07), ncols=4)

    # fig.set_size_inches(8, 3.3, forward=False)
    plt.savefig("tpch_scaling.pdf", bbox_inches="tight")


graph_q5_standalone()
graph_q9_standalone()
graph_tpch()
