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
    print("duckdbforeign/etch", np.max(np.array(nums["duckdbforeign"]) / np.array(nums["etch"])))
    print("duckdbforeign/etch", np.min(np.array(nums["duckdbforeign"]) / np.array(nums["etch"])))
    print("duckdb/etch", np.max(np.array(nums["duckdb"]) / np.array(nums["etch"])))
    print("duckdb/etch", np.min(np.array(nums["duckdb"]) / np.array(nums["etch"])))
    print("sqlite/etch", np.max(np.array(nums["sqlite"]) / np.array(nums["etch"])))
    print("sqlite/etch", np.min(np.array(nums["sqlite"]) / np.array(nums["etch"])))

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
    print("duckdbforeign/etch", np.max(np.array(nums["duckdbforeign"]) / np.array(nums["etch"])))
    print("duckdbforeign/etch", np.min(np.array(nums["duckdbforeign"]) / np.array(nums["etch"])))
    print("duckdb/etch", np.max(np.array(nums["duckdb"]) / np.array(nums["etch"])))
    print("duckdb/etch", np.min(np.array(nums["duckdb"]) / np.array(nums["etch"])))
    print("sqlite/etch", np.max(np.array(nums["sqlite"]) / np.array(nums["etch"])))
    print("sqlite/etch", np.min(np.array(nums["sqlite"]) / np.array(nums["etch"])))

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


def graph_wcoj(ax):
    SFS = ["x1", "x3", "x10", "x30", "x100", "x300", "x1000", "x3000", "x10000"]
    SF_NUMS = 100 * np.array([1, 3, 10, 30, 100, 300, 1000, 3000, 10000])

    DBS = ["sqlite", "duckdb", "etch"]

    nums = {}
    last = {}
    legend_entries = defaultdict(list)

    for db in DBS:
        nums[db] = []
        for i, sz in enumerate(SFS):
            tmp = []
            try:
                f = open(f"bench-output/run-wcoj-{sz}-{db}.txt")
            except IOError:
                continue
            with f:
                last[db] = i

                factor = 1
                if db.startswith("duckdb") or db.startswith("sqlite"):
                    r = re.compile(r"q2 took \(s\): real ([^ ]*)s.*")
                elif db.startswith("etch"):
                    r = re.compile(r"wcojx1000 took \(s\): real ([^ ]*)s.*")
                    factor = 1000

                for l in f:
                    res = r.match(l)
                    if not res:
                        continue
                    tmp.append(float(res[1]) / factor)
            nums[db].append(1000 * np.average(tmp))  # s → ms

    print(nums)

    for db in DBS:
        (p,) = ax.plot(SF_NUMS[: len(nums[db])], nums[db], label=db, **styles[db])
        legend_entries[db].append(p)

    # ax.set_xlim((58.21, 8588523), auto=False)
    ax.set_xlim(ax.get_xlim(), auto=False)
    ax.set_ylim(ax.get_ylim(), auto=False)

    ax.yaxis.set_major_locator(ticker.LogLocator(base=100, subs=[1]))
    ax.yaxis.set_minor_locator(ticker.LogLocator(base=10, subs=[1], numticks=15))
    ax.yaxis.set_minor_formatter(ticker.NullFormatter())

    for db in DBS:
        exponent = 2
        if db == "etch":
            exponent = 1

        base_x = SF_NUMS[last[db]]
        x = np.array(ax.get_xlim())
        base_y = nums[db][-1]
        multiplier = base_y / (base_x**exponent)

        label = f"$n^{exponent}$"
        (p,) = ax.plot(
            x,
            multiplier * (x**exponent),
            label=label,
            color=styles[db]["color"],
            linestyle=":",
        )
        legend_entries[label].append(p)

    print(ax.get_xlim())

    # ax.set_title("Triangle Query")
    ax.legend(
        # [(tuple(v) if len(v) > 1 else v[0]) for v in legend_entries.values()],
        # legend_entries.keys(),
        loc="upper right",
        handler_map={tuple: HandlerTuple(ndivide=None)},
        ncols=2,
        columnspacing=1,
    )


def graph_wcoj_standalone():
    fig, ax = plt.subplots()
    fig.set_size_inches((5, 2.5))
    ax.set_xscale("log", base=10)
    ax.set_yscale("log", base=10)
    graph_wcoj(ax)
    ax.set_xlabel("rows ($n$)")
    ax.set_ylabel("milliseconds")
    # ax.legend()
    plt.tight_layout()
    plt.savefig("wcoj_scaling.pdf", bbox_inches="tight")


def graph_taco():
    SFS = ["s0.0001", "s0.0003", "s0.0007", "s0.001", "s0.003", "s0.007", "s0.01", "s0.03", "s0.07", "s0.1", "s0.3", "s0.5"]
    SF_NUMS = np.array([0.0001, 0.0003, 0.0007, 0.001, 0.003, 0.007, 0.01, 0.03, 0.07, 0.1, 0.3, 0.5])
    QUERIES = ["inner2ss", "sum_add2", "sum_mul2_csr", "sum_mul2", "mttkrp", "spmv"]
    DESC = ["inner", "add", "mmul", "smul", "MTTKRP", "SpMV"]

    nums = defaultdict(lambda: defaultdict(list)) # inner2ss → taco → [x10, x16, ...]
    for sz in SFS:
        with open(f"bench-output/run-taco-{sz}.txt") as f:
            r = re.compile(r"(etch|taco)_([^ ]*) took \(s\): real ([^ ]*)s.*")
            tmp = defaultdict(lambda: defaultdict(list)) # inner2ss → taco → [att1, att2, ...]
            for l in f:
                res = r.match(l)
                if not res:
                    continue
                tmp[res[2]][res[1]].append(float(res[3]))
            for q in tmp.keys():
                for sys in tmp[q].keys():
                    nums[q][sys].append(np.average(tmp[q][sys]))

    print(nums)
    print(np.max([np.array(nums[q]["taco"]) / np.array(nums[q]["etch"]) for q in QUERIES if q != "sum_add2" and q != "sum_mul2"]))
    print(np.min([np.array(nums[q]["taco"]) / np.array(nums[q]["etch"]) for q in QUERIES if q != "sum_add2" and q != "sum_mul2"]))
    q = "sum_add2"
    print(q, np.max(np.array(nums[q]["etch"]) / np.array(nums[q]["taco"])))

    fig, axes = plt.subplots(ncols=2, nrows=3, sharex=True)
    fig.set_size_inches((9, 3))

    for i, q in enumerate(QUERIES):
        ax = axes[i // 2][i % 2]
        taco_by_etch = np.array(nums[q]["taco"]) / np.array(nums[q]["etch"])
        ax.plot(SF_NUMS, taco_by_etch, ".-")
        ax.plot(SF_NUMS, np.ones((len(SF_NUMS),)), "k:")
        ax.set_ylabel(DESC[i])
        ax.set_xscale("log", base=10)
        ax.xaxis.set_major_formatter(ticker.StrMethodFormatter("{x:g}"))
        if i // 2 == 2:
            ax.set_xlabel("sparsity", y=0.08)

    plt.tight_layout()
    plt.savefig("taco_scaling.pdf", bbox_inches="tight")


graph_q5_standalone()
graph_q9_standalone()
graph_tpch()
graph_wcoj_standalone()
graph_taco()
