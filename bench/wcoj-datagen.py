import numpy as np
from pathlib import Path
import sys

# for a description of this join problem see https://arxiv.org/pdf/1310.3314.pdf, Figure 2
def gen(n: int):
    all_ones = np.ones((n, 1), dtype=int)
    all_nums = np.array(range(1, n+1)).reshape((-1, 1))
    num_one = np.hstack([all_ones, all_nums])
    one_num = np.hstack([all_nums, all_ones])

    # interweave the two arrays
    v = np.empty((2 * n - 1, 2), dtype=int)
    v[0::2] = num_one
    v[1::2] = one_num[1:] # skip duplicate 1,1
    return v


def export(outdir: Path, tbl: str, arr: np.ndarray):
    outfile = outdir / f"{tbl}.csv"
    header = {
        "r": "a,b",
        "s": "b,c",
        "t": "a,c",
    }
    np.savetxt(outfile, arr, delimiter=",", header=header[tbl], comments='', fmt="%d")


def main(outdir: Path, n: int):
    out = gen(n)
    export(outdir, "r", out)
    export(outdir, "s", out)
    export(outdir, "t", out)


main(Path(sys.argv[1]), int(sys.argv[2]))
