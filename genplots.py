import sys
import seaborn as sns, matplotlib.pyplot as plt
import pandas as pd

sns.set(style="whitegrid")
sns.set(font_scale=2)

prefix = sys.argv[1] if len(sys.argv) > 1 else ""

n = 5
titles = [ f'title {i}' for i in range(1,n+1) ]

for (i,title) in enumerate(titles):
    plt.figure()
    name = "{prefix}plot{number}".format(prefix=prefix,number=i+1)
    tips = pd.read_csv(name + ".csv")
    gfg = sns.barplot(x="test", y="time", data=tips, capsize=.1, errorbar="sd")
    plt.xticks(rotation=22, fontsize=16)
    sns.swarmplot(x="test", y="time", data=tips, color="0", alpha=.35)
    gfg.set(xlabel ="", ylabel = "execution time", title = "")

    plt.savefig(name + ".pdf", bbox_inches='tight')
