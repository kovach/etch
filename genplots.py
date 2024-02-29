
import seaborn as sns, matplotlib.pyplot as plt
import pandas as pd

sns.set(style="whitegrid")
sns.set(font_scale=2)

titles = ['title 1','title 2', 'title 3', 'title 4']
for (i,title) in enumerate(titles):
    plt.figure()
    name = "plot{number}".format(number=i+1)
    tips = pd.read_csv(name + ".csv")
    gfg = sns.barplot(x="test", y="time", data=tips, capsize=.1, errorbar="sd")
    sns.swarmplot(x="test", y="time", data=tips, color="0", alpha=.35)
    gfg.set(xlabel ="", ylabel = "execution time", title = "")

    plt.savefig(name + ".pdf", bbox_inches='tight')
