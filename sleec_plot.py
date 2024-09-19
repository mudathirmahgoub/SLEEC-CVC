import matplotlib.pyplot as plt
import pandas as pd
import common
import cactus
import numpy as np

df = pd.read_csv("filters.csv", header=0)
filters = df["duration"]
df = pd.read_csv("quantifiers.csv", header=0)
quantifiers = df["duration"]
df = pd.read_csv("../LEGOS/Sleec/z3.csv", header=0)
z3 = df["duration"]

options = common.PLOT_OPTIONS
options["save_to"] = "cactus.png"
plotter = cactus.Cactus(options)
instances = len(filters.tolist())
accumulative_filter = np.cumsum(filters.tolist())
accumulative_z3 = np.cumsum(z3.tolist())
data = [
    ["cvc5 filters", accumulative_filter, instances, options["timeout"]],
    ["LEGOS(z3)", accumulative_z3, instances, options["timeout"]],
]

plotter.create(data)


# # filters vs quantifiers
# plt.figure(0)
# plt.xlabel("cvc5 filters")
# plt.ylabel("cvc5 quantifiers")
# plt.title("cvc5 filters vs quantifiers")
# plt.grid(linestyle="--")
# plt.axline((0, 0), slope=1, color="red")
# plt.scatter(filters, quantifiers, marker="x")
# plt.legend(["y=x", "seconds"])
# plt.savefig("filters_vs_quantifiers.png", bbox_inches="tight")

# filters vs z3
# plt.figure(1)

# plt.xlabel("cvc5 filters")
# plt.ylabel("LEGOS(z3)")
# plt.title("cvc5 filters vs LEGOS(z3)")
# plt.grid(linestyle="--")
# plt.axline((0, 0), slope=1, color="red")
# plt.scatter(filters, z3, marker="x")
# plt.legend(["y=x", "seconds"])
# plt.savefig("cvc5_vs_z3.png", bbox_inches="tight")

