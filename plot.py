import matplotlib.pyplot as plt
import pandas as pd

df = pd.read_csv('filters_vs_quantifiers.csv',header=0)
filters = df["filters duration"]
quantifiers = df["quantifiers duration"]

# filters vs quantifiers
plt.figure(0)
plt.xlabel("cvc5 filters")
plt.ylabel("cvc5 quantifiers")
plt.title("cvc5 filters vs quantifiers")
plt.grid(linestyle = '--')
plt.axline((0, 0), slope=1, color="red")
plt.scatter(filters, quantifiers, marker = '+')
plt.legend(['y=x', 'seconds'])
plt.savefig("filters_vs_quantifiers.svg", bbox_inches='tight')

plt.figure(1)
labels = ['cvc5 filters', 'cvc5 quantifiers']
plt.ylabel('seconds')
plt.title("cvc5 filters vs quantifiers")
bplot = plt.boxplot([filters, quantifiers], labels=labels)  
plt.savefig("cvc5_box_plot.svg", bbox_inches='tight')

# filters vs z3
plt.figure(2)
df = pd.read_csv('filters.csv',header=0)
filters = df["duration"]
df = pd.read_csv('../LEGOS/Sleec/z3.csv',header=0)
z3 = df["duration"]
plt.xlabel("cvc5 filters")
plt.ylabel("z3 qf formulas")
plt.title("cvc5 filters vs z3 qf formulas")
plt.grid(linestyle = '--')
plt.axline((0, 0), slope=1, color="red")
plt.scatter(filters, z3, marker = '+')
plt.legend(['y=x', 'seconds'])
plt.savefig("cvc5_vs_z3.svg", bbox_inches='tight')

plt.figure(3)
labels = ['cvc5 filters', 'z3']
plt.ylabel('seconds')
plt.title("cvc5 filters vs z3 qf formulas")
bplot = plt.boxplot([filters, z3], labels=labels)  
plt.savefig("cvc5_vs_z3_box_plot.svg", bbox_inches='tight')


