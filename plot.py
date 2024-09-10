import matplotlib.pyplot as plt
import pandas as pd

df = pd.read_csv('relations_vs_quantifiers.csv',header=0)
relations = df["relations duration"]
quantifiers = df["quantifiers duration"]

# relations vs quantifiers
plt.figure(0)
plt.xlabel("cvc5 relations")
plt.ylabel("cvc5 quantifiers")
plt.title("cvc5 relations vs quantifiers")
plt.grid(linestyle = '--')
plt.axline((0, 0), slope=1, color="red")
plt.scatter(relations, quantifiers, marker = '+')
plt.legend(['y=x', 'duration'])
plt.savefig("relation_vs_quantifiers.svg", bbox_inches='tight')

plt.figure(1)
labels = ['cvc5 relations', 'cvc5 quantifiers']
plt.ylabel('seconds')
plt.title("cvc5 relations vs quantifiers")
bplot = plt.boxplot([relations, quantifiers], labels=labels)  
plt.savefig("cvc5_box_plot.svg", bbox_inches='tight')

# relations vs z3
plt.figure(2)
df = pd.read_csv('relations.csv',header=0)
relations = df["duration"]
df = pd.read_csv('../LEGOS/Sleec/z3.csv',header=0)
z3 = df["duration"]
plt.xlabel("cvc5 relations")
plt.ylabel("z3 qf formulas")
plt.title("cvc5 relations vs z3 qf formulas")
plt.grid(linestyle = '--')
plt.axline((0, 0), slope=1, color="red")
plt.scatter(relations, z3, marker = '+')
plt.legend(['y=x', 'duration'])
plt.savefig("cvc5_vs_z3.svg", bbox_inches='tight')

plt.figure(3)
labels = ['cvc5 relations', 'z3']
plt.ylabel('seconds')
plt.title("cvc5 relations vs z3 qf formulas")
bplot = plt.boxplot([relations, z3], labels=labels)  
plt.savefig("cvc5_vs_z3_box_plot.svg", bbox_inches='tight')


