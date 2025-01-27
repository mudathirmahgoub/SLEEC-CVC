import matplotlib.pyplot as plt
import pandas as pd
import numpy as np
import math
# Read data from CSV file
files = ['data1.csv','data2.csv', 'data3.csv', 'data4.csv']

plt.figure()

for file in files:    

    data = pd.read_csv(file)

    # List of solver names (columns after the first column)
    solvers = data.columns[1:]

    # Sort and plot the cumulative performance with log scale for each solver
    for solver in solvers:
        performance = np.sort(data[solver])
        # cumulative_performance = np.cumsum(performance)
        cumulative_performance = performance
        plt.step(cumulative_performance, range(1, len(cumulative_performance) + 1), label=solver)

# Set logarithmic scale
plt.xscale('log')
# plt.yscale('log')

# Set labels and title
plt.xlabel('Time (seconds)')
plt.ylabel('# of Instances')
# plt.title('Cactus Plot')

# Add a legend
plt.legend()

# Display grid
# plt.grid(True, which="both", ls="--")

# Show the plot
plt.show()
