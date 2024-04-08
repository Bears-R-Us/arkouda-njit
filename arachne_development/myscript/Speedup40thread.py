#import tkinter
#import matplotlib
#matplotlib.use('TkAgg')
#matplotlib.use('Agg')
import matplotlib.pyplot as plt

import copy

import numpy as np
import pandas as pd
import sys

FontSize=16

# Check if a filename argument is provided
if len(sys.argv) < 2:
    print("Please provide a filename as an argument.")
    sys.exit(1)

# Get the filename from the command-line argument
filename = sys.argv[1]

# Read the text file
data = pd.read_csv(filename,sep=' ', header=None)

# Extract the graph name
graph_name = data[0]

iteration_numbers = data.iloc[:, 0:8]
iteration_numbers.index=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
print(iteration_numbers)
plt.rcParams.update({'font.size': FontSize})
ax=iteration_numbers.plot.bar(rot=0, figsize=(20, 5))

ax.legend(["FastSV", "ConnectIt","C-1m1m","C-1","C-2","C-m", "C-11mm","C-Syn"],ncol=2,loc="lower right")
plt.yscale('log',base=2) 

plt.subplots_adjust(bottom=0.19)
plt.ylabel("Speedup")
plt.xlabel("Graph ID")
plt.title("Speedup achieved using 40 threads compared to a single thread")
plt.savefig(filename+"-Speedup40.png")
plt.show()
plt.close()

