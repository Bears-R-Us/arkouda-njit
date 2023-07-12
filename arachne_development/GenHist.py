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
data = pd.read_csv(filename, sep=' ', header=None)

#plt.figure()
#plt.tight_layout()
plt.rcParams.update({'font.size': FontSize})
ax=data.hist(column=1,bins=1000)

#ax.legend(["Contour","FastSV", "ConnectIt","C-1","C-2","C-Syn"])
plt.yscale('log',base=2) 

plt.subplots_adjust(bottom=0.19)
plt.ylabel("Number of Degrees")
plt.xlabel("Degree")
plt.title("Histogram of Degrees")
plt.savefig(filename+"-Hist.png")
plt.show()
plt.close()

