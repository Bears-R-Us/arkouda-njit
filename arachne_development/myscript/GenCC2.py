#import tkinter
#import matplotlib
#matplotlib.use('TkAgg')
#matplotlib.use('Agg')
import matplotlib.pyplot as plt

import copy

import numpy as np
import pandas as pd
import sys

FontSize=26

# Check if a filename argument is provided
if len(sys.argv) < 2:
    print("Please provide a filename as an argument.")
    sys.exit(1)

# Get the filename from the command-line argument
filename = sys.argv[1]

# Read the text file
data = pd.read_csv(filename, sep=' ', header=None)

# Extract the graph name
graph_name = data[0]

# Extract iteration numbers
iteration_numbers = data.iloc[:, 1:9]
iteration_numbers.index=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]

print(iteration_numbers)
#bakdata=copy.deepcopy(iteration_numbers)
# reorder the data
'''
iteration_numbers[1]=bakdata[3]
iteration_numbers[2]=bakdata[1]
iteration_numbers[3]=bakdata[7]
iteration_numbers[4]=bakdata[5]
iteration_numbers[5]=bakdata[6]
iteration_numbers[6]=bakdata[4]
'''
#print(iteration_numbers)
# remove data will not be shown in the paper
#iteration_numbers.drop(iteration_numbers.columns[[6,7]], axis=1, inplace=True )
#print(iteration_numbers)
#iters=iteration_numbers.to_numpy()
#x = np.arange(1,9)  # the label locations

#plt.figure()
#plt.tight_layout()
plt.rcParams.update({'font.size': FontSize})
ax=iteration_numbers.plot.bar(rot=0, figsize=(30, 8))

ax.legend(["FastSV", "ConnectIt","C-1m1m","C-1","C-2","C-m", "C-11mm","C-Syn"],ncol=3)
plt.yscale('log',base=2) 
#ax.set_yscale('symlog', basey=2)

#plt.subplots_adjust(bottom=0.19)
plt.ylabel("Number of Iterations")
plt.xlabel("Graph ID")
plt.title("Comparison of Iterations")
plt.savefig(filename+"-IterNum.png")
plt.show()
plt.close()

execution_values = data.iloc[:, 10:18]
print(execution_values)
exetime=execution_values.to_numpy()
pda=pd.DataFrame(exetime,columns = range(1,9))
pda.index=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
print(pda)
'''
bakdata=copy.deepcopy(pda)
pda[1]=bakdata[3]
pda[2]=bakdata[1]
pda[3]=bakdata[7]
pda[4]=bakdata[5]
pda[5]=bakdata[6]
pda[6]=bakdata[4]
pda.drop(pda.columns[[6,7]], axis=1, inplace=True )
print(pda)
'''
#plt.figure()
#plt.tight_layout()
plt.rcParams.update({'font.size': FontSize})
ax=pda.plot.bar(rot=0, figsize=(30, 7.8))
ax.legend(["FastSV", "ConnectIt","C-1m1m","C-1","C-2","C-m", "C-11mm","C-Syn"],ncol=3)
#ax.set_yscale('symlog', basey=10)
plt.yscale('log',base=2) 
plt.ylabel("Execution Time(s)")
#plt.xlabel("Graph ID",fontsize=16)
plt.xlabel("Graph ID")
#plt.legend(ncol=3)
plt.title("Comparison of Execution Time")
#plt.subplots_adjust(bottom=0.19)
plt.savefig(filename+"-ExeTime.png")
plt.show()
plt.close()

'''
bakexetime=bakdata
bakruntime=copy.deepcopy(pda)
print(execution_values)
execution_values[1]=bakruntime[3]
execution_values[2]=bakruntime[1]
execution_values[3]=bakruntime[7]
execution_values[4]=bakruntime[5]
execution_values[5]=bakruntime[6]
execution_values[6]=bakruntime[4]
execution_values.drop(execution_values.columns[[6,7]], axis=1, inplace=True )
print(execution_values)
'''
inverse=1/pda
speedup=inverse.multiply(pda.iloc[:,0], axis=0)
speedup.index=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
print(speedup)
#plt.tight_layout()
plt.rcParams.update({'font.size': FontSize})
ax=speedup.plot.bar(rot=0, figsize=(30, 7))
#ax.legend(["FastSV", "ConnectIt","C-1m1m","C-1","C-2","C-m", "C-11mm","C-Syn"],ncol=4,loc="lower center")
ax.legend(["FastSV", "ConnectIt","C-1m1m","C-1","C-2","C-m", "C-11mm","C-Syn"],ncol=4)
#ax.set_yscale('symlog', basey=2)
#plt.yscale('log',base=2) 
plt.ylabel("Speedup")
plt.xlabel("Graph ID")
plt.title("Speedup Comparison (Baseline:FastSV)")
#plt.legend(ncol=4)
#plt.subplots_adjust(bottom=0.19)
plt.savefig(filename+"-Speedup.png")
plt.show()
plt.close()


all=pd.concat([data, speedup],axis=1)
all.to_csv(filename+"-all.csv")
#all=pd.concat([data, speedup],axis=1)
#all.to_excel(filename+"-all.xlsx")

inverse2=1/pda
speedup2=inverse.multiply(pda.iloc[:,1], axis=0)
speedup2.index=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
print(speedup2)
speedup2.drop(speedup2.columns[[0,7]], axis=1, inplace=True )
#plt.tight_layout()
plt.rcParams.update({'font.size': FontSize})
#ax=speedup2.plot.bar(rot=0, figsize=(24, 10))
ax=speedup2.plot.bar(rot=0, figsize=(30, 7))
#ax.legend(["FastSV", "ConnectIt","C-1m1m","C-1","C-2","C-m", "C-11mm","C-Syn"],ncol=4,loc="lower center")
ax.legend(["ConnectIt","C-1m1m","C-1","C-2","C-m", "C-11mm"],ncol=3)
#ax.set_yscale('symlog', basey=2)
#plt.yscale('log',base=2) 
plt.ylabel("Speedup")
plt.xlabel("Graph ID")
plt.title("Speedup Comparison (Baseline:ConnectIt)")
#plt.legend(ncol=4)
#plt.subplots_adjust(bottom=0.19)
plt.savefig(filename+"-Speedup2.png")
plt.show()
plt.close()
