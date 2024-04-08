import pandas as pd
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

# Load the data
df = pd.read_csv('benchmark_summary.csv')

# Convert execution times to numeric, as they might be read as strings
df['Arachne Execution Time'] = pd.to_numeric(df['Arachne Execution Time'], errors='coerce')
df['NetworkX Execution Time'] = pd.to_numeric(df['NetworkX Execution Time'], errors='coerce')
df['DotMotif Execution Time'] = pd.to_numeric(df['DotMotif Execution Time'], errors='coerce')

# Divide 'Num Edges' by 1000 for display purposes
df['Num Edges'] /= 1000

# Plotting
plt.figure(figsize=(10, 6))

# Plot each execution time by number of edges (scaled)
plt.scatter(df['Num Edges'], df['Arachne Execution Time'], color='red', alpha=0.5, label='Arachne')
plt.scatter(df['Num Edges'], df['NetworkX Execution Time'], color='blue', alpha=0.5, label='NetworkX')
plt.scatter(df['Num Edges'], df['DotMotif Execution Time'], color='green', alpha=0.5, label='DotMotif')

# Adding labels and title
plt.xlabel('Number of Edges (in thousands)')
plt.ylabel('Execution Time (seconds)')
plt.title('Execution Time by Number of Edges')

# Adjust x-axis to show intervals of 2 (from 0 onwards)
plt.xticks(range(0, int(max(df['Num Edges'])) + 2, 2))

# Use a fixed locator for x-axis to ensure ticks are shown correctly
plt.gca().xaxis.set_major_locator(ticker.MultipleLocator(2))

plt.legend()

# Add grid
plt.grid(True, which='both', linestyle='--', linewidth=0.5)

# Show plot
plt.show()

