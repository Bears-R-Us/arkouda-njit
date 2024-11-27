import re
import pandas as pd
import matplotlib.pyplot as plt



# Define the file name
file_name = "cit_patent.txt"

# Update the pattern to ensure correct extraction
pattern = re.compile(
    r"Size:\s+(\d+).*?"
    r"Cluster Volume:\s+(\d+).*?"
    r"Cluster cutedges:\s+(\d+).*?"
    r"Conductance:\s+([\d.]+).*?"
    r"Lower:\s+([\d.]+).*?"
    r"Upper:\s+([\d.]+).*?"
    r"Internal edges:\s+(\d+).*?"
    r"Conn value:\s+([\d.]+).*?"
    r"Final Gap:\s+([\d.]+).*?"
    r"Cut size:\s+(\d+).*?"
    r"Cluster 1 size:\s+(\d+).*?"
    r"Cluster 2 size:\s+(\d+)",
    re.DOTALL,
)

# Read the file and extract the data
with open(file_name, 'r') as file:
    content = file.read()

# Find all matches
matches = pattern.findall(content)

# Convert matches to a DataFrame
columns = [
    "Size",
    "Cluster Volume",
    "Cluster cutedges",
    "Conductance",
    "Lower",
    "Upper",
    "Internal edges",
    "Conn value",
    "Final Gap",
    "Cut size",
    "Cluster 1 size",
    "Cluster 2 size",
]
data = pd.DataFrame(matches, columns=columns)

# Convert data to appropriate types
data = data.astype({
    "Size": int,
    "Cluster Volume": int,
    "Cluster cutedges": int,
    "Conductance": float,
    "Lower": float,
    "Upper": float,
    "Internal edges": int,
    "Conn value": float,
    "Final Gap": float,
    "Cut size": int,
    "Cluster 1 size": int,
    "Cluster 2 size": int,
})

# Check and swap Cluster 1 and Cluster 2 sizes if needed
data["Cluster 1 size"], data["Cluster 2 size"] = zip(
    *data.apply(
        lambda row: (max(row["Cluster 1 size"], row["Cluster 2 size"]),
                     min(row["Cluster 1 size"], row["Cluster 2 size"])),
        axis=1
    )
)

# Save to CSV
output_csv = "cluster_analysis_cit_patent.csv"
data.to_csv(output_csv, index=False)
print(f"Data has been saved to {output_csv}.")


# Conductance Distribution Histogram with 0.1 step
plt.figure(figsize=(10, 6))
plt.hist(data["Conductance"], bins=[i * 0.1 for i in range(0, int(data["Conductance"].max() * 10) + 1)], 
         alpha=0.7, color="orange", edgecolor="black")
plt.title("Distribution of Conductance")
plt.xlabel("Conductance")
plt.ylabel("Frequency")
plt.xticks(ticks=[i * 0.1 for i in range(0, int(data["Conductance"].max() * 10) + 1)], rotation=45)
plt.grid(True)
plt.savefig("conductance_distribution_fixed.png")
print("Conductance distribution plot with fixed range saved as 'conductance_distribution_fixed.png'.")
plt.show()

# Adjusted Cluster Size Distribution Histogram
plt.figure(figsize=(10, 6))
cluster_size_bins = range(0, data["Size"].max() + 50, 50)  # Bins every 50 units
plt.hist(data["Size"], bins=cluster_size_bins, alpha=0.7, color="green", edgecolor="black")
plt.title("Distribution of Cluster Sizes")
plt.xlabel("Cluster Size")
plt.ylabel("Frequency")
plt.xticks(rotation=45)
plt.grid(True)
plt.savefig("cluster_size_distribution_adjusted.png")
print("Cluster size distribution plot with adjusted range saved as 'cluster_size_distribution_adjusted.png'.")
plt.show()

# Adjusted Gap Distribution Histogram
plt.figure(figsize=(10, 6))
gap_bins = range(0, int(data["Final Gap"].max()) + 2)  # Bins every 1 unit for smaller range
plt.hist(data["Final Gap"], bins=gap_bins, alpha=0.7, color="blue", edgecolor="black")
plt.title("Distribution of Final Gap")
plt.xlabel("Final Gap")
plt.ylabel("Frequency")
plt.xticks(rotation=45)
plt.grid(True)
plt.savefig("gap_distribution_adjusted.png")
print("Gap distribution plot with adjusted range saved as 'gap_distribution_adjusted.png'.")
plt.show()
