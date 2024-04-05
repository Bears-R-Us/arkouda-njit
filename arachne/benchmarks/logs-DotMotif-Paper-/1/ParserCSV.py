import re
import csv

# Define the path to the directory containing the files (adjust as needed)
directory_path = '.'

# CSV file to store the extracted data
output_csv = 'benchmark_summary.csv'

# Regex patterns to match the necessary lines in the files
patterns = {
    'num_nodes': re.compile(r'num_nodes =\s+(\d+)'),
    'num_edges': re.compile(r'num_edges =\s+(\d+)'),
    'density': re.compile(r'density =\s+([\d.]+)'),
    'arachne_time': re.compile(r'Arachne execution time: ([\d.]+) seconds'),
    'networkx_time': re.compile(r'NetworkX execution time: ([\d.]+) seconds'),
    'dotmotif_time': re.compile(r'DotMotif execution time: ([\d.]+) seconds'),
    'arachne_found': re.compile(r'Arachne found: ([\d.]+) isos'),
    'networkx_found': re.compile(r'NetworkX found: ([\d.]+) isos'),
    'dotmotif_found': re.compile(r'Dotmotif found: ([\d.]+) isos'),
}

# Function to process each file and extract the required information
def process_file(file_path):
    data = {}
    with open(file_path, 'r') as file:
        content = file.read()
        for key, pattern in patterns.items():
            match = pattern.search(content)
            if match:
                # Convert numerical values to float then to int for consistent comparison
                if 'found' in key:  # Applies conversion for the isos found values
                    data[key] = int(float(match.group(1)))
                else:  # Keeps other values as they are
                    data[key] = match.group(1)
    
    # Check for discrepancies in found isos
    isos = {data[k] for k in ['arachne_found', 'networkx_found', 'dotmotif_found']}
    if len(isos) > 1:
        print(f"Error in {file_path}: Discrepancy in found isos - {isos}")
    else:
        # Since all values are the same, we can pick any to represent the found isos count
        data['isos_count'] = next(iter(isos))

    return data

# Main function to iterate through the files and compile the CSV
def compile_data():
    with open(output_csv, 'w', newline='') as csv_file:
        writer = csv.writer(csv_file)
        # Write the header row, now including 'Isos Count'
        writer.writerow(['File', 'Num Nodes', 'Num Edges', 'Density', 'Arachne Execution Time', 'NetworkX Execution Time', 'DotMotif Execution Time', 'Isos Count'])
        
        for i in range(1, 973):
            file_name = f'benchmark_trial_{i}.txt'
            file_path = f'{directory_path}/{file_name}'
            try:
                data = process_file(file_path)
                # Write data rows, now including 'isos_count'
                writer.writerow([
                    file_name,
                    data.get('num_nodes', 'N/A'),
                    data.get('num_edges', 'N/A'),
                    data.get('density', 'N/A'),
                    data.get('arachne_time', 'N/A'),
                    data.get('networkx_time', 'N/A'),
                    data.get('dotmotif_time', 'N/A'),
                    data.get('isos_count', 'N/A'),  # Include isos_count value
                ])
            except FileNotFoundError:
                print(f"File {file_name} not found.")
            except Exception as e:
                print(f"Error processing {file_name}: {e}")


if __name__ == '__main__':
    compile_data()

