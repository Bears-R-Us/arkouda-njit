import re
from collections import defaultdict

def parse_file(filename):
    # Dictionary to store the values of each parameter
    parameters = defaultdict(list)
    
    # Regular expression to match the pattern
    pattern = re.compile(r'(First_state_Tin\d+|First_state_Tout\d+|Tin\d+|Tout\d+)\s*size\s*=\s*(\d+)')
    
    # Read the file and extract the values
    with open(filename, 'r') as file:
        for line in file:
            match = pattern.search(line)
            if match:
                param = match.group(1)
                value = int(match.group(2))
                parameters[param].append(value)
    
    return parameters

def calculate_means(parameters):
    # Dictionary to store the mean values
    means = {}
    
    for param, values in parameters.items():
        count = len(values)
        mean_value = sum(values) / count if count > 0 else 0
        means[param] = (count, mean_value)
    
    return means

def print_results(means):
    for param, (count, mean) in means.items():
        print(f'{param} appears {count} times with a mean value of {mean:.2f}')

if __name__ == "__main__":
    # Replace 'output.txt' with the path to your text file
    filename = 'arkouda_0.05_500.txt'
    
    parameters = parse_file(filename)
    means = calculate_means(parameters)
    print_results(means)
