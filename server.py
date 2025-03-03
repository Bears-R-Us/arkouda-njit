def main():
    unique_numbers = set()

    # Open the file in read mode
    with open("server7.txt", "r") as file:
        for line in file:
            # Check if the line contains "binary:"
            if "binary:" in line:
                # Split the line at the colon
                parts = line.strip().split(":")
                if len(parts) > 1:
                    try:
                        # Convert the part after the colon to an integer and add it to the set
                        number = int(parts[-1].strip())
                        unique_numbers.add(number)
                    except ValueError:
                        # Skip lines that don't have a valid integer after the colon
                        continue

    # Convert the set to a sorted list for readability
    unique_numbers_sorted = sorted(unique_numbers)
    
    # Print the unique numbers and their count
    print("Unique numbers:", unique_numbers_sorted)
    print("Count of unique numbers:", len(unique_numbers_sorted))


if __name__ == "__main__":
    main()
