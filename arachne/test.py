array_of_integers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]  # Replace this with your array

# Printing the array with 4 numbers per line
for i in range(0, len(array_of_integers), 4):
    line = ' '.join(map(str, array_of_integers[i:i+4]))
    print(line)