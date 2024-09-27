#!/bin/bash

# Usage function to display help
usage() {
    echo "Usage: $0 -f <source_file> -o <new_output_filename>"
    echo "  -f <source_file>    : The source file to find in compile_commands.json"
    echo "  -o <new_output_filename>: The new output filename for the compiled object file (placed in the current directory)"
}

# Parse command line arguments
while getopts "f:o:" opt; do
    case "$opt" in
        f) source_file="$OPTARG" ;;
        o) new_output_filename="$OPTARG" ;;
        *) usage ;;
    esac
done

# Check if both arguments are provided
if [ -z "$source_file" ] || [ -z "$new_output_filename" ]; then
    usage
fi

compile_commands="../external_libs/constrained-clustering/compile_commands.json"

# Check if compile_commands.json exists
if [ ! -f $compile_commands ]; then
    echo "Error: compile_commands.json not found!"
fi

# Extract the command using jq
command=$(jq -r --arg src_file "$source_file" '.[] | select(.file | endswith($src_file)) | .command' "$compile_commands")

# Check if the command was found
if [ -z "$command" ]; then
    echo "Error: No command found for source file $source_file"
fi

# Modify the output path in the command
# Extract the original output file path
original_output=$(echo "$command" | grep -oP '(?<=-o )[^ ]+')

# Set the new output path to be in the current directory with the provided filename
new_output_path="$PWD/$new_output_filename"

# Remove the original output path.
new_command=$(echo "$command" | sed "s|-o $original_output ||")

# Insert the -fPIC flag right after the -fopenmp and -c options.
new_command=$(echo "$new_command" | sed 's|-fopenmp -c|-fopenmp -c -fPIC|')

# Add the new output to the end of new command.
new_command=$(echo "${new_command} -o ${new_output_path}")

# Ensure the output directory exists (will be the current directory)
mkdir -p "$(dirname "$new_output_path")"

# Print and execute the new command
echo "Executing: $new_command"
eval "$new_command"