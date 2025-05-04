#!/bin/bash

# Set the directory name
DIR="normalized_RYT"
OUTPUT="results_${DIR}.txt"
TIMEOUT=60  # 5 minutes in seconds

# Write the CSV header to the output file.
echo "file, edusat, roundingsat" > "$OUTPUT"

# Check if the specified directory exists.
if [ ! -d "$DIR" ]; then
    echo "Error: Directory $DIR not found."
    exit 1
fi

# Function to run a command with timeout
run_with_timeout() {
    local command="$1"
    local timeout_duration="$2"
    local output_file="$3"

    # Use a subshell to run the command
    (
        # Run the command
        eval "$command" > "$output_file" 2>&1
    ) &

    local pid=$!

    # Wait for the specified timeout
    sleep "$timeout_duration"

    # Check if the process is still running
    if kill -0 "$pid" 2>/dev/null; then
        # If still running, kill the process
        kill -9 "$pid" 2>/dev/null
        return 1  # Indicate timeout
    fi

    # Wait for the process and get its exit status
    wait "$pid"
    return $?
}

# Loop through all .opb files in the directory.
for input in "$DIR"/*.opb; do
    # Skip if there are no matching files.
    [ -e "$input" ] || continue

    # Get the base filename.
    filename=$(basename "$input")
    echo "Processing file: $filename"

    # Run edusat with timeout
    if run_with_timeout "./edusat '$input'" "$TIMEOUT" "edusat_output.txt"; then
        edusat_result=$(tail -n 1 "edusat_output.txt")
    else
        edusat_result="TIMEOUT"
    fi

    # Run roundingsat with timeout
    if run_with_timeout "./roundingsat '$input'" "$TIMEOUT" "roundingsat_output.txt"; then
        roundingsat_result=$(tail -n 1 "roundingsat_output.txt")
    else
        roundingsat_result="TIMEOUT"
    fi

    # Append a CSV-formatted line to the output file.
    echo "$filename, $edusat_result, $roundingsat_result" >> "$OUTPUT"

    # Clean up temporary output files
    rm -f edusat_output.txt roundingsat_output.txt
done

echo "Results written to $OUTPUT"